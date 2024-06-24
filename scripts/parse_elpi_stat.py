"""
Reads all the stats printed by the elpi solver when the following lines are provided

Global Set Debug "elpitime".
Elpi Accumulate tc.db lp:{{
  :after "0"
  time-aux _ Msg Time :- !,
  coq.debug "[TC] Benching - Time of" Msg "is" Time. 
}}.

In particular it filters and prints the stats of all the lines
starting with 
- Elpi: query
- [TC] - Time
- COQC
"""

import re, sys, os
from functools import cmp_to_key

elpi_time = "Elpi: query"
tc_time = "\[TC\] - Time"
stdpp_file = "COQC .*.v"
chars = "Chars"
CHAR_ELPI = "ELPI TIME"
CHAR_COQ = "COQ_TIME"
total = "TOTAL"

FAIL = "fail"
WITH_FAIL = False

def normalize_elpi_override(l):
    elpi_ov = "Elpi~Override"
    if elpi_ov in l:
        return re.sub(f"{elpi_ov}.*\]", elpi_ov + "]", l)
    return l

def make_rex(s): return rf".*{s}.*"

def match_rex(s, l): return re.match(make_rex(s), l)

def valid_line(l):
    return re.match(rf".*({elpi_time}|{tc_time}|{stdpp_file}).*", l)

def filter_lines(f):
    with open(f) as F:
        return [i.replace("\"", "") for i in F.readlines()]

def get_floats(s): return list(map(float, re.findall(r"[-+]?(?:\d*\.*\d+)", s)))

"""
A dict d associates a file name to a dictionary d'
    d' associates to each stat its total time.

An example of dict could be:
{
    "stdpp/base.v": {
        "Compile Instance": 30,
        "Compile Goal": 20,
        ...
    },
    "stdpp/option.v":{
        ...
    },
    ...
}
"""
def add_dico(d, ch, k1, k2, v):
    chD = d.get(ch, dict())
    x = chD.get(k1, dict())
    x[k2] = x.get(k2, 0) + v
    chD[k1] = x
    d[ch] = chD

keysCompile = "Compiler for Instance,Compiler for Class,Compile Instance,build query,compile context, normalize ty".split(",")
keys_tc = "mode check,refine.typecheck,msolve,full instance search, instance search".split(",")
keys_elpitime = "query-compilation,static-check,optimization,runtime".split(",")
all_keys = keysCompile + keys_tc + keys_elpitime

def build_fail_key(msg): return f"{msg} {FAIL}"

def get_time_f2(f2):
    try: 
        with open(f2) as F:
            l = F.readlines()
            d = dict ()
            for i in l:
                fl = get_floats(i)
                if match_rex(chars, i):
                    i = normalize_elpi_override(i)
                    ch = i[:(i.index("] "))]
                    d[ch.replace("\"", "")] = fl[-3]
            return d
    except FileNotFoundError:
        return dict()

def get_stat_without_elpi(ch, rows_f2):
    try:
        return rows_f2[ch] #.get(ch, -1)
    except KeyError:
        print(list(rows_f2.keys()))
        return rows_f2[ch] 

def get_stats(lines, f2=dict()):
    d = dict()
    f = ""
    ch = ""
    for l in lines:
        fl = get_floats(l)
        if match_rex(stdpp_file, l):
            f = normalize_fname(l)
        elif match_rex(chars, l) and f != "options":
            l = normalize_elpi_override(l)
            ch = l[:(l.index("] "))]
            add_dico(d, f, ch, CHAR_ELPI, fl[-3])
            add_dico(d, f, ch, CHAR_COQ, get_stat_without_elpi(ch, f2))
            add_dico(d, f, total, CHAR_ELPI, fl[-3])
            add_dico(d, f, total, CHAR_COQ, get_stat_without_elpi(ch, f2))
            add_dico(d, total, "", CHAR_ELPI, fl[-3])
            add_dico(d, total, "", CHAR_COQ, get_stat_without_elpi(ch, f2))
        elif elpi_time in l:
            assert(len(fl) == 4)
            for i, k in enumerate(keys_elpitime):
                add_dico(d, f, ch, k, fl[i])
                add_dico(d, f, total, k, fl[i])
                add_dico(d, total, "", k, fl[i])
        else:
            for k in keysCompile:
                if k in l:
                    add_dico(d, f, ch, k, fl[0])
                    add_dico(d, f, total, k, fl[0])
                    add_dico(d, total, "", k, fl[0])
                    break
            for k in keys_tc:
                if k in l:
                    k = build_fail_key(k) if WITH_FAIL and FAIL in l else k
                    assert(len(fl) == 1)
                    add_dico(d, f, ch, k, fl[0])
                    add_dico(d, f, total, k, fl[0])
                    add_dico(d, total, "", k, fl[0])
                    break
    return d

def normalize_fname(fname):
    return fname.split('/')[-1].replace("\n", "").split(".")[0]

def write_all_to_dico(d, fname="stat.csv"):
    with open(fname, 'w') as f:
        all_keys = list(keysCompile + keys_tc)
        all_keys.extend(keys_elpitime)
        if WITH_FAIL:
            for i in keys_tc: 
                all_keys.append(build_fail_key(i))
        f.write("fname," + ",".join(all_keys) + "\n")
        for k in d:
            v = d[k][""] if "" in d[k] else dict()
            f.write(k)
            for i in all_keys:
                f.write(",")
                if i in v:
                    f.write("{:.4f}".format(v[i]))
            f.write("\n")

def compare(a, b):
    if get_floats(a) == []: return -1
    if get_floats(b) == []: return 1
    return get_floats(a)[0] - get_floats(b)[0] 

def stat_per_file(d, path="logs/timing-per-file/"):
    os.makedirs(path, exist_ok=True)
    all_keys = list(keysCompile + keys_tc) + [CHAR_ELPI] + [CHAR_COQ]
    for fname in d:
        if fname == "option": continue
        with open(path + fname + ".csv", "w") as f:
            f.write("code line," + ",".join(all_keys) + "\n")
            r = d[fname]
            kk = sorted(r.keys(), key=cmp_to_key(compare))
            for v in kk:
                v1 = v.replace(",","").replace("\"","")
                f.write("{}".format(v1 if v1 != "" else "TOTAL"))
                for i in all_keys:
                    f.write(",")
                    if i in r[v]:
                        f.write("{:.4f}".format(r[v][i]))
                f.write("\n")

if __name__ == "__main__":
    f1 = sys.argv[1]
    f2 = sys.argv[2] if len(sys.argv) > 2 else ""
    lines = filter_lines(sys.argv[1])
    d = get_stats(lines, get_time_f2(f2))
    write_all_to_dico(d)
    stat_per_file(d)