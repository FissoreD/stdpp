import re, sys

elpi_time = "Elpi: query"
tc_time = "\[TC\] - Time"
stdpp_file = "COQC .*.v"

FAIL = "fail"
WITH_FAIL = False

def make_rex(s): return rf".*{s}.*"

def match_rex(s, l): return re.match(make_rex(s), l)

def valid_line(l):
    return re.match(rf".*({elpi_time}|{tc_time}|{stdpp_file}).*", l)

def filter_lines(f):
    with open(f) as F:
        lines = filter(valid_line, F.readlines())
        return list(lines)

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
def add_dico(d, k1, k2, v):
    x = d.get(k1, dict())
    x[k2] = x.get(k2, 0) + v
    d[k1] = x

keysCompile = "Compiler for Instance,Compiler for Class,Compile Instance,build query,compile context, normalize ty".split(",")
keys_tc = "mode check,refine.typecheck,msolve,full instance search, instance search".split(",")
keys_elpitime = "query-compilation,static-check,optimization,runtime".split(",")
all_keys = keysCompile + keys_tc + keys_elpitime

def build_fail_key(msg): return f"{msg} {FAIL}"

def get_stats(lines):
    d = dict()
    total = "TOTAL"
    f = ""
    for l in lines:
        fl = get_floats(l)
        if match_rex(stdpp_file, l):
            f = l
        elif elpi_time in l:
            assert(len(fl) == 4)
            for i, k in enumerate(keys_elpitime):
                add_dico(d, f, k, fl[i])
                add_dico(d, total, k, fl[i])
        else:
            for k in keysCompile:
                if k in l:
                    add_dico(d, f, k, fl[0])
                    add_dico(d, total, k, fl[0])
                    break
            for k in keys_tc:
                if k in l:
                    k = build_fail_key(k) if WITH_FAIL and FAIL in l else k
                    assert(len(fl) == 1)
                    add_dico(d, f, k, fl[0])
                    add_dico(d, total, k, fl[0])
                    break
    return d

def normalize_fname(fname):
    return fname.split('/')[-1].replace("\n", "")

def write_all_to_dico(d, fname="stat.csv"):
    with open(fname, 'w') as f:
        all_keys = list(keysCompile + keys_tc)
        all_keys.extend(keys_elpitime)
        if WITH_FAIL:
            for i in keys_tc: 
                all_keys.append(build_fail_key(i))
        f.write("fname," + ",".join(all_keys) + "\n")
        for k in d:
            v = d[k]
            name = normalize_fname(k)
            f.write(name)
            for i in all_keys:
                f.write(",")
                if i in v:
                    f.write("{:.4f}".format(v[i]))
            f.write("\n")

if __name__ == "__main__":
    lines = filter_lines(sys.argv[1])
    d = get_stats(lines)
    write_all_to_dico(d)