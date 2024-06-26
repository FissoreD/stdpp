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
import matplotlib.pyplot as plt
import numpy as np

# Rows to filter
F_ELPI_QUERY = "Elpi: query"
F_ELPI_GET_AND_COMPILE = "Elpi: get_and_compile"
F_ELPI_TC = "\[TC\] - Time"
F_COMPILE = "COQC .*.v"
F_TIMING = "Chars" # Lines printed by coq when -time || TIMING=1 is active

L_TIME_ELPI = "ELPI TIME" # The time printed by TIMING=1 on a compilation using elpi solver
L_TIME_COQ = "COQ_TIME"   # The time printed by TIMING=1 on a compilation using coq
TOTAL = "TOTAL"           # The sum of everything

# Substrings to find in filtered lines
L_COMPILE = "Compiler for Instance,Compiler for Class,Compile Instance,build query,compile context, normalize ty,resolve_all_evars".split(",")
L_ELPI_TC = "mode check,refine.typecheck,msolve,full instance search, instance search".split(",")
L_ELPITIME = "query-compilation,static-check,optimization,runtime".split(",")
L_ELPI_GET_AND_COMPILE = "get_and_compile"
ALL_KEYS = L_COMPILE + L_ELPI_TC + L_ELPITIME
L_TOT_MINUS_ELPITIME = "elpitot - elpitime"   # Time computed as de difference between L_TIME_ELPI and the sum of L_ELPI_GET_AND_COMPILE + L_ELPITIME

FAIL = "fail"
WITH_FAIL = False

def normalize_elpi_override(l):
    elpi_ov = "Elpi~Overrid"
    return re.sub(f"{elpi_ov}.*\]", elpi_ov + "]", l)

def make_rex(s): return rf".*{s}.*"

def match_rex(s, l): return re.match(make_rex(s), l)

def valid_line(l):
    return re.match(rf".*({F_ELPI_QUERY}|{F_ELPI_TC}|{F_COMPILE}).*", l)

def normalize_line(f):
    return normalize_elpi_override(f.replace("\"", ""))

def read_file(f):
    with open(f) as F:
        return [normalize_line(i) for i in F.readlines()]

def get_floats(s): return list(map(float, re.findall(r"[-+]?(?:\d*\.*\d+)", s)))

def normalize_fname(fname):
    return fname.split('/')[-1].replace("\n", "").split(".")[0]

"""
A dict d associates a file name to a dictionary d'
    d' associates to each line of file (printed by the option TIMING=1) a dict d''
        d'' associates to each stat its total time.

Moreover:
 - the dict has a special key TOTAL, containing the sum of all the stats
   of all files.
 - for each file, d' has a special key TOTAL, containing the sum of the stats of the file

An example of dict could be:
{
    "stdpp/base.v": {
        "Char 400 - 1000 ...":{
            "ELPI TIME" : 50,
            "COQ TIME" : 30,
            "Compile Instance": 30,
            "Compile Goal": 20,
            ...
        },
        "Char 1020 ....":{
            ....
        },
        "TOTAL":{
            ELPI TIME: ...
        }
    },
    "stdpp/option.v":{
        ...
    },
    ...
    "TOTAL": {
        ...
    }
}
"""
def add_dico(d, ch, k1, k2, v):
    chD = d.get(ch, dict())
    x = chD.get(k1, dict())
    x[k2] = x.get(k2, 0) + v
    chD[k1] = x
    d[ch] = chD

def build_fail_key(msg): return f"{msg} {FAIL}"

def clean_time_row(l): return l[:(l.index("] "))]

"""
retrieves all the times in a log file containing the stats of
the compilation in coq where the option TIMING=1 is active
"""
def get_time_f2(f2):
    try: 
        return {clean_time_row(i): get_floats(i)[-3] for i in read_file(f2) if match_rex(F_TIMING, i)}
    except FileNotFoundError:
        return dict()

def build_next_rows(lines):
    all_rows = {}
    old_pos = 0
    for pos,i in enumerate(lines):
        if match_rex(F_TIMING, i):
            i = clean_time_row(i)
            all_rows[old_pos] = i
            old_pos = pos
    return all_rows

def get_stat_without_elpi(ch, rows_f2):
    return rows_f2[ch] #.get(ch, 0)

def get_stats(lines, f2=dict()):
    d = dict()
    def add_dico_aux(fname, row_name, label, v):
        add_dico(d, fname, row_name, label, v)
        add_dico(d, fname, TOTAL, label, v)
        add_dico(d, TOTAL, TOTAL, label, v)
    all_rows = build_next_rows(lines)
    def next_row(r):
        return all_rows.get(r, "") # [r]
    fname = ""
    row_name = ""
    row_pos = 0
    for iii,l in enumerate(lines):
        fl = get_floats(l)
        if match_rex(F_COMPILE, l):
            fname = normalize_fname(l)
        elif match_rex(F_TIMING, l) and fname != "options":
            l = normalize_elpi_override(l)
            row_name = clean_time_row(l)
            row_pos = iii
            add_dico_aux(fname, row_name, L_TIME_ELPI, fl[-3])
            add_dico_aux(fname, row_name, L_TIME_COQ, get_stat_without_elpi(row_name, f2))
            add_dico_aux(fname, row_name, L_TOT_MINUS_ELPITIME, fl[-3])
        elif F_ELPI_QUERY in l:
            row_name1 = next_row(row_pos)
            assert(len(fl) == 4)
            for i, k in enumerate(L_ELPITIME):
                add_dico_aux(fname, row_name1, k, fl[i])
                add_dico_aux(fname, row_name1, L_TOT_MINUS_ELPITIME, -fl[i])

        elif match_rex(F_ELPI_TC, l):
            row_name1 =  next_row(row_pos)
            for k in L_COMPILE:
                if k in l:
                    add_dico_aux(fname, row_name1, k, fl[0])
                    break
            for k in L_ELPI_TC:
                if k in l:
                    k = build_fail_key(k) if WITH_FAIL and FAIL in l else k
                    assert(len(fl) == 1)
                    add_dico_aux(fname, row_name1, k, fl[0])
                    break
        elif match_rex(F_ELPI_GET_AND_COMPILE, l):
            row_name1 = next_row(row_pos)
            add_dico_aux(fname, row_name1, L_ELPI_GET_AND_COMPILE, fl[0]) 
            add_dico_aux(fname, row_name1, L_TOT_MINUS_ELPITIME, -fl[0])
    return d

def write_all_to_dico(d, fname="stat.csv"):
    with open(fname, 'w') as f:
        all_keys = list(L_COMPILE + L_ELPI_TC + [L_ELPI_GET_AND_COMPILE])
        all_keys.extend(L_ELPITIME)
        if WITH_FAIL:
            for i in L_ELPI_TC: 
                all_keys.append(build_fail_key(i))
        all_keys.extend([L_TOT_MINUS_ELPITIME, L_TIME_ELPI, L_TIME_COQ])
        f.write("fname," + ",".join(all_keys) + "\n")
        for k in d:
            v = d[k][TOTAL] if TOTAL in d[k] else dict()
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
    all_keys = list(L_COMPILE + L_ELPI_TC + L_ELPITIME + [L_ELPI_GET_AND_COMPILE, L_TOT_MINUS_ELPITIME, L_TIME_ELPI, L_TIME_COQ])
    for fname in d:
        if fname == "option": continue
        with open(path + fname + ".csv", "w") as f:
            f.write("code line," + ",".join(all_keys) + "\n")
            r = d[fname]
            kk = sorted(r.keys(), key=cmp_to_key(compare))
            for v in kk:
                v1 = v.replace(",","").replace("\"","")
                f.write("{}".format(v1))
                for i in all_keys:
                    f.write(",")
                    if i in r[v]:
                        f.write("{:.4f}".format(r[v][i]))
                f.write("\n")

def all_files_to_plot(d, plot_name="plot.svg"):
    def compare(x, y):
        try:
            return d[y][TOTAL][L_TIME_ELPI] - d[x][TOTAL][L_TIME_ELPI]
        except KeyError:
            return 0
    fnames = list(d.keys())
    fnames = sorted(fnames, key=cmp_to_key(compare))
    # fnames = [TOTAL]
    # cols = list(reversed(L_ELPITIME)) + [L_ELPI_GET_AND_COMPILE, L_TIME_ELPI]
    cols = [L_TOT_MINUS_ELPITIME] + list(reversed(L_ELPITIME)) + [L_ELPI_GET_AND_COMPILE, L_TIME_ELPI]
    d1 = {}

    for coli,col in enumerate(cols) :
        d1[col] = []
        for fnamei, fname in enumerate(fnames):
            d11 = d[fname][TOTAL] if TOTAL in d[fname] else dict()
            if col != L_TIME_ELPI:
                old_sum = d1[cols[coli-1]][fnamei] if coli > 0 else 0
            else:
                old_sum = 0
            new_sum = old_sum + (d11.get(col, 0))
            d1[col].append(new_sum)

    coq_t = []
    for fname in fnames:
        d11 = d[fname][TOTAL][L_TIME_COQ] if TOTAL in d[fname] and L_TIME_COQ in d[fname][TOTAL] else 0
        coq_t.append(d11)

    x = np.arange(len(fnames))  # the label locations
    width = 0.2  # the width of the bars
    multiplier = 0

    fig, ax = plt.subplots()
    bar_colors = ['red', 'blue', 'orange', 'green', "silver", 'yellow', "tan", "black", ]

    for i,attribute in enumerate(reversed(cols)):
        measurement = d1[attribute]
        rects = ax.bar(x, measurement, width, label=attribute, color=bar_colors[i])
        if attribute == L_TIME_ELPI:
            ax.bar_label(rects, padding=3)
        multiplier += 1
    rects = ax.bar(x+width, coq_t, width, label=L_TIME_COQ)
    ax.bar_label(rects, padding=3)

    # Add some text for labels, title and custom x-axis tick labels, etc.
    ax.set_ylabel('Time')
    ax.set_title('Stats')
    ax.set_xticks(x + width, fnames, rotation="vertical")
    # ax.legend(loc='upper left', ncols=len(L_ELPITIME))
    ax.legend(loc='upper center', bbox_to_anchor=(0.5, 1.05),
            ncol=len(cols)+1, fancybox=True, shadow=True)

    ax.set_ylim(-2, 25)
    fig.set_size_inches(20,15)
    # print(fig.get_size_inches())
    plt.savefig(plot_name, format="svg")
    plt.show()
    

if __name__ == "__main__":
    f1 = sys.argv[1]
    f2 = sys.argv[2] if len(sys.argv) > 2 else ""
    lines = read_file(sys.argv[1])
    d = get_stats(lines, get_time_f2(f2))
    write_all_to_dico(d)
    stat_per_file(d)
    all_files_to_plot(d)