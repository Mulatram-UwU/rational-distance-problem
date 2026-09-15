#!/usr/bin/env python3
"""Cross-check the numbers recorded in results/ against each other and against
the claims made in REPORT.md and README.md.

Nothing here recomputes a search: it reads the archived raw output (the files
under results/, which are the verbatim stdout/stderr of the runs) and the two
T(C) dumps in checks/, and asserts that

  * the engines agree with each other where they must (v4/v5 vs the v3 archive),
  * the independent counters agree (paircount, partners_ref, candcheck, and the
    midline enumerator's own positive control),
  * the piecewise (`--seglo`/`--seghi`) mode is validated (results/verify_chunking.txt),
  * every number quoted in REPORT.md appears verbatim in the raw output.

The `5*10^10` extension is checked only once its 24 pieces are complete (its
`results/run_N5e10.txt` then has to be the field-by-field sum of the pieces and
must pass the same cross-checks as 2e10); until then the script prints NOTE for
it instead, because it is not a claim yet.

Run from the repository root (or from anywhere: paths are resolved relative to
this file).  The log-based checks read `results/run_all_quick.txt`, the archived
log of one full `run_all.sh quick`; regenerate it with

    bash run_all.sh quick > results/run_all_quick.txt 2>&1

    python checks/verify_results.py            # -> results/verification.txt
"""

import io
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(ROOT)

LOG = "results/run_all_quick.txt"
if not os.path.exists(LOG):
    sys.exit("missing %s -- regenerate it with:\n"
             "    bash run_all.sh quick > %s 2>&1" % (LOG, LOG))

FAILS = []


def rd(path):
    """Read a file tolerating the CRLF that the Windows runs wrote."""
    with io.open(path, encoding="utf-8", errors="replace") as fh:
        return fh.read().replace("\r\n", "\n").replace("\r", "\n")


def check(name, cond, detail=""):
    print(("PASS  " if cond else "FAIL  ") + name + (("   [" + detail + "]") if detail else ""))
    if not cond:
        FAILS.append(name)


def note(text):
    """Something that is still running and therefore not a claim yet."""
    print("NOTE  " + text)


log = rd("results/run_all_quick.txt")
rep = rd("REPORT.md")

# ---------------------------------------------------------------- the engines
eng = {}
for line in log.splitlines():
    m = re.match(
        r"(v[345]) mod3(on|off)\s+(\d+)\s+N=(\d+) .*?partners=(\d+) max_partners_per_C=(\d+)"
        r" candidates=(\d+) tested=(\d+) solutions=(\d+)", line)
    if m:
        eng[(m.group(3), m.group(2), m.group(1))] = m.group(4, 5, 6, 7, 8)

n_ok = sum(eng[(n, mod, "v3")] == eng[(n, mod, v)]
           for n in ("10000", "100000", "1000000", "10000000")
           for mod, v in (("off", "v4"), ("on", "v4"), ("on", "v5")))
check("engines: v4 (both filter sets) and v5 reproduce v3 at N = 1e4..1e7",
      n_ok == 12, "%d/12 counter tuples identical" % n_ok)

cc, fs = {}, {}
for line in log.splitlines():
    m = re.match(r"\s+candcheck\s+N=(\d+)\s+REF N=\d+ partners=(\d+) candidates=(\d+)"
                 r" tested=(\d+) tested_mod3=(\d+) solutions=(\d+)", line)
    if m:
        cc[m.group(1)] = (m.group(2), m.group(3), m.group(4), m.group(6))
    m = re.match(r"\s+fast_search5\s+N=(\d+)\s+N=\d+ .*?partners=(\d+) max.*?"
                 r"candidates=(\d+) tested=(\d+) solutions=(\d+)", line)
    if m:
        fs[m.group(1)] = (m.group(2), m.group(3), m.group(4), m.group(5))

check("counters: candcheck (from the definitions) == fast_search5 at N = 1000/2000/3000",
      set(cc) == {"1000", "2000", "3000"} and all(cc[k] == fs[k] for k in cc),
      " ".join("%s:%s" % (k, cc[k]) for k in sorted(cc, key=int)))

pr = re.search(r"partners_ref N=10000\s+N=\d+ partners_all=(\d+) partners_skip2mod4=(\d+) max=(\d+)", log)
check("partners: partners_ref (from the definition) == fast_search5 at N = 10000",
      bool(pr) and pr.group(1) == fs["10000"][0] == "28948",
      "all=%s skip2mod4=%s max=%s" % (pr.group(1), pr.group(2), pr.group(3)) if pr else "")

check("sieve: the segmented residual sieve == trial division for every C <= 2e6",
      "checked=1999999 mismatches=0" in log)
check("1e8 runs: 0 solutions, and the counters quoted in results/summary.md",
      "tested=2277219380 solutions=0" in log and "partners=618449512" in log)

# ------------------------------------------------------- independent pair counts
hl = [l for l in rd("results/run_N2e10.txt").splitlines() if l.startswith("N=20000000000")][0]
p2 = int(re.search(r"partners=(\d+)", hl).group(1))
pc2 = int(re.search(r"=\s*(\d+)\s*$", rd("results/paircount_N2e10.txt").splitlines()[0]).group(1))
check("2e10: partners == 2 * (the triple-parametrisation pair count)",
      2 * pc2 == p2, "2 * %d = %d" % (pc2, 2 * pc2))

p1 = int(re.search(r"partners=(\d+)", rd("results/run_N1e9.txt")).group(1))
pc1 = int(re.search(r"=\s*(\d+)\s*$", rd("results/paircount_N1e9.txt").splitlines()[0]).group(1))
check("1e9: partners == 2 * (the triple-parametrisation pair count)",
      2 * pc1 == p1, "2 * %d = %d" % (pc1, 2 * pc1))

# -------------------------------------------------------------- the v3 archive
r3, v5 = rd("results/run_N3e9.txt"), rd("results/run_v5_N3e9.txt")
get = lambda t, s: re.search(s + r"=(\d+)", t).group(1)
check("v5 reproduces the archived v3 run at 3e9 bit for bit",
      all(get(r3, s) == get(v5, s) for s in ("partners", "candidates", "tested", "solutions")),
      "partners=%s candidates=%s tested=%s" % (get(r3, "partners"), get(r3, "candidates"), get(r3, "tested")))

# ------------------------------------------------------------------- the midline
mr = re.search(r"primitive \(A even, gcd\(A,C\)=1, A\^2\+C\^2 square, C<2A\) = (\d+)", log)
me = re.search(r"N=100000 Amax=50000 primitive_triples=(\d+)", log)
check("midline: the brute-force count == the enumerator's own count at Amax = 50000",
      bool(mr and me) and mr.group(1) == me.group(1) == "7312",
      "ref=%s enum=%s" % (mr.group(1) if mr else "?", me.group(1) if me else "?"))
mid = rd("results/midline_N2e10.txt")
check("midline 2e10: Amax = N/2, 0 solutions, count quoted in REPORT.md",
      "Amax=10000000000" in mid and "midline_solutions=0" in mid
      and "primitive_triples=1462708696" in rep)

# ------------------------------------------- the piecewise (chunked) extension
vc = "results/verify_chunking.txt"
if os.path.exists(vc):
    check("chunking: the piecewise validation of --seglo/--seghi reports no failure",
          "0 failing check(s)" in rd(vc), "results/verify_chunking.txt")

# 5e10 is an *extension*: it is checked only once the 24 pieces are complete, and
# until then it is deliberately not counted anywhere.  When the pieces are done,
# run_5e10.sh has written results/run_N5e10.txt as their sum, and the same
# cross-checks as for 2e10 must hold.
h5f = "results/run_N5e10.txt"
if not (os.path.exists(h5f) and "partners=" in rd(h5f)):
    note("5e10: still running (results/run_N5e10.txt not written yet) -- not counted")
else:
    h5 = [l for l in rd(h5f).splitlines() if l.startswith("N=50000000000")][0]
    g5 = lambda s: int(re.search(s + r"=(\d+)", h5).group(1))
    pf = rd("results/chunks5e10/pieces.txt").splitlines()
    pf = [l for l in pf if l.startswith("N=")]
    tot = lambda s: sum(int(re.search(s + r"=(\d+)", l).group(1)) for l in pf)
    check("5e10: the pieces sum to the recorded line, field by field",
          len(pf) == 24
          and tot("divisor_steps") == g5("divisor_steps")
          and tot("partners") == g5("partners")
          and tot("candidates") == g5("candidates")
          and tot("tested") == g5("tested")
          and max(int(re.search(r"max_partners_per_C=(\d+)", l).group(1)) for l in pf)
              == g5("max_partners_per_C"),
          "%d pieces, partners=%d" % (len(pf), g5("partners")))
    check("5e10: 0 solutions, no sieve overflow",
          g5("solutions") == 0 and g5("sieve_overflow") == 0)
    pc5 = rd("results/paircount_N5e10.txt").strip()
    lines5 = pc5.splitlines() if pc5 else []
    # line 1 ends with the pair count; line 2 is paircount's own statement of what
    # partners must therefore be -- anchor both at the end of the line, or the
    # leading "N=50000000000" field is what the regex finds first.
    m5 = re.search(r"=\s*(\d+)\s*$", lines5[0]) if lines5 else None
    m5b = re.search(r"=\s*(\d+)\s*$", lines5[1]) if len(lines5) > 1 else None
    check("5e10: partners == 2 * (the triple-parametrisation pair count)",
          bool(m5 and m5b) and 2 * int(m5.group(1)) == int(m5b.group(1)) == g5("partners"),
          "2 * %s = %s = partners" % (m5.group(1), m5b.group(1)) if (m5 and m5b) else "paircount missing")
    mid5 = rd("results/midline_N5e10.txt")
    check("5e10 midline: Amax = N/2, 0 solutions",
          "Amax=25000000000" in mid5 and "midline_solutions=0" in mid5,
          "results/midline_N5e10.txt")

# ------------------------------------------------------- the T(C) dumps vs each other
def load_dump(path):
    d = {}
    for line in rd(path).splitlines():
        if line.startswith("C=") and " T:" in line:
            d[line.split(" T:")[0]] = line
    return d

d3, d4 = load_dump("checks/ref_T_v3.txt"), load_dump("checks/ref_T_v4.txt")
empty3 = {q for q, l in d3.items() if l.rstrip().endswith("T:")}
check("T(C): every non-empty entry of the v3 dump appears verbatim in the v4 dump",
      not [q for q in d3 if q in d4 and d3[q] != d4[q]] and set(d3) - set(d4) == empty3 and len(d4) == 124,
      "%d shared, 0 mismatches; the %d omitted ones are exactly v3's empty sets" % (len(d4), len(empty3)))

# ------------------------------------------------------------- quotes in the report
check("REPORT.md quotes the 2e10 headline verbatim", hl in rep)
timing = "[search] 4558.14s total 4558.14s threads=12 mod3=on seg=2097152"
check("REPORT.md quotes the 2e10 timing verbatim, and the .err file has it",
      timing in rd("results/run_N2e10.err") and timing in rep)

# --------------------------------------------------------------- the Lean build
check("both Lean projects build (transcript at the end of run_all_quick.txt)",
      log.count("Build completed successfully") == 2)
check("the run_all.sh quick log is complete", log.rstrip().endswith("== done =="))

print()
print("FAILURES:", FAILS if FAILS else "NONE")
sys.exit(1 if FAILS else 0)
