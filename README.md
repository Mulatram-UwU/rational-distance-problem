# Rational distances from an interior point of the unit square

**Question.** Does there exist a point `P` in the *interior* of the unit square `[0,1]²`
whose distances to all four vertices are rational?

This is a classical open problem — it is listed as `research open` in Google DeepMind's
[`formal-conjectures`](https://github.com/google-deepmind/formal-conjectures) repository.
**This repository does not solve it.** What it contains is a self-contained computational
and formalisation effort:

* an **exhaustive search** that rules out every candidate point whose two coordinates have a
  common denominator `Q ≤ 5·10¹⁰` — no solution exists below that bound;
* a **Lean 4 formalisation** of the integer reduction, of the structural theorem `12 | Q`,
  and of the *correctness of the search algorithm* (both soundness and completeness);
* **three independent implementations** that re-derive every published number by a
  different method, so that the headline count is not trusted on the authority of one
  program.

> **Authorship.** Everything in this repository — the search engines in `src/`, the
> independent cross-check programs in `checks/`, the hand-written proofs and the literature
> survey in `notes/`, the Lean 4 formalisations in `lean/` and `lean-mathlib/`, every
> numerical run recorded under `results/`, and all of this documentation — was produced
> **independently by the AI research agent `DeepSeek v4.1 flash`**. There is no human
> co-author: not one line of code, proof, measurement or sentence below was written by a
> person. See [Authorship](#authorship) for the exact division of labour.

The full write-up is [`REPORT.md`](REPORT.md) (Chinese); the hand-written proofs are in
[`notes/reduction.md`](notes/reduction.md); every raw program output quoted anywhere is
kept verbatim under [`results/`](results/).

## The reduction in one paragraph

If three of the four distances are rational then `x` and `y` are rational, so write
`x = A/Q`, `y = C/Q` with `B = Q − A`, `D = Q − C`. Because a rational number whose square
is an integer is an integer, the geometric problem is *exactly* the following integer
problem: find `Q > 0` and `0 < A,B,C,D < Q` with `A + B = C + D = Q` such that

```
A² + C²,   B² + C²,   A² + D²,   B² + D²      are all perfect squares.
```

The engines enumerate these quadruples by fixing `C`, listing the *Pythagorean partners*
`T(C) = { A ≤ N : A² + C² is a square }` via a divisor walk, and pairing `A, B ∈ T(C)`
whose sum `A+B` is also in `T(D)`. Two filters (Lemma 4, parity mod 8; Lemma 5, mod 3)
throw away most pairs before any square test is done.

## Results

Exhaustive search over all quadruples with `Q ≤ N` (12 threads on a 13th Gen Intel Core
i5-13420H — 8 cores, 4 performance + 4 efficiency; `-O3 -march=native -fopenmp`):

| `N` | engine | partners | candidates | full square tests | solutions | wall |
|---|---|---|---|---|---|---|
| `10⁸` | v1 (`fast_search`) | 309 224 756 | 13 346 674 090 | 2 277 219 380 | **0** | 62 s |
| `10⁹` | v3 (`fast_search3`) | 7 006 992 014 | 216 549 264 214 | 35 765 193 862 | **0** | 10.6 min |
| `3·10⁹` | v3 / v5 | 22 198 268 430 | 806 162 420 921 | 131 322 339 150 | **0** | 25.7 / 24.5 min |
| `2·10¹⁰` | v5 (`fast_search5`) | 161 541 752 656 | 7 650 247 495 045 | 633 326 855 574 | **0** | 76 min |
| **`5·10¹⁰`** | **v5 (`fast_search5`)** | **420 219 661 420** | **22 500 241 196 365** | **1 845 867 547 562** | **0** | **2.88 h\*** |

\* the `5·10¹⁰` row is the sum of the 24 *resumable pieces* of `run_5e10.sh` (their own
`[search] … total` times: 10 366.35 s); the surrounding wall clock was 13:38 → 16:40 = 3.0 h
on the same laptop, the first piece sharing the machine with the `paircount` / `midline`
companions. Its output line, written by the driver as the field-by-field sum of the pieces,
is `results/run_N5e10.txt`:

```
N=50000000000 divisor_steps=2649313994389 partners=420219661420 max_partners_per_C=14317 candidates=22500241196365 tested=1845867547562 solutions=0 sieve_overflow=0
```

`partners = 420 219 661 420` is exactly `2 × 210 109 830 710`, and `210 109 830 710` is what
the independent triple-parametrisation counter prints for `N = 5·10¹⁰`
(`results/paircount_N5e10.txt`); the diagonal case is separately exhausted with 0 solutions
(`results/midline_N5e10.txt`, 3 656 771 176 primitive triples, 80.87 s).

`partners` is `Σ_C |T(C)|`, i.e. the number of pairs `(A,C)` with `A,C ≤ N` and `A²+C²` a
square; `candidates` counts the pairs that pass the sum and positivity test; *full square
tests* is the number of pairs that also survive the Lemma 4 and Lemma 5 filters, i.e. the
number of times all four conditions are actually checked. The line that any re-run has to
reproduce (`results/run_N2e10.txt`):

```
N=20000000000 divisor_steps=1018553868147 partners=161541752656 max_partners_per_C=10214 candidates=7650247495045 tested=633326855574 solutions=0 sieve_overflow=0
[search] 4558.14s total 4558.14s threads=12 mod3=on seg=2097152
```

**Independent checks on that number.** `partners = 161 541 752 656` is `2 × 80 770 876 328`,
and `80 770 876 328` is the number of unordered Pythagorean pairs `(u,v)`, `u < v ≤ 2·10¹⁰`,
counted by a *completely different* program that parametrises the triples instead of walking
divisors (`src/paircount.cpp`, `results/paircount_N2e10.txt`). A third program
(`checks/partners_ref.cpp`) enumerates `T(C)` from the definition. A separate midline search
(`src/midline_search.cpp`), rewritten in 128-bit arithmetic and using primitive-triple
parametrisation, independently confirms 0 solutions on the diagonal `x = y` for the same
bound (`results/midline_N2e10.txt`). Every engine v4/v5 run reproduces the corresponding v3
run *bit for bit* from `N = 10⁴` up to `3·10⁹`, and reproduces the kernel-checked Lean
counters at `N = 1000, 2000, 3000` (see `results/summary.md`).

**What is not claimed.** The search is finite: common denominators above `5·10¹⁰` are not
excluded, and no proof of non-existence is offered — every bound above is a finite
computation, not a theorem, and the problem remains open. The `5·10¹⁰` row is an *extension*
of the `2·10¹⁰` run rather than a replacement of its evidence: it was computed on the same
binary in 24 resumable pieces (`run_5e10.sh`, per-piece output kept in `results/chunks5e10/`),
and it is accepted here only because (a) the piecewise mode was proved to reproduce whole
runs bit for bit (`checks/verify_chunking.sh`), (b) the 24 pieces sum field by field to the
recorded line, and (c) it passes the same independent checks as `2·10¹⁰` (`partners` against
the triple parametrisation, 0 solutions, no sieve overflow, and a separate exhaustive
diagonal search).

## Lean 4 formalisation

Two projects, both building green (`results/lean_verification.txt`):

* **`lean/`** — core Lean, *no Mathlib*: `ModArith`, `Parity`, `TwelveDvd` (the theorem
  `12 | Q`), `Algorithm` (`pyth_iff_div`, `candidate_sound`, `exists_enum_of_sol`,
  `parity_normal_form`, main theorem `no_sol_of_no_candidate`), `Count`
  (the engine's counters recomputed inside Lean — a different algorithm, cross-checked
  against the C++ output by `native_decide`), `Search`, `BigCheck500`.
* **`lean-mathlib/`** — the Mathlib layer: `Bridge` (the geometric statement ⟺ the integer
  system), `Midline` (the reduction of the diagonal case), `Main`. Its `lakefile.toml` reuses
  `lean/` through `srcDir = "../lean"`, so no source file exists twice.

## Repository layout

```
REPORT.md              the full report (Chinese), ~550 lines, all sections cross-referenced
run_all.sh             build everything and reproduce the checks: quick | full | deep | 5e10
run_5e10.sh            the Q <= 5e10 extension in resumable pieces (see its header)
src/                   the search engines and their independent companions
  fast_search.cpp        v1  whole partner table in memory
  fast_search2.cpp       v2  two-pass, memory-optimised table
  fast_search3.cpp       v3  no global table: u16 sieve of smallest prime factors + divisor DFS
  fast_search4.cpp       v4  segmented residual sieve; divisor walk never forms C²
  fast_search5.cpp       v5  v4 + largest-prime-first ordering so the prune fires near the root
  midline_search.cpp     the diagonal x = y, by primitive-triple parametrisation (128-bit)
  brute.cpp              independent brute force over (A,B,C) from the definition
  brute_pairs.cpp        enumerates Pythagorean pairs two ways and compares the sets
  paircount.cpp          counts unordered Pythagorean pairs by triple parametrisation
  residue_structure.py   modular structure of the system
  center_line.py         the centre line x = 1/2: reduction and rational point search
checks/                independent re-derivations of the published counters
  sievecheck.cpp         the segmented sieve's factorisation vs trial division
  partners_ref.cpp       Σ_C |T(C)| straight from the definition
  candcheck.cpp          candidates / tested straight from the definition
  midline_ref.cpp        positive control for the midline enumerator
  verify_results.py      cross-checks every number recorded in results/ (20 checks)
  verify_chunking.sh     proves the piecewise mode reproduces whole runs (1e8, 1e9)
  scan_leaks.py          publication hygiene: no local path or machine name in the tree
explore/               early exploratory cross-checks (predecessors of src/brute.cpp)
notes/                 reduction.md (all hand proofs), literature.md (survey), lean-*.md
results/               raw output of every run quoted in the report, plus summary.md
lean/, lean-mathlib/   the two Lean 4 projects
_third_party/          downloaded papers / prior-art code, .gitignore'd, not redistributable
```

Absolute local paths in `notes/` are written as placeholders: `<repo>` is the root of
this checkout and `<elan>` is the elan home directory (`~/.elan` by default). That is
deliberate — no path of the machine the work was done on belongs in the release.
`checks/scan_leaks.py` enforces it: it exits non-zero if a local path or a machine name
reappears anywhere in the tree.

## Building and running

Requirements: `g++` with OpenMP and C++17, and Python 3 for the scripts under `src/`,
`checks/` and `explore/`. Lean 4 (via `elan`) for the formalisation; the Mathlib layer
additionally needs a Mathlib checkout (see `notes/lean-setup.md`).

```bash
bash run_all.sh quick     # minutes:  small engines, all cross-checks, both Lean projects
bash run_all.sh full      # hours:    + 10⁹ / 3·10⁹ runs, brute force to 10⁴
bash run_all.sh deep      # ~1.5 h:   the headline run: every Q ≤ 2·10¹⁰ (+ midline, + paircount)
bash run_all.sh 5e10      # ~3 h:     the extension: every Q ≤ 5·10¹⁰, in resumable pieces

# or by hand
g++ -O3 -march=native -fopenmp -std=c++17 -o bin/fast_search5 src/fast_search5.cpp
./bin/fast_search5 --N 20000000000     # headline: ~76 min, 12 threads, ~2.2 GB peak
./bin/paircount 20000000000            # must print 80770876328 (= partners / 2)
./bin/midline_search 20000000000       # the diagonal, ~26 s

# the independent checks (each prints its own expected value, see the file header)
g++ -O2 -march=native -std=c++17 -o bin/candcheck checks/candcheck.cpp && ./bin/candcheck 3000
cd lean && lake build

# cross-check every number recorded under results/ (recomputes nothing, reads the
# archived output; prints one PASS/FAIL line per claim).  The result of one such
# run is results/verification.txt.
python checks/verify_results.py

# prove that the piecewise (--seglo/--seghi) mode reproduces whole runs exactly
bash checks/verify_chunking.sh > results/verify_chunking.txt 2>&1   # ~10 min

# publication hygiene: exit 0 means no local path / machine name is anywhere in the
# tree (also the last step of `bash run_all.sh quick`)
python checks/scan_leaks.py
```

`fast_search5` accepts `--N`, `--no-mod3` (drop the mod-3 filter, to compare with the
archived v3 runs), `--seg` (sieve segment size), `--stats` (counters only), `--dumpC`
(dump the partner set of one `C`) and `--seglo`/`--seghi` (visit only the segment indices
in `[lo, hi)`, which is what lets a multi-hour run be cut into resumable pieces — see
`run_5e10.sh`). `midline_search` and `paircount` take the bound as a positional argument.

## Authorship

**All of the work in this repository was carried out independently by the AI research agent
`DeepSeek v4.1 flash`.** Concretely, the agent itself:

* designed the algorithms in `src/` — the divisor walk that never forms `C²`, the segmented
  residual sieve, the residue-class pairing with its parity (mod 8) and mod-3 filters, and
  the resumable `--seglo`/`--seghi` piecewise mode;
* wrote every program: the v1…v5 engines, the brute-force and enumerator programs, the
  independent counters under `checks/`, the shell drivers `run_all.sh` / `run_5e10.sh`, and
  the Python cross-check scripts;
* wrote the Lean 4 formalisations, including the machine-checked proof that the search is
  both sound *and* complete, the `12 | Q` structural theorem, and the Mathlib geometry
  bridge;
* searched and read the literature, and flagged every claim it could not verify;
* ran every computation on the machine described in `results/summary.md` and recorded the
  raw output verbatim under `results/`;
* wrote this README, `REPORT.md`, `results/summary.md` and every check that cross-verifies
  them.

Human involvement was limited to four things: stating the problem, supplying the machine,
imposing the working discipline (no fabricated results; every number traceable to raw
output; never give up), and GPG-signing the release commit. No human wrote, edited or
corrected any mathematical or computational content here.

## Licence

MIT — see [`LICENSE`](LICENSE). Everything under `_third_party/` is material by other
authors (downloaded papers and prior-art code) that is kept locally only for provenance and
is **not** covered by this licence; it is excluded from the repository by `.gitignore`.
