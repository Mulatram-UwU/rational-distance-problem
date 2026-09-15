# Raw results

All runs on this machine: 13th Gen Intel Core i5-13420H (8 cores / 12 threads --
4 performance + 4 efficiency), 16.9 GB RAM, Windows 10 build 10.0.26200, GCC 16.1,
`-O2 -march=native -fopenmp`, every engine at `threads=12`.
Meaning of the columns: a run with parameter `N`
enumerates **every** quadruple `Q,A,B,C,D` with `0 < A,B,C,D < Q <= N`,
`A+B = C+D = Q` and `A^2+C^2`, `B^2+C^2`, `A^2+D^2`, `B^2+D^2` all perfect
squares (see `notes/reduction.md`, Theorems 2 and 3 for why this is exactly the
statement "there is a point of the unit square at rational distance from all
four vertices whose coordinates have a common denominator <= N").  `candidates`
counts pairs `(A,B) ⊆ T(C)` passing the sum/positivity test, `tested` counts
those that also pass the parity filter of Lemma 4 (i.e. the number of full
four-square tests performed).

> **Authorship.** Every program whose output is archived here, and every run
> recorded below, was written and executed **independently by the AI research
> agent `DeepSeek v4.1 flash`** — no human co-author, no human-written code and
> no human-edited number.  See `REPORT.md` §11 and the *Authorship* section of
> `README.md`.

> **Line endings.** The programs print CRLF on Windows; `.gitattributes`
> (`* text=auto eol=lf`) stores and checks these files out with LF, so a fresh
> checkout differs from a re-run's stdout only in `\r`.  `checks/verify_results.py`
> and `checks/verify_chunking.sh` strip `\r` before comparing for exactly this
> reason (the same reason the first version of the chunking check reported a
> false "DIFFERS").

> **No local paths.** Absolute paths of the machine this was done on are not part
> of the release: in `notes/` and in `results/lean_verification.txt` they are
> written `<repo>` (root of this checkout) and `<elan>` (elan home,
> `~/.elan` by default).  `checks/scan_leaks.py` re-checks the whole tree for
> local paths and machine names and exits non-zero if any come back.

## Engine v1 (`src/fast_search.cpp`, whole partner table in memory)

| N | pairs | candidates | tested | solutions | wall |
|---|---|---|---|---|---|
| 10^5 | 185 864 | 2 141 875 | 421 893 | **0** | 0.01 s |
| 10^6 | 2 269 788 | 42 803 454 | 7 954 420 | **0** | 0.21 s |
| 10^7 | 26 809 924 | 781 367 361 | 138 567 430 | **0** | 4.02 s |
| 10^8 | 309 224 756 | 13 346 674 090 | 2 277 219 380 | **0** | 61.6 s |

## Engine v2 (`src/fast_search2.cpp`, two-pass memory-optimised table)

| N | table entries | candidates | tested | solutions | wall |
|---|---|---|---|---|---|
| 10^5 | 371 728 | 2 141 875 | 421 893 | **0** | 0.01 s |
| 10^6 | 4 539 576 | 42 803 454 | 7 954 420 | **0** | 0.17 s |
| 10^7 | 53 619 848 | 781 367 361 | 138 567 430 | **0** | 2.71 s |
| 10^8 | 618 449 512 | 13 346 674 090 | 2 277 219 380 | **0** | 42 s |
| 3·10^8 | 1 973 076 898 | 50 729 090 130 | 8 516 493 714 | **0** | 360.6 s (build 232.0 s, search 128.6 s) |

Raw output of the 3·10^8 run (`results/run_N3e8.txt`):

```
[build] N=300000000 entries=1973076898 232.01s
N=300000000 entries=1973076898 candidates=50729090130 survivors=8516493714 tested=8516493714 solutions=0
[search] 128.62s total 360.63s threads=12 parity=on mod3=off three=off
```

## Engine v3 (`src/fast_search3.cpp`, no global table; partner lists from divisors of C^2)

| N | divisor steps | partner entries | max partners/C | candidates | tested | solutions | wall |
|---|---|---|---|---|---|---|---|
| 10^4 | 338 220 | 28 948 | 59 | 93 740 | 19 909 | **0** | 0.0 s |
| 10^5 | 5 027 731 | 371 728 | 145 | 2 141 875 | 421 893 | **0** | 0.1 s |
| 10^6 | 69 955 248 | 4 539 576 | 341 | 42 803 454 | 7 954 420 | **0** | 0.4 s |
| 10^7 | 928 186 388 | 53 619 848 | 825 | 781 367 361 | 138 567 430 | **0** | 1.8 s |
| 10^8 | 11 885 034 948 | 618 449 512 | 1 855 | 13 346 674 090 | 2 277 219 380 | **0** | 45.8 s |
| 10^9 | 148 039 211 084 | 7 006 992 014 | 3 954 | 216 549 264 214 | 35 765 193 862 | **0** | 633.3 s |
| 3·10^9 | 489 228 649 307 | 22 198 268 430 | 5 842 | 806 162 420 921 | 131 322 339 150 | **0** | 1540.0 s (25m40s) |

Raw outputs (`results/run_N1e9.txt`, `results/run_N3e9.txt`):

```
[sieve] N=1000000000 22.82s
N=1000000000 divisor_steps=148039211084 partners=7006992014 max_partners_per_C=3954
             candidates=216549264214 tested=35765193862 solutions=0
[search] 610.51s total 633.34s threads=12 parity=on mod3=off three=off

[sieve] N=3000000000 53.19s
N=3000000000 divisor_steps=489228649307 partners=22198268430 max_partners_per_C=5842
             candidates=806162420921 tested=131322339150 solutions=0
[search] 1486.78s total 1539.97s threads=12 parity=on mod3=off three=off
```


## Engine v4 (`src/fast_search4.cpp`) and v5 (`src/fast_search5.cpp`): the run at 2*10^10

v3 cannot reach `2*10^10` for two hard reasons: its least-prime-factor sieve needs
2 bytes per `C <= N` (40 GB), and its divisor walk forms `C*C` in `u64`, which
overflows as soon as `C > 4.3*10^9`.  v4 replaces the flat sieve with a segmented
residual sieve (peak memory `O(segment)`, ~2.2 GB here, independent of `N`) and
never forms `C^2`: a divisor `u | C^2, u <= C` is built multiplicatively together
with its complement `v = C^2/u = prod p^(2e-f)`, both capped by 128-bit compares.
The cap is `v <= 3N`, which is exactly the condition `A = (v-u)/2 <= N`; a node
whose accumulated complement already exceeds it is pruned with its whole subtree
(the complement only grows as the walk descends).  The pair loop is additionally
organised by residue class, using Lemma 4 (parity) and Lemma 5 (`3 | Q`) as
necessary conditions; that is what makes `C = 2 (mod 4)` skippable and what cuts
the number of pairs actually visited by ~6x.  v5 changes only two speeds: it
visits the primes of `C` largest-first, so the `v <= 3N` prune fires near the
root instead of near the leaves, and it insertion-sorts the short partner lists.
`--no-mod3` restricts v4/v5 to Lemma 4's classes, i.e. exactly v3's filter set.

Agreement with v3.  `partners`, `max_partners_per_C`, `candidates` and `tested`
must be *identical*; only `divisor_steps`/`walk_nodes` differ, and only because
the v4/v5 walk prunes more.

| N | v3 (mod3 off) | v3 (mod3 on) | v4/v5 |
|---|---|---|---|
| 10^4 | partners 28948, cand 93740, tested 19909 | tested 9626 | identical |
| 10^5 | partners 371728, cand 2141875, tested 421893 | tested 211636 | identical |
| 10^6 | partners 4539576, cand 42803454, tested 7954420 | tested 4051329 | identical |
| 10^7 | partners 53619848, cand 781367361, tested 138567430 | tested 71198794 | identical |
| 10^8 | (v3 45.8 s) | partners 618449512, cand 13346674090, tested 1176085218 | identical |
| 10^9 | partners 7006992014, cand 216549264214, tested 35765193862 | - | identical to the 10^9 archive line |

`tested` at `10^9` (mod3 off) = 35 765 193 862 is v3's archived number
(`results/run_N1e9.txt`); v4 and v5 reproduce it exactly.  Walk nodes at `10^9`:
v3 148.0e9 (unpruned), v4 141.8e9, v5 44.2e9.

Timing at 10^8 (v5, whole machine free): sieve+factorisation 2.7 s, divisor walk
6.3 s, sort + candidate counting 3.3 s, pair loop + isqrt 3.4 s; total 15.7 s
(v3: 45.8 s with mod3 off, v4: 18.4 s with mod3 on).

The deep run (`results/run_N2e10.txt`, 4558 s wall, 12 threads, ~2.2 GB peak):

```
$ ./bin/fast_search5.exe --N 20000000000
N=20000000000 divisor_steps=1018553868147 partners=161541752656 max_partners_per_C=10214 candidates=7650247495045 tested=633326855574 solutions=0 sieve_overflow=0
[search] 4558.14s total 4558.14s threads=12 mod3=on seg=2097152
```

`partners = 161 541 752 656 = 2 * 80 770 876 328`, the latter being the independent
triple-parametrisation count of `src/paircount.cpp` (`results/paircount_N2e10.txt`).
`sieve_overflow = 0` says the segmented sieve never saw a `C` with more than 10
distinct small prime factors, so every factorisation it produced is complete.
The middle line at the same bound (`results/midline_N2e10.txt`, 26 s):

```
$ ./bin/midline_search.exe 20000000000
N=20000000000 Amax=10000000000 primitive_triples=1462708696 isqrt_tests=1462708696 midline_solutions=0
```

## The 5*10^10 extension (complete: piecewise and resumable)

**Result: 0 solutions with common denominator <= 5*10^10.**  The driver writes the
field-by-field sum of its 24 pieces to `results/run_N5e10.txt`:

```
$ cat results/run_N5e10.txt
N=50000000000 divisor_steps=2649313994389 partners=420219661420 max_partners_per_C=14317 candidates=22500241196365 tested=1845867547562 solutions=0 sieve_overflow=0
```

The 24 pieces' own `[search] ... total` times sum to **10 366.35 s = 2.88 h**; the
surrounding wall clock was **13:38 -> 16:40 = 3.0 h** on the same laptop (the
first piece shared the machine with the `paircount` / `midline` companions, and
the low-`C` pieces are the expensive ones -- per-piece costs are tabulated in
`notes/cost-5e10.md`).  Every cross-check passed:

* `partners = 420 219 661 420 = 2 * 210 109 830 710`, the latter being the
  independent triple-parametrisation count at the same bound
  (`results/paircount_N5e10.txt`);
* `solutions = 0` and `sieve_overflow = 0`;
* the 24 pieces sum to the recorded line **field by field**
  (`results/chunks5e10/pieces.txt`, asserted by `checks/verify_results.py`);
* the diagonal `A = B` is separately exhausted (3 656 771 176 primitive triples,
  0 solutions, 80.87 s).

The whole-run form cannot survive a reboot.  `fast_search5 --N 50000000000`
prints its counters only when it finishes, and stdout redirected to a file is
block buffered, so the first attempt (started 2026-09-15 10:32) lost 11000 of
its 23842 segments to a power cut with a 0-byte stdout.  Its raw progress log is
kept as `results/attempt1_5e10_interrupted.err`.

v5 therefore takes `--seglo k --seghi k'`: only the segment indices `[k,k')` are
visited.  The engine handles each `C` independently of the segment `C` falls in,
and every counter it prints is a sum over `C`, so the printed lines of the
pieces add up to exactly the whole-run line (`partners`, `candidates`, `tested`,
`solutions`, `divisor_steps` and `sieve_overflow` add; `max_partners_per_C` is a
maximum).  `checks/verify_chunking.sh` (output `results/verify_chunking.txt`)
checks this on real runs: at `N = 10^8` the three pieces sum to the whole run
bit for bit, and the whole runs at `10^8` and `10^9` reproduce the v3 archives
field for field (only `divisor_steps` is smaller, as in the table above).

`run_5e10.sh` ran the extension in 24 pieces, cut by *estimated* work (about
`C^1.8`, guessing that this would make the pieces take comparable time).  The
guess was too strong: the real per-segment cost falls off much more slowly, so
the pieces are deliberately unequal in time (piece 00 `[0,4079)` took 3932 s,
piece 23 `[23285,23842)` took 110.91 s) -- which is harmless, since every
segment is visited exactly once either way and the sum is what is published.
Boundaries of the `2^21`-residue segments:

```
0 4079 5995 7510 8811 9974 11037 12024 12950 13826 14659 15456 16222 16960
17672 18363 19033 19685 20320 20940 21545 22137 22717 23285 23842
```

Every piece's raw stdout/stderr stays in `results/chunks5e10/part_kk.{txt,err}`;
pieces that are already finished are skipped when the script is run again, and
when all 24 were done their sum was written to `results/run_N5e10.txt` (with
`results/chunks5e10/pieces.txt` holding the concatenation of the 24 raw lines).

The extension is counted as a result: it passes the same cross-checks as the
`2*10^10` line, namely `partners = 2 * paircount(5*10^10)`, `solutions = 0`
and `sieve_overflow = 0`, plus the piecewise-sum identity.  Two independent
computations at the same bound constrain the answer the search had to produce:

```
$ ./bin/paircount.exe 50000000000          # results/paircount_N5e10.txt
N=50000000000  unordered Pythagorean pairs (u<v, both <= N) = 210109830710
N=50000000000  v3 'partners' must equal 2*pairs = 420219661420

$ ./bin/midline_search.exe 50000000000     # results/midline_N5e10.txt, 80.87s
N=50000000000 Amax=25000000000 primitive_triples=3656771176 isqrt_tests=3656771176 midline_solutions=0
```

So the search's `partners` at `5*10^10` had to come out as exactly
`420 219 661 420` -- and it did (`420219661420`, above) -- and the diagonal case
`A = B` has no solution with denominator up to `5*10^10`.

## Cross-validation (v4/v5 additions)

* v4 and v5 reproduce v3 **bit for bit** on `partners`, `max_partners_per_C`,
  `candidates`, `tested` and `solutions` at `N = 10^4, 10^5, 10^6, 10^7` (both
  filter sets), at `10^8` (mod3 on), and against the *archived* outputs
  `results/run_N1e9.txt` (`10^9`) and `results/run_N3e9.txt` (`3*10^9`,
  reproduced in `results/run_v5_N3e9.txt`).  Only the walk node count differs
  (3e9: v5 1.40e11 vs v3 4.89e11).
* v4/v5 reproduce the **kernel-checked** Lean counters of
  `lean/RationalDistance/Count.lean` at `N = 1000, 2000, 3000`
  (`(partners, candidates, tested, solutions)` =
  `(2068,3295,774,0)`, `(4642,9293,2111,0)`, `(7388,16868,3774,0)`).
* `src/paircount.cpp` at `N = 2*10^10` gives 80 770 876 328 unordered
  Pythagorean pairs, so `partners` must be 161 541 752 656; the headline run
  prints exactly that.
* `src/midline_search.cpp` after its 128-bit rewrite reproduces its own
  pre-rewrite output at `N = 3*10^9` (`primitive_triples=219406350`, 0
  solutions), and its enumerator agrees with the parametrisation-free brute
  force `checks/midline_ref.cpp` at `Amax = 50000` (7312 = 7312).
* `checks/candcheck.cpp` recomputes `partners`, `candidates` and `tested` straight
  from the definitions (no divisor walk, no segmentation) and matches the engines
  at `N = 1000, 2000, 3000`, which are also the three values kernel-checked inside
  Lean by `native_decide` (`lean/RationalDistance/Count.lean`).
* `checks/partners_ref.cpp` recomputes `partners` and `max_partners_per_C` from the
  definition (128-bit square test per pair): `N = 10000` gives
  `partners_all=28948 max=59`, matching `fast_search5 --N 10000 --no-mod3`.
* `checks/sievecheck.cpp` compares the segmented residual sieve of
  `src/fast_search4.cpp` against trial division for every `C <= 2*10^6`:
  `checked=1999999 mismatches=0`, i.e. the factorisation the divisor walk relies on
  is complete, and no `C` in that range has more than 10 distinct prime factors
  (which is why the engines' 10-slot buffer can never overflow: the product of the
  first 11 primes is 200 560 490 130 > 2*10^10, and the headline run confirms
  `sieve_overflow=0`).

The four programs in `checks/` are the ones `run_all.sh quick` runs first; each
prints its own reference value next to the engine's, so a regression shows up as a
mismatch in the log rather than as a silently different headline number.

## Cross-validation

1. **v1 vs v2 vs v3** agree *exactly* (same `candidates`, same `tested`, same
   `solutions`) for `N = 10^4, 10^5, 10^6, 10^7` — see
   `results/consistency.txt`.  v2/v1 also agree at `10^8`, v3 at `10^8`.
2. **Independent brute force** (`src/brute.cpp`, written independently by a
   sub-agent: a direct `O(N^3)` scan over all `(Q,A,C)`, exact integer isqrt)
   agrees on the whole range it can reach: **0 solutions for every `Q <= 10^4`**
   (333 283 335 000 candidates tested, 235.9 s under load), and 0 solutions in
   its `--symmetric` mode which also admits the degenerate boundary cases
   `B = 0` or `D = 0`.  Its candidate counts match the closed forms
   `sum_{Q<=N}(Q-1)^2` by construction.  Raw log: `results/brute_runs.txt`.
   Extra checks by that agent: its `isqrt` was compared against Python
   `math.isqrt` on 27 029 values (including 23 660 values above `2^52`) with 0
   mismatches; and a *relaxed* build (conditions 3 and 4 disabled) does find
   solutions, e.g. `Q A C B D = 6 3 4 3 2`, so the zero results are not a dead
   code path.  (That agent also found and fixed a bug in its own first
   divisor-mode enumerator, caught by the A-vs-B comparison below.)
3. **Independent Pythagorean-pair enumerators** agree: the pairs
   `(u,v), u,v <= 200000, u^2+v^2` a square, produced by the triple
   parametrisation (my engine, 396 481 canonical pairs) and by a different
   algorithm (`src/brute_pairs.cpp`, divisor method, 792 962 ordered lines =
   2 × 396 481) are the *same set*: 0 differences both ways.  That agent
   additionally verified that its two internal methods (divisor method vs
   triple parametrisation) produce **byte-identical** files at `N = 2000,
   20000, 200000`, and that an independent Python re-implementation reproduces
   the 200000 file byte-identically.
4. **Relaxed-problem plumbing test**: for the problem in which only
   `A^2+C^2, B^2+C^2, A^2+D^2` are required (last one dropped) and `A < B`, the
   engine's output for `N = 300` is identical tuple-by-tuple to a direct Python
   `O(N^3)` enumeration: 6 solutions each, no extra, none missing.  (For the
   full four-condition problem both find none — this is why the relaxed test
   matters: it shows the enumeration actually *strikes* when solutions exist.)
5. **Parity filter** (`--no-parity` vs default) gives identical results on every
   `N` tested, and `--mod3` (the `3 | Q` filter of Lemma 5) as well.
6. **Table-size cross-check at `N = 10^9`**: `src/paircount.cpp` counts
   unordered Pythagorean pairs `(u<v, both <= N)` by the classical triple
   parametrisation and gets 3 503 496 007 at `N = 10^9`; engine v3 — which
   builds the same lists from the *factorisation of `C^2`* instead — reports
   `partners = 7 006 992 014 = 2 × 3 503 496 007`.  Exact match (and likewise at
   `N = 10^6` and `10^8`), which independently validates v3's table at the
   scale of the headline run.
7. **Lemma 4 at residue level** (independent of the hand proof): enumerating all
   residue quadruples mod `m` that satisfy `A+B ≡ C+D` and the four
   square-residue conditions, and discarding the all-even patterns, gives
   `Q mod 8 ∈ {0,4}` and `Q mod 16 ∈ {0,4,8,12}` — i.e. `4 | Q` is forced at
   modulus 8 already (modulus 4 alone allows `Q ≡ 2`, as it must).

## Other computations

* `src/residue_structure.py` — all residue quadruples mod `m` for
  `m ∈ {2,3,4,8,16,32,9,27,5,25,7,49,11,13,6,12,24,48,36,72,144,60,120,168,210}`;
  output quoted in `notes/reduction.md` §3.  Confirms `3 | Q` locally, that no
  modulus forces more than `12 | Q`, and that no prime `p` divides `A,B,C,D`
  locally.
* `src/center_line.py` — the centre line `x = 1/2`: exact rational verification
  of the algebraic reduction to `nu^2 = λ^4+8λ^3+18λ^2-8λ+1` (2000 random λ,
  plus 12 712 finite-field instances with 0 failures), an exhaustive search for
  rational points with `λ = p/q`, `|p|,q <= 1500` (**none found**), and an
  exhaustive direct search of `1+u^2`, `1+(2-u)^2` squares for `u = p/q <= 1500`
  (**none**).

## Reproducing all of this

```bash
bash run_all.sh quick    # minutes: rebuild everything, all small cross-checks
bash run_all.sh full     # hours:   + the 1e9 / 3e9 runs and the brute force to 1e4
bash run_all.sh deep     # ~1.5 h:  the headline run: every Q <= 2e10
bash run_all.sh 5e10     # ~3 h:    the extension: every Q <= 5e10, in resumable pieces
```

`results/run_all_quick.txt` is the log of one full `quick` run.  Each check in
`checks/` prints its own reference value next to the engine's, so a regression
shows up as a visible mismatch in that log rather than as a silently different
headline number.

`python checks/verify_results.py` then cross-checks the numbers recorded here
against each other and against the quotes in `REPORT.md` (20 assertions,
recomputing nothing); its output is archived as `results/verification.txt`.
`bash checks/verify_chunking.sh` does the same for the piecewise mode of v5
(`--seglo`/`--seghi`), comparing whole runs with piecewise sums and with the v3
archives; its output is archived as `results/verify_chunking.txt`.
