# `explore/` — the early independent cross-checks

The three Python scripts here were written in the first hours of the project, before the C++
engines existed. They attack the problem by a route that shares no code and no data structure
with `src/`: for a side `L` and an `x`-numerator `p`, they enumerate the `y`-numerators `r`
directly from the factorisation of `n⁴ + w² = z²` via `(z−w)(z+w) = n⁴`. The candidate set is
exactly `partners(p²) ∩ partners((L−p)²)`, and one then needs `r` and `L−r` both in that set.
The enumeration is complete in `y` for the given `L` and `p`.

They were superseded by `src/brute.cpp` (which enumerates from the definition on the engines'
own parameterisation) and are **not** part of `run_all.sh`. They are kept because one of them
is the check cited in `notes/literature.md` §3.3:

| file | search | result |
|---|---|---|
| `extsearch.py` | partner sets built once from a bounded triple enumeration (`LMAX = 400`) | 0 solutions |
| `extsearch2.py` | partner sets from the divisors of `n⁴` (`LMAX = 1000`) | 0 solutions |
| `extsearch3.py` | as above, with explicit factorisation and memoisation; `LMAX` from `argv` | see the log |

`extsearch3_run.log` is the retained run: **`LMAX = 2000`** (43 s), `x`-numerator over
`[−2L, 3L]` — i.e. `x ∈ [−2, 3]`, covering the interior plus a band of exterior — with
**0 non-boundary solutions**. That is the "consistent with the literature" line in the survey.
Note that this is a *denominator* bound of 2000 only, three orders of magnitude below what the
C++ engines reach; it is a sanity check on the whole approach, not a competing search.

```bash
python explore/extsearch3.py 2000     # reproduces explore/extsearch3_run.log
```
