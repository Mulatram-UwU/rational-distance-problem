# Lean formalisation of `12 | Q` (Theorem 6) and the parity lemma (Lemma 4)

Environment: Lean 4.34.0-rc2 at `<elan>`, **no Mathlib** (see
`notes/lean-setup.md` for why: `github.com:443` is unreachable for `lake`, and
the Lean release host transfers ~128 B/s).  Everything below uses core Lean
only.  `<repo>` is the root of this checkout and `<elan>` the elan home directory
(`~/.elan` by default); they stand in for absolute paths on the machine these notes
were written on.

## Build command (verified, run from `<repo>\lean`)

```bash
<elan>/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lake.exe build
```

Observed last run: `Build completed successfully (6 jobs).`  The five modules
(`Smoke`, `ModArith`, `Search`, `Parity`, `TwelveDvd`) each produced their
`.olean` under `.lake/build/lib/lean/RationalDistance/`.

## What is machine-checked, and where

| module | declaration | statement |
|---|---|---|
| `ModArith.lean` | `sq_mod8` | `n*n % 8 = 0 ∨ 1 ∨ 4` |
| | `sq_mod3` | `n*n % 3 = 0 ∨ 1` |
| | `odd_left_forces` | `(∃ k, k*k = A*A + C*C) → A % 2 = 1 → C % 4 = 0` |
| | `three_dvd_Q` | the four-square conditions + `A+B = C+D = Q` → `3 ∣ Q` |
| `Parity.lean` | `sq_mod4`, `odd_sq_mod4` | squares mod 4 are `0,1`; an odd square is `1` |
| | `not_both_odd` | `(∃ k, k*k = A*A+C*C) → ¬(A % 2 = 1 ∧ C % 2 = 1)` |
| | `swap_sq_sum` | order of the two squares in a hypothesis is immaterial |
| | `four_dvd_of_odd_partner` | `X % 2 = 1 → (∃ k, k*k = X*X+Y*Y) → 4 ∣ Y` |
| | `four_dvd_Q` | four conditions + `A+B = C+D = Q` + `¬(all four even)` → `4 ∣ Q` |
| `TwelveDvd.lean` | `mul4` | `(2*k)*(2*k) = 4*(k*k)` |
| | `even_of_sq_dvd_four` | `4 ∣ k*k → k % 2 = 0` |
| | `sq_of_four_mul_add` | `k*k = 4*m + 4*n → ∃ k', k'*k' = m + n` |
| | `twelve_dvd_Q_aux` | bounded induction `Q ≤ n` (core Lean has no `Nat.strong_induction_on`): if all four entries are even, halve the whole tuple — the four hypotheses shrink by the factor 4 via `sq_of_four_mul_add`, the sum drops to `A'+B' ≤ n`, and the induction hypothesis applies; otherwise `four_dvd_Q` and `three_dvd_Q` combine to `12 ∣ Q` |
| | **`twelve_dvd_Q`** | **Theorem 6: the four-square conditions + `A+B = C+D = Q` → `12 ∣ Q`** |
| `Search.lean` | `no_solution_Q_le_100` | `noSolutionUpto 100 = true` by `native_decide` (exhaustive over all `Q ≤ 100`, no symmetry reduction) |
| | `good3 52 24 28 45 7 = true`, `good 52 24 28 45 7 = false` | positive control: with the fourth condition dropped the tuple is accepted, with all four it is rejected — the same tuple the C++ relaxed search finds (see `results/summary.md`) |

Nothing else in the Lean project is claimed.  In particular the analytic
reductions of the report (Theorems 1–3: rationality of the coordinates and the
integer equivalence) are **not** formalised, and neither is the large-scale
search of §3 — those are a hand proof (`notes/reduction.md`) and a C++
computation (`results/`), respectively.

## Notes on the core-Lean-only proof style

* `omega` handles the linear Nat arithmetic (including `%` and `/` by
  numerals), `decide` the residue checks, `native_decide` the finite search.
* There is no `ring`: polynomial identities such as `(2*k)*(2*k) = 4*(k*k)`
  are proved by `simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]`
  (commutative-monoid normalisation).
* There is no `Nat.strong_induction_on`; the halo of the descent argument is
  therefore carried by the auxiliary bounded statement `twelve_dvd_Q_aux`.
* Two mistakes were hit and fixed while developing `Parity.lean`/`TwelveDvd.lean`
  (recorded here because they are the kind of thing that silently breaks a
  formalisation): (i) `rw` closes a goal by `rfl` when it can, so an extra
  `decide` after `rw` produces "no goals to be solved"; (ii) `match` on a term
  containing a free variable leaves that variable in the goal, so residue
  lemmas must take the residue as an explicit variable with a bound hypothesis
  (the `*_aux` pattern used throughout).
