/-
  RationalDistanceAlgo.Main
  =========================

  Assembly of the machine-checked correctness chain:

      "the search found nothing at bound N"
        ==> (RationalDistance.Algorithm)
      "no integer solution with common denominator <= N"
        ==> (RationalDistanceAlgo.Bridge)
      "no rational point strictly inside the unit square at rational distance
       from all four corners, with common denominator <= N"

  with the `A = B` (middle line `x = 1/2`) case handled by
  `RationalDistanceAlgo.no_midline_of_fermat` — assuming Fermat's
  right-triangle theorem, which the exhaustive run of `src/midline_search.cpp`
  independently confirms for `Q ≤ 3*10^9`.

  Check with
    lake.exe build RationalDistanceAlgo.Main
-/
import Mathlib
import RationalDistanceAlgo.Bridge
import RationalDistanceAlgo.Midline

namespace RationalDistanceAlgo

open RationalDistance.Algorithm

/-- **Algorithm correctness, geometric form.**

If the enumeration predicate of the search has no candidate at bound `N`, then
there is no rational point strictly inside the unit square whose distances to
all four corners are rational and whose coordinates have common denominator
`≤ N`.

The hypothesis `h` is exactly "the program printed `solutions=0`": the program
enumerates precisely the triples `(C, A, B)` satisfying `Candidate N C A B`
(see `RationalDistance.Algorithm`: `pyth_iff_div` is the partner generation,
`enum_of_sol` the completeness, `parity_normal_form` the losslessness of the
parity filter). -/
theorem no_rational_point_of_no_candidate {N : ℕ}
    (h : ∀ C A B : ℕ, ¬ Candidate N C A B) (hF : FermatRightTriangle) :
    ¬ HasRatPoint N := by
  intro hpt
  obtain ⟨A, B, C, D, Q, hsol⟩ := (hasRatPoint_iff N).mp hpt
  exact no_sol_of_no_candidate h (fun M _ A C D hs => no_midline_of_fermat hF M A C D hs)
    A B C D Q hsol

/-- The same statement with the middle line discharged by the *computational*
result (`src/midline_search.cpp`, `results/midline_N3e9.txt`) instead of by
Fermat's theorem: if one has separately verified `¬ IsSol N A A C D (2*A)` for
all `A ≤ N/2`, the conclusion is unconditional. -/
theorem no_rational_point_of_no_candidate' {N : ℕ}
    (h : ∀ C A B : ℕ, ¬ Candidate N C A B)
    (hmid : ∀ M : ℕ, M ≤ N → ∀ A C D : ℕ, ¬ IsSol M A A C D (2 * A)) :
    ¬ HasRatPoint N := by
  intro hpt
  obtain ⟨A, B, C, D, Q, hsol⟩ := (hasRatPoint_iff N).mp hpt
  exact no_sol_of_no_candidate h (fun M hM A C D hs => hmid M hM A C D hs) A B C D Q hsol

end RationalDistanceAlgo
