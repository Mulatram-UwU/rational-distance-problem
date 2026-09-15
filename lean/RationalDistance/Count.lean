/-
  RationalDistance.Count
  ======================

  Implementation-fidelity cross-check between the *actual* C++ program
  (`src/fast_search3.cpp`) and an independent Lean implementation of the same
  specification.

  The C++ program generates the partner set `T(C) = {A : A^2+C^2 a square}`
  from the *divisors* of `C^2` (`pyth_iff_div` in `RationalDistance.Algorithm`),
  keeps `A < B` pairs, applies the parity filter, and runs two integer square
  tests.  `stats` below computes the identical four counters by a completely
  different route: it tests every `A <= N` for squareness with `Nat.sqrt`.

  The `example`s record the C++ output (verbatim from `results/`), so
  `native_decide` machine-checks that the two implementations agree.

  This is exactly the check that catches the class of bug found earlier in
  `fast_search2.cpp` (partner lists truncated at `N/2`): a wrong partner set or
  a wrong loop bound changes `partners`/`candidates`/`tested` immediately.

  Core Lean only.  Check with
    lake.exe build RationalDistance.Count
-/
import RationalDistance.Algorithm

namespace RationalDistance.Count

/-- `isSq n` is `true` iff `n` is a perfect square of a natural number. -/
def isSq (n : Nat) : Bool := Nat.sqrt n * Nat.sqrt n == n

/-- Computable version of `Pyth C A`: `A^2 + C^2` is a perfect square. -/
def pythB (C A : Nat) : Bool := isSq (A * A + C * C)

/-- The parity filter of the search, as a `Bool`. -/
def parityB (A B C D : Nat) : Bool :=
  (A % 2 == 1 && B % 2 == 1 && C % 4 == 0 && D % 4 == 0) ||
    (C % 2 == 1 && D % 2 == 1 && A % 4 == 0 && B % 4 == 0)

/-- The partners of `C` among `1 .. N`. -/
def partners (N C : Nat) : List Nat :=
  (List.range (N + 1)).filter (fun A => decide (1 ≤ A) && pythB C A)

/-- All ordered pairs of partners of `C`. -/
def allPairs (N C : Nat) : List (Nat × Nat) :=
  (partners N C).foldl (fun acc A => acc ++ (partners N C).map (fun B => (A, B))) []

/-- The candidate pairs `A < B` of partners of `C` with `A + B ≤ N` and `C < A + B`. -/
def cands (N C : Nat) : List (Nat × Nat) :=
  (allPairs N C).filter (fun p =>
    decide (p.1 < p.2) && decide (p.1 + p.2 ≤ N) && decide (C < p.1 + p.2))

/-- The candidates accepted by the final two integer square tests. -/
def hits (N C : Nat) : List (Nat × Nat) :=
  (cands N C).filter (fun p =>
    pythB (p.1 + p.2 - C) p.1 && pythB (p.1 + p.2 - C) p.2)

/-- Statistics of the search at bound `N`, in the order printed by
`fast_search3.cpp`: `(partners, candidates, tested, solutions)`, where
* `partners`   = `Σ_{C ≤ N} |T(C)|`,
* `candidates` = number of `A < B` pairs of partners of `C` with
  `A + B ≤ N` and `C < A + B`,
* `tested`     = the same but only the pairs passing the parity filter,
* `solutions`  = those where `A^2+D^2` and `B^2+D^2` are both squares
  (`D = A + B - C`).

`C` runs over `1 .. N` to match the C++ loop (`for Ci = 1; Ci <= N`).  Getting
that range wrong is itself detected by the cross-check below: with `C` starting
at `0` the counter `partners` is off by exactly `N`, because every `A` is a
partner of `C = 0`.

Every quantity is `List.length`, so this is a direct transcription of the C++
counters, not an optimised version of them. -/
def stats (N : Nat) : Nat × Nat × Nat × Nat :=
  ((List.range (N + 1)).filter (fun C => decide (1 ≤ C))).foldl (fun acc C =>
    let L := partners N C
    let cd := cands N C
    let ts := cd.filter (fun p => parityB p.1 p.2 C (p.1 + p.2 - C))
    (acc.1 + L.length, acc.2.1 + cd.length, acc.2.2.1 + ts.length,
      acc.2.2.2 + (hits N C).length)) (0, 0, 0, 0)

/-! ## Cross-checks against the C++ program

`src/fast_search3.cpp` prints, verbatim:

```
N=1000 divisor_steps=20594 partners=2068  max_partners_per_C=21 candidates=3295  tested=774  solutions=0
N=2000 divisor_steps=48463 partners=4642  max_partners_per_C=30 candidates=9293  tested=2111 solutions=0
N=3000 divisor_steps=79499 partners=7388  max_partners_per_C=37 candidates=16868 tested=3774 solutions=0
```

The counters below are `(partners, candidates, tested, solutions)`. -/

example : stats 1000 = (2068, 3295, 774, 0) := by native_decide

example : stats 2000 = (4642, 9293, 2111, 0) := by native_decide

example : stats 3000 = (7388, 16868, 3774, 0) := by native_decide

/-! ## Sanity of the two square tests -/

example : isSq 144 = true := by native_decide

example : isSq 145 = false := by native_decide

/-- Non-vacuity: the *relaxed* three-condition version of the problem does have
solutions (`(Q,A,B,C,D) = (52,24,28,45,7)`), so the enumeration is not
vacuously reporting zeros. -/
example : pythB 45 24 && pythB 45 28 && pythB 7 24 = true := by native_decide

example : pythB 7 28 = false := by native_decide

end RationalDistance.Count
