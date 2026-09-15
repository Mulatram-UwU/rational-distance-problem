/-
  RationalDistance.Algorithm
  ==========================

  Machine-checked correctness of the *search algorithm* used in
  `REPORT.md` §2/§6 and implemented by `src/fast_search*.cpp`.

  The algorithm (integer form; see Theorem 2 of `notes/reduction.md`):

      for C = 1 .. N:
        T(C) := { A : 1 <= A <= N, A^2 + C^2 is a perfect square }      (partners of C)
        for A < B in T(C) with A + B <= N:                              (pair loop)
          if A + B <= C: skip                                           (D would be <= 0)
          Q := A + B ;  D := Q - C
          if parity filter fails: skip
          if Q <= N and A^2 + D^2 and B^2 + D^2 are perfect squares:
            report (Q, A, B, C, D)

  What this file proves about it:

  * `pyth_iff_div`  — the characterisation the partner generation relies on:
        A^2 + C^2 a square  <=>  exists a divisor u | C^2 with u < C and
                                 u + 2*A = C^2/u .
    (This is exactly "run over the divisors u of C^2, put v = C^2/u,
     test v - u even, output (v-u)/2".)

  * `candidate_sound` — *soundness*: everything the enumeration reports
    really is a solution of the four-square system.

  * `enum_of_sol` / `exists_enum_of_sol` — *completeness*: every solution with
    common denominator Q <= N and `A <> B` is enumerated (the `A < B`
    restriction is harmless by the reflection symmetry `sol_swap`).
    NOTE (correction, 2026-09-15): the hypothesis `A <> B` here is stronger
    than necessary.  The `A = B` case is *also* covered, by the other
    symmetry of the problem: the diagonal reflection
    `(A,B,C,D) <-> (C,D,A,B)` (i.e. `(x,y) <-> (y,x)`).  After that
    relabelling the engine's pair is `(C,D)`, and `C <> D`, because
    `A = B` together with `C = D` forces `A = C` and hence the square
    `A^2 + C^2 = 2*A^2`.  Dropping `A <> B` therefore only needs the
    arithmetic lemma "`2*A*A` is not a positive square" (the integer form
    of the irrationality of `sqrt 2`), which is not proved here.

  * `parity_normal_form` — the parity filter of the algorithm is *lossless*:
    from any solution one obtains a solution of the same kind that passes
    the filter (`parity_dichotomy` is the dichotomy behind it).

  * `no_sol_of_no_candidate` — the headline: if the enumeration finds no
    candidate at bound `N`, then there is **no** solution with common
    denominator `Q <= N`, except possibly a point on the middle line
    `x = 1/2` (the `A = B` case), which is passed in as the explicit
    hypothesis `hmid` and discharged outside Lean by a separate exhaustive
    search (`src/midline_search.cpp`).  By the NOTE above, `hmid` is in fact
    redundant — the same `(A,B,C,D) <-> (C,D,A,B)` reflection covers `A = B`
    — so this is a theorem whose hypotheses are stronger than needed, not a
    theorem with a gap.  The middle-line reduction behind it is `midline_key`
    in `RationalDistanceAlgo/Midline.lean`.

  Core Lean only: no Mathlib.  Check with

    lake.exe build RationalDistance.Algorithm
-/
import RationalDistance.TwelveDvd

namespace RationalDistance.Algorithm

open RationalDistance.ModArith (odd_left_forces)
open RationalDistance.Parity (not_both_odd four_dvd_of_odd_partner swap_sq_sum)
open RationalDistance.TwelveDvd (sq_of_four_mul_add)

/-! ## 1. Definitions -/

/-- `Pyth C A`: `A^2 + C^2` is a perfect square (`A` is a Pythagorean partner of `C`). -/
def Pyth (C A : Nat) : Prop := ∃ h : Nat, A * A + C * C = h * h

/-- The other orientation of `Pyth`, matching the hypotheses of `ModArith`/`Parity`. -/
theorem pyth_iff' {C A : Nat} : Pyth C A ↔ ∃ k : Nat, k * k = A * A + C * C :=
  ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩

/-- Symmetry of the partner relation. -/
theorem pyth_comm {C A : Nat} (h : Pyth C A) : Pyth A C := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by omega⟩

/-- Integer form of a solution with common denominator `Q <= N`.

`IsSol N A B C D Q` says: `A + B = C + D = Q`, all four entries are strictly
between `0` and `Q`, `Q <= N`, and all four of `A^2+C^2, B^2+C^2, A^2+D^2,
B^2+D^2` are perfect squares.  By Theorem 2 of `notes/reduction.md` this is
exactly "the point `(A/Q, C/Q)` lies strictly inside the unit square and is at
rational distance from all four corners, with common denominator `Q`". -/
def IsSol (N A B C D Q : Nat) : Prop :=
  A + B = Q ∧ C + D = Q ∧ 0 < A ∧ 0 < B ∧ 0 < C ∧ 0 < D ∧ Q ≤ N ∧
  Pyth C A ∧ Pyth C B ∧ Pyth D A ∧ Pyth D B

/-- The parity filter of the search (`--no-parity` switches it off). -/
def ParityOK (A B C D : Nat) : Prop :=
  (A % 2 = 1 ∧ B % 2 = 1 ∧ C % 4 = 0 ∧ D % 4 = 0) ∨
  (C % 2 = 1 ∧ D % 2 = 1 ∧ A % 4 = 0 ∧ B % 4 = 0)

/-- The candidate predicate of the enumeration, without the parity filter. -/
def Enum (N C A B : Nat) : Prop :=
  0 < A ∧ 0 < C ∧ Pyth C A ∧ Pyth C B ∧ A < B ∧ A + B ≤ N ∧ C < A + B ∧
  Pyth (A + B - C) A ∧ Pyth (A + B - C) B

/-- What the algorithm actually enumerates (parity filter included). -/
def Candidate (N C A B : Nat) : Prop :=
  Enum N C A B ∧ ParityOK A B C (A + B - C)

/-! ## 2. Elementary algebra -/

/-- Square of a double. -/
theorem sq_two (a : Nat) : (2 * a) * (2 * a) = 4 * (a * a) := by
  rw [Nat.mul_assoc, Nat.mul_left_comm a 2 a]
  rw [show (4 : Nat) = 2 * 2 from rfl, Nat.mul_assoc]

/-- Distributing a factor `4` over a sum. -/
theorem four_add (x y : Nat) : 4 * x + 4 * y = 4 * (x + y) := (Nat.mul_add 4 x y).symm

/-- `u * (u + 2A) = u*u + u*A + u*A`. -/
theorem mul_two_add (u A : Nat) : u * (u + 2 * A) = u * u + u * A + u * A := by
  rw [Nat.mul_add]
  have h : u * (2 * A) = u * A + u * A := by
    rw [Nat.mul_comm 2 A, ← Nat.mul_assoc, Nat.mul_comm (u * A) 2]
    omega
  rw [h]
  omega

/-- `(u + A)^2 = u*u + u*A + u*A + A*A`. -/
theorem sq_expand (u A : Nat) : (u + A) * (u + A) = u * u + u * A + u * A + A * A := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm A u]
  omega

/-- The square identity behind the partner/divisor correspondence. -/
theorem sq_add_expand (u A : Nat) : (u + A) * (u + A) = u * (u + 2 * A) + A * A := by
  rw [mul_two_add, sq_expand]

/-- Converse bookkeeping: from `A^2 + C^2 = (A+u)^2` read off `u*(u+2A) = C^2`. -/
theorem key2 (A u C : Nat) (hh : A * A + C * C = (A + u) * (A + u)) :
    u * (u + 2 * A) = C * C := by
  rw [Nat.add_comm A u] at hh
  rw [sq_expand] at hh
  rw [mul_two_add]
  omega

/-- If `A^2 + C^2` is a square and `C > 0` then `A < h`. -/
theorem h_gt_A (A C h : Nat) (hC : 0 < C) (hh : A * A + C * C = h * h) : A < h := by
  have hCpos : 0 < C * C := Nat.mul_pos hC hC
  have hlt : A * A < h * h := by omega
  exact (Nat.mul_self_lt_mul_self_iff).mp hlt

/-- In a divisor pair `u * v = C^2` with `0 < u < v` one has `u < C`. -/
theorem u_lt_C (u v C : Nat) (hu : 0 < u) (huv : u * v = C * C) (huv' : u < v) :
    u < C := by
  have h1 : u * u < u * v := (Nat.mul_lt_mul_left hu).mpr huv'
  rw [huv] at h1
  exact (Nat.mul_self_lt_mul_self_iff).mp h1

/-! ## 3. The partner set of `C` is the set of divisors of `C^2`

This is the mathematical content of the partner generation: `fast_search3.cpp`
walks the divisors `u` of `C^2` with `u <= C`, puts `v = C^2/u`, keeps the ones
with `v - u` even, and outputs `A = (v-u)/2`.  We show this is *exactly* the
set of `A` with `A^2 + C^2` a perfect square. -/

/-- One half of the correspondence: a divisor `u` with `u + 2A = C^2/u`
produces a partner `A`. -/
theorem pyth_of_dvd {C A u v : Nat} (huv : u * v = C * C) (hlin : u + 2 * A = v) :
    Pyth C A := by
  subst hlin
  refine ⟨u + A, ?_⟩
  rw [sq_add_expand, huv]
  omega

/-- The other half: every partner `A > 0` is produced by such a divisor. -/
theorem dvd_of_pyth {C A : Nat} (hC : 0 < C) (hA : 0 < A) (h : Pyth C A) :
    ∃ u v : Nat, u * v = C * C ∧ u < C ∧ u + 2 * A = v := by
  obtain ⟨k, hk⟩ := h
  have hAk : A < k := h_gt_A A C k hC hk
  have hAik : A ≤ k := Nat.le_of_lt hAk
  have hu_pos : 0 < k - A := Nat.sub_pos_of_lt hAk
  have hkv : (k - A) + 2 * A = k + A := by omega
  have hkey : A * A + C * C = (A + (k - A)) * (A + (k - A)) := by
    rw [Nat.add_sub_of_le hAik]
    exact hk
  have hmul : (k - A) * ((k - A) + 2 * A) = C * C := key2 A (k - A) C hkey
  have huv : (k - A) * (k + A) = C * C := by rw [← hkv]; exact hmul
  refine ⟨k - A, k + A, huv, ?_, hkv⟩
  have hlt : k - A < k + A := by omega
  exact u_lt_C (k - A) (k + A) C hu_pos huv hlt

/-- **Partner/divisor characterisation.**  For `C > 0` and `A > 0`:

    `A^2 + C^2` is a perfect square
      iff
    there is a divisor `u | C^2` with `u < C` and `u + 2*A = C^2/u`. -/
theorem pyth_iff_div {C A : Nat} (hC : 0 < C) (hA : 0 < A) :
    Pyth C A ↔ ∃ u v : Nat, u * v = C * C ∧ u < C ∧ u + 2 * A = v :=
  ⟨dvd_of_pyth hC hA, fun ⟨_, _, huv, _, hlin⟩ => pyth_of_dvd huv hlin⟩

/-! ## 4. Soundness -/

/-- Everything the enumeration reports is a genuine solution. -/
theorem candidate_sound {N C A B : Nat} (h : Candidate N C A B) :
    IsSol N A B C (A + B - C) (A + B) := by
  obtain ⟨⟨hApos, hCpos, hCA, hCB, hAB, hQN, hCQ, hDA, hDB⟩, _⟩ := h
  have hBpos : 0 < B := Nat.lt_of_lt_of_le hApos (Nat.le_of_lt hAB)
  have hne : C + (A + B - C) = A + B := by omega
  refine ⟨by omega, hne, hApos, hBpos, hCpos, Nat.sub_pos_of_lt hCQ, hQN,
    hCA, hCB, hDA, hDB⟩

/-! ## 5. Completeness of the enumeration -/

/-- The reflection `x -> 1 - x` of the square swaps `A` and `B`. -/
theorem sol_swap {N A B C D Q : Nat} (h : IsSol N A B C D Q) : IsSol N B A C D Q := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨by omega, h2, h4, h3, h5, h6, h7, h9, h8, h11, h10⟩

/-- A solution with `A < B` satisfies the enumeration predicate (filter aside). -/
theorem enum_of_sol {N A B C D Q : Nat} (h : IsSol N A B C D Q) (hlt : A < B) :
    Enum N C A B := by
  obtain ⟨hAB, hCD, hApos, hBpos, hCpos, hDpos, hQN, hCA, hCB, hDA, hDB⟩ := h
  have hD : D = A + B - C := by omega
  rw [hD] at hDA hDB
  exact ⟨hApos, hCpos, hCA, hCB, hlt, by omega, by omega, hDA, hDB⟩

/-- **Completeness.**  Every solution with `Q <= N` and `A <> B` is enumerated,
up to the harmless reflection `A <-> B`. -/
theorem exists_enum_of_sol {N A B C D Q : Nat} (h : IsSol N A B C D Q) (hne : A ≠ B) :
    ∃ A' B' C' D' Q', IsSol N A' B' C' D' Q' ∧ Enum N C' A' B' := by
  by_cases hlt : A < B
  · exact ⟨A, B, C, D, Q, h, enum_of_sol h hlt⟩
  · have hlt' : B < A := by omega
    exact ⟨B, A, C, D, Q, sol_swap h, enum_of_sol (sol_swap h) hlt'⟩

/-! ## 6. The parity filter is lossless -/

/-- The parity filter is symmetric in `A`, `B`. -/
theorem parityOK_swap {A B C D : Nat} (h : ParityOK A B C D) : ParityOK B A C D := by
  rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · exact Or.inl ⟨h2, h1, h3, h4⟩
  · exact Or.inr ⟨h1, h2, h4, h3⟩

/-- **Parity dichotomy (Lemma 4, sharp form).**  For a solution which is not
all-even, exactly the two parity patterns tested by the filter can occur:
either `A, B` are odd and `C, D` are divisible by `4`, or `C, D` are odd and
`A, B` are divisible by `4`. -/
theorem parity_dichotomy {A B C D Q : Nat} (hAB : A + B = Q) (hCD : C + D = Q)
    (h1 : Pyth C A) (h2 : Pyth C B) (h3 : Pyth D A) (h4 : Pyth D B)
    (hne : ¬ (A % 2 = 0 ∧ B % 2 = 0 ∧ C % 2 = 0 ∧ D % 2 = 0)) :
    ParityOK A B C D := by
  by_cases hAodd : A % 2 = 1
  · -- `A` odd: `C` and `D` are the even partners of an odd number, so `4 | C, 4 | D`;
    -- then `Q = C + D` is even and `B = Q - A` is odd.
    have hC4 : C % 4 = 0 := odd_left_forces A C 0 (pyth_iff'.mp h1) hAodd
    have hD4 : D % 4 = 0 := odd_left_forces A D 0 (pyth_iff'.mp h3) hAodd
    exact Or.inl ⟨hAodd, by omega, hC4, hD4⟩
  · have hAeven : A % 2 = 0 := by omega
    by_cases hBodd : B % 2 = 1
    · -- impossible: `4 | C, 4 | D` makes `Q = C + D` even, but `A + B` is odd
      exfalso
      have hC4 : C % 4 = 0 := odd_left_forces B C 0 (pyth_iff'.mp h2) hBodd
      have hD4 : D % 4 = 0 := odd_left_forces B D 0 (pyth_iff'.mp h4) hBodd
      omega
    · have hBeven : B % 2 = 0 := by omega
      have hCorD : C % 2 = 1 ∨ D % 2 = 1 := by
        by_cases hc : C % 2 = 1
        · exact Or.inl hc
        · refine Or.inr ?_
          by_cases hd : D % 2 = 1
          · exact hd
          · exact absurd ⟨hAeven, hBeven, by omega, by omega⟩ hne
      rcases hCorD with hCodd | hDodd
      · have hA4 : A % 4 = 0 := odd_left_forces C A 0 (swap_sq_sum (pyth_iff'.mp h1)) hCodd
        have hB4 : B % 4 = 0 := odd_left_forces C B 0 (swap_sq_sum (pyth_iff'.mp h2)) hCodd
        exact Or.inr ⟨hCodd, by omega, hA4, hB4⟩
      · have hA4 : A % 4 = 0 := odd_left_forces D A 0 (swap_sq_sum (pyth_iff'.mp h3)) hDodd
        have hB4 : B % 4 = 0 := odd_left_forces D B 0 (swap_sq_sum (pyth_iff'.mp h4)) hDodd
        exact Or.inr ⟨by omega, hDodd, hA4, hB4⟩

/-- Halving a Pythagorean pair. -/
theorem pyth_halve {a c A C h : Nat} (hA : A = 2 * a) (hC : C = 2 * c)
    (e : A * A + C * C = h * h) : ∃ h', h' * h' = a * a + c * c := by
  have hm : h * h = 4 * (a * a) + 4 * (c * c) := by
    rw [← e, hA, hC, sq_two a, sq_two c]
  exact sq_of_four_mul_add hm

/-- Halving an all-even solution gives a solution with half the denominator. -/
theorem sol_halve {N A B C D Q a b c d : Nat}
    (hA : A = 2 * a) (hB : B = 2 * b) (hC : C = 2 * c) (hD : D = 2 * d)
    (h : IsSol N A B C D Q) : IsSol N a b c d (a + b) := by
  obtain ⟨hAB, hCD, hAp, hBp, hCp, hDp, hQN, hp1, hp2, hp3, hp4⟩ := h
  obtain ⟨k1, hk1⟩ := hp1
  obtain ⟨k2, hk2⟩ := hp2
  obtain ⟨k3, hk3⟩ := hp3
  obtain ⟨k4, hk4⟩ := hp4
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    ?_, ?_, ?_, ?_⟩
  · exact pyth_iff'.mpr (pyth_halve hA hC hk1)
  · exact pyth_iff'.mpr (pyth_halve hB hC hk2)
  · exact pyth_iff'.mpr (pyth_halve hA hD hk3)
  · exact pyth_iff'.mpr (pyth_halve hB hD hk4)

/-- Bounded induction: every solution has an all-even-free representative. -/
theorem parity_normal_aux (N : Nat) : ∀ n A B C D Q, Q ≤ n → IsSol N A B C D Q →
    ∃ A' B' C' D' Q', IsSol N A' B' C' D' Q' ∧ ParityOK A' B' C' D' := by
  intro n
  induction n with
  | zero =>
      intro A B C D Q hQ h
      exfalso
      obtain ⟨hAB, _, hApos, hBpos, _, _, _, _, _, _, _⟩ := h
      omega
  | succ n ih =>
      intro A B C D Q hQ h
      by_cases hall : A % 2 = 0 ∧ B % 2 = 0 ∧ C % 2 = 0 ∧ D % 2 = 0
      · obtain ⟨hAe, hBe, hCe, hDe⟩ := hall
        obtain ⟨a, hA⟩ : ∃ a, A = 2 * a := ⟨A / 2, by omega⟩
        obtain ⟨b, hB⟩ : ∃ b, B = 2 * b := ⟨B / 2, by omega⟩
        obtain ⟨c, hC⟩ : ∃ c, C = 2 * c := ⟨C / 2, by omega⟩
        obtain ⟨d, hD⟩ : ∃ d, D = 2 * d := ⟨D / 2, by omega⟩
        have hs : IsSol N a b c d (a + b) := sol_halve hA hB hC hD h
        obtain ⟨hAB, _, _, _, _, _, hQN, _, _, _, _⟩ := h
        exact ih a b c d (a + b) (by omega) hs
      · have hpar : ParityOK A B C D := by
          have h' := h
          obtain ⟨hAB, hCD, _, _, _, _, _, hp1, hp2, hp3, hp4⟩ := h'
          exact parity_dichotomy hAB hCD hp1 hp2 hp3 hp4 hall
        exact ⟨A, B, C, D, Q, h, hpar⟩

/-- **Losslessness of the parity filter.**  Every solution can be replaced by a
solution (with the same bound and a denominator dividing the original one)
which passes the filter. -/
theorem parity_normal_form {N A B C D Q : Nat} (h : IsSol N A B C D Q) :
    ∃ A' B' C' D' Q', IsSol N A' B' C' D' Q' ∧ ParityOK A' B' C' D' :=
  parity_normal_aux N Q A B C D Q (Nat.le_refl Q) h

/-! ## 7. The headline theorem -/

/-- If the enumeration is empty at bound `N`, then there is no solution with
common denominator `Q <= N` — *provided* there is no midline solution (the
`A = B` case, which the algorithm skips by insisting on `A < B`).

The midline hypothesis is discharged in `RationalDistanceAlgo/Midline.lean`,
which reduces it to Fermat's theorem that no right triangle with integer sides
has a square area (equivalently `FLT(4)`), and is also confirmed
computationally by `src/midline_search.cpp` for `Q <= 3*10^9`. -/
theorem no_sol_of_no_candidate {N : Nat} (h : ∀ C A B, ¬ Candidate N C A B)
    (hmid : ∀ M, M ≤ N → ∀ A C D, IsSol M A A C D (2 * A) → False) :
    ∀ A B C D Q, IsSol N A B C D Q → False := by
  intro A B C D Q hsol
  obtain ⟨A', B', C', D', Q', hsol', hpar⟩ := parity_normal_form hsol
  have hD' : D' = A' + B' - C' := by
    obtain ⟨h1, h2, _, _, _, _, _, _, _, _, _⟩ := hsol'
    omega
  by_cases hne : A' = B'
  · rw [hne] at hsol'
    have hQ : Q' = 2 * B' := by
      obtain ⟨h1, _⟩ := hsol'
      omega
    rw [hQ] at hsol'
    exact hmid N (Nat.le_refl N) B' C' D' hsol'
  · by_cases hlt : A' < B'
    · have hcan : ParityOK A' B' C' (A' + B' - C') := by
        rw [← hD']; exact hpar
      exact h C' A' B' ⟨enum_of_sol hsol' hlt, hcan⟩
    · have hlt' : B' < A' := by omega
      have hcan : ParityOK B' A' C' (B' + A' - C') := by
        rw [Nat.add_comm B' A', ← hD']
        exact parityOK_swap hpar
      exact h C' B' A' ⟨enum_of_sol (sol_swap hsol') hlt', hcan⟩

end RationalDistance.Algorithm
