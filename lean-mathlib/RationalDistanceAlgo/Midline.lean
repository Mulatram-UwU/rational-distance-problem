/-
  RationalDistanceAlgo.Midline
  ============================

  The `A = B` case, i.e. a point on the middle line `x = 1/2`.

  The search algorithm enumerates pairs with `A < B` (the reflection
  `x ↦ 1-x` swaps `A` and `B`, so this is harmless *except* when `A = B`).
  `A = B` happens exactly when `x = 1/2`, and this file shows:

  * `midline_key` — a solution with `A = B` satisfies the *integer* identity
        `(C - D)^4 + 4*Q^4 = 16*h1^2*h2^2`,
    where `Q = 2A` and `h1^2 = A^2+C^2`, `h2^2 = A^2+D^2`.  (Pure polynomial
    identity: `rewrite with Q = 2A, C = 2A-D` and `ring`.)

  * `two_mul_sq_not_sq` — `2*A^2` is never a nonzero square, hence `C ≠ D`.

  * Consequence: a midline solution would give **nonzero** integers
    `(C-D, Q, 4*h1*h2)` with `x^4 + 4*y^4 = z^2`, i.e. an integer right triangle
    with a square area.  `FermatRightTriangle` below is Fermat's classical
    theorem that this is impossible (equivalent to `FLT(4)`, cf. Mathlib's
    `fermatLastTheoremFour` / `not_fermat_42`).

  Independently of this reduction, `src/midline_search.cpp` exhaustively
  checked the midline for `Q ≤ 3*10^9` (219,406,350 primitive triples, no
  solution) — see `results/midline_N3e9.txt`.
-/
import Mathlib
import RationalDistance.Algorithm

namespace RationalDistanceAlgo

open RationalDistance.Algorithm

/-- **Midline key identity.**  With `Q = A + A = C + D` and
`A^2 + C^2 = h1^2`, `A^2 + D^2 = h2^2` (all in `ℤ`),

    `(C - D)^4 + 4*Q^4 = 16*h1^2*h2^2` . -/
theorem midline_key {A C D Q h1 h2 : ℤ} (hA2 : A + A = Q) (hCD : C + D = Q)
    (e1 : A * A + C * C = h1 * h1) (e2 : A * A + D * D = h2 * h2) :
    (C - D) ^ 4 + 4 * Q ^ 4 = 16 * h1 ^ 2 * h2 ^ 2 := by
  have hQ : Q = 2 * A := by omega
  have h1sq : h1 ^ 2 = A ^ 2 + C ^ 2 := by nlinarith [e1]
  have h2sq : h2 ^ 2 = A ^ 2 + D ^ 2 := by nlinarith [e2]
  have hC : C = 2 * A - D := by omega
  rw [hQ, h1sq, h2sq, hC]
  ring

/-- `2 * A^2` is never a positive perfect square (equivalently `√2` is
irrational).  Proved by the classical descent: `2 ∣ h` and `2 ∣ A`, halve and
repeat. -/
theorem two_mul_sq_not_sq : ∀ A : ℕ, 0 < A → ∀ h : ℕ, h * h ≠ 2 * (A * A) := by
  intro A
  induction A using Nat.strong_induction_on with
  | _ A ih =>
    intro hA h hh
    have h2h : 2 ∣ h := by
      have hh2 : 2 ∣ h ^ 2 := ⟨A * A, by rw [pow_two]; exact hh⟩
      exact Nat.Prime.dvd_of_dvd_pow Nat.prime_two hh2
    obtain ⟨h1, rfl⟩ := h2h
    have hmid : 2 * (h1 * h1) = A * A := by nlinarith [hh]
    have h2A : 2 ∣ A := by
      have hA2 : 2 ∣ A ^ 2 := ⟨h1 * h1, by rw [pow_two]; exact hmid.symm⟩
      exact Nat.Prime.dvd_of_dvd_pow Nat.prime_two hA2
    obtain ⟨A1, rfl⟩ := h2A
    have hA1 : 0 < A1 := by nlinarith
    have hlt : A1 < 2 * A1 := by omega
    exact ih A1 hlt hA1 h1 (by nlinarith [hmid])

/-- On the middle line the two "y-coordinates" differ: if `C = D` then
`C = D = A` and `2*A^2 = h1^2`, impossible. -/
theorem midline_C_ne_D {A C D h1 : ℕ} (hA : 0 < A) (hCD : C + D = 2 * A)
    (e1 : A * A + C * C = h1 * h1) (hCD' : C = D) : False := by
  have hCA : C = A := by omega
  rw [hCA] at e1
  exact two_mul_sq_not_sq A hA h1 (by nlinarith [e1])

/-- **Fermat's right-triangle theorem**, in the form needed here: no nonzero
integers satisfy `x^4 + 4*y^4 = z^2` (equivalently: no right triangle with
integer sides has a square area).  This is the classical theorem equivalent to
`FLT(4)`; Mathlib has the `FLT(4)` counterpart as
`fermatLastTheoremFour`/`not_fermat_42`. -/
def FermatRightTriangle : Prop :=
  ∀ x y z : ℤ, x ≠ 0 → y ≠ 0 → x ^ 4 + 4 * y ^ 4 ≠ z ^ 2

/-- **No midline solution.**  Assuming Fermat's right-triangle theorem, there is
no solution with `A = B` — i.e. no point on the middle line `x = 1/2`.

A solution with `A = B` has `Q = 2A`, and the key identity turns it into
nonzero integers `(C-D, Q, 4*h1*h2)` with `x^4 + 4*y^4 = z^2`. -/
theorem no_midline_of_fermat (hF : FermatRightTriangle) :
    ∀ N A C D : ℕ, IsSol N A A C D (2 * A) → False := by
  intro N A C D h
  obtain ⟨hAA, hCD, hApos, _, _, _, _, hp1, _, hp3, _⟩ := h
  obtain ⟨h1, e1⟩ := hp1
  obtain ⟨h2, e2⟩ := hp3
  have hne : (C : ℤ) - D ≠ 0 := by
    intro hz
    exact midline_C_ne_D hApos hCD e1 (Nat.cast_inj.mp (sub_eq_zero.mp hz))
  have hkey : ((C : ℤ) - D) ^ 4 + 4 * (2 * (A : ℤ)) ^ 4 = 16 * (h1 : ℤ) ^ 2 * (h2 : ℤ) ^ 2 :=
    midline_key (by ring) (by exact_mod_cast hCD) (by exact_mod_cast e1) (by exact_mod_cast e2)
  have hA2ne : 2 * (A : ℤ) ≠ 0 := by
    have : (2 * A : ℕ) ≠ 0 := by omega
    exact_mod_cast this
  refine hF ((C : ℤ) - D) (2 * (A : ℤ)) (4 * (h1 : ℤ) * h2) hne hA2ne ?_
  rw [show (4 * (h1 : ℤ) * h2) ^ 2 = 16 * (h1 : ℤ) ^ 2 * (h2 : ℤ) ^ 2 by ring]
  exact hkey

end RationalDistanceAlgo
