/-
  Core-Lean formalisation of the local (2-adic and 3-adic) structure of the
  rational-distance problem for the unit square.

  Setting (integer form): integers `A B C D Q` with
    (H1)  A + B = Q,  C + D = Q,  0 < A, B, C, D
    (H2)  A^2 + C^2,  B^2 + C^2,  A^2 + D^2,  B^2 + D^2  are perfect squares.

  This file proves:
    * `sq_mod8`            (P2) squares mod 8 are 0, 1 or 4
    * `sq_mod3`            (P2) squares mod 3 are 0 or 1
    * `odd_left_forces`    (P3) A odd and A^2 + C^2 a square  =>  4 | C
    * `three_dvd_Q`        (P4) (H1) + (H2)  =>  3 | Q

  No Mathlib; only `Init` (default prelude) lemmas are used.
-/

namespace RationalDistance.ModArith

/-! ## (P2) Squares modulo 8 and modulo 3 -/

/-- Residue form of `sq_mod8`: a square of a residue `< 8` is `0`, `1` or `4` mod 8. -/
theorem sq_mod8_aux (r : Nat) (hr : r < 8) :
    r * r % 8 = 0 ∨ r * r % 8 = 1 ∨ r * r % 8 = 4 := by
  match r with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | 5 => decide
  | 6 => decide
  | 7 => decide
  | k + 8 => exact absurd hr (by omega)

/-- **(P2)** A perfect square of a natural number is `0`, `1` or `4` modulo 8. -/
theorem sq_mod8 (n : Nat) : n * n % 8 = 0 ∨ n * n % 8 = 1 ∨ n * n % 8 = 4 := by
  have h : n * n % 8 = (n % 8) * (n % 8) % 8 := by rw [Nat.mul_mod]
  rw [h]
  exact sq_mod8_aux (n % 8) (Nat.mod_lt _ (by decide))

/-- Residue form of `sq_mod3`: a square of a residue `< 3` is `0` or `1` mod 3. -/
theorem sq_mod3_aux (r : Nat) (hr : r < 3) : r * r % 3 = 0 ∨ r * r % 3 = 1 := by
  match r with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | k + 3 => exact absurd hr (by omega)

/-- **(P2)** A perfect square of a natural number is `0` or `1` modulo 3. -/
theorem sq_mod3 (n : Nat) : n * n % 3 = 0 ∨ n * n % 3 = 1 := by
  have h : n * n % 3 = (n % 3) * (n % 3) % 3 := by rw [Nat.mul_mod]
  rw [h]
  exact sq_mod3_aux (n % 3) (Nat.mod_lt _ (by decide))

/-! ## (P3) `A` odd forces `4 | C`

Proof shape (all in core Lean): an odd number is `1 mod 8`; the square
`A^2 + C^2` is `0`, `1` or `4 mod 8`; with `A` odd this forces `C^2 ≡ 0 mod 8`,
and a number whose square is `0 mod 8` is divisible by `4`. -/

/-- An odd residue `< 8` has square `1 mod 8`. -/
theorem odd_sq_mod8_aux (r : Nat) (hr : r < 8) (h : r % 2 = 1) : r * r % 8 = 1 := by
  match r with
  | 0 => exact absurd h (by decide)
  | 1 => decide
  | 2 => exact absurd h (by decide)
  | 3 => decide
  | 4 => exact absurd h (by decide)
  | 5 => decide
  | 6 => exact absurd h (by decide)
  | 7 => decide
  | k + 8 => exact absurd hr (by omega)

/-- Residue step: if `(1 + r*r) mod 8` is `0`, `1` or `4` then `4 | r`. -/
theorem odd_forces_aux (r : Nat) (hr : r < 8)
    (h : (1 + r * r % 8) % 8 = 0 ∨ (1 + r * r % 8) % 8 = 1 ∨ (1 + r * r % 8) % 8 = 4) :
    r % 4 = 0 := by
  match r with
  | 0 => decide
  | 1 => rcases h with h | h | h <;> exact absurd h (by decide)
  | 2 => rcases h with h | h | h <;> exact absurd h (by decide)
  | 3 => rcases h with h | h | h <;> exact absurd h (by decide)
  | 4 => decide
  | 5 => rcases h with h | h | h <;> exact absurd h (by decide)
  | 6 => rcases h with h | h | h <;> exact absurd h (by decide)
  | 7 => rcases h with h | h | h <;> exact absurd h (by decide)
  | k + 8 => exact absurd hr (by omega)

set_option linter.unusedVariables false in
/-- **(P3)** If `A` is odd and `A^2 + C^2` is a perfect square then `4 | C`.

`Q` is part of the signature for compatibility with the surrounding development
and is not needed for this half of the parity lemma. -/
theorem odd_left_forces (A C Q : Nat) (h : ∃ k, k * k = A * A + C * C) (hA : A % 2 = 1) :
    C % 4 = 0 := by
  obtain ⟨k, hk⟩ := h
  have hk8 : k * k % 8 = 0 ∨ k * k % 8 = 1 ∨ k * k % 8 = 4 := sq_mod8 k
  have hsum8 : (A * A + C * C) % 8 = 0 ∨ (A * A + C * C) % 8 = 1 ∨
      (A * A + C * C) % 8 = 4 := by
    rw [← hk]; exact hk8
  have hAodd : A % 8 % 2 = 1 := by
    have h1 : A % 8 % 2 = A % 2 := Nat.mod_mod_of_dvd A ⟨4, rfl⟩
    rw [h1, hA]
  have hA8 : A * A % 8 = 1 := by
    have h1 : A * A % 8 = (A % 8) * (A % 8) % 8 := by rw [Nat.mul_mod]
    rw [h1]
    exact odd_sq_mod8_aux (A % 8) (Nat.mod_lt _ (by decide)) hAodd
  have h2 : (A * A + C * C) % 8 = (1 + C * C % 8) % 8 := by rw [Nat.add_mod, hA8]
  rw [h2] at hsum8
  have h3 : C * C % 8 = (C % 8) * (C % 8) % 8 := by rw [Nat.mul_mod]
  rw [h3] at hsum8
  have hres : C % 8 % 4 = 0 := odd_forces_aux (C % 8) (Nat.mod_lt _ (by decide)) hsum8
  have h4 : C % 8 % 4 = C % 4 := Nat.mod_mod_of_dvd C ⟨2, rfl⟩
  rw [h4] at hres
  exact hres

/-! ## (P4) `3 | Q` -/

/-- A non-zero residue `< 3` has square `1 mod 3`. -/
theorem sq_mod3_of_ne_zero (r : Nat) (hr : r < 3) (h : r ≠ 0) : r * r % 3 = 1 := by
  match r with
  | 0 => exact absurd rfl h
  | 1 => decide
  | 2 => decide
  | k + 3 => exact absurd hr (by omega)

/-- Residue step: if `(1 + r*r) mod 3` is `0` or `1` then `r = 0`. -/
theorem three_aux (r : Nat) (hr : r < 3)
    (h : (1 + r * r % 3) % 3 = 0 ∨ (1 + r * r % 3) % 3 = 1) : r = 0 := by
  match r with
  | 0 => rfl
  | 1 => rcases h with h | h <;> exact absurd h (by decide)
  | 2 => rcases h with h | h <;> exact absurd h (by decide)
  | k + 3 => exact absurd hr (by omega)

/-- Key step of (P4): if `3 ∤ A` and `A^2 + C^2` is a perfect square then `3 ∣ C`. -/
theorem three_dvd_of_not_dvd (A C : Nat) (h : ∃ k, k * k = A * A + C * C) (hA : A % 3 ≠ 0) :
    3 ∣ C := by
  obtain ⟨k, hk⟩ := h
  have hk3 : k * k % 3 = 0 ∨ k * k % 3 = 1 := sq_mod3 k
  have hsum : (A * A + C * C) % 3 = 0 ∨ (A * A + C * C) % 3 = 1 := by
    rw [← hk]; exact hk3
  have hA1 : A * A % 3 = 1 := by
    have h1 : A * A % 3 = (A % 3) * (A % 3) % 3 := by rw [Nat.mul_mod]
    rw [h1]
    exact sq_mod3_of_ne_zero (A % 3) (Nat.mod_lt _ (by decide)) hA
  have h2 : (A * A + C * C) % 3 = (1 + C * C % 3) % 3 := by rw [Nat.add_mod, hA1]
  rw [h2] at hsum
  have h3 : C * C % 3 = (C % 3) * (C % 3) % 3 := by rw [Nat.mul_mod]
  rw [h3] at hsum
  have hres : C % 3 = 0 := three_aux (C % 3) (Nat.mod_lt _ (by decide)) hsum
  exact Nat.dvd_iff_mod_eq_zero.mpr hres

/-- If `3 ∣ C`, `3 ∣ D` and `C + D = Q` then `3 ∣ Q`. -/
theorem three_dvd_sum {C D Q : Nat} (h : C + D = Q) (hC : 3 ∣ C) (hD : 3 ∣ D) :
    3 ∣ Q := by
  obtain ⟨c, rfl⟩ := hC
  obtain ⟨d, rfl⟩ := hD
  exact ⟨c + d, by omega⟩

/-- **(P4)** If `A + B = C + D = Q` and all four numbers `A^2+C^2`, `B^2+C^2`,
`A^2+D^2`, `B^2+D^2` are perfect squares, then `3 ∣ Q`.

Case analysis: if `3 ∤ A` then `3 ∣ C` and `3 ∣ D`, so `3 ∣ Q = C + D`.
If `3 ∣ A` and `3 ∣ B` then `3 ∣ Q = A + B`.  If `3 ∣ A` and `3 ∤ B`, the
same argument with `B` in place of `A` gives `3 ∣ C` and `3 ∣ D`, so again
`3 ∣ Q = C + D`. -/
theorem three_dvd_Q (A B C D Q : Nat) (hAB : A + B = Q) (hCD : C + D = Q)
    (h1 : ∃ k, k * k = A * A + C * C) (h2 : ∃ k, k * k = B * B + C * C)
    (h3 : ∃ k, k * k = A * A + D * D) (h4 : ∃ k, k * k = B * B + D * D) : 3 ∣ Q := by
  by_cases hA : A % 3 = 0
  · by_cases hB : B % 3 = 0
    · have hQ : Q % 3 = 0 := by
        have h : Q % 3 = (A % 3 + B % 3) % 3 := by rw [← hAB, Nat.add_mod]
        rw [hA, hB] at h
        omega
      exact Nat.dvd_iff_mod_eq_zero.mpr hQ
    · exact three_dvd_sum hCD (three_dvd_of_not_dvd B C h2 hB)
        (three_dvd_of_not_dvd B D h4 hB)
  · exact three_dvd_sum hCD (three_dvd_of_not_dvd A C h1 hA)
      (three_dvd_of_not_dvd A D h3 hA)

end RationalDistance.ModArith
