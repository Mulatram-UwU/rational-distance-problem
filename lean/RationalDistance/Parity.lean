/-
  Core-Lean formalisation of the *2-adic* half of the parity lemma
  (`notes/reduction.md`, Lemma 4), i.e. the statement

      A + B = C + D = Q,  all four of A^2+C^2, B^2+C^2, A^2+D^2, B^2+D^2 squares,
      and A,B,C,D not all even
        ==>  4 | Q .

  (This is the part of Theorem 6 (`12 | Q`) whose 3-adic half is
  `RationalDistance.ModArith.three_dvd_Q`.)

  Only core Lean is used (`decide`, `omega`, `match`, `rcases`); no Mathlib.

  Build/check (from the repository root, with `lake` on PATH):
    lake env lean lean/RationalDistance/Parity.lean
-/
import RationalDistance.ModArith

namespace RationalDistance.Parity

open RationalDistance.ModArith

/-! ## Squares modulo 4 -/

/-- Residue form: a square of a residue `< 4` is `0` or `1` mod 4. -/
theorem sq_mod4_aux (r : Nat) (hr : r < 4) : r * r % 4 = 0 ∨ r * r % 4 = 1 := by
  match r with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | k + 4 => exact absurd hr (by omega)

/-- A square is `0` or `1` modulo 4. -/
theorem sq_mod4 (n : Nat) : n * n % 4 = 0 ∨ n * n % 4 = 1 := by
  have h : n * n % 4 = (n % 4) * (n % 4) % 4 := by rw [Nat.mul_mod]
  rw [h]
  exact sq_mod4_aux (n % 4) (Nat.mod_lt n (by decide))

/-- Residue form: the square of an odd residue `< 4` is `1` mod 4. -/
theorem odd_sq_mod4_aux (r : Nat) (hr : r < 4) (h : r % 2 = 1) : r * r % 4 = 1 := by
  match r with
  | 0 => exact absurd h (by decide)
  | 1 => decide
  | 2 => exact absurd h (by decide)
  | 3 => decide
  | k + 4 => exact absurd hr (by omega)

/-- The square of an odd number is `1` modulo 4. -/
theorem odd_sq_mod4 (n : Nat) (h : n % 2 = 1) : n * n % 4 = 1 := by
  have hmul : n * n % 4 = (n % 4) * (n % 4) % 4 := by rw [Nat.mul_mod]
  have hmod2 : n % 4 % 2 = 1 := by
    have e : n % 4 % 2 = n % 2 := Nat.mod_mod_of_dvd n ⟨2, rfl⟩
    rw [e, h]
  rw [hmul]
  exact odd_sq_mod4_aux (n % 4) (Nat.mod_lt n (by decide)) hmod2

/-! ## No Pythagorean-type pair has both entries odd -/

/-- If `A^2 + C^2` is a perfect square then `A` and `C` are not both odd. -/
theorem not_both_odd (A C : Nat) (h : ∃ k, k * k = A * A + C * C) :
    ¬ (A % 2 = 1 ∧ C % 2 = 1) := by
  rintro ⟨hA, hC⟩
  obtain ⟨k, hk⟩ := h
  have hA4 := odd_sq_mod4 A hA
  have hC4 := odd_sq_mod4 C hC
  have hk4 := sq_mod4 k
  have hsum : (A * A + C * C) % 4 = 2 := by rw [Nat.add_mod, hA4, hC4]
  have hk2 : k * k % 4 = 2 := by rw [hk]; exact hsum
  rcases hk4 with h | h <;> omega

/-! ## The 2-adic statement -/

/-- The order of the two squares in the hypothesis does not matter. -/
theorem swap_sq_sum {X Y : Nat} (h : ∃ k, k * k = X * X + Y * Y) :
    ∃ k, k * k = Y * Y + X * X := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, by rw [hk, Nat.add_comm]⟩

/-- `4 | Y` whenever `Y` is the "even partner" of an odd `X` in a Pythagorean
pair; this is `RationalDistance.ModArith.odd_left_forces` with the roles of the
two entries exchanged. -/
theorem four_dvd_of_odd_partner (X Y : Nat) (hX : X % 2 = 1)
    (h : ∃ k, k * k = X * X + Y * Y) : 4 ∣ Y :=
  Nat.dvd_iff_mod_eq_zero.mpr (odd_left_forces X Y 0 h hX)

/-- **(Lemma 4, 2-adic part)** If `A + B = C + D = Q`, the four numbers
`A^2+C^2, B^2+C^2, A^2+D^2, B^2+D^2` are perfect squares and `A,B,C,D` are not
all even, then `4 | Q`.

(The two parity patterns (P1) and (P2) of the hand proof are the two branches
`hAodd` and `hCodd` below; only their common consequence `4 | Q` is stated
here.) -/
theorem four_dvd_Q (A B C D Q : Nat) (hAB : A + B = Q) (hCD : C + D = Q)
    (h1 : ∃ k, k * k = A * A + C * C) (h2 : ∃ k, k * k = B * B + C * C)
    (h3 : ∃ k, k * k = A * A + D * D) (h4 : ∃ k, k * k = B * B + D * D)
    (hne : ¬ (A % 2 = 0 ∧ B % 2 = 0 ∧ C % 2 = 0 ∧ D % 2 = 0)) : 4 ∣ Q := by
  have hAC := not_both_odd A C h1
  have hAD := not_both_odd A D h3
  have hBC := not_both_odd B C h2
  have hBD := not_both_odd B D h4
  have hA2 := Nat.mod_lt A (by decide : 0 < 2)
  have hB2 := Nat.mod_lt B (by decide : 0 < 2)
  have hC2 := Nat.mod_lt C (by decide : 0 < 2)
  have hD2 := Nat.mod_lt D (by decide : 0 < 2)
  -- `4 | Q` from `4 | C` and `4 | D`
  have fromCD : 4 ∣ C → 4 ∣ D → 4 ∣ Q := by
    intro hc hd
    obtain ⟨c, hc⟩ := hc
    obtain ⟨d, hd⟩ := hd
    exact ⟨c + d, by omega⟩
  have fromAB : 4 ∣ A → 4 ∣ B → 4 ∣ Q := by
    intro ha hb
    obtain ⟨a, ha⟩ := ha
    obtain ⟨b, hb⟩ := hb
    exact ⟨a + b, by omega⟩
  by_cases hAodd : A % 2 = 1
  · -- (P1): A odd, so C and D are even, and each of them is the even partner
    -- of the odd number A, hence divisible by 4
    have hCeven : C % 2 = 0 := by
      by_cases h : C % 2 = 1
      · exact absurd ⟨hAodd, h⟩ hAC
      · omega
    have hDeven : D % 2 = 0 := by
      by_cases h : D % 2 = 1
      · exact absurd ⟨hAodd, h⟩ hAD
      · omega
    exact fromCD (four_dvd_of_odd_partner A C hAodd h1) (four_dvd_of_odd_partner A D hAodd h3)
  · have hAeven : A % 2 = 0 := by omega
    by_cases hBodd : B % 2 = 1
    · exact fromCD (four_dvd_of_odd_partner B C hBodd h2) (four_dvd_of_odd_partner B D hBodd h4)
    · have hBeven : B % 2 = 0 := by omega
      -- A and B are both even, so (not all even) forces C or D to be odd
      by_cases hCodd : C % 2 = 1
      · exact fromAB (four_dvd_of_odd_partner C A hCodd (swap_sq_sum h1))
          (four_dvd_of_odd_partner C B hCodd (swap_sq_sum h2))
      · have hCeven : C % 2 = 0 := by omega
        have hDodd : D % 2 = 1 := by
          by_cases h : D % 2 = 1
          · exact h
          · exfalso
            have hDeven : D % 2 = 0 := by omega
            exact hne ⟨hAeven, hBeven, hCeven, hDeven⟩
        exact fromAB (four_dvd_of_odd_partner D A hDodd (swap_sq_sum h3))
          (four_dvd_of_odd_partner D B hDodd (swap_sq_sum h4))

end RationalDistance.Parity
