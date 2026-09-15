/-
  Core-Lean formalisation of Theorem 6 of `notes/reduction.md`:

      A + B = C + D = Q,  A^2+C^2, B^2+C^2, A^2+D^2, B^2+D^2 all perfect squares
        ==>  12 | Q .

  The proof is the one in the notes: `3 | Q` always (ModArith.three_dvd_Q), and
  `4 | Q` for a tuple that is not all even (Parity.four_dvd_Q); a tuple that is
  all even is halved, which keeps all hypotheses (the four squares simply shrink
  by a factor 4) and strictly decreases `Q`, so induction on a bound for `Q`
  finishes.  Core Lean has no `Nat.strong_induction_on`, so the induction is
  carried out on the bounded statement `Q <= n`.

  Check (from `lean/`): `lake build RationalDistance.TwelveDvd`
-/
import RationalDistance.Parity

namespace RationalDistance.TwelveDvd

open RationalDistance.ModArith
open RationalDistance.Parity

/-- Commutative-monoid normalisation of a product of naturals. -/
theorem mul4 (k : Nat) : (2 * k) * (2 * k) = 4 * (k * k) := by
  simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-- `k` is even whenever `k * k` is divisible by 4. -/
theorem even_of_sq_dvd_four {k : Nat} (h : 4 ∣ k * k) : k % 2 = 0 := by
  by_cases hodd : k % 2 = 1
  · have h1 : k * k % 4 = 1 := odd_sq_mod4 k hodd
    obtain ⟨t, ht⟩ := h
    omega
  · have hlt : k % 2 < 2 := Nat.mod_lt k (by decide)
    omega

/-- If `k * k = 4 * m + 4 * n` then `m + n` is a perfect square. -/
theorem sq_of_four_mul_add {k m n : Nat} (h : k * k = 4 * m + 4 * n) :
    ∃ k', k' * k' = m + n := by
  have h4 : 4 ∣ k * k := ⟨m + n, by omega⟩
  have hk2 : k % 2 = 0 := even_of_sq_dvd_four h4
  obtain ⟨k', rfl⟩ := Nat.dvd_of_mod_eq_zero hk2
  refine ⟨k', ?_⟩
  rw [mul4] at h
  omega

/-- Auxiliary statement for the induction: `P n` says that every quadruple whose
sum `Q` is at most `n` has `12 | Q`. -/
theorem twelve_dvd_Q_aux : ∀ n Q : Nat, Q ≤ n → ∀ A B C D : Nat, A + B = Q → C + D = Q →
    (∃ k, k * k = A * A + C * C) → (∃ k, k * k = B * B + C * C) →
    (∃ k, k * k = A * A + D * D) → (∃ k, k * k = B * B + D * D) →
    12 ∣ Q := by
  intro n
  induction n with
  | zero =>
    intro Q hQ A B C D hAB hCD h1 h2 h3 h4
    have hQ0 : Q = 0 := by omega
    rw [hQ0]
    exact ⟨0, rfl⟩
  | succ n ih =>
    intro Q hQ A B C D hAB hCD h1 h2 h3 h4
    by_cases hsmall : Q ≤ n
    · exact ih Q hsmall A B C D hAB hCD h1 h2 h3 h4
    · have hQeq : Q = n + 1 := by omega
      have h3Q : 3 ∣ Q := three_dvd_Q A B C D Q hAB hCD h1 h2 h3 h4
      by_cases hall : A % 2 = 0 ∧ B % 2 = 0 ∧ C % 2 = 0 ∧ D % 2 = 0
      · -- all four even: halve the tuple; the sum drops to `Q / 2 <= n`
        obtain ⟨hA0, hB0, hC0, hD0⟩ := hall
        obtain ⟨A', hA'⟩ := Nat.dvd_of_mod_eq_zero hA0
        obtain ⟨B', hB'⟩ := Nat.dvd_of_mod_eq_zero hB0
        obtain ⟨C', hC'⟩ := Nat.dvd_of_mod_eq_zero hC0
        obtain ⟨D', hD'⟩ := Nat.dvd_of_mod_eq_zero hD0
        have e1 : A * A = 4 * (A' * A') := by rw [hA', mul4]
        have e2 : B * B = 4 * (B' * B') := by rw [hB', mul4]
        have e3 : C * C = 4 * (C' * C') := by rw [hC', mul4]
        have e4 : D * D = 4 * (D' * D') := by rw [hD', mul4]
        have g1 : ∃ k, k * k = A' * A' + C' * C' := by
          obtain ⟨k, hk⟩ := h1
          rw [e1, e3] at hk
          exact sq_of_four_mul_add hk
        have g2 : ∃ k, k * k = B' * B' + C' * C' := by
          obtain ⟨k, hk⟩ := h2
          rw [e2, e3] at hk
          exact sq_of_four_mul_add hk
        have g3 : ∃ k, k * k = A' * A' + D' * D' := by
          obtain ⟨k, hk⟩ := h3
          rw [e1, e4] at hk
          exact sq_of_four_mul_add hk
        have g4 : ∃ k, k * k = B' * B' + D' * D' := by
          obtain ⟨k, hk⟩ := h4
          rw [e2, e4] at hk
          exact sq_of_four_mul_add hk
        -- the halved tuple sums to `Q2 := A' + B'`, and `Q = 2 * Q2`
        let Q2 : Nat := A' + B'
        have hsumA : A' + B' = Q2 := rfl
        have hsumC : C' + D' = Q2 := by omega
        have hQ2 : Q2 ≤ n := by omega
        have ihalf : 12 ∣ Q2 := ih Q2 hQ2 A' B' C' D' hsumA hsumC g1 g2 g3 g4
        have hQeven : Q = 2 * Q2 := by omega
        rw [hQeven]
        obtain ⟨t, ht⟩ := ihalf
        exact ⟨2 * t, by omega⟩
      · -- not all even: combine the two machine-checked halves
        have h4Q : 4 ∣ Q := four_dvd_Q A B C D Q hAB hCD h1 h2 h3 h4 hall
        obtain ⟨a, ha⟩ := h3Q
        obtain ⟨b, hb⟩ := h4Q
        have h3b : 3 ∣ b := by omega
        obtain ⟨c, rfl⟩ := h3b
        exact ⟨c, by omega⟩

/-- **Theorem 6.** Every quadruple satisfying the four-square condition with
`A + B = C + D = Q` has `12 | Q`. -/
theorem twelve_dvd_Q (A B C D Q : Nat) (hAB : A + B = Q) (hCD : C + D = Q)
    (h1 : ∃ k, k * k = A * A + C * C) (h2 : ∃ k, k * k = B * B + C * C)
    (h3 : ∃ k, k * k = A * A + D * D) (h4 : ∃ k, k * k = B * B + D * D) :
    12 ∣ Q :=
  twelve_dvd_Q_aux Q Q (by omega) A B C D hAB hCD h1 h2 h3 h4

end RationalDistance.TwelveDvd
