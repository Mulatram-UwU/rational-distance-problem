/-
  RationalDistanceAlgo.Bridge
  ===========================

  The bridge between the *geometry* of the rational-distance problem and the
  *integer system* that the search algorithm actually runs on
  (`REPORT.md` §1, `notes/reduction.md` Theorems 1–3).

  Geometric statement: a point `(x, y)` of the open unit square is at rational
  distance from all four corners iff `x^2+y^2`, `(1-x)^2+y^2`, `x^2+(1-y)^2`,
  `(1-x)^2+(1-y)^2` are all squares in `ℚ`.

  Integer statement (`RationalDistance.Algorithm.IsSol`): there are `A B C D Q`
  with `A + B = Q = C + D`, `0 < A,B,C,D < Q`, `Q <= N` and
  `A^2+C^2`, `B^2+C^2`, `A^2+D^2`, `B^2+D^2` all perfect squares in `ℕ`.

  `hasRatPoint_iff` proves the two are equivalent, so the machine-checked
  correctness theorems about the algorithm (`RationalDistance.Algorithm`)
  really do speak about the *geometric* problem.

  The only non-elementary ingredient is `nat_isSquare_of_rat_isSquare`: a
  rational number whose square is a natural number is a natural number.
-/
import Mathlib
import RationalDistance.Algorithm

namespace RationalDistanceAlgo

open RationalDistance.Algorithm

/-! ## A rational with an integral square -/

/-- If a rational number has a square root in `ℚ` whose square is a natural
number, then that number is a perfect square of a natural.

Proof: write `q = q.num / q.den`.  Squaring and clearing denominators gives
`q.num^2 = n * q.den^2`, so `q.den` divides `q.num^2`; since `q.num.natAbs` and
`q.den` are coprime (`Rat.reduced`), `q.den = 1`, i.e. `q` is an integer. -/
theorem nat_isSquare_of_rat_isSquare {n : ℕ} {q : ℚ} (h : q * q = (n : ℚ)) :
    ∃ k : ℕ, k * k = n := by
  -- clear denominators
  have hnum : (q.num : ℤ) ^ 2 = (n : ℤ) * (q.den : ℤ) ^ 2 := by
    have h' : ((q.num : ℚ)) ^ 2 = (n : ℚ) * (q.den : ℚ) ^ 2 := by
      have h2 : (q.num : ℚ) / (q.den : ℚ) = q := Rat.num_div_den q
      have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
      rw [← h2] at h
      field_simp at h
      linarith [h]
    exact_mod_cast h'
  -- pass to `ℕ` and conclude `q.den = 1`
  have hnat : q.num.natAbs ^ 2 = n * q.den ^ 2 := by
    have := congrArg Int.natAbs hnum
    simpa [Int.natAbs_pow, Int.natAbs_mul] using this
  have hdvd : q.den ∣ q.num.natAbs ^ 2 := ⟨n * q.den, by rw [hnat]; ring⟩
  have hcop : q.den.Coprime (q.num.natAbs ^ 2) := (Rat.reduced q).symm.pow_right 2
  have h1 : q.den = 1 := hcop.eq_one_of_dvd hdvd
  -- hence `q` is the integer `q.num`, and `q.num.natAbs` is the wanted root
  have hq : (q.num : ℚ) = q := by
    rw [← Rat.num_div_den q, h1]
    norm_num
  have h4 : (q.num : ℤ) ^ 2 = (n : ℤ) := by
    have h2 : (q.num : ℚ) ^ 2 = (n : ℚ) := by rw [hq, sq]; exact h
    exact_mod_cast h2
  have hnat2 : q.num.natAbs ^ 2 = n := by
    have := congrArg Int.natAbs h4
    simpa [Int.natAbs_pow] using this
  exact ⟨q.num.natAbs, by rw [← sq]; exact hnat2⟩

/-- The `IsSquare` form used for each of the four distance conditions: a rational
square root of `(A/Q)^2 + (C/Q)^2` yields a natural square root of `A^2 + C^2`. -/
theorem nat_sq_of_rat_sq_sum {Q A C : ℕ} (hQ : 0 < Q) {a : ℚ}
    (h : a * a = ((A : ℚ) / Q) ^ 2 + ((C : ℚ) / Q) ^ 2) :
    ∃ k : ℕ, k * k = A ^ 2 + C ^ 2 := by
  refine nat_isSquare_of_rat_isSquare (n := A ^ 2 + C ^ 2) (q := (Q : ℚ) * a) ?_
  have hQ' : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hmul : ((Q : ℚ) * a) * ((Q : ℚ) * a) = (Q : ℚ) ^ 2 * (a * a) := by ring
  rw [hmul, h]
  field_simp
  push_cast
  ring

/-! ## The two formulations -/

/-- `RatDist x y` : the point `(x, y)` is at rational distance from all four
corners of the unit square. -/
def RatDist (x y : ℚ) : Prop :=
  IsSquare (x ^ 2 + y ^ 2) ∧ IsSquare ((1 - x) ^ 2 + y ^ 2) ∧
    IsSquare (x ^ 2 + (1 - y) ^ 2) ∧ IsSquare ((1 - x) ^ 2 + (1 - y) ^ 2)

/-- There is a rational point **strictly inside** the open unit square, at
rational distance from all four corners, whose coordinates can be written over
a common denominator `Q <= N`. -/
def HasRatPoint (N : ℕ) : Prop :=
  ∃ Q A C : ℕ, 0 < Q ∧ Q ≤ N ∧ 0 < A ∧ A < Q ∧ 0 < C ∧ C < Q ∧
    RatDist ((A : ℚ) / Q) ((C : ℚ) / Q)

/-- **Bridge.**  The geometric existence statement is equivalent to the integer
system the search algorithm runs on.

(Reading off the coordinates `x = A/Q`, `y = C/Q` with `0 < x, y < 1` gives
`0 < A, C < Q`; conversely a rational point can always be written over the
common denominator `lcm (den x) (den y)`.) -/
theorem hasRatPoint_iff (N : ℕ) :
    HasRatPoint N ↔ ∃ A B C D Q : ℕ, IsSol N A B C D Q := by
  constructor
  · -- geometric  =>  integer
    rintro ⟨Q, A, C, hQ, hQN, hA, hAQ, hC, hCQ, hd1, hd2, hd3, hd4⟩
    obtain ⟨a, ha⟩ := hd1
    obtain ⟨b, hb⟩ := hd2
    obtain ⟨c, hc⟩ := hd3
    obtain ⟨d, hd⟩ := hd4
    -- each of the four rational squares becomes a natural square
    have e1 : ∃ k : ℕ, k * k = A ^ 2 + C ^ 2 :=
      nat_sq_of_rat_sq_sum hQ (A := A) (C := C) (a := a) ha.symm
    have e2 : ∃ k : ℕ, k * k = (Q - A) ^ 2 + C ^ 2 := by
      refine nat_sq_of_rat_sq_sum (Q := Q) hQ (A := Q - A) (C := C) (a := b) ?_
      rw [← hb]
      have hcast : (((Q - A : ℕ) : ℚ)) / Q = 1 - (A : ℚ) / Q := by
        push_cast [Nat.cast_sub hAQ.le]
        field_simp
      rw [hcast]
    have e3 : ∃ k : ℕ, k * k = A ^ 2 + (Q - C) ^ 2 := by
      refine nat_sq_of_rat_sq_sum (Q := Q) hQ (A := A) (C := Q - C) (a := c) ?_
      rw [← hc]
      have hcast : (((Q - C : ℕ) : ℚ)) / Q = 1 - (C : ℚ) / Q := by
        push_cast [Nat.cast_sub hCQ.le]
        field_simp
      rw [hcast]
    have e4 : ∃ k : ℕ, k * k = (Q - A) ^ 2 + (Q - C) ^ 2 := by
      refine nat_sq_of_rat_sq_sum (Q := Q) hQ (A := Q - A) (C := Q - C) (a := d) ?_
      rw [← hd]
      have hcastA : (((Q - A : ℕ) : ℚ)) / Q = 1 - (A : ℚ) / Q := by
        push_cast [Nat.cast_sub hAQ.le]
        field_simp
      have hcastC : (((Q - C : ℕ) : ℚ)) / Q = 1 - (C : ℚ) / Q := by
        push_cast [Nat.cast_sub hCQ.le]
        field_simp
      rw [hcastA, hcastC]
    obtain ⟨k1, hk1⟩ := e1
    obtain ⟨k2, hk2⟩ := e2
    obtain ⟨k3, hk3⟩ := e3
    obtain ⟨k4, hk4⟩ := e4
    exact ⟨A, Q - A, C, Q - C, Q, by omega, by omega, hA, by omega, hC, by omega,
      hQN, ⟨k1, by conv_lhs => rw [← pow_two, ← pow_two]; exact hk1.symm⟩, ⟨k2, by conv_lhs => rw [← pow_two, ← pow_two]; exact hk2.symm⟩, ⟨k3, by conv_lhs => rw [← pow_two, ← pow_two]; exact hk3.symm⟩, ⟨k4, by conv_lhs => rw [← pow_two, ← pow_two]; exact hk4.symm⟩⟩
  · -- integer  =>  geometric
    rintro ⟨A, B, C, D, Q, hAB, hCD, hA, hB, hC, hD, hQN, hp1, hp2, hp3, hp4⟩
    obtain ⟨k1, hk1⟩ := hp1
    obtain ⟨k2, hk2⟩ := hp2
    obtain ⟨k3, hk3⟩ := hp3
    obtain ⟨k4, hk4⟩ := hp4
    have hQA : ((Q - A : ℕ) : ℚ) = (Q : ℚ) - A := by
      push_cast [Nat.cast_sub (by omega : A ≤ Q)]; ring
    have hQC : ((Q - C : ℕ) : ℚ) = (Q : ℚ) - C := by
      push_cast [Nat.cast_sub (by omega : C ≤ Q)]; ring
    have hBQ : (B : ℚ) = (Q : ℚ) - A := by
      have : (Q : ℕ) = A + B := hAB.symm
      rw [this]; push_cast; ring
    have hDQ : (D : ℚ) = (Q : ℚ) - C := by
      have : (Q : ℕ) = C + D := hCD.symm
      rw [this]; push_cast; ring
    have hQ' : (Q : ℚ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
    have hQ' : (Q : ℚ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
    refine ⟨Q, A, C, by omega, hQN, hA, by omega, hC, by omega, ?_, ?_, ?_, ?_⟩
    · refine ⟨(k1 : ℚ) / Q, ?_⟩
      have hq : (k1 : ℚ) * k1 = (A : ℚ) * A + (C : ℚ) * C := by
        have h0 : ((k1 * k1 : ℕ) : ℚ) = ((A * A + C * C : ℕ) : ℚ) := by rw [hk1]
        push_cast at h0
        linarith [h0]
      rw [div_mul_div_comm, hq]
      field_simp
    · refine ⟨(k2 : ℚ) / Q, ?_⟩
      have hq : (k2 : ℚ) * k2 = (B : ℚ) * B + (C : ℚ) * C := by
        have h0 : ((k2 * k2 : ℕ) : ℚ) = ((B * B + C * C : ℕ) : ℚ) := by rw [hk2]
        push_cast at h0
        linarith [h0]
      rw [div_mul_div_comm, hq, hBQ]
      field_simp
    · refine ⟨(k3 : ℚ) / Q, ?_⟩
      have hq : (k3 : ℚ) * k3 = (A : ℚ) * A + (D : ℚ) * D := by
        have h0 : ((k3 * k3 : ℕ) : ℚ) = ((A * A + D * D : ℕ) : ℚ) := by rw [hk3]
        push_cast at h0
        linarith [h0]
      rw [div_mul_div_comm, hq, hDQ]
      field_simp
    · refine ⟨(k4 : ℚ) / Q, ?_⟩
      have hq : (k4 : ℚ) * k4 = (B : ℚ) * B + (D : ℚ) * D := by
        have h0 : ((k4 * k4 : ℕ) : ℚ) = ((B * B + D * D : ℕ) : ℚ) := by rw [hk4]
        push_cast at h0
        linarith [h0]
      rw [div_mul_div_comm, hq, hBQ, hDQ]
      field_simp

end RationalDistanceAlgo
