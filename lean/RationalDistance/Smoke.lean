/-
  Smoke tests for a CORE-LEAN-ONLY environment (no Mathlib).

  Every test in this file compiles against the bare Lean 4 core
  distribution (default prelude, no external packages).  Tests for
  Mathlib-only tactics live in `RationalDistance/MathlibTactics.lean.off`
  so that they do not break `lake build`.
-/

namespace RationalDistance.Smoke

/-! ## `decide` and `native_decide` (core) -/

theorem twelve_sq : (12 : Nat) ^ 2 = 144 := by decide

/-- Integer square identity, a Pythagorean triple: 7² + 24² = 25². -/
theorem pythag_7_24_25 :
    (7 : Nat) ^ 2 + (24 : Nat) ^ 2 = (25 : Nat) ^ 2 := by decide

theorem twelve_sq_native : (12 : Nat) ^ 2 = 144 := by native_decide

/-- A negative statement, also by `decide`. -/
theorem three_ne_four : ¬ (3 = 4) := by decide

/-- Larger computation: 2^10 = 1024, kernel-checked. -/
theorem two_pow_ten : (2 : Nat) ^ 10 = 1024 := by decide

/-- Same statement over `Int` (integer squares). -/
theorem pythag_int :
    (7 : Int) ^ 2 + (24 : Int) ^ 2 = (25 : Int) ^ 2 := by decide

/-! ## `omega` (core Presburger / linear arithmetic) -/

theorem omega_le_succ (a b : Nat) (h : a ≤ b) : a + 1 ≤ b + 1 := by omega

theorem omega_subst (a b c : Nat) (h1 : a + b = 10) (h2 : c = a + b) : c = 10 := by omega

theorem omega_int_antisymm (a b : Int) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by omega

/-! ## `simp` (core simplifier) -/

theorem simp_add_zero (a : Nat) : a + 0 = a := by simp

theorem simp_mul_one (a : Nat) : a * 1 = a := by simp

theorem simp_all_test (p : Prop) (h : p) : p := by simp_all

/-! ## Structural / basic core tactics -/

theorem rfl_test : 1 = 1 := rfl

theorem trivial_test : True := trivial

theorem intro_exact (p q : Prop) (h : p) : q → p := by intro _; exact h

theorem cases_test (n : Nat) : n = 0 ∨ n > 0 := by
  cases n with
  | zero => left; rfl
  | succ k => right; exact Nat.succ_pos k

theorem subst_test (a b : Nat) (h : a = b) : b = a := by subst h; rfl

theorem by_cases_test (p : Prop) : p ∨ ¬ p := by
  by_cases h : p
  · left; exact h
  · right; exact h

theorem exfalso_test (p : Prop) (h : False) : p := by exfalso; exact h

theorem induction_test (n : Nat) : n + 0 = n := by
  induction n <;> simp_all

theorem calc_test (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  calc a = b := h1
       _ = c := h2

theorem ext_test (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g := by
  ext x; exact h x

theorem funext_test (f g : Nat → Nat) (h : ∀ x, f x = g x) : f = g := by
  funext x; exact h x

/-! ## Cast tactics (core) -/

theorem norm_cast_test (a : Nat) : ((a : Int) + 0) = a := by norm_cast

theorem push_cast_test (a : Nat) : ((a : Int) + 0) = (a : Int) := by push_cast; rfl

end RationalDistance.Smoke
