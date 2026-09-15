import Mathlib

example : (3 : Nat) ^ 2 = 9 := by norm_num
example (a b : Nat) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring
