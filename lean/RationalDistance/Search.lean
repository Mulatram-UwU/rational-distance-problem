/-
  (P1) Exhaustive machine-checked search.

  `noSolutionUpto N = true` means: there is no quadruple `A B C D` with
  `A + B = Q = C + D`, all four entries positive, and all four of
  `A^2+C^2, B^2+C^2, A^2+D^2, B^2+D^2` perfect squares, for any `Q <= N`.

  This is the integer form of "no point strictly inside the unit square at
  rational distance from all four corners whose coordinates can be written
  over a common denominator `<= N`".

  The headline search result at bound 500 lives in `BigCheck500.lean` at the
  project root.  That file is deliberately NOT part of this library's glob, so
  the default `lake build` stays fast; see `notes/lean-formalisation.md` for
  the exact command to run it.
-/

/-- `isSq n` is `true` iff `n` is a perfect square of a natural number. -/
def isSq (n : Nat) : Bool := Nat.sqrt n * Nat.sqrt n == n

/-- The four-square condition (H1) + (H2), as a Bool-valued checker. -/
def good (Q A B C D : Nat) : Bool :=
  (A + B == Q) && (C + D == Q) && decide (0 < A) && decide (0 < B) &&
  decide (0 < C) && decide (0 < D) &&
  isSq (A * A + C * C) && isSq (B * B + C * C) &&
  isSq (A * A + D * D) && isSq (B * B + D * D)

/-- The *relaxed* condition: `good` without the `B^2 + D^2` check.  Used only
to exhibit a non-vacuous example (see below). -/
def good3 (Q A B C D : Nat) : Bool :=
  (A + B == Q) && (C + D == Q) && decide (0 < A) && decide (0 < B) &&
  decide (0 < C) && decide (0 < D) &&
  isSq (A * A + C * C) && isSq (B * B + C * C) && isSq (A * A + D * D)

/-- `searchQ Q` is `true` iff no quadruple with common denominator `Q`
satisfies `good`.  `B = Q - A` and `D = Q - C` are determined, and `good`
itself enforces `0 < A, B, C, D`, so this ranges over exactly the tuples with
`A + B = C + D = Q` and all four entries positive. -/
def searchQ (Q : Nat) : Bool :=
  (List.range (Q + 1)).all (fun A =>
    (List.range (Q + 1)).all (fun C => !(good Q A (Q - A) C (Q - C))))

/-- No solution with common denominator `Q <= N`. -/
def noSolutionUpto (N : Nat) : Bool := (List.range (N + 1)).all searchQ

/-! ## Sanity / non-vacuity checks

Note: these use `native_decide`, not `decide`.  `Nat.sqrt` is defined by
well-founded recursion, so the *kernel* evaluator behind `decide` cannot reduce
it; `native_decide` compiles the expression instead and works fine. -/

/-- `isSq` accepts a perfect square. -/
example : isSq 144 = true := by native_decide

/-- `isSq` rejects a non-square. -/
example : isSq 145 = false := by native_decide

example : isSq 0 = true := by native_decide

/-- **Non-vacuity**: `(Q,A,B,C,D) = (52, 24, 28, 45, 7)` *does* satisfy the
relaxed three-condition problem — `24^2+45^2 = 51^2`, `28^2+45^2 = 53^2`,
`24^2+7^2 = 25^2` — so the checkers are not vacuously false. -/
example : good3 52 24 28 45 7 = true := by native_decide

/-- The same tuple is rejected by the full checker: `28^2 + 7^2 = 833` is not a
perfect square.  The fourth condition is what rules it out. -/
example : good 52 24 28 45 7 = false := by native_decide

/-! ## (P1) The finite-check theorem, bound 100 (compiles in ~18 s) -/

/-- **(P1)** There is no solution with common denominator `Q <= 100`.

Machine-checked by `native_decide`: Lean compiles the `Bool`-valued expression
`noSolutionUpto 100`, evaluates it, and checks the resulting `true` in the
kernel via `Lean.ofReduceBool`. -/
theorem no_solution_Q_le_100 : noSolutionUpto 100 = true := by native_decide
