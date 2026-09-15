# Machine-checked formalisation (core Lean 4, no Mathlib)

Toolchain: Lean **4.34.0-rc2** (`x86_64-w64-windows-gnu`), Lake 5.0.0-src.
Project: `<repo>/lean` (the `lean/` directory of this repository).
Toolchain bin dir: `<elan>/toolchains/leanprover--lean4---v4.34.0-rc2/bin`
(abbreviated `$TC` below).  `<repo>` is the root of this checkout, `<elan>` the elan
home directory (`~/.elan` by default); both stand in for absolute paths on the machine
these notes were written on, so that no local path is published.

Everything below is **core Lean only** — no Mathlib, no external packages.
The whole file set uses only `Init` (the default prelude).

> On another machine, read `$TC/lake.exe` as `lake` from your `PATH` (installed by
> `elan`).  Both `lakefile.toml` files are relative (`lean-mathlib` picks up the core
> project through `srcDir = "../lean"`), so the two projects travel together.

---

## 1. The build command (verified)

```bash
cd <repo>/lean
TC=<elan>/toolchains/leanprover--lean4---v4.34.0-rc2/bin
"$TC/lake.exe" build
```

Observed output (2026-09-14), exit code **0**:

```
✔ [3/6] Built RationalDistance.ModArith (5.3s)
✔ [4/6] Built RationalDistance.Search (5.4s)
✔ [5/6] Built RationalDistance (3.6s)
Build completed successfully (6 jobs).
```

Wall clock ~11 s. `lake build RationalDistance` gives the same result.
There are **no errors and no warnings**.

Library layout (`lakefile.toml`): package `RationalDistance`, one
`[[lean_lib]] name = "RationalDistance"`, and a root module
`RationalDistance.lean` that imports the three modules:

```lean
import RationalDistance.Smoke
import RationalDistance.ModArith
import RationalDistance.Search
```

Single-file check without Lake:

```bash
TC=<elan>/toolchains/leanprover--lean4---v4.34.0-rc2/bin
"$TC/lean.exe" RationalDistance/ModArith.lean     # exit 0
```

`lake env` is needed when a file must import the library's own modules:

```bash
"$TC/lake.exe" env "$TC/lean.exe" -DmaxHeartbeats=0 <file>
```

---

## 2. Trust model — read this before quoting the results

`#print axioms` on the four residue/divisibility results:

```
'RationalDistance.ModArith.sq_mod8'          depends on axioms: [propext, Quot.sound]
'RationalDistance.ModArith.sq_mod3'          depends on axioms: [propext, Quot.sound]
'RationalDistance.ModArith.odd_left_forces'  depends on axioms: [propext, Quot.sound]
'RationalDistance.ModArith.three_dvd_Q'      depends on axioms: [propext, Quot.sound]
```

`propext` and `Quot.sound` are the two standard Lean axioms — these theorems are
fully kernel-checked, no `sorryAx`.

The **P1 search theorems are different**: they are proved by `native_decide`,
which is (as documented by Lean) *trusted* rather than purely kernel-checked. It
compiles the `Bool` expression, evaluates it natively, and asserts the result:

```
'no_solution_Q_le_100' depends on axioms: [no_solution_Q_le_100._native.native_decide.ax_1_1]
```

That axiom is the native-evaluation certificate. This is the standard
`native_decide` caveat and is inherent to the method (the task asked for
`native_decide`); it is *not* a `sorry`. Concretely it means: the search result
trusts Lean's own compiler+runtime, not just the kernel.

One practical consequence, which cost real time here: **`decide` alone cannot
prove anything involving `isSq`**. `Nat.sqrt` is defined by well-founded
recursion, so the kernel evaluator gets stuck:

```
error: Tactic `decide` failed for proposition
  good 52 24 28 45 7 = false
because its `Decidable` instance ... did not reduce to `isTrue` or `isFalse`.
After unfolding the instances ..., reduction got stuck at the `Decidable` instance
```

Use `native_decide` for every `isSq`/`good`/`noSolutionUpto` statement.

---

## 3. PROVED — (P2) squares modulo 8 and modulo 3

File: `<repo>/lean/RationalDistance/ModArith.lean`
Both are kernel-checked, axioms `[propext, Quot.sound]`.

### `sq_mod8`

```lean
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
```

### `sq_mod3`

```lean
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
```

**Technique note.** Core Lean has no `interval_cases` and no `Nat.ModEq`, and
`omega` cannot do the nonlinear step `n*n`. The idiom used throughout is:
reduce to the residue via `Nat.mul_mod`, then `match` on the residue with the
eight (resp. three) literal cases closed by `decide` and the catch-all pattern
`k + 8` (resp. `k + 3`) closed by `exact absurd hr (by omega)`.

---

## 4. PROVED — (P3) `A` odd forces `4 | C`

File: `<repo>/lean/RationalDistance/ModArith.lean`
Kernel-checked, axioms `[propext, Quot.sound]`.

Exactly the requested signature.

```lean
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
/-- **(P3)** If `A` is odd and `A^2 + C^2` is a perfect square then `4 | C`. -/
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
```

Notes:
* The `Q` parameter (present in the requested signature) is unused; the
  `set_option linter.unusedVariables false in` attribute suppresses the
  resulting warning, so the build is warning-free.
* `Nat.mod_mod_of_dvd` is the core lemma that lowers `% 8` to `% 2` / `% 4`.

---

## 5. PROVED — (P4) `3 | Q`

File: `<repo>/lean/RationalDistance/ModArith.lean`
Kernel-checked, axioms `[propext, Quot.sound]`.

```lean
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
`A^2+D^2`, `B^2+D^2` are perfect squares, then `3 ∣ Q`. -/
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
```

The case analysis follows the sketch in `reduction.md` Lemma 5. Note that the
"`3 ∣ A` and `3 ∤ B`" branch is not even needed as a contradiction: the same
argument with `B` in place of `A` directly yields `3 ∣ C`, `3 ∣ D`, hence
`3 ∣ Q = C + D`.

---

## 6. PROVED — (P1) the exhaustive search

Files:
* `<repo>/lean/RationalDistance/Search.lean` — definitions, non-vacuity
  checks, and the bound-100 theorem (part of the default build).
* `<repo>/lean/BigCheck500.lean` — the bound-500 theorem (deliberately
  **excluded** from the default build, see below).

### Definitions (exactly as requested)

```lean
/-- `isSq n` is `true` iff `n` is a perfect square of a natural number. -/
def isSq (n : Nat) : Bool := Nat.sqrt n * Nat.sqrt n == n

/-- The four-square condition (H1) + (H2), as a Bool-valued checker. -/
def good (Q A B C D : Nat) : Bool :=
  (A + B == Q) && (C + D == Q) && decide (0 < A) && decide (0 < B) &&
  decide (0 < C) && decide (0 < D) &&
  isSq (A * A + C * C) && isSq (B * B + C * C) &&
  isSq (A * A + D * D) && isSq (B * B + D * D)

/-- The *relaxed* condition: `good` without the `B^2 + D^2` check. -/
def good3 (Q A B C D : Nat) : Bool :=
  (A + B == Q) && (C + D == Q) && decide (0 < A) && decide (0 < B) &&
  decide (0 < C) && decide (0 < D) &&
  isSq (A * A + C * C) && isSq (B * B + C * C) && isSq (A * A + D * D)

/-- `searchQ Q` is `true` iff no quadruple with common denominator `Q` satisfies `good`. -/
def searchQ (Q : Nat) : Bool :=
  (List.range (Q + 1)).all (fun A =>
    (List.range (Q + 1)).all (fun C => !(good Q A (Q - A) C (Q - C))))

/-- No solution with common denominator `Q <= N`. -/
def noSolutionUpto (N : Nat) : Bool := (List.range (N + 1)).all searchQ
```

`B = Q - A` and `D = Q - C` are determined by `A + B = Q = C + D`, and `good`
itself enforces `0 < A, B, C, D`, so the `List.range (Q+1) × List.range (Q+1)`
loop ranges over exactly the tuples with `A + B = C + D = Q` and all four
entries positive. Hence the search is complete for those conditions.

### The theorem (in the default build)

```lean
/-- **(P1)** There is no solution with common denominator `Q <= 100`. -/
theorem no_solution_Q_le_100 : noSolutionUpto 100 = true := by native_decide
```

Source: `RationalDistance/Search.lean`, last line.
Observed: part of `lake build`, exit 0, no output (the whole build is ~11 s).

### The large bound (NOT in the default build)

```lean
import RationalDistance.Search

set_option maxHeartbeats 0 in
/-- **(P1)** There is no solution with common denominator `Q <= 500`. -/
theorem no_solution_Q_le_500 : noSolutionUpto 500 = true := by native_decide
```

Source: `<repo>/lean/BigCheck500.lean`.
Run it with:

```bash
cd <repo>/lean
TC=<elan>/toolchains/leanprover--lean4---v4.34.0-rc2/bin
"$TC/lake.exe" env "$TC/lean.exe" -DmaxHeartbeats=0 BigCheck500.lean
```

Observed: **exit 0, no output, 139-140 s** (139 s in the first run, 140 s in the
repeat run that verified this exact command).

Why it is excluded: a root-level module named `BigCheck500` does not match the
glob `["RationalDistance", "RationalDistance.*"]` that Lake derives from
`[[lean_lib]] name = "RationalDistance"`, and Lake only builds modules reachable
from the root module `RationalDistance.lean`. So the default build stays at
~11 s instead of ~2.5 min. This was verified: `lake build` and
`lake build RationalDistance` both report `Build completed successfully (6 jobs)`
and never mention `BigCheck500`.

### Largest bounds that compiled

| bound `N` | wall clock | result |
|---|---|---|
| 100 | 18 s | exit 0, no output |
| 200 | 33 s | exit 0, no output |
| 300 | 64 s | exit 0, no output |
| 400 | 90 s | exit 0, no output |
| **500** | **139 s** | **exit 0, no output — largest verified** |

**Largest verified bound: `N = 500`** (`theorem no_solution_Q_le_500 :
noSolutionUpto 500 = true`, exit 0, no output, 139 s). Bounds above 500 were
not attempted; the cost is cubic (`~N^3/3` tuples × 4 `Nat.sqrt` calls), so
`N = 1000` would be on the order of 18 minutes.

### Non-vacuity checks (also in the default build)

These exist so the reader can see the checker is not vacuously `false`; all are
`native_decide` because of the `Nat.sqrt` issue in section 2.

```lean
example : isSq 144 = true := by native_decide
example : isSq 145 = false := by native_decide
example : isSq 0 = true := by native_decide
example : good3 52 24 28 45 7 = true := by native_decide   -- 3 of 4 conditions hold
example : good 52 24 28 45 7 = false := by native_decide   -- 4th fails: 28^2+7^2 = 833
```

The second-to-last line is the interesting one: `(Q,A,B,C,D) = (52, 24, 28, 45, 7)`
satisfies the *relaxed* problem with three conditions —
`24^2 + 45^2 = 51^2`, `28^2 + 45^2 = 53^2`, `24^2 + 7^2 = 25^2` — and is
rejected by the full checker because `28^2 + 7^2 = 833` is not a square. So the
full checker demonstrably rejects near-misses rather than rejecting everything.

---

## 7. NOT DONE — clearly marked

* **The full parity lemma (Lemma 4 of `reduction.md`).** Not proved. Only the
  requested half, **(P3)** `A` odd ⇒ `4 | C`, is proved. The matching half
  (`C` odd ⇒ `4 | A`), the statement that neither `A,C` nor `A,D` nor `B,C` nor
  `B,D` can both be odd, and the resulting dichotomy (P1)/(P2) with `4 | Q` are
  **not formalised**.
* **Theorem 6 (`12 | Q`).** **Not done.** This needs a descent / well-founded
  induction halving all four entries while all are even, on top of the complete
  Lemma 4. Not started in this work.
* **The `¬ ∃` restatement of (P1).** Not proved. Only the `Bool`-valued form
  `noSolutionUpto N = true` is machine-checked. Connecting it to
  `¬ ∃ Q ≤ N, ∃ A B C D, good Q A B C D = true` would need `List.all_eq_true`
  plus `omega` rewrites to identify `Q - A = B`; it is straightforward but was
  not needed for the headline result and was left out to keep the build clean.
* **Mathlib.** Unavailable on this machine — see `notes/lean-setup.md`. Nothing
  here uses Mathlib, `norm_num`, `ring`, `linarith`, `positivity`, `aesop`, etc.
* **`Parity.lean`, `TwelveDvd.lean`** (in `RationalDistance/`) were produced by
  a *different* agent working in parallel on the stretch goals.
  `Parity.lean` compiles (exit 0). `TwelveDvd.lean` **does not currently
  compile** (exit 1, a failed `rw` at line 79) and is in-progress work by that
  agent — it is not mine and I have deliberately not modified or deleted it. It
  is not imported by `RationalDistance.lean`, so it does not affect
  `lake build`, which was verified to succeed with it present.

---

## 8. Summary

| item | status | file | bound / signature |
|---|---|---|---|
| (P1) no solution `Q <= 100` | PROVED (`native_decide`) | `RationalDistance/Search.lean` | `noSolutionUpto 100 = true` |
| (P1) no solution `Q <= 500` | PROVED (`native_decide`), excluded from default build | `BigCheck500.lean` | `noSolutionUpto 500 = true` |
| (P2) `sq_mod8` | PROVED, kernel | `RationalDistance/ModArith.lean` | `n*n % 8 = 0 ∨ … = 1 ∨ … = 4` |
| (P2) `sq_mod3` | PROVED, kernel | `RationalDistance/ModArith.lean` | `n*n % 3 = 0 ∨ … = 1` |
| (P3) `odd_left_forces` | PROVED, kernel | `RationalDistance/ModArith.lean` | `A % 2 = 1 → C % 4 = 0` |
| (P4) `three_dvd_Q` | PROVED, kernel | `RationalDistance/ModArith.lean` | `3 ∣ Q` |
| (P5) Lemma 4 full parity lemma | **NOT DONE** | — | — |
| (P5) Theorem 6 `12 ∣ Q` | **NOT DONE** | — | — |

Build: `cd <repo>/lean && <elan>/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lake.exe build`
→ `Build completed successfully (6 jobs).` exit 0, no errors, no warnings.

---

# 附录（2026-09-15 更新）：Mathlib 可用后的新增形式化

**环境变化**：GitHub 恢复可达。`mathlib4@master` 的 `lean-toolchain` 与本机已装工具链
`leanprover/lean4:v4.34.0-rc2` **完全相同**，故 `lake update` + `lake exe cache get`
（官方预编译 olean）后 `lake build` 直接通过。上一版"Mathlib 不可用"的说明作废。

**工程结构**（全仓库每个源文件只有一份）：

```
lean/                    核心 Lean，无 Mathlib
  RationalDistance/ModArith.lean     P2/P3/P4：平方剩余、odd_left_forces、3|Q
  RationalDistance/Parity.lean       not_both_odd、four_dvd_of_odd_partner、4|Q
  RationalDistance/TwelveDvd.lean    折半下降引理 + 12|Q
  RationalDistance/Search.lean       Q ≤ 100 穷尽（native_decide）
  RationalDistance/Algorithm.lean    ★ 搜索算法正确性（本次新增）
  RationalDistance/Count.lean        ★ 与 C++ 的计数器交叉核对（本次新增）
  CheckAxioms.lean                   #print axioms 复核脚本
lean-mathlib/            Mathlib 层
  lakefile.toml                      [[lean_lib]] srcDir = "../lean" 复用上面
  RationalDistanceAlgo/Bridge.lean   ★ 几何桥 hasRatPoint_iff（本次新增）
  RationalDistanceAlgo/Midline.lean  ★ 中线归约 midline_key（本次新增）
  RationalDistanceAlgo/Main.lean     ★ 主定理拼装（本次新增）
  CheckAxioms.lean
```

## A. `RationalDistance/Algorithm.lean`（核心 Lean）

陈述（`Prop`，非计算）：

```lean
def Pyth (C A : Nat) : Prop := ∃ h : Nat, A * A + C * C = h * h
def IsSol (N A B C D Q : Nat) : Prop :=
  A + B = Q ∧ C + D = Q ∧ 0 < A ∧ 0 < B ∧ 0 < C ∧ 0 < D ∧ Q ≤ N ∧
  Pyth C A ∧ Pyth C B ∧ Pyth D A ∧ Pyth D B
def ParityOK (A B C D : Nat) : Prop :=
  (A % 2 = 1 ∧ B % 2 = 1 ∧ C % 4 = 0 ∧ D % 4 = 0) ∨
  (C % 2 = 1 ∧ D % 2 = 1 ∧ A % 4 = 0 ∧ B % 4 = 0)
def Enum (N C A B : Nat) : Prop :=
  0 < A ∧ 0 < C ∧ Pyth C A ∧ Pyth C B ∧ A < B ∧ A + B ≤ N ∧ C < A + B ∧
  Pyth (A + B - C) A ∧ Pyth (A + B - C) B
def Candidate (N C A B : Nat) : Prop := Enum N C A B ∧ ParityOK A B C (A + B - C)
```

证明（全部编译通过）：

| 定理 | 内容 |
|---|---|
| `pyth_iff_div` | `0<C`、`0<A`：`Pyth C A ↔ ∃ u v, u*v = C*C ∧ u < C ∧ u + 2*A = v`——这就是"枚举 `C²` 的除数、`v = C²/u`、`A = (v−u)/2`"。反向证明只有一行：`(u+A)*(u+A) = u*(u+2A) + A*A`。 |
| `candidate_sound` | 可靠性：`Candidate ⟹ IsSol`。 |
| `sol_swap` | `IsSol N A B C D Q ⟹ IsSol N B A C D Q`（反射 `x↦1−x`）。 |
| `enum_of_sol` / `exists_enum_of_sol` | 完备性（无过滤器）：`IsSol` 且 `A ≠ B` ⟹ 存在交换后的解满足 `Enum`。**注**：`A ≠ B` 这条假设是多余的，见下面的更正。 |
| `pyth_halve` / `sol_halve` | 全偶四元组整体折半仍是解。 |
| `parity_dichotomy` | 四条件 + 不全偶 ⟹ **恰好** `ParityOK` 的一个分支（引理 4 的精细化）。 |
| `parity_normal_form` | 过滤器的**无损性**：任一解 ⟹ 同界 `Q' ≤ Q` 的解满足 `ParityOK`（对 `Q` 的有界归纳）。 |
| `no_sol_of_no_candidate` | 主定理：`(∀ C A B, ¬ Candidate N C A B)` + `hmid` ⟹ `∀ A B C D Q, IsSol N A B C D Q → False`。 |

要点（**2026-09-15 更正**）：这里曾经写着"`A < B` 是严格的，`A = B`（即 `x = 1/2`）在反射下不变、
补偿不了，所以主定理必须把它作为显式假设
`hmid : ∀ M, M ≤ N → ∀ A C D, IsSol M A A C D (2*A) → False`，这是上一版没有指出的**真实覆盖缺口**"。
**这句话是错的**：`A = B` 由问题的**另一条**对称性覆盖——对角线反射 `(A,B,C,D) ↔ (C,D,A,B)`
（即 `(x,y) ↔ (y,x)`），它把解重排成"引擎框架里数对为 `(C,D)`"的形态，而 `C ≠ D`（`A = B ∧ C = D`
会推出 `A = C` 与 `2A²` 是平方，与 `√2` 无理矛盾）。`notes/reduction.md` §6 从一开始就是这么写的。
所以：**两个定理都为真，只是假设 `A ≠ B` / `hmid` 比需要的强**；拿掉它们只差一个算术引理
（"`2A²` 不是正平方"）加上把这条交换补进完备性证明。`hmid` 恰好是中线程序实测验证的命题，
因此主定理的两条假设都由实际计算满足，计算结果不受影响。

`#print axioms`：这些定理只用 `[propext, Classical.choice, Quot.sound]`（`pyth_iff_div` 用到
`Classical.choice`，其余只用 `propext`/`Quot.sound`），无 `sorryAx`、无额外公理。

## B. `RationalDistance/Count.lean`（核心 Lean）

用**完全不同的算法**（对每个 `A ≤ N` 直接 `Nat.sqrt` 判平方，而非用 `C²` 的除数）实现同一套计数器，
`native_decide` 机器核对与 C++ 打印逐位相同：

```lean
example : stats 1000 = (2068,  3295,  774,   0) := by native_decide
example : stats 2000 = (4642,  9293,  2111,  0) := by native_decide
example : stats 3000 = (7388,  16868, 3774,  0) := by native_decide
```

对照 `fast_search3.cpp` 的输出：`N=1000 partners=2068 candidates=3295 tested=774 solutions=0` 等 ✓。
注意 `C` 必须从 1 开始（C++ 是 `for Ci = 1; Ci <= N`）；写成从 0 开始会让 `partners` 恰好多 `N`——
这条也被这次核对暴露并修正了。

## C. `RationalDistanceAlgo/Bridge.lean`（Mathlib）

```lean
def RatDist (x y : ℚ) : Prop := IsSquare (x^2+y^2) ∧ IsSquare ((1-x)^2+y^2) ∧
                                IsSquare (x^2+(1-y)^2) ∧ IsSquare ((1-x)^2+(1-y)^2)
def HasRatPoint (N : ℕ) : Prop :=
  ∃ Q A C, 0 < Q ∧ Q ≤ N ∧ 0 < A ∧ A < Q ∧ 0 < C ∧ C < Q ∧ RatDist (A/Q) (C/Q)
theorem hasRatPoint_iff (N : ℕ) : HasRatPoint N ↔ ∃ A B C D Q, IsSol N A B C D Q
```

关键辅助引理 `nat_isSquare_of_rat_isSquare {n : ℕ} {q : ℚ} (h : q*q = n) : ∃ k : ℕ, k*k = n`：
写 `q = q.num/q.den`，平方去分母 ⇒ `q.num² = n·q.den²` ⇒ `q.den ∣ q.num²`；由 `Rat.reduced`
（`q.den` 与 `q.num.natAbs` 互素）得 `q.den = 1`。

## D. `RationalDistanceAlgo/Midline.lean`（Mathlib）

```lean
theorem midline_key {A C D Q h1 h2 : ℤ} (hA2 : A + A = Q) (hCD : C + D = Q)
    (e1 : A*A + C*C = h1*h1) (e2 : A*A + D*D = h2*h2) :
    (C - D)^4 + 4 * Q^4 = 16 * h1^2 * h2^2      -- 证明：代入 Q=2A、C=2A−D 后 ring

theorem two_mul_sq_not_sq : ∀ A : ℕ, 0 < A → ∀ h : ℕ, h*h ≠ 2*(A*A)   -- 经典下降
theorem midline_C_ne_D : ... ⟹ C ≠ D

def FermatRightTriangle : Prop :=
  ∀ x y z : ℤ, x ≠ 0 → y ≠ 0 → x^4 + 4*y^4 ≠ z^2      -- 经典 Fermat 直角三角形定理

theorem no_midline_of_fermat (hF : FermatRightTriangle) :
    ∀ N A C D : ℕ, IsSol N A A C D (2*A) → False
```

即：中线解会给出**非零**整数 `(C−D, Q, 4h1h2)` 满足 `x⁴ + 4y⁴ = z²`。Mathlib 有 `FLT(4)` 的
对应形式 `not_fermat_42 : a⁴+b⁴ ≠ c²`，但**没有** `x⁴+4y⁴ = z²` 形式；从前者推出后者需要与
`FLT(4)` 证明中同样的无穷下降，**本次未完成**。所以这一步目前是"给定 Fermat 定理"的条件定理，
中线结论的独立支撑来自 `src/midline_search.cpp` 的穷尽计算（第二轮已推进到 `Q ≤ 2×10¹⁰`，0 个解；
该程序按上面的更正属于**冗余的独立验证**，不是补缺口所必需）。

## E. 复现

```bash
TC=<elan>/toolchains/leanprover--lean4---v4.34.0-rc2/bin
cd <repo>/lean        && "$TC/lake.exe" build                      # 6 jobs
cd <repo>/lean-mathlib && "$TC/lake.exe" build RationalDistanceAlgo.Main   # 8928 jobs
```
输出存档：`results/lean_verification.txt`。
