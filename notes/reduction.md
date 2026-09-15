# The rational-distance problem for the unit square: reductions and local structure

All statements here are elementary and completely proved below.  Everything
labelled **Proof** is a full proof, not a sketch; the numerical claims marked
*computed* are reproduced by the programs in `src/` (see the report for exact
commands and outputs).

*Written independently by the AI research agent `DeepSeek v4.1 flash` — every proof,
computation and sentence in this file, with no human co-author (see `REPORT.md` §11).*

**Attribution note (verified against the literature, see `notes/literature.md`).**
Theorem 1 (a solution's coordinates must be rational) is *not new*: it is stated
e.g. in Bremner–Ulas arXiv:1502.07312 (their equation (2) is the displayed
formula for a rectangle, and gives this for `a = 1`), in McCloskey
arXiv:1904.12097 ("Any point (x,y) that is rational distance from all four
vertices of the rectangle must have rational coordinates"), in Love
arXiv:2310.02534 §2.2 and in Yang Ji arXiv:2105.05250.  Lemma 5 (`3 | Q`) is
equivalent to McCloskey's theorem `v_3(x) < 0 or v_3(y) < 0` for the unit square,
so it too is known; we only give a shorter proof.  The centre-line case of §5 is
*proved impossible* in the literature (Yang Ji, arXiv:2105.05250, by infinite
descent, and the proof is stated to extend to the whole plane); §5 below is an
independent equivalent reformulation, not a new result.  The 2-adic half of
Theorem 6 (`4 | Q`, Lemma 4, and the primitive parity patterns) was **not found**
in the literature searched; whether it is new is not something we can assert.


Throughout, the unit square is `[0,1]^2` with vertices
`V00 = (0,0)`, `V10 = (1,0)`, `V01 = (0,1)`, `V11 = (1,1)`.

The question (the *interior rational distance problem*):

> **(Q)** Is there a point `P = (x,y)` with `0 < x < 1`, `0 < y < 1` whose four
> distances to the vertices are all rational?

---

## 1. The coordinates of a solution are rational

**Theorem 1.** *Let `P = (x,y)` be any point of the plane (interior or not) at
rational distance from `V00`, `V10`, `V01`.  Then `x, y ∈ Q`.  Explicitly, if
`a = |P V00|`, `b = |P V10|`, `c = |P V01|` then*

```
x = (a^2 - b^2 + 1)/2 ,      y = (a^2 - c^2 + 1)/2 .
```

*Proof.* `a^2 = x^2 + y^2` and `b^2 = (1-x)^2 + y^2`, so
`a^2 - b^2 = x^2 - (1-x)^2 = 2x - 1`, whence `x = (a^2-b^2+1)/2`.  The
computation for `y` is identical using `c^2 = x^2 + (1-y)^2`.  Since
`a,b,c ∈ Q` the displayed expressions are rational.  ∎

Consequently the search space is *countable and explicit*: **a solution, if it
exists, has rational coordinates.**  (This is presumably folklore; the residue
of the problem is purely arithmetic.)

## 2. Integer form, and what an exhaustive search over `Q <= N` really covers

Write `x = A/Q`, `y = C/Q` with `Q ∈ Z_{>0}` a common denominator and
`A = Qx`, `C = Qy`; put `B = Q - A`, `D = Q - C`.

**Theorem 2.** *For integers `Q > 0` and `0 < A,B,C,D < Q` with `A+B = Q` and
`C+D = Q`, the following are equivalent:*

1. *the point `P = (A/Q, C/Q)` is at rational distance from all four vertices;*
2. *the four integers `A^2+C^2`, `B^2+C^2`, `A^2+D^2`, `B^2+D^2` are all perfect
   squares of integers.*

*Proof.* The squared distances from `P` to `V00, V10, V01, V11` are
`(A^2+C^2)/Q^2`, `(B^2+C^2)/Q^2`, `(A^2+D^2)/Q^2`, `(B^2+D^2)/Q^2`.  A rational
number whose square is an integer is an integer: if `(p/q)^2 = n` with
`gcd(p,q)=1` then `q^2 | p^2`, so `q = 1`.  Hence the four distances are
rational iff the four numerators are perfect squares.  The converse is
immediate.  ∎

**Theorem 3 (coverage of a search).** *Let `N >= 1`.  There is a point `P` as in
(Q) with `lcm(den x, den y) <= N` if and only if there are integers
`Q <= N` and `0 < A,B,C,D < Q` with `A+B = C+D = Q` satisfying the four-square
condition of Theorem 2(2).*

*Proof.* (⇒) Put `Q = lcm(den x, den y) <= N`; then `A = Qx` and `C = Qy` are
integers with `0 < A,C < Q`, `B = Q-A`, `D = Q-C`, and Theorem 2 gives the four
squares.  (⇐) Given such integers, `P = (A/Q, C/Q)` lies strictly inside the
square and Theorem 2 gives rational distances; and `lcm(den x, den y) <= Q <= N`.
∎

Thus the programs in `src/` — which enumerate *every* quadruple
`(Q,A,B,C,D)` with `Q <= N` meeting the conditions of Theorem 2 — decide
exactly: *"is there a solution whose coordinates can be written over a common
denominator at most `N`?"*

## 3. Local structure: the 2-adic and 3-adic shape of a solution

**Lemma 4 (mod 8 / parity).** *Let `A+B = C+D = Q` and suppose the four numbers
of Theorem 2(2) are perfect squares.  If `A,B,C,D` are not all even, then
either*

* **(P1)** `A`, `B` are odd and `4 | C`, `4 | D`,  or
* **(P2)** `C`, `D` are odd and `4 | A`, `4 | B`.

*In both cases `4 | Q`.*

*Proof.* Squares are `0, 1, 4 (mod 8)`; an odd square is `1 (mod 8)`, and the
square of an even number is `0` or `4 (mod 8)`.

*Neither `A` and `C`, nor `A` and `D`, nor `B` and `C`, nor `B` and `D` can both
be odd*, because then their squares would sum to `1 + 1 = 2 (mod 4)`, which is
not a square mod 4 (squares mod 4 are 0, 1).

Suppose some element is odd.

* If `A` is odd: `C` and `D` are even.  From `A^2 + C^2 ≡ 1 + C^2 (mod 8)` being
  a square mod 8 we get `1 + C^2 ∈ {0,1,4} (mod 8)`; with `C` even,
  `C^2 ∈ {0,4} (mod 8)`, so `1+C^2 ∈ {1,5}`, leaving `C^2 ≡ 0 (mod 8)`, i.e.
  `4 | C`.  The same argument with `D` gives `4 | D`.  Hence
  `Q = C + D ≡ 0 (mod 4)`.  Finally `B = Q - A` with `Q ≡ 0 (mod 4)` and `A`
  odd gives `B` odd.
* If `C` is odd (and `A` is even by the previous bullet): symmetrically
  `4 | A` and `4 | B`, so `Q = A + B ≡ 0 (mod 4)` and `D` is odd.

If no element is odd, all are even, contrary to hypothesis.  ∎

**Lemma 5 (mod 3).** *With `A+B = C+D = Q` and the four squares, `3 | Q`.*

*Proof.* Squares mod 3 are `0,1`.  If `3 ∤ A` then `A^2 ≡ 1 (mod 3)`, and
`A^2 + C^2` must be a square mod 3, so `1 + C^2 ∈ {0,1} (mod 3)`, which forces
`C^2 ≡ 0`, i.e. `3 | C`.  Likewise `3 | D`.  Then `Q = C + D ≡ 0 (mod 3)`.

If `3 | A` and `3 ∤ B`, the same argument with `B` in place of `A` gives `3 | C`
and `3 | D`, hence `Q = C + D ≡ 0`, but also `Q = A + B ≡ B ≢ 0 (mod 3)` — a
contradiction.  So `3 | A` forces `3 | B`, and then `Q = A + B ≡ 0 (mod 3)`.
Every case gives `3 | Q`.  ∎

**Theorem 6.** *Every solution `(Q,A,B,C,D)` of the conditions of Theorem 2
satisfies `12 | Q`.*

*Proof.* `3 | Q` is Lemma 5.  For `4 | Q`: if `A,B,C,D` are not all even, use
Lemma 4.  If they are all even, then `(Q/2, A/2, B/2, C/2, D/2)` again satisfies
the conditions (`A+B = C+D` and the four squares all scale by `4`), and the
values stay positive integers; iterating this halving terminates in a tuple that
is not all even, whose `Q' = Q/2^k` satisfies `4 | Q'` by Lemma 4, whence
`4 | Q`.  ∎

**Corollary 7.** *For any solution, `12 | lcm(den x, den y)`.*

*Proof.* Apply Theorem 6 to `Q = lcm(den x, den y)`.  ∎

**Remark (this is optimal locally).**  `src/residue_structure.py` enumerates, for
each modulus `m`, all residue quadruples satisfying `A+B ≡ C+D` and the four
"squares mod m" conditions (a finite exact computation).  Results:

| m | possible `Q mod m` | forced divisibility of `Q` |
|---|---|---|
| 4 | 0, 2 | 2 only (local analysis is weaker than Theorem 6) |
| 8 | 0, 2, 4, 6 | 2 |
| 16 | 0, 4, 8, 12 | 4 |
| 32 | 0, 4, 8, 12, 16, 20, 24, 28 | 4 |
| 3 | 0 | 3 |
| 9 | 0, 3, 6 | 3 |
| 27 | multiples of 3 | 3 |
| 12 | 0, 6 | 6 |
| 24 | 0, 6, 12, 18 | 6 |
| 144 | multiples of 12 | 12 |
| 5, 7, 11, 13, 25, 49 | everything | none |
| 60, 120, 168, 210 | — | 6, 6, 6, 3 resp. |

So the modulus-by-modulus analysis never forces more than `12 | Q`, and it never
forces `p | A,B,C,D` for any prime `p` (there are valid residue patterns with
`p ∤ gcd(A,B,C,D)`, e.g. `(A,B,C,D) ≡ (0,0,1,-1) (mod p)` for the `3`-pattern).
In particular no *local* descent beyond `12 | Q` is available; Theorem 6 is the
sharp statement of this kind, and it needs the *global* halving argument (not
just a residue computation) to upgrade the `mod 4` pattern to `4 | Q`.

A cleaner way to see the sharpness, and a second (purely finite) proof of the
primitive case of Theorem 6: restricting the enumeration to residue patterns
that are *not all even* (which every primitive tuple satisfies) gives

| m | patterns | possible `Q mod m` | forces `12 | Q` ? |
|---|---|---|---|
| 16 | 256 | 0, 4, 8, 12 | no |
| 24 | 160 | 0, 12 | **yes** |
| 48 | 1280 | 0, 12, 24, 36 | yes |
| 96 | 10240 | multiples of 12 | yes |
| 144 | 34560 | multiples of 12 | yes |
| 288 | 276480 | multiples of 12 | yes |

So for a primitive tuple the divisibility `12 | Q` is already a *local* fact at
the modulus 24 (a finite check over `24^3` triples `(A,B,C)` with `D ≡ Q-C`),
and the halving descent of Theorem 6 then removes the primitivity hypothesis.
This finite check is what the Lean formalisation in `lean/` performs.

Note for reading the table: mod-4 allows `Q ≡ 2`, but every such residue
quadruple fails mod 8 (e.g. `A,C` odd is impossible mod 4; `A ≡ 2, C` odd gives
`A^2+C^2 ≡ 5 (mod 8)`), which is why Lemma 4 is stated mod 8.  Likewise mod-12
allows `Q ≡ 6`, which has `Q ≡ 2 (mod 4)` and is killed by the halving argument.

## 4. Immediate special cases

**Diagonals.**  If `x = y` then the distance to `V00` is `x√2`, rational only if
`x = 0`; if `x + y = 1` then the distance to `V01` is `x√2`.  So no solution has
`P` on either diagonal (in particular not at the centre `(1/2,1/2)`).

**Symmetry.**  The conditions of Theorem 2 are invariant under `A ↔ B`,
`C ↔ D` and under the swap `(A,B) ↔ (C,D)` (the latter is `(x,y) ↔ (y,x)`), so
one may search up to these symmetries.

## 5. The centre line `x = 1/2`: reduction to a genus-1 curve

For `x = 1/2` we have `A = B = Q/2` and the four distances collapse to two:
`A^2 + C^2` and `A^2 + D^2` must be squares, with `C + D = 2A`.

**Proposition 8.** *Put `u = C/A ∈ Q ∩ (0,2)` (so `D = A(2-u)`).  Then a
solution with `x = 1/2` exists iff there is a rational `u`, `0 < u < 2`, such
that both `1 + u^2` and `1 + (2-u)^2` are squares of rationals.*

*Proof.* `A^2 + C^2 = A^2(1+u^2)` is a square iff `1+u^2` is (both are squares of
rationals / integers, and `A^2` is a square), and similarly for `D`.  ∎

**Proposition 9 (parametrisation).** *`1 + u^2 = w^2` with `u,w ∈ Q` iff
`u = (1/λ - λ)/2` for some `λ ∈ Q \ {0}` (namely `λ = w - u`).  Consequently the
centre-line solutions correspond to rational points `(λ, ν)` of the quartic*

```
ν^2 = λ^4 + 8λ^3 + 18λ^2 - 8λ + 1 ,        λ ∈ Q \ {0} ,
```

*subject to the range conditions `0 < u < 2` and `0 < 2-u < 2`, where
`u = (1/λ - λ)/2` and `2 - u = (1/μ - μ)/2` with
`μ = (-(λ^2+4λ-1) ± ν)/(2λ)`.*

*Proof.* `1 + u^2 = w^2 ⟺ (w-u)(w+u) = 1`; putting `λ = w-u` gives
`w+u = 1/λ`, hence `u = (1/λ-λ)/2`, and `λ ≠ 0` because `w + u > 0`.  Similarly
`2 - u = (1/μ-μ)/2`.  Adding the two parametrised equations,
`(1/λ-λ) + (1/μ-μ) = 4`, i.e. after multiplying by `λμ`,
`λμ^2 + (λ^2+4λ-1)μ - λ = 0`, a quadratic in `μ` whose discriminant is
`(λ^2+4λ-1)^2 + 4λ^2 = λ^4+8λ^3+18λ^2-8λ+1`; a rational `μ` exists iff this
discriminant is a rational square `ν^2`.  ∎

**Structural remark.**  Writing `Δ(λ) = λ^4+8λ^3+18λ^2-8λ+1` one checks the
identity `Δ(λ) = λ^4 Δ(-1/λ)` and, with `v = λ - 1/λ`,

```
Δ(λ) = λ^2 (v^2 + 8v + 20).
```

Hence the quartic condition is *equivalent* to: `v^2 + 8v + 20` is a square and
`v = λ - 1/λ` is a difference `λ - 1/λ` for a rational `λ`, i.e. `v^2 + 4` is a
square.  Both conditions are conics, so the centre line is governed by the genus
one curve obtained by intersecting them — as expected, the parametrisation above
makes the quartic a *conic* only over `Q(λ)`, not over `Q`.

**Computational status.**  The main search (Theorem 3) with `N >= 10^8` covers
every centre-line candidate whose common denominator is at most `N`, i.e. every
`u` whose numerator and denominator are bounded by `~10^8`: no such candidate
exists.  Emptiness of the whole centre line is *not* proved here (it would
require determining the Mordell–Weil group of the quartic's Jacobian).

## 6. Why the search of `src/fast_search*.cpp` is complete

The engine fixes the index `C` and runs over pairs `A < B` taken from
`T(C) = {A : A^2+C^2 = square}`; it that way *enumerates pairs from a sorted
list*, so the pair always satisfies `A < B`.  Two symmetries make this lossless.

1. **Reflection `x -> 1-x`.**  Replacing `(A,B)` by `(B,A)` (and keeping `C,D`)
   permutes the four conditions among themselves, so a solution with `A > B`
   has a reflected solution with `A < B` and the same `Q,C,D`.  Hence "`A < B`"
   costs nothing for the *full* four-condition problem.
2. **Swap `(x,y) -> (y,x)`.**  Replacing `(A,B,C,D)` by `(C,D,A,B)` also
   permutes the four conditions, so a solution may be presented in either
   orientation.

These two reductions are what handle the potentially degenerate cases:

* `y = 1/2` (`C = D`): in the engine's own frame the pair is `(A,B)` with
  `A ≠ B`, and the last two checks `A^2+D^2`, `B^2+D^2` collapse to
  `A^2+C^2`, `B^2+C^2`, which hold by construction; such a point is found.
* `x = 1/2` (`A = B`): degenerate in the frame where `C` is the y-numerator, but
  the swapped presentation has engine-frame `x` equal to the original `y ≠ 1/2`,
  so the engine-frame pair is non-degenerate and the point is found.
  (Both coordinates cannot be `1/2`: the centre point has distance `1/√2`.)

Consequently the engine decides exactly the statement of Theorem 3, for every
`N` it is run with.  This was checked empirically as well: for the *relaxed*
problem (skip only the `B^2+D^2` check) the engine's solution set for `N = 300`
is identical, tuple by tuple, to a direct `O(N^3)` enumeration in Python
(6 solutions, both ways, no extra and no missing); and for the full problem both
find none.

The parity filter of Lemma 4 is also lossless for the search: given any solution
tuple, repeatedly halving while all four entries are even leaves a tuple that is
not all even (values stay `>= 1`), which by Lemma 4 satisfies (P1) or (P2), and
the halved tuple is again a solution, at a smaller `Q` that is still `<= N`.  So
excluding parity patterns other than (P1), (P2) cannot lose a solution.

## 7. Files

| file | content |
|---|---|
| `src/fast_search.cpp` | search v1, holds the full partner table in memory |
| `src/fast_search2.cpp` | search v2, two-pass memory-optimised table |
| `src/fast_search3.cpp` | search v3, **no** global table: partner lists from divisors of `C^2` |
| `src/residue_structure.py` | the mod-`m` computations of the Remark above |
| `results/` | raw outputs of the runs |
| `lean/` | machine-checked versions of the finite parts (see report) |

v1, v2 and v3 agree exactly (same `candidates`, same `survivors`, same
`solutions`) on every `N` tested, and the independent brute force
`src/brute.cpp` agrees on small `N`; see the report for the raw numbers.
