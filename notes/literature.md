# Rational distance problem for the unit square — literature reconnaissance

Prepared 2026-09-14. Every claim below carries the URL that was actually fetched in this session.
**Every search, fetch, reading and judgement below was carried out independently by the AI
research agent `DeepSeek v4.1 flash`** (no human co-author; see `REPORT.md` §11).
Claim-level provenance tags:

- **[F]** = I fetched the page/text myself and read the stated content.
- **[FW]** = fetched via a search engine's indexing of the page (the page itself was NOT retrievable
  from this environment — DNS/proxy blocked or JS bot-check); treat as second-hand.
- **[MV]** = verified by me numerically with Python in this session (exact rational arithmetic).
- **[unverified]** = could not confirm; do not rely on it.

---

## 0. Headline answers (short version)

1. **Name / statement.** Standard names: *"the rational distance problem"*, *"the four-distance problem"*,
   and historically **Dodge's "square problem"** (posed 1976). It appears as **Problem D19** in
   R. K. Guy, *Unsolved Problems in Number Theory*. Critically, the standard statement is about a point
   **in the plane** — not restricted to the interior of the square.
2. **Rational coordinates.** Yes, this is stated explicitly and repeatedly in the literature. Your
   derivation is correct and is essentially equation (2) of Bremner–Ulas.
3. **Largest search bound.** The only bound I could **verify by fetching the artifact itself** is a
   self-published 2026 archive: **no solution with common denominator q ≤ 100 000 (exhaustive)** and a
   leg-based exhaustive search to 5 000 000. The largest *claimed* bound is a forum post by
   **Tim Roberts: no solution with the point inside a square of side < 6 000 000** (and none with sides
   *and* coordinates all < 2 000 000, interior or exterior) — I could **not** fetch that page.
4. **Proven partial results.** Boundary points (Barbara 2011); diagonals / midlines / edges plus a
   side-length condition (Yang Ji 2021); a 3-adic valuation obstruction ruling out 1/4 of bounded-height
   candidates (McCloskey 2019). Robertson 1986 special case (equal side-distances) with no published proof.
5. **Claimed full proofs.** Only one found: **Song Li, viXra:2605.0013** — unrefereed, on viXra, and
   carrying a viXra admin note that it looks AI-written. **Not credible.** No arXiv claimed proof exists.
6. **Exterior solutions for the unit square: none are known.** The premise that exterior parametric
   families exist for the *square* is **false**; exterior parametric families do exist for *rectangles*
   (Bremner–Ulas) and I verified two of them numerically. Details in §7.

---

## 1. Standard name(s) and exact statement

### 1.1 MathWorld — "Rational Distance Problem" **[F]**
URL: <https://mathworld.wolfram.com/RationalDistanceProblem.html>

> "It is not known if there exists a point in a unit square all of whose distances from the corners are
> rational."

Rational distances are equivalent to integer distances after clearing denominators. MathWorld credits
**J. H. Conway and M. Guy** with infinitely many solutions in which *three* of the distances are integers,
and references **Guy, R. K., §D19 in *Unsolved Problems in Number Theory*, 2nd ed., Springer, 1994,
pp. 181–185**. MathWorld gives no computational search bounds.

### 1.2 Bremner–Ulas (arXiv:1502.07312) — the "plane", not the interior **[F]**
URL: <https://arxiv.org/abs/1502.07312> ; full text read via <https://ar5iv.labs.arxiv.org/html/1502.07312>

> "However, it is a notorious and unsolved problem to determine whether there exists a rational point **in
> the plane** at rational distance from the four corners of the unit square (see Problem D19 in Guy's book
> [5])."

They also note (quoting Guy D19, p. 284) that the analogous **rectangle** problem is treated there.
This is the single most important statement for your project: **the open problem is over the whole plane,
so any exterior solution would also solve it.**

### 1.3 Yang Ji (arXiv:2105.05250) — history of the statement **[F]**
URL: <https://arxiv.org/abs/2105.05250> ; full text via <https://ar5iv.labs.arxiv.org/html/2105.05250>

From the paper body (verbatim, lightly de-formatted):

> "45 years ago, C.W. Dodge asked 'a square problem' in the Mathematical Magazine [Dodge 1976]: is there a
> point in a unit square which has all rational distances to the four vertices? He had no answer. 10 years
> later, in the same journal a comment [MathMag 1986] said that **John P. Robertson proved a special case:
> there is no such a square if two of the distances from the point to the sides are equal.** However, no
> details of the proof was given. A book published in 2005, *Research Problems in Discrete Geometry*
> [Brass–Moser–Pach], still regarded the square problem as unproved."

So: **Dodge, Problem 966, *Mathematics Magazine* 49 (1976)**, with a 1986 comment in vol. 59, p. 52.
(The search index additionally reports the citation as "C. W. Dodge, Problem 966, *Mathematics Magazine*,
49 (1976), p. 43" and a partial solution by G. Shute and K. L. Yocom in *Mathematics Magazine* 50 (1977),
pp. 166–67 — **[FW]**, not directly fetched.)

### 1.4 Roy Barbara (Math. Gazette 2011) — statement is "in the plane" **[F]**
URL (question + quoted answer): <https://math.stackexchange.com/questions/1379191/simplified-rational-distance-problem>
(fetched via the Stack Exchange API, `api.stackexchange.com/2.3/questions/1379191/answers`).
The accepted-style answer quotes Barbara verbatim:

> "It is not known whether there is a point **in the plane** of a unit square, that is at a rational distance
> from each of the four corners. See [1, 2, 3]. Here, we give a **negative answer for boundary points**,
> using the non-existence of particular Pythagorean triangles."

Full citation: **Roy Barbara, "95.01 The rational distance problem", *The Mathematical Gazette* 95 (532),
March 2011, pp. 59–61.** (JSTOR 23248619 cited in the search index **[FW]**.)

### 1.5 Love (arXiv:2310.02534) — formal name "Square four-distance" **[F]**
URL: <https://arxiv.org/abs/2310.02534> ; full text via <https://ar5iv.labs.arxiv.org/html/2310.02534>

> "*'Square four-distance:'* Find a point (x, y) ∈ ℝ² such that the distance to each of (0,0), (1,0),
> (0,1), and (1,1) is rational."

and

> "The perfect cuboid problem and square four-distance problem are classic unsolved problems (see Section 2);
> this paper does not present a solution to either of them."

### 1.6 Lean/formal status — officially "open" **[F]**
URL: <https://raw.githubusercontent.com/google-deepmind/formal-conjectures/main/FormalConjectures/Wikipedia/RationalDistanceProblem.lean>

```lean
def UnitSquareCorners : Fin 4 → ℝ² := ![!₂[0, 0], !₂[1, 0], !₂[1, 1], !₂[0, 1]]

/-- Does there exist a point in the plane at rational distance from all four vertices of the unit square? -/
@[category research open, AMS 11 51]
theorem rational_distance_problem :
    answer(sorry) ↔ ∃ P : ℝ² , ∀ i, ¬ Irrational (dist P (UnitSquareCorners i)) := by sorry
```

Note again **`∃ P : ℝ²`** — the whole plane. References listed: Wikipedia, mathoverflow/418260,
and Guy's D19.

### 1.7 Open Problem Garden / MathPages — **not found**
- **Open Problem Garden**: I could not retrieve an entry for the unit-square four-distance problem.
  The Garden's nearby entry is "Dense rational distance sets in the plane" (Erdős–Ulam) **[FW]**.
  The URL <https://www.openproblemgarden.org/op/rational_distance_problem> returns **HTTP 404 [F]**.
- **MathPages (K. S. Brown)**: **no article found.** A site-restricted search (`site:mathpages.com` with
  "rational", "rational distance", "four corners", "kmath") returned **no** rational-distance article **[FW]**,
  and direct fetches of `mathpages.com/home/contents.htm` were refused with **HTTP 406 [F]**.
  → **Your recollection of a MathPages article on this appears to be mistaken (or I could not locate it).**

---

## 2. Must a solution point have rational coordinates? — YES, stated in the literature

This is **not** your original observation; it is standard and appears explicitly in several places.

### 2.1 McCloskey, arXiv:1904.12097 (2019) **[F]**
URL: <https://arxiv.org/abs/1904.12097> ; full text via <https://ar5iv.labs.arxiv.org/html/1904.12097>

Abstract (verbatim):

> "Place the vertices of a rectangle at {(0, ±1/2), (a, ±1/2)}, where a is rational. **Any point (x, y) that
> is rational distance from all four vertices of the rectangle must have rational coordinates.** We prove
> that if v₃(a) = 0, then either v₃(x) < 0 or v₃(y) < 0, where v₃(·) is the 3-adic valuation. … For the
> four-distance problem, our result rules out one-fourth of all potential solutions with bounded height."

And in the body, parenthetically: "**(Any solution to the four-distance problem must have rational
coordinates.)**"

### 2.2 Bremner–Ulas, arXiv:1502.07312, equation (2) **[F]** — *this is your formula*
From the proof of Theorem 2.1, for the rectangle with vertices (0,0), (0,1), (a,0), (a,1) and distances
P, Q, R, S to those four points respectively:

$$x=\frac{1}{2a}\left(a^{2}+P^{2}-R^{2}\right),\qquad y=\frac{1}{2}\left(P^{2}-Q^{2}+1\right)$$

For the **unit square** (a = 1) this gives exactly

$$x=\tfrac{1}{2}\bigl(1+P^{2}-R^{2}\bigr),\qquad y=\tfrac{1}{2}\bigl(1+P^{2}-Q^{2}\bigr),$$

i.e. your $x=(a^2-b^2+1)/2$ with $a$ = distance to (0,0) and $b$ = distance to (1,0) (and similarly for y
with the distance to (0,1)). Since P, Q, R are rational, **x and y are rational**. In fact plain subtraction
of two squared-distance equations gives this, so it is folklore.

### 2.3 Love, arXiv:2310.02534, §2.2 **[F]** — states it for the *three*-distance problem
> "The coordinates x, y are not a priori assumed to be rational, but since x² + y², x² + (1−y)², and
> (1−x)² + (1−y)² must all be rational, the differences 2y − 1 and 2x − 1 must also be rational, so in fact
> **P ∈ ℚ²**."

### 2.4 Yang Ji, arXiv:2105.05250 **[F]**
> "Clearly, the coordinates of the point P must be rational."

### 2.5 Who stated it *first*? — **[unverified]**
I could not establish a first attribution. It is treated as elementary/folklore in all sources I fetched.
A search index mentions a CalState Channel Islands M.A. thesis (V. M. Moreno Martinez, 2009,
<https://scholarworks.calstate.edu/concern/theses/np193b05b>) whose "Lemma 3.2.6" is said to prove exactly
this — **the repository returns HTTP 403 [F], so this is [unverified]**.

---

## 3. Computational searches — bounds and formulations

Different sources bound **different quantities** (side length, coordinate numerator/denominator, common
denominator, Pythagorean leg). I keep them separate; do not compare them as if they were the same bound.

| Source | Formulation of the bound | Reported result | Fetched? |
|---|---|---|---|
| **Zenodo/GitHub archive "Rational-Distance Points in the Unit Square"** (Yuan Si, Apr 2026) | Coordinates x = p/q, y = r/q with **common denominator q ≤ 100 000**, exhaustive | **no solution** | **[F]** |
| same archive, run 3 (`search_5M.py`) | "Pythagorean legs ≤ 5 000 000" — leg-based, *not* a denominator bound (the archive's own v1.1 changelog says "Corrected search coverage claims (leg-based, not denominator-based for Runs 2–3)") | **no solution**; script prints "denominators up to ~2·LEG_MAX" ≈ 10 000 000 | **[F]** |
| **Tim Roberts** (unsolvedproblems.org / groups.io, c. 2013) | (1) square **side < 6 000 000**, point inside; (2) side **and** point coordinates all **< 2 000 000**, point inside *or* outside | **no solution** in either case; author explicitly does not guarantee his programs | **[FW]** |
| **MSE 1379191** (Yimin Rong, 2015-07-30) | search over the *reduced* condition: Pythagorean triples (L,a,p) and (L,b,q) with **a + b = L**, for **L < 2³¹** | no exact solution; closest hits are a + b = L ± 1 (L = 1344, 1600, 1508, 29040, 142912, …, 513405900) | **[F]** (via Stack Exchange API) |
| **This session, my own check** | common denominator **q ≤ 2000**, x numerator in [−2q, 3q], y arbitrary with denominator dividing q | 0 solutions (boundary cases excluded) | **[MV]** |

### 3.1 The bound I could actually verify by fetching the artifact **[F]**
GitHub repo: <https://github.com/SamSi0322/rational-distance-unit-square> (fetched via GitHub API and raw
file), DOI 10.5281/zenodo.19613346 / 10.5281/zenodo.19613981, README v1.2 dated 2026-04-17.
README verbatim rows:

> | No solution with denominator q <= 100,000 | Exact, exhaustive | Report 2, Run 1 |
> | No solution with Pythagorean legs <= 5,000,000 | Exact, exhaustive | Report 2, Run 3 |

The pre-registered search model, taken from `scripts/search/direct_search.py` (downloaded and read) **[F]**:

```
Search model: x = p/q, y = r/q with 0 < r < p < q, gcd(p,r,q)=1.
Test: are p^2+r^2, (q-p)^2+r^2, p^2+(q-r)^2, (q-p)^2+(q-r)^2 all perfect squares?
```

**Caveat / credibility:** this is **unrefereed, self-published, single-author** work posted 2026 on Zenodo
and GitHub. It explicitly says "**No complete solution is claimed; the problem remains open**", and it lists
its own unverified gaps ("Stage-2 to Q_{−1} bridge — Not verified"). Treat the *search* as a claim, not a
refereed result. It is nonetheless the only place where I could read the actual search code and its
precise formulation.

### 3.2 The largest *claimed* bound (interior case) **[FW]**
Forum post, quoted identically by the search index across several independent queries:

> "(1) there are NO solutions to the problem that lie inside of a square with sides less than 6 million."
> "(2) there are NO solutions to the problem where the point lies inside or outside of a square and the
> sides of the square and the coordinates of the point are all less than 2 million."

URL: <https://groups.io/g/UnsolvedProblems/topic/67887461> — author **Tim S Roberts**
(also the maintainer of <http://unsolvedproblems.org>, whose "Rational Distance" page I *did* fetch **[F]**;
that page cites Guy D19 and Barbara 2011 but contains **no** numerical bounds). The search index also quotes
Roberts elsewhere: "I got up to values of L, x, and y of 2,000,000, I think."
**I could not fetch the groups.io thread itself** — it sits behind a JavaScript bot-check
(Monocle/spur.us) and returns an empty body to both the fetch tool and `curl` **[F]**.
Roberts himself is quoted as not guaranteeing correctness because of possible program bugs **[FW]**.

**Answer to "largest verified published search bound":**
- **Verified by me, precise formulation:** *no solution of the interior four-distance problem with the
  point's coordinates having common denominator q ≤ 100 000* — from the 2026 Zenodo/GitHub archive
  (unrefereed). [Also: the archive's leg-based run to 5 000 000 legs, which is **not** a denominator bound.]
- **Largest claimed, interior, precise formulation:** *no solution with the point inside a square of side
  less than 6 000 000* (Tim Roberts, forum post c. 2013) — **[FW] / unrefereed**.
- **Largest reduced-problem bound I verified:** L < 2³¹ for the two-Pythagorean-triples condition, MSE 2015.

### 3.3 My own independent check **[MV]**
Script: `explore/extsearch3.py`. Method: enumerate all w > 0 with n⁴ + w² a perfect square
via the divisor factorisation (z−w)(z+w) = n⁴, hence for each side L and each x-numerator p, the candidate
y-numerators are exactly `partners(p²) ∩ partners((L−p)²)`, and one needs r and L−r both in that set.
This is complete in y for the given L and p.

Result: **0 non-boundary solutions for every common denominator L ≤ 2000** with the x-numerator ranging
over [−2L, 3L] (i.e. x ∈ [−2, 3], which covers the interior plus a band of exterior). Consistent with the
literature: no solution found at all, interior or exterior.

---

## 4. Proven partial results

### 4.1 Boundary points: impossible
- **Barbara 2011** (Math. Gazette 95, 59–61): "we give a negative answer for **boundary points**, using the
  non-existence of particular Pythagorean triangles" **[F]**, quoted at
  <https://math.stackexchange.com/questions/1379191/simplified-rational-distance-problem>.
- **Yang Ji 2021**, Theorem 1 covers the edges and is explicitly stated to be *not new* (it duplicates
  Barbara) **[FW]**.

### 4.2 Diagonals, midlines, edges: impossible (Yang Ji 2021) **[F]**
<https://ar5iv.labs.arxiv.org/html/2105.05250> — the paper proves, by Fermat's method of infinite descent:

> "if the point sits on the diagonals, the midlines or the edges of the square, or the side-length of the
> square is n times the distance from the point to one side (both n and (n²+4) are prime numbers), the
> distances from this point to the four vertices can not be all rational."

and crucially:

> "**The proof here can be extended to the whole plane**, instead of being limited to the interior of the
> square."

So the diagonal/midline exclusions apply to **exterior** points on those lines as well. This already rules
out the natural construction of an exterior example on a centre line.

### 4.3 Robertson's special case (equal distances to two sides) — *proof never published* **[F]**
Reported by Yang Ji (see §1.3), sourced to a *Mathematics Magazine* 59 (1986), p. 52 comment: no such square
exists if two of the distances from the point to the sides are equal; "no details of the proof was given".

### 4.4 McCloskey's 3-adic obstruction (arXiv:1904.12097, 2019) **[F]**
Theorem: for the rectangle with a = 1 (unit square) and v₃(a) = 0, any rational-distance point (x, y) must
satisfy **v₃(x) < 0 or v₃(y) < 0**. Equivalently it **rules out one-quarter of all candidates of bounded
height** in a computer search. This is a genuine, refereed-looking conditional sieve (arXiv preprint;
I did not verify journal status).

### 4.5 Three-distance problem: abundantly solvable (contrast case)
- Bremner–Ulas, §1 **[F]**: "Berry [1] showed that the set of rational points in the plane with rational
  distances to **three** given vertices of the unit square is infinite", via infinitely many parametric
  solutions, generalising earlier work of **Leech**.
- Love, arXiv:2310.02534 §2.2 **[F]**: "The first one-parameter family of nontrivial solutions was found in
  **1967 by J.H. Hunter**, and then many more infinite families were found in rapid succession; a historical
  overview is given by Berry, who also presents an 'extraordinary abundance' of solutions lying in infinitely
  many one-parameter families."
- MathWorld **[F]**: Conway and Guy found infinitely many solutions with three integer corner-distances.

### 4.6 Rectangle four-distance problem: solvable for a dense set of aspect ratios
See §7 — Bremner–Ulas Theorem 2.1 (density) and Bremner–Elkies (per Elkies' MathOverflow answer **[F]**).

### 4.7 3-dimensional relaxation: trivially solvable
Bremner–Ulas, §1 **[F]**: "(½, ½, ¼) lies at rational distance to the four vertices (0,0,0), (0,1,0),
(1,0,0), (1,1,0) of the square." Further (§4, Theorem 4.1) they show the relevant variety in ℚ³ is
**unirational**, giving a parametric family; and (§3) such points are dense on the lines x = ½, y = ½ and on
the plane x = ½. **This 3D family is likely what you were thinking of as "outside" families — but it is
3D, not planar.**

---

## 5. Related problems

### 5.1 Perfect cuboid / Euler brick (open)
- Definition confirmed **[F]** at <https://www.unsolvedproblems.org/index_files/PerfectCuboid.htm>: a perfect
  cuboid is an Euler brick whose space diagonal is also an integer; problem open. **That page gives no
  numerical search bounds.**
- Search-index claims (**[FW] / [unverified]**, Wikipedia unreachable from this environment): smallest edge
  > 10¹⁰ (Rathbun); odd edge > 3×10¹² (Butler); later no odd edge < 2.5×10¹³ and no side < 5×10¹¹ (Rob Matson).
  **I could not fetch a primary source for these numbers — do not cite them without re-checking.**
- Love's paper **[F]** gives the cleanest modern framing: the "body cuboid" case reduces to rational points
  on E : y² = x³ + (a²+b²)x² + a²b²x, with **Halbeisen–Hungerbühler** [10] and a survey by **van Luijk** [13];
  nondegenerate solutions exist iff E(ℚ) has positive rank ("double-pythapotent pair").
- **Relation to our problem** **[F]**: Love's Table 1 places "Perfect cuboid", "Body cuboid", "Square
  four-distance", "Square three-distance", "Rectangle four-distance" etc. in one family of rational
  configuration problems, with the key remark:

  > "for every problem in Table 1 besides the perfect cuboid problem and the square four-distance problem,
  > rational configurations correspond to solutions … to a single polynomial in multiple variables that is
  > **linear in each variable**."

  i.e. the square four-distance problem and the perfect cuboid are exactly the two "hard" members — there is
  **no** proven implication between them in this source. A forum post claims the parallels (four squares in
  each case) — **[FW]**, <https://groups.io/g/UnsolvedProblems/topic/67890973>.

### 5.2 Rational distance sets / Erdős–Ulam problem (open)
- Ascher–Braune–Turchet, arXiv:1901.02616 **[F]** (<https://arxiv.org/abs/1901.02616>): "Assuming Lang's
  Conjecture, we prove that cardinalities of rational distance sets in general position are uniformly bounded,
  extending results of **Solymosi–de Zeeuw, Makhul–Shaffaf, Shaffaf, and Tao**." Also a criterion for
  varieties with non-canonical singularities to be of general type.
- **Solymosi–de Zeeuw** (unconditional, via Faltings): a rational distance set contained in a real algebraic
  curve is finite unless the curve has a line or circle component. **Tao 2014** and **Shaffaf 2018**
  independently: Bombieri–Lang ⇒ no dense rational distance set. **Pasten**: abc ⇒ same. All **[FW]**
  (from the Erdős–Ulam search summary; Wikipedia not fetchable here).
- **Noam Elkies' MathOverflow answer** **[F]**
  (<https://mathoverflow.net/questions/460755/a-rational-distance-problem-with-possibly-multiple-solutions>,
  fetched via SE API) gives a concrete infinite configuration class:

  > "let S = { z² : z ∈ ℚ(i), z·z̄ = 1 }, which is infinite because there are infinitely many primitive
  > Pythagorean triples (a,b,c) and each yields z = (a+bi)/c with z·z̄ = 1" — and any two points of S are at
  > rational distance. "starting from the 3,4,5 triangle and scaling by 25 we find that the rectangle with
  > vertices (±7, ±24) has all sides and both diagonals rational, and there are infinitely many points on its
  > circumcircle x² + y² = 25² at rational distances from all four vertices, starting with (x, y) = (±25, 0)."

  Another answer on the same page **[F]**: "The rectangle with vertices (±60, ±15) has rational distances
  from the corners to both (±52, 0), because both (15,8,17) and (15,112,113) are Pythagorean triples."
  These are **rectangle/quadrilateral** examples, **not** unit-square examples.

### 5.3 Congruent numbers (adjacent, not equivalent)
- Love arXiv:2310.02534 §2.3 **[F]** defines congruent numbers and explicitly compares *methods* with the
  rational-configuration problems, calling it "not a rational configuration problem".
- MacLeod, "Rational distance sets on xy = 1", *J. Integer Seq.* 15 (2012), Art. 12.2.5: "The search for such
  points has links to both congruent and concordant numbers" — **[FW]** (PDF at the EMIS mirror returned 404;
  abstract confirmed via zbMATH/Semantic Scholar search entries).
- **No source I fetched proves any implication "unit-square solution ⇒ congruent-number condition".**
  Treat any such claim as **[unverified]**.

### 5.4 3D Euler brick / cube: open
Bremner–Ulas §6 **[F]**: "Whether there exist points in ℚ³ at rational distance from the eight vertices of
the unit cube is another seemingly intractable problem which we leave as open". They show the variety for
six of the eight distances has infinitely many rational curves on the plane x = ½ (Theorem 6.1), and "we
found just one point with five of the distances rational" without symmetry.

---

## 6. Claimed proofs / solutions — credibility

### 6.1 Song Li, "A Complete Proof of the Rational Distance Problem for the Unit Square" — **NOT credible** **[F]**
URL: <https://vixra.org/abs/2605.0013>
Fetched facts: author **Song Li**; viXra:2605.0013; 10 pages; submission history "[v1] 2026-05-05 00:16:52";
abstract claims the point must have rational coordinates, reduces to an integer Diophantine problem, splits
into three parity cases and derives contradictions, concluding **no interior point exists**.

**Red flag, verbatim from the page's Comments field:**

> "Note by viXra Admin: Please submit article written with AI assistance to ai.viXra.org"

Assessment: **crankery / not credible.** It is on viXra (a repository that itself states submissions "may
not yet have been verified by peer-review"), it is not on arXiv, it is not refereed, it carries an
AI-assistance warning from the site's own admin, and the problem is independently listed as **open** in the
2025 Google DeepMind `formal-conjectures` repository (§1.6) and in every fetched source. The search index
additionally reports an earlier version **viXra:2503.0070 (2025-03-11)** **[FW]**.

### 6.2 MathOverflow 418260 "4-distance problem and elliptic curves" **[F]**
URL: <https://mathoverflow.net/questions/418260/4-distance-problem-and-elliptic-curves>
(asked by Yuan Yang; fetched via SE API; **no answers posted**). The question itself contains a
self-correction:

> "One can easily prove that as long as for any r, if one of the curves E_r and E_{1−r} has rank 0, then the
> 4-distance problem has a negative answer … **(however this is not true according to Joachim's comment.)**"

Relevant content: the family E_r : y² = x³ + (1/r² − 1)x² − (2/r²)x + 1/r², where E_r encodes points P = (x,y)
with x = r and PA, PB rational. Reported (unverified by me) that for r = 0, 1/2, 1/3, 1/4, 1/5, 2/5 at least
one of E_r, E_{1−r} has rank 0. **No proof claim; correctly framed as open.**

### 6.3 Other items
- No arXiv paper claiming a resolution was found.
- A family of 2026 dated "Zenodo research archive" items plus an "Elliptic decomposition of the Pell-chord
  genus-five obstruction" paper exists **[FW]**; these are self-published and are flagged by their own author
  as incomplete. Not credibility-worthy as proofs.
- A search index result mentioning a "DIC method / Decomposition-Intersection-Control" manuscript and an
  "audit-style" Zenodo monograph **[FW]** — speculative, no proof claim verified.

---

## 7. Exterior solutions — the premise needs correcting

### 7.1 For the **unit square in the plane**: NO exterior solution is known **[F]**
Because the standard problem is stated over the whole plane (§1.2, §1.4, §1.6), an exterior solution for
the unit square *is* a solution of the open problem. Hence **no parametric family of exterior solutions for
the unit square exists in the literature** — you cannot have one without solving the problem. Additionally
Yang Ji's diagonal/midline/edge exclusions extend to the whole plane (§4.2), killing the obvious exterior
constructions. **Treat "known exterior parametric families for the square" as a false premise.**

### 7.2 What *does* exist: exterior families for **rectangles** (Bremner–Ulas) **[F] [MV]**
arXiv:1502.07312, Theorem 2.1 + its proof. For the rectangle with vertices (0,0), (0,1), (a,0), (a,1) and

$$a=\frac{1-t^{2}}{2t},$$

the point

$$x=\frac{4tu\,(v^{2}-u^{2})\bigl((t^{2}-1)u-(t^{2}+1)v\bigr)}{D^{2}},\qquad
y=\frac{2u\bigl((t-1)u-(t+1)v\bigr)\bigl((t+1)u-(t-1)v\bigr)\bigl((t^{2}-1)u-(t^{2}+1)v\bigr)}{D^{2}},$$

$$D=(t^{2}+1)u^{2}-2(t^{2}-1)uv+(1+t^{2})v^{2}$$

is at rational distance from all four corners, for all rational t, u, v (generic). The paper proves these
points are **never inside** the rectangle:

> "x (a−x) y (1−y) = −4u²(u²−v²)²( … )² … **which is evidently negative. Thus the point (x, y) can never lie
> within the rectangle R.**"

Note $a = (1-t^2)/(2t)$ is rational for rational $t$, but $a = 1$ (the **square**) forces $t = -1 \pm \sqrt{2}$,
**irrational** — so this family degenerates to no rational square solution, exactly as expected.

**Concrete examples — I computed these from the formulas and verified every distance exactly [MV]**
(one-off Python script using exact rational arithmetic — `abs(d)^2 == d` checked as a perfect rational
square — not retained in the repository):

| t | u | v | rectangle width a (height 1) | P = (x, y) | dist to (0,0) | dist to (0,1) | dist to (a,0) | dist to (a,1) |
|---|---|---|---|---|---|---|---|---|
| 1/3 | 1 | −5 | **a = 4/3** | (28/75, −7/25) | 7/15 | 4/3 | 1 | 8/5 |
| 1/4 | 1 | −5 | **a = 15/8** | (1680/5329, −1925/5329) | 35/73 | 102/73 | 935/584 | 1209/584 |
| 1/2 | 1 | −5 | a = 3/4 | (264/625, −77/625) | 11/25 | 6/5 | 7/20 | 117/100 |
| 5 | 1 | 2 | a = −12/5 | (−420/289, −224/289) | 28/17 | 39/17 | 104/85 | 171/85 |

For the first row I re-checked by hand as well: P = (28/75, −7/25) with a = 4/3 gives
√((28/75)² + (7/25)²) = √(1225/5625) = 7/15, √((28/75)² + (32/25)²) = √(10000/5625) = 4/3,
√((24/25)² + (7/25)²) = 25/25 = 1, √((24/25)² + (32/25)²) = 40/25 = 8/5. The verification script printed
`ALLSQ=True` for both the a = 4/3 and a = 15/8 cases, and `x(a−x)y(1−y) < 0` in both.

### 7.3 Bremner–Ulas Theorem 2.3 — infinitely many points over ℚ(√2) for the **unit square** **[F]**
For K a number field with √2 ∈ K, the set of K-rational points at K-rational distance from the four vertices
of the **unit square** is **infinite**; explicit parametrisation given with t = 1+√2 (so a = 1) and
v = 1, u ∈ K. Caveat: the distances live in K = ℚ(√2), **not** in ℚ, so this does **not** give a rational
solution of the open problem.

### 7.4 Rectangles/quadrilaterals with rational distance sets (Elkies) **[F]**
See §5.2: rectangle with vertices (±7, ±24) (from the 3-4-5 triple scaled by 25) and the rectangle
(±60, ±15) with points (±52, 0). These are neighbours of the problem, not unit-square solutions.

---

## 8. Uncertainties / things I could not verify

1. **Tim Roberts' search bounds (6 000 000 / 2 000 000)** — quoted identically by the search index in several
   independent queries, but the groups.io thread (<https://groups.io/g/UnsolvedProblems/topic/67887461>) and
   every `groups.io/g/UnsolvedProblems/message/...` URL returned an **empty body** to WebFetch and to `curl`
   because of a JavaScript bot-check. **Not directly verified.** Also unrefereed and explicitly not
   guaranteed by the author.
2. **Perfect-cuboid search bounds** (10¹⁰, 3×10¹², 2.5×10¹³, 5×10¹¹) — **not found in any source I could
   fetch.** The one page I did fetch (<https://www.unsolvedproblems.org/index_files/PerfectCuboid.htm>)
   has no bounds. Do not cite these without re-checking.
3. **First attribution of the "rational coordinates" lemma** — **not found.** All fetched sources treat it
   as folklore. The CalState thesis that apparently contains a Lemma 3.2.6 proof returns HTTP 403.
4. **Wikipedia's "Périat" claim** — the live article was unreachable from this environment. Archived copies
   (via search index) carry the sentence "according to Périat, the only points included in the square of
   rational distances of the four vertices are necessarily on the sides", followed by a derivation that
   appears to *assume* what it sets out to prove (it sets x² + (1−y)² = (A/B − 1)² for distances that are not
   forced to differ by 1). **Unsourced and almost certainly garbled/incorrect as it stands on the page —
   do not cite it.** (Search-index copies are at
   `web.archive.org/web/20200614232220/https://en.wikipedia.org/wiki/Unit_square` and
   `thefreedictionary.com` mirrors **[FW]**.)
5. **MathPages** — could not fetch `mathpages.com` (HTTP 406 on the contents page) and site-restricted
   searches found no rational-distance article. **Not found**, possibly because it does not exist.
6. **Open Problem Garden** — the natural URL 404s; I could not confirm any entry exists for the unit-square
   four-distance problem (as opposed to the Erdős–Ulam / dense-rational-distance-sets entry).
7. **Yang Ji's papers' journal status / whether Theorem 1's priority note is accurate** — I read only the
   arXiv/ar5iv text; the claim that Theorem 1 duplicates Barbara 2011 appeared in a search-index summary
   **[FW]**, and the paper's abstract I fetched does not itself say so.
8. **McCloskey arXiv:1904.12097 publication venue** — read as an arXiv preprint; I did not confirm
   peer-review status.
9. **The 2026 Zenodo/GitHub archive's searches** — I read the README and the search scripts, but I did not
   re-run them, and their completeness claims (especially that run 3 at 5 000 000 legs is exhaustive for the
   *interior* problem) rest on the author's own reasoning, which their own changelog partly retracts. Its
   geometric/algebraic claims (genus-3 curve, F₄ degree-16 surface in ℙ⁶, 46 nodes, arithmetic genus 7) are
   **not independently verified** by me.
10. **MSE 1379191's reduction** — the OP states the problem "can be expressed more simply as: are there
    Pythagorean triples (L,a,p) and (L,b,q) such that a + b = L?" I report the search (L < 2³¹) as the OP
    framed it, but I could **not** determine from the page exactly which sub-case of the four-distance problem
    that reduction captures, so do not present it as a bound on the full interior problem.
11. **"Square concurrence / rational orthodiagonal quadrilateral"** framing (search index attributes it to a
    groups.io thread) — **[FW]**, not fetched, not verified.
12. **Erdős–Ulam secondary claims** (Solymosi–de Zeeuw 2010; Tao 2014 blog post; Shaffaf 2018; Pasten 2017;
    Kreisel–Kurz 2008 seven-point set) — all **[FW]** from search summaries; I only fetched the
    Ascher–Braune–Turchet arXiv abstract directly.

---

## 9. Files produced / reproducible artifacts in this session

- `explore/extsearch3.py` — exhaustive (in y) search for four-distance points,
  common denominator ≤ 2000, x-numerator ∈ [−2L, 3L]; reported **0 solutions**
  (log kept as `explore/extsearch3_run.log`).
- `_third_party/downloads/` holds the downloaded primary texts used above
  (`bu.txt` = Bremner–Ulas, `ji.txt` = Yang Ji, `mc.txt` = McCloskey, `ar_2310.02534.txt` = Love,
  and the Stack Exchange API JSON dumps `mse1379191.json`, `mse1379191a.json`, `mo418260.json`,
  `mo460755.json`, `mo460755a.json`); `_third_party/prior_art/` holds the Zenodo/GitHub archive
  (`rdREADME.md` + `rd_*.py`) and the Lean statement (`rdp.lean`). That directory is third-party
  material, `.gitignore`d and **not** redistributed with this repository — see
  `_third_party/README.md`.
