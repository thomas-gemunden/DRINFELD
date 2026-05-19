# Trajectory C: parallel-workstream design

This document specifies the implementation of Trajectory C as a graph
of independent workstreams, each composed of bite-sized issues that
agentic researchers and developers can pick up and complete in
isolation. Each leaf issue is a single deliverable; each workstream
has an "epic" meta-issue tracking aggregate progress.

The trajectory itself, including motivation and decision-theoretic
role of each tier, is recorded in `writeup.md` §§5–8 and the
companion `transgression_improvements_design.md`.

## 1. Orientation

Goal: settle Keller's conjecture (`writeup.md` §1) for $E_+(m)$ at
$m \in \{2, 3, 5, 7\}$ in turn, with two preplanned decision points
that branch on observed kernel-of-transgression outcomes. The
trajectory uses all four tiers of discriminator (Tier-1 closed-form
entries; Tier-3 $\mathrm{Aut}(N, T)$; Tier-4 transgression kernel;
Tier-5 Frobenius–Schur indicators) and is structured so that no
single agent has the full pipeline in scope at once.

## 2. Workstream graph

```
                  +-------------------+
                  | Q: Quillen H^3    | math-heavy, no upstream deps
                  +---------+---------+
                            |
          +----------+      v       +-------------+
          | T: Trans-+----> A: Per-m+----> W: Paper|
          |  gression|     | apps   |    | writeup |
          +----+-----+     +---+----+    +---------+
               |               |               ^
               |               v               |
          +----+----+     +----+----+         |
          | V: Vali-+---->| X: Cross+---------+
          |  dators |     |  checks |
          +---------+     +---------+
               ^
               |
          +----+----+
          | K: KRR  | optional, parallel
          | adapter |
          +---------+
```

Q (Quillen analytical $H^3$), T (Transgression core) and V (Validators)
are the foundational streams whose outputs feed A (Application). K
(KRR pipeline adapter) is optional in Trajectory C — the trajectory
compares against abstract $\omega$, not against KRR's pipeline output —
but adds cross-validation and is run in parallel. X (Cross-checks)
tests every other stream's outputs against $D_8$, $Q_8$, $E_+(2)$
ground truth. W (Writeup) is the synthesis stream.

## 3. Label conventions

Every issue carries one *status* label and zero or more *attribute*
labels. Status labels are exclusive — exactly one per issue at any
time. Attribute labels are independent.

**Status labels** (mutually exclusive):
- `ready` — all dependencies satisfied; an agent can start now.
- `in progress` — currently claimed; the assignee is the owner.
- `blocked` — at least one upstream dependency is incomplete.
- `requires user input` — the issue cannot proceed without a
  human-supplied decision (e.g. choice between math routes,
  acceptance of a result that depends on convention).

**Attribute labels** (independent, multi-assignable):
- `epic` — workstream meta-issue.
- `math` — primary work is mathematical (proof, derivation,
  reference-tracking).
- `code` — primary work is implementation in GAP/Python.
- `doc` — primary work is documentation/writeup.
- `regression` — issue is a test or validation against ground truth.
- `decision-point` — issue triggers a branch in the trajectory.

Status flow:
```
[blocked] -> (deps resolve) -> [ready] -> (claimed) -> [in progress] -> (closed)
                                  |
                                  +-> [requires user input] -> (user response) -> [ready]
```

## 4. Issue template

Every leaf issue follows this template. The fields are GitHub-issue-ready:
title goes in the issue title field, the rest goes in the body.

```
**Title.** [<workstream>-<id>] <imperative verb> <object>

**Workstream.** <workstream letter and name>

**Background.**
<2–4 paragraphs: where the work lives in the trajectory, what
problem it solves, and what existing code/docs it builds on. Cite
specific file paths and line numbers where applicable.>

**Goal.**
<single-sentence statement of what the issue delivers.>

**Acceptance criteria.**
- <bullet list of testable conditions; ideally each maps to a
  regression test or measurable wall-clock target.>

**Dependencies.**
- <list of upstream issue IDs that must close before this one starts>

**Estimated effort.**
<small numeric range in days, including review.>

**Files likely affected.**
- <file paths or new file names>

**Out of scope.**
- <explicit non-goals to prevent scope creep>
```

## 5. Workstream Q — Quillen analytical $H^3$ pipeline

**Status:** active, math-heavy. Long-pole for $E_+(7)$.

**Aim.** Replace HAP's `ResolutionFiniteGroup(E_+(m), 4)` and
`UniversalCoefficientsTheorem(K, 3)` with an analytical pipeline that
extracts the torsion of $H^3(E_+(m); U(1))$ and explicit cocycle
representatives directly from Quillen's polynomial-times-exterior
presentation of $H^*(E_+(m); \mathbb F_2)$. The pipeline is required
at $m = 7$, where HAP fails at the resolution step, and is also a
correctness cross-check at $m \le 3$.

**Math entry points.** Quillen [Qui71]; Adem–Milgram
[AM04, §IV.4-§IV.5 (Thm 4.3, Thm 5.6)]; Bockstein operations in
[AM04, III.3]; universal-coefficient sequence relating $\mathbb F_2$
and $\mathbb Z$ coefficients [Br82, Ch. II]. The citation chain in
detail: Adem--Milgram framework (§IV.4--§IV.5) $\to$ Quillen 1971 Thm
5.10 (explicit $H^*(E_+(m); \mathbb F_2)$) $\to$ Harada--Kono 1987
Thm 1.1 (integer $A(k)$ summand) $\to$ UCT for $U(1)$ coefficients.
See R-1 (`docs/superpowers/research/2026-05-17-detecting-family-literature.md`)
for the full synthesis.

### Q-EPIC

**Title.** `[Q-EPIC] Quillen analytical H^3 pipeline`

**Body.**
Tracks workstream Q. Closes when Q-1 through Q-8 close; Q-9 is an
independent verification path that may close before or after the
main pipeline.

**Status:** `in progress` (this design doc).
**Attribute labels:** `epic`, `math`, `code`.

### Q-1

**Title.** `[Q-1] Polynomial-times-exterior algebra data structure (F_2 coefficients)`

**Workstream.** Q.

**Background.**
The mod-2 cohomology of an extraspecial 2-group has the form
$\mathbb F_2[c, x_1, \ldots, x_{2m}] \otimes \Lambda(y_1, \ldots, y_{2m})$
modulo Quillen relations [Qui71, Thm 5.4]. Implementing this as a
GAP module requires a graded-algebra data structure supporting
polynomial multiplication, exterior multiplication with sign, and
quotient by a finitely-generated ideal.

**Goal.** A GAP module `quillen_algebra.g` exposing a
`PolynomialTimesExterior(symPolys, extPolys, relations)` constructor
returning a graded-algebra object with multiplication and quotient
operations.

**Acceptance criteria.**
- Constructor accepts symbolic generator names with degrees and a
  list of relations as homogeneous polynomials.
- `Multiply(a, b)` returns the product reduced modulo the ideal.
- `BasisInDegree(d)` returns a $\mathbb F_2$-basis of the
  degree-$d$ component.
- Smoke test: $\Lambda(y) \otimes \mathbb F_2[x]$ ($m=0$ case)
  returns the expected dimensions $(1, 2, 2, 2, \ldots)$ in degrees
  $(0, 1, 2, 3, \ldots)$.
- Smoke test: $\Lambda(y_1, y_2) \otimes \mathbb F_2[c]$ with one
  relation returns a known sequence of dimensions.

**Dependencies.** None.

**Estimated effort.** 3–5 days.

**Files likely affected.**
- New `scripts/quillen_algebra.g`.
- New `scripts/test_quillen_algebra.g` regression suite.

**Out of scope.**
- Quillen relations specific to $E_+(m)$ (Q-2).
- Bockstein operations (Q-4).

**Status:** `ready`. **Labels:** `code`, `math`.

### Q-2

**Title.** `[Q-2] Quillen presentation specialised to E_+(m), degrees ≤ 4`

**Workstream.** Q.

**Background.**
Quillen [Qui71, Thm 5.4] gives the explicit relations on the
generators $c, x_i, y_j$ for $H^*(E_+(m); \mathbb F_2)$. For our
purposes only the degrees up to 4 matter (since
$H^3(G; U(1)) \cong H^4(G; \mathbb Z)$ for finite $G$). Encode the
generators with their degrees and the relations Quillen proves.

**Goal.** A function `QuillenPresentation(m)` returning a
`quillen_algebra` object instantiated with the correct generators
and relations for $E_+(m)$.

**Acceptance criteria.**
- Output dimensions in degrees $\le 4$ match Quillen's published
  values for $m = 1, 2, 3$.
- For $m = 3$, the function must agree with HAP's
  `Cohomology(R, n; mod 2)` outputs in degrees $1, 2, 3, 4$.
- Documented mapping from generators ($c, x_i, y_j$) to subgroup-
  cohomology classes (so cocycle realisation in Q-3, Q-4 is
  unambiguous).

**Dependencies.** Q-1.

**Estimated effort.** 3–5 days.

**Files likely affected.**
- `scripts/quillen_algebra.g` extension.
- New `scripts/quillen_presentation_em.g`.

**Out of scope.**
- Bar-resolution cup product (Q-3).
- Bockstein (Q-4).

**Status:** `blocked` on Q-1. **Labels:** `math`, `code`.

### Q-3

**Title.** `[Q-3] Bar-resolution cup product on E_+(m) via Frattini abelianisation`

**Workstream.** Q.

**Background.**
Quillen's generators $x_i, y_j$ in degree 1 represent the projection
$E_+(m) \twoheadrightarrow E_+(m)/[E_+(m), E_+(m)] \cong (\mathbb F_2)^{2m}$
followed by an explicit character. Cohomology classes built from these
in higher degrees are cup products at the cochain level; for
representative cocycles on $E_+(m)$, the cup product must be evaluated
on group triples via the bar-resolution composition, restricted
through the abelianisation map.

**Goal.** An evaluator
`CupProductBarResolution(class_a, class_b)(g_1, g_2, ..., g_{n})` that
returns the value of $a \cup b$ on a tuple of $n = \deg a + \deg b$
group elements, where $a, b$ are classes in `quillen_algebra` form.

**Acceptance criteria.**
- For two degree-1 classes (linear characters $\chi_1, \chi_2$),
  $(\chi_1 \cup \chi_2)(g, h) = \chi_1(g) \chi_2(h)$ matches the
  product evaluation.
- Associativity: $(a \cup b) \cup c = a \cup (b \cup c)$ on a sample
  of degree-1 + 1 + 1 cup products.
- HAP cross-check: at $m = 2, 3$, the cup product evaluator must
  reproduce HAP's `CupProduct` outputs on a sample of class pairs.

**Dependencies.** Q-1.

**Estimated effort.** 1 week.

**Files likely affected.**
- New `scripts/quillen_cup_product.g`.

**Out of scope.**
- Steenrod operations / Bockstein (Q-4).

**Status:** `blocked` on Q-1. **Labels:** `math`, `code`.

### Q-4

**Title.** `[Q-4] Integral Bockstein at the cochain level`

**Workstream.** Q.

**Background.**
The integral Bockstein $\beta \colon H^n(G; \mathbb F_2) \to H^{n+1}(G; \mathbb Z)$
is the connecting map of the short exact sequence
$0 \to \mathbb Z \to \mathbb Z \to \mathbb F_2 \to 0$. At the cochain
level it lifts an $\mathbb F_2$-cocycle to a $\mathbb Z$-cochain and
returns its $\mathbb Z$-coboundary divided by 2. Implementation needs
care: the lifted cochain is non-canonical, but the coboundary modulo
2 is well-defined as a $\mathbb Z$-cocycle.

**Goal.** An operation `Bockstein(class)` taking a cohomology class
in degree $n$ in `quillen_algebra` form and returning a class in
degree $n+1$ over $\mathbb Z$ (encoded via the
universal-coefficient sequence to be implemented in Q-5).

**Acceptance criteria.**
- Bockstein squared is zero on every test class.
- $\beta(y_i) = $ a class corresponding to the universal-coefficient
  output for the corresponding linear character with $\mathbb Z$-lift.
- HAP cross-check: at $m = 2, 3$, $\beta$ on each generator agrees
  with HAP's `IntegralRingGenerators` followed by reduction.

**Dependencies.** Q-1.

**Estimated effort.** 4 days.

**Files likely affected.**
- `scripts/quillen_algebra.g` extension.

**Out of scope.**
- The universal-coefficient sequence wrapper (Q-5).

**Status:** `blocked` on Q-1. **Labels:** `math`, `code`.

### Q-5

**Title.** `[Q-5] Universal-coefficient sequence: extract H^*(G; Z) from H^*(G; F_2) and Bockstein`

**Workstream.** Q.

**Background.**
For a finite group $G$, $H^n(G; \mathbb Z)$ is a finite abelian
group computable from $H^*(G; \mathbb F_2)$ together with the
Bockstein, via the short exact sequence
$0 \to H^n(G; \mathbb Z) \otimes \mathbb F_2 \to H^n(G; \mathbb F_2) \to \mathrm{Tor}(H^{n+1}(G; \mathbb Z), \mathbb F_2) \to 0$.
At each $n$ this gives the 2-primary part of $H^n(G; \mathbb Z)$;
since $E_+(m)$ is a 2-group, the full integral cohomology equals
its 2-primary part.

**Goal.** A function `IntegralCohomology(class_F2_alg, n)` returning
the torsion vector of $H^n(G; \mathbb Z)$ together with a basis of
generators expressed in terms of $\mathbb F_2$-classes plus
Bocksteins.

**Acceptance criteria.**
- For $E_+(2)$: torsion vector matches $[2^9, 8]$ (HAP output).
- For $E_+(3)$: torsion vector matches $[2^{34}, 4]$.
- For $D_8$: torsion vector at $n = 4$ matches $[8]$ (so $H^3(D_8; U(1)) = \mathbb Z/8$).

**Dependencies.** Q-2, Q-4.

**Estimated effort.** 4 days.

**Files likely affected.**
- `scripts/quillen_algebra.g` extension.

**Out of scope.**
- $U(1)$ coefficient bridge (Q-6).

**Status:** `blocked` on Q-2, Q-4. **Labels:** `math`, `code`.

### Q-6

**Title.** `[Q-6] H^n(G; U(1)) as H^{n+1}(G; Z) at n = 3`

**Workstream.** Q.

**Background.**
For finite $G$, $H^n(G; \mathbb R) = 0$ for $n \ge 1$, so the short
exact sequence $0 \to \mathbb Z \to \mathbb R \to U(1) \to 0$ gives
$H^n(G; U(1)) \cong H^{n+1}(G; \mathbb Z)$. At $n = 3$ this is
$H^3(G; U(1)) \cong H^4(G; \mathbb Z)$.

**Goal.** A wrapper `UnitCircleCohomology(G, n)` invoking Q-5 at
$n + 1$ and returning the result as $H^n(G; U(1))$ data: torsion
vector plus a basis-realising lift to standard cocycles.

**Acceptance criteria.**
- For $E_+(2)$: returns torsion $[2^9, 8]$ at $n = 3$ — same as HAP's
  `UCT.torsion`.
- API matches the existing `setup.UCT.lift` and `setup.torsion`
  shape, so `transgression_kernel.g` can use it as a drop-in.
- HAP cross-check: every generator's standard-cocycle realisation
  matches HAP's at $m = 2, 3$ on a fixed evaluation tuple.

**Dependencies.** Q-5.

**Estimated effort.** 3 days.

**Files likely affected.**
- New `scripts/quillen_h3_u1.g`.

**Out of scope.**
- The lift to a callable $G^3 \to \mathbb Z/m$ (Q-7).

**Status:** `blocked` on Q-5. **Labels:** `math`, `code`.

### Q-7

**Title.** `[Q-7] Cocycle representatives: H^3 generators as callables G^3 -> Z/m`

**Workstream.** Q.

**Background.**
Tier-4 evaluation requires each $H^3$ generator $e_i$ to be realised
as a function $G^3 \to \mathbb Z/m$. HAP's `StandardCocycle` does
this via the bar resolution; the Quillen pipeline must produce a
direct callable from the polynomial-times-exterior expression of
$e_i$ via Q-3 (cup product) and Q-4 (Bockstein).

**Goal.** A function `StandardCocycleQuillen(class_alg)` returning a
3-argument function `G x G x G -> Z/m` evaluating the cocycle.

**Acceptance criteria.**
- Cocycle condition: for every generator class, $\delta f = 0$
  identically on a sample of $G^4$ tuples.
- Cross-check at $m = 2$: each generator's evaluation table on a
  sampled subset of $G^3$ agrees with HAP's `StandardCocycle` output.
- Performance: 1000 random evaluations per second per generator at
  $m = 7$.

**Dependencies.** Q-3, Q-6.

**Estimated effort.** 3 days.

**Files likely affected.**
- `scripts/quillen_h3_u1.g` extension.

**Out of scope.**
- Cross-check against HAP at $m = 2, 3$ (Q-8).

**Status:** `blocked` on Q-3, Q-6. **Labels:** `math`, `code`.

### Q-8

**Title.** `[Q-8] Quillen pipeline cross-check against HAP at m = 2, 3`

**Workstream.** Q.

**Background.**
HAP works comfortably at $m \le 3$, providing ground truth for the
Quillen pipeline. End-to-end cross-check: torsion vectors must agree;
standard-cocycle evaluations on each generator must agree on a
representative tuple sample.

**Goal.** A regression script that runs the Quillen pipeline on
$E_+(2)$ and $E_+(3)$ and asserts byte-for-byte agreement with HAP
outputs.

**Acceptance criteria.**
- Torsion vector at $m = 2$ matches $[2^9, 8]$ from HAP.
- Torsion vector at $m = 3$ matches $[2^{34}, 4]$ from HAP.
- For each Quillen generator, $\ge 95\%$ of 100 random
  $G^3$-evaluations agree with the HAP-side standard cocycle (with
  the same generator chosen).
- Documented record of any sign/section convention differences.

**Dependencies.** Q-7.

**Estimated effort.** 3 days.

**Files likely affected.**
- New `scripts/test_quillen_vs_hap.g`.

**Out of scope.**
- $m \ge 4$ runs.

**Status:** `blocked` on Q-7. **Labels:** `regression`, `math`, `code`.

### Q-9

**Title.** `[Q-9] Detecting-subgroup variant for H^3(E_+(m); U(1))`

**Workstream.** Q.

**Background.**
An independent path to $H^3(E_+(m); U(1))$ uses a *detecting subgroup*
$H \le E_+(m)$ for which $\mathrm{res}^G_H \colon H^3(G; U(1)) \to H^3(H; U(1))$
is injective ([AM04, V.6]). For an extraspecial 2-group, candidates
are recorded in [AM04, §IV.4-§IV.5 (Thm 4.3, Thm 5.6)] and consist of
a maximal elementary abelian subgroup combined with one extraspecial
section.

**Goal.** An alternative implementation of `UnitCircleCohomology(G, 3)`
that pulls $H^3(G; U(1))$ back from $H^3(H; U(1))$ via restriction,
where $H$ is HAP-tractable.

**Acceptance criteria.**
- For $m = 2, 3$: outputs agree with Q-6 and HAP byte-for-byte.
- For $m = 7$: produces a torsion vector and basis (the only
  technique that does, if HAP fails on the centraliser too).
- Documented detecting subgroup choice, including a proof
  reference for the injectivity claim.

**Dependencies.** None (independent of Q-1 through Q-8).

**Estimated effort.** 1 week.

**Files likely affected.**
- New `scripts/quillen_detecting_subgroup.g`.

**Out of scope.**
- The Q-1 through Q-8 path is the primary; Q-9 is redundancy.

**Status:** `ready`. **Labels:** `math`, `code`.

## 6. Workstream T — Transgression core

### T-EPIC

**Title.** `[T-EPIC] Transgression-kernel infrastructure`

**Body.**
Tracks workstream T. Closes when T-1 through T-6 close. The aim is
the cross-cutting infrastructure described in
`transgression_improvements_design.md` §2: HAP-native coboundary,
SNF wrapper, BRW reduction, centraliser-type caching, resumability,
and regression.

**Status:** `in progress` (this design doc). **Labels:** `epic`, `code`, `math`.

### T-1

**Title.** `[T-1] HAP-native IsCoboundary2 replacing SolutionIntMat-augmented baseline`

**Workstream.** T.

**Background.**
The current `IsCoboundary2(H, c, m)` in `scripts/transgression_kernel.g`
lines 83–111 builds an $n^2 \times (n + n^2)$ augmented integer
matrix and calls `SolutionIntMat`. At $n = 64$ this is ~30 s per
query and is the wall-clock bottleneck of the Tier-4 sweep.

**Goal.** Replace with a HAP-native variant `IsCoboundary2HAP` that
reuses the bar-resolution boundary maps already present in
`ResolutionFiniteGroup(H, 3)` to decide exactness.

**Acceptance criteria.**
- Identical Boolean output to baseline on every input.
- Regression: full $D_8$ enumeration matches existing
  `test_transgression_d8.g` outputs.
- Regression: $E_+(2)$ per-generator output reproduces existing
  on-disk results from `test_transgression_per_gen_e2.g`.
- Wall-clock at $n = 64$: ratio $\le 0.1$ over baseline averaged
  over 10 sample inputs.

**Dependencies.** None.

**Estimated effort.** 2 days.

**Files likely affected.**
- New `scripts/iscoboundary2_hap.g`.
- New `scripts/test_iscoboundary2_hap.g`.

**Out of scope.**
- SNF wrapper (T-2).
- BRW reduction (T-3).

**Status:** `ready`. **Labels:** `code`, `regression`.

### T-2

**Title.** `[T-2] SNF wrapper for transgression matrix`

**Workstream.** T.

**Background.**
The per-generator script `transgression_per_generator.g` produces one
row of the transgression matrix $M$ per generator. To compute $\ker \mathrm{Tr}$
exactly the matrix must be assembled and run through Smith Normal
Form, then intersected with the source torsion lattice.

**Goal.** A function `KernelOfTransgression(M, source_torsion)` that
computes $\ker \mathrm{Tr}$ as an explicit subgroup of
$\prod \mathbb Z/d_i$.

**Acceptance criteria.**
- Returns a list of $\prod \mathbb Z/d_i$-elements generating the
  kernel.
- Cross-check: on $D_8$, returns $[]$ (kernel trivial).
- Cross-check: on $E_+(2)$, applied to the existing per-generator
  output, agrees with brute-force enumeration of 4096 classes
  (decisive).
- API integrates with the per-generator script as a single
  one-line call after the loop.

**Dependencies.** None (operates on existing per-generator output).

**Estimated effort.** 3 days.

**Files likely affected.**
- New `scripts/transgression_snf.g`.
- New `scripts/test_transgression_snf.g`.

**Out of scope.**
- HAP-native coboundary (T-1).

**Status:** `ready`. **Labels:** `code`, `regression`.

### T-3a

**Title.** `[T-3a] Explicit BRW(m) construction as a matrix subgroup of O(2^m, R)`

**Workstream.** T.

**Background.**
The BRW group $\mathrm{BRW}(m) = N_{O(2^m)}(E_+(m))$ is the outer
normaliser of $E_+(m)$. Its construction in terms of explicit matrix
generators (KRR §3.1: $H, D, GL(m, 2)$ plus the $\sigma$ generators)
is partially recorded in `scripts/em_construction.g`; this issue
extends it to a full $\mathrm{BRW}(m)$ matrix subgroup.

**Goal.** A function `BRW(m)` returning the matrix subgroup of
$O(2^m, \mathbb Q)$ generated by the explicit generators.

**Acceptance criteria.**
- For $m = 2$: $|\mathrm{BRW}(2)|$ matches the published value (the
  group is $\mathbb Z_2 \cdot S_6 \cdot 2^{1+4}_+$ or equivalent
  per KRR §3.1).
- For $m = 3$: `Centralizer(BRW(3), -I)` contains $E_+(3)$ as a
  subgroup of index 2.
- For $m = 5, 7$: matrices realised in $O(2^m, \mathbb Q)$ rather
  than $O(2^m, \mathbb R)$ for exact arithmetic.

**Dependencies.** None.

**Estimated effort.** 4 days.

**Files likely affected.**
- `scripts/em_construction.g` extension.
- New `scripts/brw_construction.g`.

**Out of scope.**
- BRW action on $H^3$ (T-3b, T-3c).

**Status:** `ready`. **Labels:** `code`, `math`.

### T-3b

**Title.** `[T-3b] BRW(m) outer-automorphism action on E_+(m)-conjugacy classes`

**Workstream.** T.

**Background.**
For $y \in \mathrm{BRW}(m)$ and $g \in E_+(m)$, conjugation
$\alpha_y(g) = y g y^{-1}$ permutes $E_+(m)$ but acts trivially on
the inner-conjugacy classes. The induced action on the
4 BRW-orbits ($\{1\}, \{-1\}, \sigma_2$-type, $\sigma_1\sigma_2$-type)
must be made explicit.

**Goal.** A function `BRWConjugacyAction(m)` returning, for each
generator $y$ of $\mathrm{BRW}(m)/E_+(m)$, its induced permutation of
$E_+(m)$-conjugacy classes.

**Acceptance criteria.**
- Output preserves BRW-orbit structure: every generator's
  permutation maps a class in BRW-orbit $O$ to a class in the same
  orbit.
- For $m = 3$: against the 65 conjugacy classes computed by GAP,
  every BRW generator's action is an explicit permutation in $S_{65}$.
- Group-theoretic check: the generated subgroup of $S_{65}$ has
  order $|\mathrm{BRW}(m)/E_+(m)|$.

**Dependencies.** T-3a.

**Estimated effort.** 3 days.

**Files likely affected.**
- `scripts/brw_construction.g` extension.

**Out of scope.**
- Action on $H^3$ (T-3c).
- Per-class loop integration (T-3d).

**Status:** `blocked` on T-3a. **Labels:** `code`, `math`.

### T-3c

**Title.** `[T-3c] BRW(m) outer-automorphism action on H^3(E_+(m); U(1)) generators`

**Workstream.** T.

**Background.**
Conjugation by $y \in \mathrm{BRW}(m)$ pulls back to an action on
$Z^3(E_+(m); U(1))$ and descends to $H^3(E_+(m); U(1))$. For the BRW
reduction in T-3d we need this action on a fixed basis $e_1, \ldots, e_k$
of $H^3$ as integer matrices in $\mathrm{Mat}_k(\mathbb Z/m)$.

**Goal.** A function `BRWH3Action(m)` returning, for each generator
$y$ of $\mathrm{BRW}(m)/E_+(m)$, the induced
$\mathrm{Aut}(\prod \mathbb Z/d_i)$ action on the $H^3$ generators.

**Acceptance criteria.**
- Output is a list of $k \times k$ integer matrices with the source
  torsion structure preserved.
- Cross-check: the matrices generate a subgroup of
  $\mathrm{Aut}(\prod \mathbb Z/d_i)$ of the expected order.
- For $m = 2$: empirically validated against an explicit
  hand-computation on the 10 generators of $H^3(E_+(2); U(1))$.

**Dependencies.** T-3a.

**Estimated effort.** 4 days.

**Files likely affected.**
- `scripts/brw_construction.g` extension.

**Out of scope.**
- Per-class integration (T-3d).

**Status:** `blocked` on T-3a. **Labels:** `code`, `math`.

### T-3d

**Title.** `[T-3d] Per-class loop integration: BRW reduction of the transgression evaluation`

**Workstream.** T.

**Background.**
Combine T-3b (BRW action on classes) and T-3c (BRW action on $H^3$)
to evaluate $\mathrm{Tr}_g$ for one $g$ per BRW orbit (4
representatives) and pull the result back to all classes in the
orbit. Replaces the inner per-class loop in
`transgression_per_generator.g`.

**Goal.** A drop-in replacement
`PerGeneratorTransgressionBRW(setup, i, classes)` that evaluates
$\mathrm{Tr}(e_i)$ using the BRW reduction.

**Acceptance criteria.**
- For $m = 2$: output matches `TestGenerator(setup, i, classes)` on
  every generator.
- For $m = 3$: completes in $\le 1/4$ of the wall-clock of the
  baseline (4 BRW orbit representatives instead of 65 classes,
  plus the $H^3$-pullback overhead).
- Documented test case showing the BRW pullback agrees with a
  direct evaluation at one orbit element.

**Dependencies.** T-2, T-3b, T-3c.

**Estimated effort.** 3 days.

**Files likely affected.**
- `scripts/transgression_per_generator.g` extension or new
  `scripts/transgression_per_generator_brw.g`.

**Out of scope.**
- Centraliser-type caching (T-4).

**Status:** `blocked` on T-2, T-3b, T-3c. **Labels:** `code`.

### T-4

**Title.** `[T-4] Centraliser-type caching: persist HAP resolutions per centraliser type`

**Workstream.** T.

**Background.**
For $E_+(m)$ the centralisers fall into 4 types per BRW orbit
(`writeup.md` §2.4); the resolution `ResolutionFiniteGroup(C, 4)`
takes ~minutes per type and is constant across runs. Persist these
resolutions once per type per $m$ to avoid recomputation.

**Goal.** A caching wrapper around `ResolutionFiniteGroup` that
checks for an existing resolution on disk before recomputing, with
a per-$m$ directory layout matching
`computed/transgression/<m>/resolution_<type>.g`.

**Acceptance criteria.**
- First call to `ResolutionFiniteGroupCached(H, 4, key)` computes
  and persists; subsequent calls with the same `key` return the
  cached object.
- Cross-machine reproducibility: a cached resolution from one host
  loads correctly on another.
- Storage: ≤ 100 MB per resolution at $m = 5$.

**Dependencies.** None.

**Estimated effort.** 2 days.

**Files likely affected.**
- New `scripts/resolution_cache.g`.

**Out of scope.**
- Resumable run-state (T-5).

**Status:** `ready`. **Labels:** `code`.

### T-5

**Title.** `[T-5] Resumable run-state for long-running per-generator sweeps`

**Workstream.** T.

**Background.**
Tier-4 sweeps at $m = 3$ take hours; at $m = 5, 7$ they take days.
A long-running per-generator sweep that crashes mid-run loses all
intermediate data. Persist per-generator output incrementally so a
restart can resume from the last completed generator.

**Goal.** A wrapper around `transgression_per_generator` that
appends each generator's output to disk as it completes, and a
resume function that picks up from the last persisted generator.

**Acceptance criteria.**
- Crash mid-sweep, then restart: the resumed run completes without
  re-evaluating any already-completed generator.
- Output format compatible with T-2 (the SNF wrapper consumes the
  same on-disk format).
- Storage: incremental, $O(k_{\text{completed}})$ per file.

**Dependencies.** T-2 (output format must align).

**Estimated effort.** 2 days.

**Files likely affected.**
- New `scripts/transgression_resume.g`.

**Out of scope.**
- Distributed parallelism across machines (future enhancement).

**Status:** `blocked` on T-2. **Labels:** `code`.

### T-6

**Title.** `[T-6] D_8 regression test for the upgraded Tier-4 pipeline`

**Workstream.** T.

**Background.**
$D_8$ is the smallest extraspecial 2-group ($E_+(1)$) and has full
Tier-4 ground truth (kernel trivial via 16-class enumeration). Use
it as a continuous regression for every component in workstream T.

**Goal.** A regression script that runs the full upgraded pipeline
(HAP-native coboundary + SNF + BRW reduction + centraliser caching)
on $D_8$ and asserts $\ker \mathrm{Tr} = 0$.

**Acceptance criteria.**
- Wall-clock target: completes in $\le 10$ s.
- Output `kernel_size = 0`.
- Per-generator $\mathrm{Tr}(e_i) \ne 0$ for every generator.
- Test fails loudly if any component deviates.

**Dependencies.** T-1, T-2, T-3d, T-4.

**Estimated effort.** 1 day.

**Files likely affected.**
- New `scripts/test_transgression_d8_upgraded.g`.

**Out of scope.**
- $E_+(2)$ regression (X-3).

**Status:** `blocked` on T-1, T-2, T-3d, T-4. **Labels:** `regression`, `code`.

## 7. Workstream V — Validators (Tiers 1, 3, 5)

### V-EPIC

**Title.** `[V-EPIC] Validators for Tiers 1, 3, 5`

**Body.**
Tracks workstream V. Three validator pipelines: Tier 1 ($\varepsilon_\omega$
phase), Tier 3 ($\mathrm{Aut}(N, T)$), Tier 5 (FS indicators).
Closes when V-1 through V-7 close.

**Status:** `in progress`. **Labels:** `epic`, `code`, `math`.

### V-1

**Title.** `[V-1] Tier-1 ε_ω phase callable, CGR convention`

**Workstream.** V.

**Background.**
Per `writeup.md` §6.2, the twisted-$S$ phase
$\varepsilon_\omega(g_1, g_2, a, b)$ is computable in $O(1)$ from $\omega$
as a callable $G^3 \to \mathbb Z/m$. The clean form is from
[CGR2000, §4]; precise sign convention must be recorded.

**Goal.** A function `EpsilonOmega(omega, g1, g2, a, b)` returning
the phase in $\mathbb Z/m$.

**Acceptance criteria.**
- $\varepsilon_\omega \equiv 1$ identically when $\omega = 0$ (the
  trivial cocycle), on a sample of $G^4$ tuples.
- For $G = Q_8$ with the order-2 cocycle, the resulting $S^\omega$
  matrix entries via the §6.3 closed form match the existing
  `modular_data/8/4/2.txt` byte-for-byte on at least 10 sampled
  central-row entries.
- Sign convention documented in the function docstring with a
  reference to the source paper (CGR or DPR or NN08).

**Dependencies.** None.

**Estimated effort.** 3 days.

**Files likely affected.**
- New `scripts/epsilon_omega.g`.
- New `scripts/test_epsilon_omega.g`.

**Out of scope.**
- Closed-form $S^\omega$ central-row evaluator (V-2).

**Status:** `ready`. **Labels:** `code`, `math`.

### V-2

**Title.** `[V-2] Tier-1 closed-form S^ω entry for central rows`

**Workstream.** V.

**Background.**
Per `writeup.md` §6.3, central-row $S^\omega$ entries collapse to
two evaluations of $\varepsilon_\omega$ and two character
evaluations. Build the per-entry evaluator on top of V-1.

**Goal.** A function `STwistedCentralEntry(G, omega, g1, chi1, g2, chi2)`
returning the value of $S^\omega_{((g_1, \chi_1), (g_2, \chi_2))}$
when $g_1 \in \{1, -1\}$.

**Acceptance criteria.**
- $\omega = 0$ case agrees with the §4.3 closed form on 100 random
  test entries at $m = 3$.
- For $Q_8$ order-2 cocycle, agrees with `modular_data/8/4/2.txt`.
- Throws an error if $g_1 \notin \{1, -1\}$.

**Dependencies.** V-1.

**Estimated effort.** 2 days.

**Files likely affected.**
- New `scripts/s_twisted_central.g`.

**Out of scope.**
- Non-central rows (out of Trajectory C scope).

**Status:** `blocked` on V-1. **Labels:** `code`, `math`.

### V-3

**Title.** `[V-3] Tier-5 FSIforDoubles thin wrapper for one-shot queries`

**Workstream.** V.

**Background.**
`DRINFELD/src/universal_coefficients.g` line 355 defines
`FSIforDoubles(G, f, class, proj, i, n, listG, pivalues, m)`, but
the calling convention requires substantial setup (`pivalues`,
`PC`, `listG`, etc.). Wrap with a one-shot interface.

**Goal.** A function `FSI(G, omega, g, chi, n)` returning
$\nu_n((g, \chi))$ for $D^\omega(G)$ with the IMN closed form.

**Acceptance criteria.**
- For $\omega = 0$ on $Q_8$: $\nu_2$ values match the classical
  $\nu_2(\rho) = (1/|G|) \sum_g \chi_\rho(g^2)$ on every irrep.
- For $Q_8$ order-2 cocycle: $\nu_2$ values match the published
  values in [MN05].
- Wall-clock at $m = 3$, single $\nu_n$ query: $\le 1$ s.

**Dependencies.** V-4 (broken `GaugeInvariants` may be in the call
path; ensure it isn't).

**Estimated effort.** 1 day.

**Files likely affected.**
- New `scripts/fsi_wrapper.g`.

**Out of scope.**
- The `GaugeInvariants` fix (V-4).

**Status:** `ready`. **Labels:** `code`, `regression`.

### V-4

**Title.** `[V-4] Fix GaugeInvariants undeclared-locals bug`

**Workstream.** V.

**Background.**
`DRINFELD/src/universal_coefficients.g` line 422 references
`hombasis` without declaring it in the `local` block on lines
392–416. Other functions in the same block reference `pivalues`
similarly. As a result, `GaugeInvariants(G)` does not run.

**Goal.** Add the missing locals; verify on $Q_8$ that the function
runs end-to-end and produces sensible output.

**Acceptance criteria.**
- `GaugeInvariants(Q_8)` runs without error and returns a record
  with the documented shape.
- Output for the trivial cocycle agrees with element-wise
  invocation of `FSIforDoubles` on a sample of simples.

**Dependencies.** None.

**Estimated effort.** 1 day.

**Files likely affected.**
- `DRINFELD/src/universal_coefficients.g` lines 392–446.

**Out of scope.**
- Fix `FSIforAGT` parser errors (V-8).

**Status:** `ready`. **Labels:** `code`.

### V-8

**Title.** `[V-8] Fix FSIforAGT parser errors`

**Workstream.** V.

**Background.**
`DRINFELD/src/universal_coefficients.g` lines ~562–600 define
`FSIforAGT(G, N, omega)` for adaptated-cocycle FS indicators on
almost-group-theoretical (AGT) fusion subcategories. The function
currently has two surface-level bugs that prevent GAP from parsing
the file cleanly:

1. The token `listG:-Enumerator` (Pascal-style member-access
   operator) appears where `Enumerator(listG)` or `listG[...]` is
   intended. GAP does not parse `:-`.
2. The inner anonymous function `nu` is missing a closing bracket;
   the resulting parse error cascades to the rest of the file.

The mathematics is correct (per [MN05]); only the surface code is
broken.

**Goal.** Fix the parser errors so that `FSIforAGT(G, N, omega)`
runs end-to-end. Verify on a small AGT example.

**Acceptance criteria.**
- `FSIforAGT(Q_8, N, omega)` runs without error for $N$ a small
  normal subgroup of $Q_8$ (e.g. $\langle -1 \rangle$) and a chosen
  $\omega \in H^3(Q_8; U(1))$.
- Output is a list of indicator vectors with the documented shape
  (one per double coset of $N$ in $G$).
- For $\omega = 0$ and $N = G$: output reduces to the regular
  Frobenius–Schur indicators of $G$, agreeing with V-3
  (`FSIforDoubles`) on shared simples.
- For $\omega = 0$ and $N = 1$: output is empty / trivial as the
  AGT subcategory degenerates.

**Dependencies.** None.

**Estimated effort.** 1 day.

**Files likely affected.**
- `DRINFELD/src/universal_coefficients.g` lines ~562–600.
- New `scripts/test_fsi_for_agt.g` smoke test on $Q_8$.

**Out of scope.**
- Application of `FSIforAGT` at $m \ge 3$ (downstream issue, not
  yet ticketed; AGT subcategories at $E_+(m)$ are a separate
  research direction).

**Status:** `ready`. **Labels:** `code`.

### V-5a

**Title.** `[V-5a] Aut(N, T) engine: T-block + dimension partition`

**Workstream.** V.

**Background.**
Computing $|\mathrm{Aut}(N, T)|$ as a backtracking search starts
with a refinement of $\{1, \ldots, r\}$ by invariants preserved by
all automorphisms. The cheapest are the T-eigenvalue and the
quantum dimension. For $E_+(m)$ the T-eigenvalue partition has 4
blocks; the QD partition splits each further.

**Goal.** A function `InitialPartition(N, T, QD)` returning the
joint refinement of $\{1, \ldots, r\}$ by T-value and QD.

**Acceptance criteria.**
- For $D(Q_8)$: returns the expected 22-element partition.
- For $\mathrm{Mod}(D^1(E_+(2)))$: returns the expected partition
  matching the $\{1^{102}, (-1)^{70}, i^6, (-i)^6\}$ T-multiset
  refined by QD.
- API: returns a list of disjoint subsets covering $\{1, \ldots, r\}$.

**Dependencies.** None.

**Estimated effort.** 2 days.

**Files likely affected.**
- New `scripts/aut_n_t.g`.

**Out of scope.**
- Colour refinement on N (V-5b), backtracking (V-5c).

**Status:** `ready`. **Labels:** `code`, `math`.

### V-5b

**Title.** `[V-5b] Aut(N, T) engine: colour refinement on fusion-row signatures`

**Workstream.** V.

**Background.**
Refine the V-5a partition further by the row signature of $N$:
$\sigma(i) = $ multiset of $\{N_{ij}^k : (j, k) \in \text{partition}\}$.
Iterate to a stable colour refinement.

**Goal.** A function `RefineByFusion(partition, N)` returning the
stable colour-refinement of the input partition under fusion-row
signatures.

**Acceptance criteria.**
- For $D(Q_8)$: stable refinement reproduces the 22-element
  fusion-T partition determined by hand.
- For $\mathrm{Mod}(D^1(E_+(2)))$: stable refinement consistent
  with the dense fusion ring computed via Verlinde from the on-disk
  $S$.

**Dependencies.** V-5a.

**Estimated effort.** 3 days.

**Files likely affected.**
- `scripts/aut_n_t.g` extension.

**Out of scope.**
- Backtracking (V-5c).

**Status:** `blocked` on V-5a. **Labels:** `code`, `math`.

### V-5c

**Title.** `[V-5c] Aut(N, T) engine: backtracking with refinement-based pruning`

**Workstream.** V.

**Background.**
With the V-5a + V-5b partition in hand, search for permutations
preserving $(N, T)$ via backtracking. Each branch fixes a target
for one orbit representative, refines, and recurses.

**Goal.** A function `AutNT(N, T, QD)` returning the order
$|\mathrm{Aut}(N, T)|$ and a generating set.

**Acceptance criteria.**
- For $D(Q_8)$: returns 6 (trivial cocycle case) and 24 (order-2
  cocycle case) — reproducing the existing `q8_extension_type/`
  result.
- For $\mathrm{Mod}(D^1(E_+(2)))$: returns the expected value
  (computed once via direct enumeration; cached as ground truth).
- Wall-clock at $E_+(3)$ rank 2272: completes in $\le 1$ day.

**Dependencies.** V-5b.

**Estimated effort.** 4 days.

**Files likely affected.**
- `scripts/aut_n_t.g` extension.

**Out of scope.**
- BRW-quotient mode (V-6).

**Status:** `blocked` on V-5b. **Labels:** `code`, `math`.

### V-6

**Title.** `[V-6] Aut(N, T) BRW-quotient mode`

**Workstream.** V.

**Background.**
Per `writeup.md` §8.3, $\mathrm{Aut}(N, T)$ contains the BRW
outer-automorphism action as a known subgroup. The substantive
content is the quotient $\mathrm{Aut}(N, T)/\mathrm{BRW}$. Compute
it directly to halve the search space.

**Goal.** A variant `AutNTModBRW(N, T, QD, BRW_action)` returning
the order and generators of the quotient.

**Acceptance criteria.**
- For $\mathrm{Mod}(D^1(E_+(2)))$: returns `|Aut| / |BRW(2)/E_+(2)|`
  consistent with V-5c output.
- Wall-clock: $\le 1/4$ of V-5c on $E_+(3)$.

**Dependencies.** V-5c, T-3c.

**Estimated effort.** 3 days.

**Files likely affected.**
- `scripts/aut_n_t.g` extension.

**Out of scope.**
- Computing $\mathrm{Aut}(N, T)$ on Keller's MTC side (requires K-2).

**Status:** `blocked` on V-5c, T-3c. **Labels:** `code`, `math`.

### V-7a

**Title.** `[V-7a] Single-S-entry primitive from canonical-block storage`

**Workstream.** V.

**Background.**
At $m = 5, 7$ the dense $S$ is unstorable but the 22 BRW-canonical
blocks are persisted (`computed/E_plus_5/structural/`,
`computed/E_plus_7/structural/`). Lookup of $S_{ij}$ requires:
identify the BRW-orbit type pair, find the canonical block, look up
via per-class permutation.

**Goal.** A function `SEntry(m, i, j)` returning $S_{ij}$ in $O(1)$
amortised.

**Acceptance criteria.**
- For $m = 3$: agrees with the dense $S$ on 1000 random index pairs.
- For $m = 5$: completes a query in $\le 1$ ms.
- For $m = 7$: documented behaviour for the 13 missing canonical
  blocks (zero blocks return 0; central-block triplets use closed
  form).

**Dependencies.** None (canonical blocks already on disk).

**Estimated effort.** 3 days.

**Files likely affected.**
- New `scripts/s_entry_canonical.g`.

**Out of scope.**
- Verlinde loop (V-7b).

**Status:** `ready`. **Labels:** `code`.

### V-7b

**Title.** `[V-7b] Verlinde-on-canonical-blocks: fusion-coefficient query primitive`

**Workstream.** V.

**Background.**
With V-7a giving $O(1)$ $S$-entries, the fusion coefficient
$N_{ij}^k = \sum_a S_{ia} S_{ja} \overline{S_{ka}} / S_{0a}$ becomes
an $O(r)$-time query. For $r \sim 5 \cdot 10^5$ this is sub-second
per coefficient.

**Goal.** A function `FusionCoefficient(m, i, j, k)` returning
$N_{ij}^k$ as a non-negative integer.

**Acceptance criteria.**
- For $m = 3$: matches direct Verlinde from the dense $S$ on 100
  random triples.
- For $m = 5$: produces non-negative integer outputs on a sample of
  100 triples.
- Wall-clock: $\le 1$ s per query at $m = 5$.

**Dependencies.** V-7a.

**Estimated effort.** 2 days.

**Files likely affected.**
- `scripts/s_entry_canonical.g` extension.

**Out of scope.**
- Materialising the full $N$ tensor (out of scope at $m \ge 5$).

**Status:** `blocked` on V-7a. **Labels:** `code`.

## 8. Workstream K — KRR pipeline → S-entry adapter

### K-EPIC

**Title.** `[K-EPIC] KRR pipeline to S-entry adapter`

**Body.**
Tracks workstream K. Optional in Trajectory C — the trajectory
compares against abstract $\omega$ — but provides cross-validation
against KRR's published intertwiner outputs. Closes when K-1
through K-3 close.

**Status:** `in progress`. **Labels:** `epic`, `code`, `math`.

### K-1

**Title.** `[K-1] Implement projector formula KRR24 eq (2.1.2)`

**Workstream.** K.

**Background.**
The projector formula in [KRR24, §2.1, eq. (2.1.2)] expresses each
$S^{\mathrm{Keller}}$-matrix entry as a sum of intertwiner traces on
twisted modules. This is the missing adapter between
`scripts/defect_rep_minus_id_optim.g` (which produces single
intertwiner entries) and a single $S$-matrix entry.

**Goal.** A function `ProjectorFormula(W_g1, W_g2, intertwiner_data)`
returning the value of $S^{\mathrm{Keller}}_{((g_1, \chi_1), (g_2, \chi_2))}$
for one index pair.

**Acceptance criteria.**
- Output is a complex number representable in GAP's cyclotomic
  arithmetic.
- For $\omega = 0$ at $m = 3$: agrees with the dense untwisted $S$ on
  central-row entries.

**Dependencies.** None (uses existing intertwiner machinery).

**Estimated effort.** 1 week.

**Files likely affected.**
- New `scripts/krr_projector.g`.

**Out of scope.**
- Full $S^{\mathrm{Keller}}$ adapter (K-2).

**Status:** `ready`. **Labels:** `code`, `math`.

### K-2

**Title.** `[K-2] Single-entry S^Keller adapter`

**Workstream.** K.

**Background.**
Wrap K-1 with the index-decoding logic that maps a global simple
index $(g, \chi)$ to the appropriate twisted-module data and
intertwiner inputs.

**Goal.** A function `SKeller(m, i, j)` returning
$S^{\mathrm{Keller}}_{ij}$ for one index pair.

**Acceptance criteria.**
- For $m = 3$ on central-row entries: agrees with V-2's
  $S^\omega$ for $\omega = 0$ within numerical tolerance ($10^{-12}$).
- For $m = 7$: completes a query in $\le 5$ minutes.

**Dependencies.** K-1.

**Estimated effort.** 1 week.

**Files likely affected.**
- `scripts/krr_projector.g` extension.

**Out of scope.**
- Cross-check against $S^0$ (K-3).

**Status:** `blocked` on K-1. **Labels:** `code`.

### K-3

**Title.** `[K-3] Cross-check S^Keller vs S^0 closed forms at m = 3`

**Workstream.** K.

**Background.**
For $\omega = 0$, the KRR pipeline must reproduce the untwisted
$S^0$ matrix. Use the central-row closed forms (writeup §4.3) as
ground truth.

**Goal.** A regression script confirming `SKeller(3, i, j)` agrees
with the §4.3 closed form on every central-row entry.

**Acceptance criteria.**
- 100% agreement on the 16 × 2272 central-row entries (8 rows × 2272
  columns × 2 row variants).

**Dependencies.** K-2, V-2.

**Estimated effort.** 3 days.

**Files likely affected.**
- New `scripts/test_krr_vs_central_closed_form.g`.

**Out of scope.**
- Non-central agreement (would require full $S$, infeasible at
  $m = 3$ already, infeasible at $m \ge 5$).

**Status:** `blocked` on K-2, V-2. **Labels:** `regression`, `code`.

## 9. Workstream A — Application sweeps

### A-EPIC

**Title.** `[A-EPIC] Application sweeps for E_+(m) at m = 2, 3, 5, 7`

**Body.**
Tracks workstream A. Per-$m$ orchestrators wire together T, V, Q
outputs at each stage; decision-point dispatchers at the end of $m = 3$
and $m = 5$ stages branch to next steps based on observed kernel
outcomes.

**Status:** `in progress`. **Labels:** `epic`, `code`.

### A-2

**Title.** `[A-2] E_+(2) Tier-4 SNF closure`

**Workstream.** A.

**Background.**
The existing per-generator output for $E_+(2)$ shows every
$\mathrm{Tr}(e_i) \ne 0$. Apply T-2's SNF wrapper to read off
$\ker \mathrm{Tr}$ exactly. This is the smallest non-trivial
end-to-end test of the upgraded Tier-4 pipeline.

**Goal.** A driver script that loads the existing per-generator
output, runs the SNF wrapper, and persists the kernel.

**Acceptance criteria.**
- Cross-check against brute-force enumeration of 4096 $H^3$
  classes (decisive ground truth).
- Output stored at `computed/transgression/2/kernel.g` in a
  documented format.

**Dependencies.** T-2.

**Estimated effort.** 1 day.

**Files likely affected.**
- New `scripts/run_e_plus_2_kernel.g`.

**Out of scope.**
- Tier-1/3/5 application at $m = 2$.

**Status:** `blocked` on T-2. **Labels:** `code`.

### A-3a

**Title.** `[A-3a] E_+(3) Tier-4 driver: full kernel computation`

**Workstream.** A.

**Background.**
End-to-end orchestrator at $m = 3$: cross-cutting infrastructure
(T-1, T-2, T-3d, T-4) plus $E_+(3)$ data produces the integer
matrix $M$, then the SNF gives the kernel.

**Goal.** A driver script `run_e_plus_3_kernel.g` that produces
$\ker \mathrm{Tr}(E_+(3))$ as an explicit subgroup of
$\mathbb Z/2^{34} \oplus \mathbb Z/4$.

**Acceptance criteria.**
- Wall-clock $\le 1$ hour total.
- Output stored at `computed/transgression/3/kernel.g`.
- Cross-check against direct evaluation on 100 random sample
  classes.

**Dependencies.** T-1, T-2, T-3d, T-4, T-5.

**Estimated effort.** 3 days.

**Files likely affected.**
- New `scripts/run_e_plus_3_kernel.g`.

**Out of scope.**
- Decision-point dispatch (A-3b).

**Status:** `blocked` on T-1, T-2, T-3d, T-4, T-5. **Labels:** `code`.

### A-3b

**Title.** `[A-3b] DP-I auto-dispatcher: m = 3 outcome → next-stage selection`

**Workstream.** A.

**Background.**
The kernel computed in A-3a deterministically selects the next
stage. The dispatcher reads the output, evaluates the predicate
`kernel = 0`, and updates downstream issue labels accordingly. No
human review.

**Goal.** A script that reads the A-3a output, persists a verdict,
and emits machine-readable output suitable for an automated label
update on the GitHub side.

**Acceptance criteria.**
- Verdict text follows the format
  `DP-I: |ker Tr| = N. Next: <branch label>`.
- Status persisted to `computed/transgression/3/dp_i_verdict.g`.
- Emits a JSON payload on stdout listing which issues to unblock
  (kernel = 0 ⇒ A-3d, A-5a; kernel ≠ 0 ⇒ A-3c, A-3d, A-5a).
- Tested on a synthetic kernel = 0 input and a synthetic kernel ≠ 0
  input; correct branch in each case.

**Dependencies.** A-3a.

**Estimated effort.** 1 day.

**Files likely affected.**
- New `scripts/dp_i_dispatch.g`.

**Out of scope.**
- The candidate-elimination loop itself (A-3c).
- Implementation of automated GitHub label updates (CI/automation
  concern, separate ticket if needed).

**Status:** `blocked` on A-3a. **Labels:** `decision-point`, `code`.

### A-3c

**Title.** `[A-3c] E_+(3) Tier-1/5 candidate-elimination loop (conditional)`

**Workstream.** A.

**Background.**
If $\ker \mathrm{Tr}(E_+(3)) \ne 0$, eliminate each non-zero
candidate $[\omega] \in \ker \mathrm{Tr}$ via Tier-1
($\varepsilon_\omega$ on a chosen central-row entry) and/or Tier-5
($\nu_n((g, \chi))$ on a chosen simple). Report which candidates
disagree from $\omega = 0$ (eliminated) and which agree (potentially
problematic).

**Goal.** A driver `run_e_plus_3_elimination.g` looping over
non-zero kernel candidates, applying V-2 (Tier 1) and V-3 (Tier 5),
and producing a per-candidate report.

**Acceptance criteria.**
- For each candidate, log: candidate vector, $S^\omega$ on the
  chosen entry, $\nu_n$ on the chosen simple, verdict
  (eliminated / agrees-on-test).
- Wall-clock budget: $\le 1$ hour per candidate.

**Dependencies.** A-3b (DP-I says non-trivial kernel), V-2, V-3.

**Estimated effort.** 3 days.

**Files likely affected.**
- New `scripts/run_e_plus_3_elimination.g`.

**Out of scope.**
- Aut(N, T) cross-validation (A-3d).

**Status:** `blocked` on A-3b, V-2, V-3.
**Labels:** `code`, `decision-point` (only runs in the non-trivial
kernel branch).

### A-3d

**Title.** `[A-3d] E_+(3) Tier-3 |Aut(N, T)| cross-validation`

**Workstream.** A.

**Background.**
Run V-5c on the dense $E_+(3)$ untwisted modular data (Verlinde
yields $N$); separately run on the same data after applying a
non-zero kernel candidate (or, if $\ker = 0$, only the untwisted
side). Compare $|\mathrm{Aut}(N, T)|$ between sides.

**Goal.** A driver `run_e_plus_3_aut.g` producing
$|\mathrm{Aut}(N^0, T^0)|$ at $m = 3$, plus per-candidate
$|\mathrm{Aut}(N^\omega, T^\omega)|$ if applicable.

**Acceptance criteria.**
- Untwisted output is consistent with the BRW lower bound
  (expected: $|\mathrm{Aut}| \ge |\mathrm{BRW}(3)/E_+(3)|$).
- Wall-clock: $\le 1$ day on a single CPU.

**Dependencies.** V-5c, V-7b.

**Estimated effort.** 2 days.

**Files likely affected.**
- New `scripts/run_e_plus_3_aut.g`.

**Out of scope.**
- Sub-MTC variants for $m = 5$ (A-5d).

**Status:** `blocked` on V-5c, V-7b. **Labels:** `code`.

### A-5a

**Title.** `[A-5a] E_+(5) Tier-4 HAP attempt + DP-II auto-dispatcher`

**Workstream.** A.

**Background.**
At $m = 5$ ($|G| = 2048$), `ResolutionFiniteGroup(E_+(5), 4)` may or
may not succeed within a 60 GB heap budget. Run a timed attempt;
record peak memory, wall-clock, and outcome. The dispatcher
deterministically selects the next route — HAP if successful,
Quillen otherwise. No human review.

**Goal.** A driver `run_e_plus_5_resolution.g` plus an auto-dispatch
script `dp_ii_dispatch.g` that branches on the resolution outcome.

**Acceptance criteria.**
- Resolution attempt logs: peak RSS, wall-clock, success boolean.
- DP-II verdict persisted to
  `computed/transgression/5/dp_ii_verdict.g`.
- Emits machine-readable output: "HAP succeeded" → unblock A-5b;
  "HAP failed" → unblock A-5c (or escalate Q-7 priority if Q-7 not
  yet ready).

**Dependencies.** A-3a (Tier-4 pipeline validated at $m = 3$),
T-1, T-2, T-3d, T-4, T-5.

**Estimated effort.** 2 days.

**Files likely affected.**
- New `scripts/run_e_plus_5_resolution.g`,
  `scripts/dp_ii_dispatch.g`.

**Out of scope.**
- The actual Quillen pivot (Q-1 through Q-8).

**Status:** `blocked` on A-3a. **Labels:** `decision-point`, `code`.

### A-5b

**Title.** `[A-5b] E_+(5) Tier-4 driver (HAP route)`

**Workstream.** A.

**Background.**
Conditional on DP-II "HAP succeeded": run the full Tier-4 pipeline
at $m = 5$ using the same upgraded infrastructure as $m = 3$.

**Goal.** Driver script analogous to A-3a, persisting
$\ker \mathrm{Tr}(E_+(5))$.

**Acceptance criteria.**
- Wall-clock $\le 1$ day single-CPU.
- Output at `computed/transgression/5/kernel.g`.

**Dependencies.** A-5a (HAP-succeeded branch), T-3d, T-4.

**Estimated effort.** 2 days.

**Files likely affected.**
- New `scripts/run_e_plus_5_kernel.g`.

**Out of scope.**
- Quillen-route variant (A-5c).

**Status:** `blocked` on A-5a. **Labels:** `decision-point`, `code`.

### A-5c

**Title.** `[A-5c] E_+(5) Tier-4 driver (Quillen route)`

**Workstream.** A.

**Background.**
Conditional on DP-II "HAP failed": run Tier-4 at $m = 5$ using the
Quillen analytical pipeline (Q-7 / Q-9) instead of HAP.

**Goal.** Driver script analogous to A-5b, with Q-7's standard
cocycle generator replacing HAP's.

**Acceptance criteria.**
- Wall-clock $\le 2$ days single-CPU.
- Output at `computed/transgression/5/kernel.g`.

**Dependencies.** A-5a (HAP-failed branch), Q-7 or Q-9.

**Estimated effort.** 3 days.

**Files likely affected.**
- New `scripts/run_e_plus_5_kernel_quillen.g`.

**Out of scope.**
- HAP-route variant (A-5b).

**Status:** `blocked` on A-5a, Q-7. **Labels:** `decision-point`, `code`.

### A-5d

**Title.** `[A-5d] E_+(5) Tier-3 on subset (central + one non-central class)`

**Workstream.** A.

**Background.**
Per `writeup.md` §8.5: full $\mathrm{Aut}(N, T)$ at $m = 5$ is
infeasible, but on the subset "central simples + one non-central
class" it is. Use V-5c with V-7b's on-demand $N$-queries.

**Goal.** Driver producing $|\mathrm{Aut}|$ on the chosen subset.

**Acceptance criteria.**
- Wall-clock $\le 3$ days.
- Subset chosen and documented (e.g.
  $\sigma_2$-orbit representative).

**Dependencies.** V-5c, V-7b, A-5b or A-5c.

**Estimated effort.** 1 week.

**Files likely affected.**
- New `scripts/run_e_plus_5_aut.g`.

**Out of scope.**
- $E_+(7)$ Aut(N, T) (out of scope per writeup §8.6).

**Status:** `blocked` on V-5c, V-7b, A-5b or A-5c. **Labels:** `code`.

### A-7a

**Title.** `[A-7a] E_+(7) Tier-4 driver via Quillen analytical H^3`

**Workstream.** A.

**Background.**
At $m = 7$ HAP's resolution OOMs. Tier-4 must use the Quillen
pipeline (Q-7) for $H^3(E_+(7); U(1))$ generators, plus the
upgraded T-stack for evaluation.

**Goal.** Driver producing $\ker \mathrm{Tr}(E_+(7))$ as an explicit
subgroup of the analytical $H^3$.

**Acceptance criteria.**
- Wall-clock $\le 2$ weeks single-CPU (parallelisable across BRW
  orbit representatives).
- Output at `computed/transgression/7/kernel.g`.

**Dependencies.** Q-7 (or Q-9), T-1, T-2, T-3d, T-4, T-5.

**Estimated effort.** 2 weeks.

**Files likely affected.**
- New `scripts/run_e_plus_7_kernel.g`.

**Out of scope.**
- Tier-1/5 elimination (A-7b).

**Status:** `blocked` on Q-7 (or Q-9), T-* full stack.
**Labels:** `code`, `decision-point` (final result decides Keller's conjecture).

### A-7b

**Title.** `[A-7b] E_+(7) Tier-1/5 candidate-elimination loop (conditional)`

**Workstream.** A.

**Background.**
Conditional on `kernel ≠ 0` at $m = 7$: eliminate non-zero
candidates via Tier-1 / Tier-5. At $m = 7$, single-entry $\nu_n$
queries take $\sim 1$ minute; budget per candidate accordingly.

**Goal.** Driver applying V-2, V-3 to each kernel candidate.

**Acceptance criteria.**
- Per-candidate report: V-2 verdict, V-3 verdict, status.
- Wall-clock budget: $\le 1$ day per candidate.

**Dependencies.** A-7a, V-2, V-3.

**Estimated effort.** 1 week (depends on candidate count).

**Files likely affected.**
- New `scripts/run_e_plus_7_elimination.g`.

**Out of scope.**
- Tier-3 (infeasible at $m = 7$).

**Status:** `blocked` on A-7a. **Labels:** `code`, `decision-point`.

## 10. Workstream X — Cross-checks and regression

### X-EPIC

**Title.** `[X-EPIC] Cross-checks and regression`

**Body.**
Tracks workstream X. Always-on validation against $D_8$, $Q_8$,
$E_+(2)$ ground truth.

**Status:** `in progress`. **Labels:** `epic`, `regression`.

### X-1

**Title.** `[X-1] Q_8 regression suite`

**Workstream.** X.

**Background.**
The $Q_8$ investigation (`q8_extension_type/`) provides ground truth
for Tier-3 ($|\mathrm{Aut}(N, T)|$ = 6 vs 24) and partially for
Tier-1/5 (closed-form $S^\omega$ entries via $\omega \in H^3(Q_8) = \mathbb Z/8$).

**Goal.** A regression script asserting V-1, V-2, V-3, V-5c
reproduce the $Q_8$ ground-truth values.

**Acceptance criteria.**
- $|\mathrm{Aut}(N^0, T^0)| = 6$, $|\mathrm{Aut}(N^{\omega_4}, T^{\omega_4})| = 24$.
- $S^{\omega_4}$ on disk (`modular_data/8/4/2.txt`) reproducible
  via V-2 byte-for-byte on central rows.
- $\nu_n$ values on $Q_8$ match published [MN05] values.

**Dependencies.** V-1, V-2, V-3, V-5c.

**Estimated effort.** 3 days.

**Files likely affected.**
- New `scripts/test_q8_regression.g`.

**Out of scope.**
- $D_8$ regression (X-2).

**Status:** `blocked` on V-1, V-2, V-3, V-5c. **Labels:** `regression`.

### X-2

**Title.** `[X-2] D_8 regression suite`

**Workstream.** X.

**Background.**
$D_8 = E_+(1)$ has full Tier-4 ground truth: kernel is trivial.
Use as a regression for the upgraded Tier-4 pipeline.

**Goal.** A regression script asserting T-1, T-2, T-3d, T-4 produce
`kernel = 0` end-to-end on $D_8$.

**Acceptance criteria.**
- Output: `kernel_size = 0`.
- Wall-clock $\le 10$ s with the upgraded pipeline (vs minutes on
  the original).

**Dependencies.** T-1, T-2, T-3d, T-4.

**Estimated effort.** 2 days.

**Files likely affected.**
- New `scripts/test_d8_regression.g`.

**Out of scope.**
- $E_+(2)$ regression (X-3).

**Status:** `blocked` on T-* full stack. **Labels:** `regression`.

### X-3

**Title.** `[X-3] E_+(2) regression suite`

**Workstream.** X.

**Background.**
$E_+(2)$ has full per-generator Tier-4 ground truth (every
$\mathrm{Tr}(e_i) \ne 0$) and full $(S, T)$ on disk
(`modular_data/32/49/1.txt`). Comprehensive regression covers
every workstream.

**Goal.** A regression script running T, V (with QFusion ring from
the on-disk $S$), and Tier-3 V-5c pipelines on $E_+(2)$.

**Acceptance criteria.**
- Tier-4: SNF kernel at $E_+(2)$ matches brute-force enumeration
  of all 4096 $H^3$ classes (the decisive ground truth).
- Tier-3: $|\mathrm{Aut}(N, T)|$ at $m = 2$ matches a one-time
  hand-computed reference.
- Tier-5: $\nu_2$ values consistent with the classical
  character-table formula at $\omega = 0$.

**Dependencies.** T-1, T-2, V-1, V-2, V-3, V-5c.

**Estimated effort.** 2 days.

**Files likely affected.**
- New `scripts/test_e_plus_2_regression.g`.

**Out of scope.**
- $E_+(3)$ application validation (A-3a).

**Status:** `blocked` on T-* + V-* full stack. **Labels:** `regression`.

### X-4

**Title.** `[X-4] CI integration: GAP test suite on every push`

**Workstream.** X.

**Background.**
Continuous-integration infrastructure to run X-1, X-2, X-3 on every
push. Without CI the regression suite drifts; with CI the tier
pipelines are continuously validated.

**Goal.** A `.github/workflows/ci.yml` (or equivalent) running the
GAP regression suite against a pinned GAP + HAP environment.

**Acceptance criteria.**
- CI completes in $\le 30$ minutes.
- Failures block merges to the main branch.
- Documented environment: GAP version, HAP version, IO version
  (and `hapco` for `universal_coefficients.g`).

**Dependencies.** X-1, X-2, X-3.

**Estimated effort.** 2 days.

**Files likely affected.**
- New `.github/workflows/ci.yml`.
- `Makefile` or `run_tests.sh` driver.

**Out of scope.**
- Distributed CI (single-runner sufficient for current suite size).

**Status:** `blocked` on X-1, X-2, X-3. **Labels:** `regression`, `code`.

## 11. Workstream W — Writeup

### W-EPIC

**Title.** `[W-EPIC] Methodology paper / writeup synthesis`

**Body.**
Tracks workstream W. The "writeup" is `writeup.md` extended with
results from each $m$ stage; eventual conversion to a paper draft
via the W-1 issues.

**Status:** `in progress`. **Labels:** `epic`, `doc`.

### W-1a

**Title.** `[W-1a] Methodology paper outline + introduction draft`

**Workstream.** W.

**Goal.** Outline + introductory section of a methodology paper
covering: Keller's conjecture, the four-tier framework, the
trajectory-C plan, and the $E_+(m)$ application.

**Acceptance criteria.**
- 2-page outline mapped to writeup.md sections.
- 4-page introduction draft.

**Dependencies.** None.

**Estimated effort.** 1 week.

**Files likely affected.**
- New `paper/outline.md`, `paper/introduction.tex`.

**Status:** `ready`. **Labels:** `doc`.

### W-1b

**Title.** `[W-1b] Paper §3: cross-cutting infrastructure`

**Workstream.** W.

**Goal.** Section drafting the upgraded Tier-4 pipeline (T-1
through T-6), referencing implementation outcomes.

**Dependencies.** T-EPIC (closed).

**Estimated effort.** 1 week.

**Files likely affected.**
- `paper/section_3_infrastructure.tex`.

**Status:** `blocked` on T-EPIC. **Labels:** `doc`.

### W-1c

**Title.** `[W-1c] Paper §4: per-m applications`

**Workstream.** W.

**Goal.** Section drafting the $m = 2, 3, 5, 7$ application results,
including the decision-point branches.

**Dependencies.** A-EPIC (closed for the relevant $m$).

**Estimated effort.** 1–2 weeks.

**Files likely affected.**
- `paper/section_4_applications.tex`.

**Status:** `blocked` on A-EPIC. **Labels:** `doc`.

### W-1d

**Title.** `[W-1d] Paper §5: conclusions and open questions`

**Workstream.** W.

**Goal.** Closing section: settling/falsifying status of Keller for
each $m$, remaining open questions (e.g. $E_+(7)$ if HAP-Quillen
hybrid was needed), future directions.

**Dependencies.** W-1c.

**Estimated effort.** 1 week.

**Files likely affected.**
- `paper/section_5_conclusions.tex`.

**Status:** `blocked` on W-1c. **Labels:** `doc`.

### W-2

**Title.** `[W-2] Final results tables and figures`

**Workstream.** W.

**Goal.** Tables and figures summarising the per-$m$ outcomes
(kernel sizes, FS-indicator separations, Aut counts).

**Dependencies.** A-EPIC (closed).

**Estimated effort.** 3 days.

**Files likely affected.**
- `paper/figures/`, `paper/tables/`.

**Status:** `blocked` on A-EPIC. **Labels:** `doc`.

### W-3

**Title.** `[W-3] Reproducibility appendix`

**Workstream.** W.

**Goal.** Appendix giving exact commands to reproduce every result;
GAP / HAP version pin.

**Dependencies.** A-EPIC + X-EPIC (both closed).

**Estimated effort.** 2 days.

**Files likely affected.**
- `paper/appendix_reproducibility.tex`.

**Status:** `blocked` on A-EPIC + X-EPIC. **Labels:** `doc`.

## 12. Dependency graph (table)

Issue → upstream dependencies. Issues not listed have no upstream
dependencies and are `ready` immediately.

| Issue | Depends on |
|---|---|
| Q-2 | Q-1 |
| Q-3 | Q-1 |
| Q-4 | Q-1 |
| Q-5 | Q-2, Q-4 |
| Q-6 | Q-5 |
| Q-7 | Q-3, Q-6 |
| Q-8 | Q-7 |
| T-3b | T-3a |
| T-3c | T-3a |
| T-3d | T-2, T-3b, T-3c |
| T-5 | T-2 |
| T-6 | T-1, T-2, T-3d, T-4 |
| V-2 | V-1 |
| V-5b | V-5a |
| V-5c | V-5b |
| V-6 | V-5c, T-3c |
| V-7b | V-7a |
| K-2 | K-1 |
| K-3 | K-2, V-2 |
| A-2 | T-2 |
| A-3a | T-1, T-2, T-3d, T-4, T-5 |
| A-3b | A-3a |
| A-3c | A-3b, V-2, V-3 |
| A-3d | V-5c, V-7b |
| A-5a | A-3a |
| A-5b | A-5a (HAP succeeded branch) |
| A-5c | A-5a (HAP failed branch), Q-7 |
| A-5d | V-5c, V-7b, A-5b ∨ A-5c |
| A-7a | Q-7, T-* full stack |
| A-7b | A-7a, V-2, V-3 |
| X-1 | V-1, V-2, V-3, V-5c |
| X-2 | T-1, T-2, T-3d, T-4 |
| X-3 | T + V full stack |
| X-4 | X-1, X-2, X-3 |
| W-1b | T-EPIC |
| W-1c | A-EPIC |
| W-1d | W-1c |
| W-2 | A-EPIC |
| W-3 | A-EPIC, X-EPIC |

## 13. Decision points and dispatcher logic

Two preplanned decision points; both are explicit issues in
workstream A. **Both auto-dispatch the next stage based on a
deterministic predicate over the upstream artefact.** Human review
is not required at either point — the dispatchers run as soon as
their input is available, persist a verdict to disk, and trigger
the appropriate downstream issue label transition (`blocked` →
`ready`) automatically.

**DP-I (issue A-3b)** — triggered at end of A-3a.
- Predicate: `kernel = 0` ?
- Branch `yes` (kernel trivial): KRR + Tier-4 sufficient at $m = 3$.
  A-3c is closed as `not applicable`; A-3d unblocks for the Tier-3
  cross-validation; A-5a unblocks immediately on A-3d's start.
- Branch `no` (kernel non-trivial): A-3c unblocks (Tier-1/5
  elimination loop) in parallel with A-3d. A-5a unblocks once both
  A-3c and A-3d complete.

**DP-II (issue A-5a)** — triggered at end of `ResolutionFiniteGroup(E_+(5), 4)`.
- Predicate: did HAP complete within the heap budget?
- Branch `yes`: A-5b unblocks. A-5c is closed as `not applicable`.
  A-7a remains blocked on Q-7 (or Q-9) regardless of $m = 5$ route,
  since $m = 7$ always needs the analytical pipeline.
- Branch `no`: A-5c unblocks (assuming Q-7 has landed; otherwise
  A-5c remains `blocked` on Q-7 alone). A-5b is closed as `not applicable`.
  Workstream Q is escalated in priority to unblock A-5c and A-7a.

Both dispatchers persist their verdict to
`computed/transgression/<m>/dp_verdict.g` for traceability and
downstream consumers.

**When human review *is* requested.** The `requires user input`
label is reserved for genuine adjudication needs that the
dispatcher cannot resolve mechanically:

- A regression test (X-1, X-2, X-3) failing in a way that suggests
  a math-convention disagreement rather than a bug — the failing
  agent flips its issue to `requires user input` to invoke
  research-level adjudication.
- HAP-vs-Quillen torsion-vector disagreement at Q-8 — likewise.
- Final paper sign-off (W-1d) — reviewed at PR time, no special
  label needed.

In every other case, an agent picking up an issue may decide
conventions, write tests, and move forward unilaterally; conventions
are reviewed at PR time as part of normal code review.

## 14. Initial label assignments and recommended dispatch wave

**Wave 0 — `ready` from day 1, pickup in any order:**

| Issue | Workstream | Labels |
|---|---|---|
| Q-1 | Q | `ready`, `code`, `math` |
| Q-9 | Q | `ready`, `math`, `code` |
| T-1 | T | `ready`, `code`, `regression` |
| T-2 | T | `ready`, `code`, `regression` |
| T-3a | T | `ready`, `code`, `math` |
| T-4 | T | `ready`, `code` |
| V-1 | V | `ready`, `code`, `math` |
| V-3 | V | `ready`, `code`, `regression` |
| V-4 | V | `ready`, `code` |
| V-5a | V | `ready`, `code`, `math` |
| V-7a | V | `ready`, `code` |
| V-8 | V | `ready`, `code` |
| K-1 | K | `ready`, `code`, `math` |
| W-1a | W | `ready`, `doc` |

Wave 0 has 14 issues, all genuinely independent: 14 agents could
work in parallel from day 1 without colliding on the same files.

**Wave 1 — unblocked once Wave 0 starts landing:**

Q-2, Q-3, Q-4 (Wave 1a, after Q-1).
T-3b, T-3c, T-5, T-6 (Wave 1b, after T-2/T-3a).
V-2, V-5b, V-7b (Wave 1c, after V-1/V-5a/V-7a).
K-2 (after K-1).

Cumulative parallelism in Wave 1: ~12 additional issues runnable.

**Wave 2 — application sweeps as Wave 0/1 close:**

A-2 (after T-2): minimal issue, can run while T-3 stack is still in
flight.
A-3a + A-3b (after T-* full stack).
X-1, X-2 (regression as soon as relevant deps land).

**Wave 3 — decision-point-conditional and large-m work:**

A-3c, A-3d, A-5a, A-5b/c, A-5d, A-7a, A-7b.
W-1b, W-1c, W-1d.

**`requires user input` — reserved for genuine adjudication only.**
None of the trajectory's preplanned decision points carry this
label by default; both DP-I and DP-II auto-dispatch (§13). The
label is applied dynamically by an agent when it encounters one of:

- a regression failure suggesting a math-convention disagreement
  rather than a bug;
- HAP-vs-Quillen torsion-vector disagreement at Q-8;
- any test result whose interpretation is research-level rather
  than mechanical.

Convention choices (Q-1 signs, V-1 $\varepsilon$-formula
parameterisation, etc.) are made by the implementing agent,
documented in the issue PR, and reviewed during normal code
review — not paused on a `requires user input` label.

## 15. Status of this document

This document is the source of truth for issue creation. Once
approved, each leaf issue (Q-1 through W-3) maps to a single
GitHub issue created from its template; each `*-EPIC` maps to a
GitHub epic / tracking issue linking to its leaves. The dependency
table (§12) drives the initial label assignment; the dispatcher
logic (§13) is implemented in workstream A.

Updates and revisions:
- The structure may evolve as Wave 0 issues close and reveal
  unexpected coupling — particularly between Q (analytical) and T
  (HAP-native) routes if HAP-Quillen agreement at $m = 3$ is more
  delicate than anticipated.
- Decision-point outcomes may add or remove later issues; the
  dispatcher scripts will record the relevant deltas to this
  document for traceability.

### 15.1 Per-issue execution template

The canonical TDD template every agent should follow when picking
up an issue is recorded at
[`docs/superpowers/plans/2026-05-08-issue-T-1-tdd.md`](../docs/superpowers/plans/2026-05-08-issue-T-1-tdd.md).
Copy its structure (failing test → minimal impl → regression →
benchmark → close) and substitute your issue's specifics.

For doc-only issues (e.g. `W-1a`), skip the failing-test pattern
and structure the plan as outline → draft → revise → commit.

For math-heavy issues (the Q workstream in particular), include a
"verify against published reference" step before the implementation
step — Quillen [Qui71] for cohomology presentations,
Iovanov–Mason–Ng [IMN14] for FS-indicator formulas, etc.

### 15.2 Agent dispatch protocol

For each `ready`-labelled issue:

1. An agent claims it by adding the `in progress` label and
   removing `ready`, with a comment "Claimed by &lt;agent ID&gt;".
2. The agent works in a feature branch
   `&lt;workstream&gt;/&lt;issue-id&gt;-&lt;short-slug&gt;` (e.g.
   `T/T-1-hap-native-iscoboundary2`).
3. The agent follows the TDD template at
   `docs/superpowers/plans/2026-05-08-issue-T-1-tdd.md`.
4. On completion, the agent opens a PR closing the issue and
   triggers `scripts/dispatch/relabel_on_close.sh &lt;issue-id&gt;`
   to advance dependents.

The relabel hook is *not* automated by a GitHub Action at present;
the closing agent must invoke it manually after the PR merges.
Adding a `workflow_dispatch` action wrapper around it is a
nice-to-have but is deferred until at least one Wave-0 issue
closes and we observe whether the manual flow is sufficient.
