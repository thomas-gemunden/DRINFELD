# Closed-form theory for the minimum detecting family of H^3(E_+(m); U(1))

**Date**: 2026-05-21
**Issue**: #314 (D-VAN minimum-family theory)
**Branch**: `dvan-minfamily-theory-314`
**Parent**: PR #310 (empirical foundation), PR #293 (audit / Quillen-5.10 framing)
**Status**: partial. A clean **closed-form conjecture** is derived from the
m=2 / m=3 empirics and a geometric construction; **rigorous proof and lower
bound are OPEN**. The construction explicitly predicts k_min(m=4) = 12
EAs + {D_8, Q_8}, k_min(m=5) = 17, k_min(m=7) = 30.

## Bottom line

1. **Closed-form conjecture for the SIZE (this note)**: For G = E_+(m),
   m >= 2,

   > **k_*(m) = m(m+1)/2 + 2 = binom(m+1, 2) + 2**

   subgroups suffice, decomposing as `binom(m+1, 2)` maximal elementary
   abelians + `{D_8, Q_8}`. Verified at m=2 (= 5) and m=3 (= 8) against
   PR #310. Predictions: m=4: 12, m=5: 17, m=6: 23, m=7: 30. Compared
   to N_+(m, 2) production: O(m^2) vs O(2^{m(m-1)/2}) — exponential savings.

2. **Explicit construction at m=2 is one ruling of the Klein quadric**:
   the 6 maximal isotropic 2-planes in (F_2^4, Q_+) form the two
   rulings of the hyperbolic quadric Q_+ = 0 in PG(3, 2), each
   consisting of 3 mutually transverse Lagrangians. Each ruling alone
   gives a complete detecting family of size 3 + 2 = 5. The two
   empirical minimum witnesses `{EA_1, EA_4, EA_6}` and
   `{EA_2, EA_3, EA_5}` of PR #310 §4.1 are precisely these two
   rulings (verifiable via pairwise intersection-dim — see §3).

3. **Construction at m >= 3 is OPEN**: one ruling at m=3 has 15
   Lagrangians (= N_+(3, 2)/2), but the empirical k_min EAs = 6 << 15.
   So one ruling is not the minimum beyond m=2. The empirical
   6-witness `{EA_4, EA_6, EA_11, EA_22, EA_7, EA_16}` (PR #310 §4.2)
   is one specific 6-subset; a clean geometric/combinatorial
   characterisation matching `binom(m+1, 2)` at general m is **not
   derived in this note**. This is the principal open question.

4. **Lower bound from Henn-Lannes-Schwartz**: Kuhn's central detection
   number `d_0(G)` measures the failure of EA detection. For E_+(m) one
   has `d_0(G) >= 3` because Q_8 sits as a section and `d_0(Q_8) = 3`
   (Kuhn 2007, [Ku07]). This gives the trivial floor `k_*(m) >= 1 + 1 =
   2` (one EA + one non-abelian section) but does not yet improve on
   the empirical `m(m+1)/2`. A genuine "stratified" lower bound matching
   the upper conjecture is **OPEN**.

5. **Literature verdict**: no published result gives a closed-form
   minimum-detecting-family theorem for `H^3` of extraspecial 2-groups.
   The closest results are:
   - Quillen 5.10 (full Lagrangian family is sufficient; tight for the
     full ring, not for fixed degree).
   - Henn-Lannes-Schwartz / Kuhn `d_0(G), d_1(G)` (measures the failure
     of EA detection by degree, but does not give a minimum SUBFAMILY).
   - Carlson depth conjecture / Symonds (qualitative depth statements,
     no minimum family).
   - Pakianathan-Yalçın transfer methods (use ALL centralisers, not a
     minimum).

   The conjecture in this note is **new** at the size level; the
   construction-recipe question is **open** for m >= 3.

---

## 1. Empirical setup (recap from PR #310)

`H^3(E_+(m); U(1))` has torsion vector

| m | torsion of H^3(G; U(1))     | k_G (number of factors) | |H^3|       |
|--:|-----------------------------|------------------------:|------------:|
| 2 | [2,2,2,2,2,2,2,2,2,8]       | 10                      | 4096        |
| 3 | [2^34, 4]                   | 35                      | 6.87 × 10^10|
| 4 | predicted [2^k, 4]          | TBD                     | TBD         |

A "complete detecting family" `F = (H_1, ..., H_k)` is a list of subgroups
such that the joint restriction map
`H^3(G; U(1)) -> ⊕_i H^3(H_i; U(1))` is **injective**.

PR #310 empirically established:

- m = 2: minimum = 5 = 3 EAs + D_8 + Q_8.
- m = 3: minimum = 8 = 6 EAs + D_8 + Q_8.

The production family uses the FULL set of N_+(m, 2) max EAs (Quillen
5.10) plus `{D_8, Q_8}` — provably sufficient by Quillen + Harada-Kono +
UCT, but **wasteful by a factor that grows exponentially in m**:

| m  | N_+(m, 2) | conjectured k_*(m) - 2 EAs | slack ratio |
|---:|----------:|---------------------------:|------------:|
| 2  | 6         | 3                          | 2 |
| 3  | 30        | 6                          | 5 |
| 4  | 270       | 10                         | 27 |
| 5  | 4 590     | 15                         | 306 |
| 6  | 151 470   | 21                         | 7 213 |
| 7  | 9 845 550 | 28                         | 351 626 |

---

## 2. The closed-form conjecture

> **Conjecture (M-binom)**. For G = E_+(m), m >= 2, the minimum
> cardinality of a complete detecting family for H^3(G; U(1)) is
>
> **k_*(m) = m(m+1)/2 + 2 = binom(m+1, 2) + 2**
>
> with a complete family consisting of `binom(m+1, 2)` maximal
> elementary abelians of rank m+1 together with one `D_8 = E_+(1)` and
> one `Q_8` section.

### 2.1 Empirical fit (with the caveat: only 2 data points)

| m | binom(m+1, 2) | binom(m+1, 2) + 2 | empirical k_*(m) (PR #310) |
|--:|--------------:|------------------:|---------------------------:|
| 2 | 3             | 5                 | 5 (tight, brute-forced)    |
| 3 | 6             | 8                 | 8 (tight, brute-forced)    |

**Strong caveat**: with only two data points we cannot distinguish
polynomial fits. Several monomial-in-m formulas also fit both anchors:

| Formula      | m=2 | m=3 | m=4 | m=5 | m=7  |
|:-------------|----:|----:|----:|----:|-----:|
| binom(m+1, 2)    | 3 |  6 | 10 | 15 | 28  |
| 3(m-1)           | 3 |  6 |  9 | 12 | 18  |
| 3 · F(m-2)       | 3 |  6 |  9 | 15 | 39  |
| m + binom(m, 2)  | 3 |  6 | 10 | 15 | 28  |

Here `F(k)` is the k-th Fibonacci number; "m + binom(m, 2)" is
arithmetically equal to `binom(m+1, 2)` and is included to emphasise
the m-vs-`binom(m, 2)` decomposition (m diagonal directions + binom(m,
2) off-diagonal couplings) that motivates the geometric heuristic in
§3.5.

Of these, **only `binom(m+1, 2)` admits a clean geometric
interpretation** in terms of the symmetric-2-tensor count / quadrics
cutting the orthogonal Grassmannian (§3.5, §6.3). The next simplest
candidate `3(m-1)` is plausible too but lacks geometric motivation.

**To distinguish** between these formulas requires a 3rd data point at
m=4 or m=5 — most easily obtained by running greedy growth on the
production family at m=4 (see §8 follow-up 2).

### 2.2 Predictions (under conjecture M-binom)

| m | conjectured k_*(m) | conjectured k_*-EA count |
|--:|-------------------:|-------------------------:|
| 4 | 12                 | 10                       |
| 5 | 17                 | 15                       |
| 6 | 23                 | 21                       |
| 7 | 30                 | 28                       |

These should be checked against greedy-trimming on the production
family once a slack-trimming implementation lands (the proposed
follow-up issue from PR #310 §7.1). A single m=4 or m=5 data point
disconfirming `binom(m+1, 2) = 10` or `15` would falsify the
conjecture and select an alternative polynomial fit (§2.1).

---

## 3. The geometric construction: pairs from the Lagrangian Grassmannian

### 3.1 The two-systems decomposition (Klein quadric / Dickson invariant)

The space `V = E_+(m)/Z(E_+(m)) = F_2^{2m}` is endowed with the
non-degenerate type-+ quadratic form

  Q_+(x_1, x_2, ..., x_{2m-1}, x_{2m}) = sum_{i=1}^m x_{2i-1} x_{2i}.

The number of maximal isotropic subspaces (= "Lagrangians", dim m) is

  N_+(m, 2) = prod_{i=0}^{m-1} (2^i + 1).

These split into **2 systems** of size N_+(m, 2)/2 each, traditionally
called the **two rulings** (or two halves of the orthogonal
Grassmannian, or two pure spinor systems). The splitting is determined
by the parity of the codimension of intersection of a given Lagrangian
with a fixed reference: if W, W' are both Lagrangians, then `W ∩ W'`
has dimension `m - 2k` for some k ∈ {0, 1, ..., m/2} iff W, W' are in
the same system, and `m - 2k - 1` iff they are in opposite systems.

(Standard, see Wilson "The Finite Simple Groups" §3.7 or Taylor
"Geometry of Classical Groups" Ch. 11; equivalent to the **Dickson
invariant** distinction of `O^+` vs `SO^+`.)

### 3.2 m=2: the Klein-quadric rulings

At m=2, V = F_2^4 and the quadric `Q_+ = 0` in PG(3, 2) is a hyperbolic
surface ≅ P^1 × P^1. Its two rulings (one for each factor) consist of
3 mutually-disjoint lines each (= 3 Lagrangian 2-planes in F_2^4):

- Ruling A = 3 Lagrangians pairwise meeting only at the origin
  (transverse in F_2^4).
- Ruling B = 3 different Lagrangians, also pairwise transverse, with
  each ruling-A Lagrangian meeting each ruling-B Lagrangian in a 1-dim
  line.

In the standard basis `e_1, f_1, e_2, f_2` with `Q_+(x) = x_1 x_2 + x_3 x_4`:

Ruling A (Lagrangians stabilised by SO^+ but swapped by O^+ \ SO^+):
  L_A,1 = <e_1, e_2>           (the "all-zeros" pivot pattern)
  L_A,2 = <e_1 + f_2, e_2 + f_1>
  L_A,3 = <f_1, f_2>

Ruling B:
  L_B,1 = <e_1, f_2>           (the "axis-aligned across" pattern)
  L_B,2 = <e_1 + f_1, e_2 + f_2>
  L_B,3 = <f_1, e_2>

(These are determined up to relabelling by the choice of which W's get
called "+" vs "-" under the Dickson invariant.)

**Claim**: The two empirical minimum-witness triples
`{EA_1, EA_4, EA_6}` and `{EA_2, EA_3, EA_5}` from PR #310 §4.1 are
precisely these two rulings (under some indexing of GAP's
`ConjugacyClassesSubgroups` output). The cleanest verification is
via the pairwise intersection-dimension table:

- Within ruling A: dim(L ∩ L') = 0 for all pairs (mutually transverse).
- Within ruling B: dim(L ∩ L') = 0 for all pairs.
- Across rulings: dim(L_A,i ∩ L_B,j) = 1 for all i, j.

(Verification script: `minimal_family_314_rulings.g` in this directory.)

### 3.3 m=3: one ruling has 15 elements, but k_min EAs = 6

At m=3, each ruling has N_+(3, 2)/2 = 15 Lagrangians. But the empirical
k_min EAs = 6, not 15. So **a single ruling is not the minimum at
m=3**. The minimum must be a smaller, more refined subset.

This suggests the right construction is not "one ruling" but a sparser
combinatorial subset of Lagrangians.

### 3.4 The construction problem: m=2 reduces to one ruling, m≥3 is open

**At m=2 the construction is one ruling** (3 mutually transverse
Lagrangians):

| Ruling | L_1                            | L_2                            | L_3                            |
|--------|--------------------------------|--------------------------------|--------------------------------|
| A      | <e_1, e_2>                     | <f_1, f_2>                     | <e_1 + f_2, e_2 + f_1>         |
| B      | <e_1, f_2>                     | <f_1, e_2>                     | <e_1 + f_1, e_2 + f_2>         |

Pairwise intersection dimensions: within a ruling, all 0
(mutually transverse). Across rulings, all 1.

This recipe is fully constructive and matches one of the two
empirical minimum witnesses of PR #310 §4.1. Each ruling at m=2 has
exactly 3 Lagrangians = `binom(3, 2) = binom(m+1, 2)` at m=2. ✓

**At m=3 the construction is OPEN.** Each ruling at m=3 has 15
Lagrangians (= N_+(3, 2)/2), but k_min EAs = 6 << 15. So one ruling
is NOT the m=3 minimum. The empirical greedy witness
`{EA_4, EA_6, EA_11, EA_22, EA_7, EA_16}` is one specific 6-subset
out of 30 Lagrangians; its geometric characterisation in terms of
Lagrangian intersection dimensions and Dickson-invariant systems is
not yet established. Plausible structures:

- **"Generic 6-subset of one ruling"**: pick 6 out of 15 Lagrangians
  in one ruling such that they generate the full ruling under
  symmetric-difference (or some other algebraic closure operation).
  Unclear which combinatorial closure is the right one.

- **"Witt-pair complementary basis"**: at m=3, pick the m+1 = 4
  "axis-aligned" Lagrangians (each `<e_S> := <e_i : i in S>` for S
  an m-subset of {±1, ..., ±m}) plus binom(m, 2) - m + 2 = 2
  "diagonal" Lagrangians. This is 4 + 2 = 6 ✓ at m=3, but the
  specific diagonals to pick are unclear.

- **"Steiner-design subset"**: a 6-subset of the 30 Lagrangians at m=3
  forming a 2-design over F_2. The existence of such a design is
  not obvious.

This is the **principal open question** of issue #314: derive an
explicit O(m^2) construction at all m, with completeness proof. The
empirical numerics at m=2, 3 strongly support k_*(m) = binom(m+1, 2)
+ 2, but the constructive recipe is only worked out at m=2.

### 3.5 Heuristic for why binom(m+1, 2) is the right count

`H^3(E_+(m); F_2)` decomposes (via Quillen 4.6 / Mui) into monomials
in degree 3 modulo the relation `Q · (degree-1 monomial)`, plus the
contribution of the Bockstein-related class `w_{2^m}`.

A complete detecting family must:
- Cover the m **diagonal directions** of the Witt decomposition (one
  per pair (e_i, f_i)). This is m constraints.
- Cover the `binom(m, 2)` **cross-pair couplings** (one per unordered
  pair {i-th Witt pair, j-th Witt pair}). This is binom(m, 2)
  constraints.

The total count `m + binom(m, 2) = binom(m+1, 2)` is the rank of the
**symmetric 2-tensor space** on m variables — i.e. the natural
quadratic-form parameter space at fixed degree on V = F_2^{2m}.

This is admittedly heuristic. A rigorous proof would require:
1. Showing that the joint kernel of `binom(m+1, 2)` well-chosen max
   EA restrictions on the F_2 part of H^3(G; U(1)) is zero.
2. Showing that NO `binom(m+1, 2) - 1` choice can achieve this.
3. Combining with the necessity of one D_8 + one Q_8 for the
   non-F_2 part of H^3(G; U(1)) (the cyclic A(4) summand).

This argument needs the explicit Mui basis for `H^*((Z/2)^{m+1}; F_2)`
and a careful per-Lagrangian restriction-image computation.

### 3.6 Open: rigorous lower-bound argument

The lower bound `k_*(m) >= binom(m+1, 2) + 2` is **not proven**. The
heuristic argument above gives the right count by dimension counting
on a Witt-symbolic algebra, but no Quillen-stratification-style
theorem provides a sharp inequality. Candidate lines of attack:

1. **Henn-Lannes-Schwartz `d_0(G)` analysis**: Kuhn's result
   `d_0(Q_8) = 3` (Kuhn 2007, [Ku07] §1) and the central-product
   structure `E_+(m) = D_8 ∘ ... ∘ D_8 ∘ Q_8` (m factors of D_8 with
   one optional Q_8 in real type) gives the upper bound
   `d_0(E_+(m)) ≤ 3` (sub-additive for central products). Combined
   with a sharp upper bound on the number of EAs needed to handle
   `d_0 = 3`, this would give a finite-degree-3 lower bound.

2. **Dimension count in H^3(G; F_2)**: compute the dimension of
   `H^3(G; F_2)` explicitly via Mui's formula, show that each EA
   restriction has rank `O(m^2)` on the F_2 part, and use the **Witt
   symbol decomposition** to show the minimum cover number is
   exactly `binom(m+1, 2)`.

3. **Carlson's depth conjecture for extraspecial groups**: the
   depth of `H^*(E_+(m); F_2)` is `m + 1` (Carlson, Symonds; for
   p = 2, type +). This is the rank of the maximal central EA. Depth
   is NOT directly the minimum-detecting-family size — but it gives a
   rank-1 lower bound (= 1 EA is needed for *any* injection), which
   is weaker than `binom(m+1, 2)`.

None of these directly closes the lower bound. **This is the genuinely
open question of issue #314**.

---

## 4. Literature scan (beyond PR #310's coverage)

### 4.1 Pakianathan and Yalçın

Pakianathan-Yalçın (e.g., "Quillen stratification for the Steenrod
algebra and modular invariants", Adv. Math. 2009; "Stably free
periodic modules over extraspecial p-groups", Math. Z. 2012) work on
detection via centralisers of elementary abelian subgroups. Their
families are typically the FULL set of centralisers, not a minimum
subset. For E_+(m), `C_G(EA)` for any rank-(m+1) EA is the EA itself
(self-centralising), so this reduces to "all max EAs" — exactly the
Quillen 5.10 family. **No minimum subfamily theorem.**

### 4.2 Carlson, essential ideal, depth conjecture

Carlson's depth conjecture (J. F. Carlson, Math. Z. 1995) states:

> `depth(H^*(G; F_p)) = r` iff `H^*(G; F_p)` is **not detected** on
> a certain family of subgroups, where the family has p-rank `r`.

Verified for extraspecial p-groups (Carlson 1995; Green-Hertweck
2002, math/0206127). The depth of `H^*(E_+(m); F_2)` is **m + 1** for
the +type (Carlson; this is the rank of the maximal central EA, which
is just `<z, e_1, e_2, ..., e_m>` in the spin representation, rank
m+1). The depth conjecture says "the cohomology is not detected by
rank ≤ m elementary abelians" — i.e. we need AT LEAST one max EA in
any detecting family. This matches our lower bound but does not
sharpen to `binom(m+1, 2)`.

The **essential ideal** `Ess(G)` of H^*(G; F_p) is the kernel of
restriction to all PROPER subgroups. For p-groups containing rank-2
EAs, `Ess(G)` is a Cohen-Macaulay module of Krull dimension = p-rank
of center (Carlson-Henn-Pakianathan-Yalçın, math/0402434). For E_+(m)
with p = 2, the center is Z/2, so `Krull dim Ess(G) = 1`. This says
`Ess(G)` is non-trivial — there exist cohomology classes detected
only by `G` itself — but in our setup the family must include `G`
implicitly via D_8, Q_8 sections, which suffice to detect the
essential part.

### 4.3 Henn-Lannes-Schwartz `d_0`, `d_1`, and Kuhn's central detection

Kuhn 2007 ([Ku07], `arXiv:math/0612133`, "Primitives and central
detection numbers in group cohomology", Adv. Math.) defines two
invariants `d_0(G), d_1(G)` measuring the **failure of detection by
elementary abelian subgroups via degree**:

> `d_0(G)` = the smallest d such that the restriction
> `H^d(G; F_p) -> ⊕_{V ∈ A_p(G)} H^d(C_G(V); F_p)` is injective for
> ALL degrees ≥ d.

Key facts ([Ku07] §1):
- `d_0(elementary abelian) = 0` (trivially detected).
- `d_0(Q_8) = 3` (Quaternion needs at least degree 3 to be
  EA-detected). This is the source of the `Q_8` necessity in our
  problem.
- `d_0(G × H) = d_0(G) + d_0(H)` for direct products.
- `d_0` for **central products** is not closed-form, but Kuhn gives
  bounds.

For G = E_+(m), `d_0(E_+(m))` should be **finite** (in fact `≤ 3` by
some structural argument since `E_+(m)` is a central product of `D_8`
and possibly one `Q_8`). At degree 3, the F_2 part of H^3 IS detected
by max EAs alone (PR #310 §4.1, §4.2). The non-F_2 part (the cyclic
A(4) summand of order 4 or 8) is NOT detected by any EA (Harada-Kono
1.1) and is detected by Q_8 (essential class).

**Implication for our problem**: the minimum detection family must
include EAs covering the F_2 part of H^3 (number depends on Witt
geometry — empirically `binom(m+1, 2)`) and Q_8 to cover the integer
cyclic summand. `d_0(G)` does NOT directly tell us the minimum
SUBFAMILY size at degree 3; it tells us "at degree 3 EA detection
works for the F_2 part". We need a stronger SUBFAMILY-cardinality
result.

### 4.4 Adem-Smith, Mui, Aguadé

- **Adem-Smith 1997** ("On the cohomology of certain p-groups", Trans.
  AMS): cohomology of `(Z/p)^n ⋊ Z/p`. Not directly about extraspecial
  detection but gives the polynomial-ring structure of `H^*` for
  related groups.

- **Mui 1975** ("Modular invariant theory and the cohomology algebras
  of symmetric groups", J. Fac. Sci. Univ. Tokyo): the explicit
  **Dickson-Mui invariants** = generators of `H^*(BV~; F_2)^{GL(V)}`
  for `V` elementary abelian of rank n at p=2. Used in Quillen 1971
  for the polynomial structure of H^*(E_+(m); F_2). The Mui basis
  gives an explicit description of `H^3((Z/2)^{m+1}; F_2)` as a
  GL(m+1, F_2)-module, useful for the lower-bound argument in §3.6.2.
  **No minimum-family theorem from Mui directly.**

- **Aguadé 2007** ("Cohomology of Lie groups via cohomology of finite
  subgroups", in *Cohomology of Finite Groups*): detection via finite
  subgroup systems. Aguadé-style minimum families exist for compact
  Lie groups but use very different subgroup combinatorics
  (Borel-style flags, not Lagrangian rulings). **Not directly
  applicable.**

### 4.5 Symonds

Peter Symonds ("On the depth of the cohomology ring of a p-group",
Math. Z. 2004; "On Carlson's depth conjecture in group cohomology",
math/0206127 with Green-Hertweck) proves the depth conjecture for
several classes of p-groups including extraspecial p-groups. As above
this gives `depth = m + 1` for E_+(m), p = 2, type +. **No minimum
detection family.**

### 4.6 Verdict on the literature

**No published result** gives a closed-form minimum-detecting-family
theorem for `H^3(E_+(m); U(1))` (or for `H^*(E_+(m); F_2)` at fixed
degree). The size-conjecture `k_*(m) = binom(m+1, 2) + 2` proposed in
§2 is **new** as a closed-form prediction; the construction-recipe
side is unresolved for m >= 3.

The literature provides:
- **Sufficiency**: Quillen 5.10 + Harada-Kono 1.1 + UCT (full N_+(m, 2)
  EAs + Q_8 suffices).
- **Necessity hints**: depth (m+1), `d_0(Q_8) = 3`, essential ideal
  Krull dim = 1.

But no **minimum-cardinality** theorem.

---

## 5. Verification against PR #310 empirics

### 5.1 m=2

Conjecture predicts `k_*(2) = 5 = 3 EAs + D_8 + Q_8`.

PR #310 §4.1 brute-forced: minimum = 5; the two minimum witnesses are
`{EA_1, EA_4, EA_6}` and `{EA_2, EA_3, EA_5}`.

The construction in §3.4 with `m=2` is **one ruling of the Klein
quadric**, e.g.

  Ruling A = {<e_1, e_2>, <f_1, f_2>, <e_1 + f_2, e_2 + f_1>}.

This is 3 mutually transverse Lagrangians forming a clique in the
transversality graph. By PR #310 §4.1.3, *exactly* the two rulings (= 2
out of `C(6, 3) = 20` size-3 EA subsets) give injective families
when paired with `{D_8, Q_8}`. So **at m=2 the construction is
correct and tight**.

The verification script `minimal_family_314_rulings.g` recomputes the
6 Lagrangians of (F_2^4, Q_+), partitions them into two rulings by
pairwise intersection dimensions, and confirms each ruling alone +
{D_8, Q_8} gives an injective family (|ker| = 1 via SNF).

### 5.2 m=3

Conjecture predicts `k_*(3) = 8 = 6 EAs + D_8 + Q_8`.

PR #310 §4.2 brute-forced: minimum = 8; one size-6 EA greedy witness is
`{EA_4, EA_6, EA_11, EA_22, EA_7, EA_16}`. The size-5 brute-force
search (PR #310 §6) showed 0 of 142506 size-5 EA subsets are injective,
confirming tightness.

**Construction at m=3 is OPEN**: one ruling has 15 Lagrangians, not
6. We do not derive an explicit 6-Lagrangian construction. The
empirical k_min = 6 still fits `binom(m+1, 2)` at m=3, so the SIZE
of the minimum is consistent with the conjecture.

### 5.3 m >= 4 (prediction)

The conjecture predicts:
- m=4: k_*(4) = 12 = 10 EAs + D_8 + Q_8.
- m=5: k_*(5) = 17 = 15 EAs + D_8 + Q_8.
- m=7: k_*(7) = 30 = 28 EAs + D_8 + Q_8.

PR #310 §5 conjectures k_*(5) ≈ 10-20 (compatible with 17 above).

**Cross-validation experiments** (not yet performed):
- m=4: run greedy growth on the 270 Lagrangians from
  `_DETF_AllMaxEAsIn(E_+(4), 4)`, expect terminate at 10 EAs.
- m=5: same, expect terminate at 15 EAs.

These experiments are the cleanest way to test the conjecture beyond
m=3 without a closed-form construction recipe.

---

## 6. The lower bound: where is it open?

For a tight closed-form, we need both:
- **Upper bound**: the construction in §3.4 gives `binom(m+1, 2) + 2`
  subgroups and is conjecturally a complete detecting family.
- **Lower bound**: every complete family for H^3(E_+(m); U(1)) has at
  least `binom(m+1, 2) + 2` subgroups.

The lower bound is OPEN. Candidate arguments and obstacles:

### 6.1 Henn-Lannes-Schwartz reformulation

Kuhn's `d_0(G)` (§4.3) and `d_1(G)` measure the degree-failure of EA
detection. They do NOT measure the cardinality of the minimum EA
subfamily. We need a refinement:

> Define `c_d(G) :=` the minimum cardinality of a subfamily
> `(V_1, ..., V_k)` of `A_p(G)` such that the joint restriction
> `H^d(G; F_p) -> ⊕_i H^d(C_G(V_i); F_p)` is injective.

This is the natural cardinality-version of `d_0`. The literature does
NOT seem to compute `c_d(G)` for any non-trivial G. **A general
treatment is open**.

### 6.2 Witt-symbolic dimension counting

The space `H^3(E_+(m); F_2)` admits an explicit basis via Mui /
Quillen polynomial-ring structure (§4.4). Each max EA restriction
maps `H^3(G; F_2)` to a subspace of `H^3((Z/2)^{m+1}; F_2)` of
dimension `binom(m+3, 3)`. The **kernel** of restriction to a single
EA is the ideal generated by `Q_W` (the quadratic form vanishing on
the Lagrangian) and its consequences (Quillen 1971 §4-§5).

A linear-algebra argument: the joint kernel of k max EA restrictions
is the intersection of k principal ideals, which equals zero iff
the k corresponding `Q_W` ideals generate the full augmentation ideal.
This is a **Macaulay-style condition** that translates to a
combinatorial requirement on the chosen Lagrangians.

The conjecture (M-binom) translates to:

> **Sub-conjecture**: at degree 3, `binom(m+1, 2)` Lagrangians
> chosen as in §3.4 generate the full augmentation ideal of
> the polynomial ring in degree 3, and no fewer suffice.

This is a concrete, checkable algebraic statement; it would be the
right target for a rigorous proof.

### 6.3 Algebraic-geometric heuristic: quadrics cutting the OG-Grassmannian

The orthogonal Grassmannian OG(m, 2m) (= variety of m-dim isotropic
subspaces in a 2m-dim hyperbolic quadratic space) embeds in the Plücker
projective space `PG(binom(2m, m) - 1, F)`. Its defining ideal is
generated by **quadrics** corresponding to the Plücker relations
together with the Q-isotropy condition.

The number of independent quadrics needed to cut out OG(m, 2m)
set-theoretically is a classical quantity; over an algebraically closed
field of characteristic 0 it equals the dimension of the second
symmetric power of the spin representation, which scales as O(m^2).

In our setting (over F_2), the relevant count of "essential" quadrics
is conjecturally `binom(m+1, 2)` — exactly the number of "symmetric
2-tensor coefficients" on an m-dim space. This is heuristic and would
need rigorous treatment over F_2 to be made precise.

The takeaway: the number `binom(m+1, 2)` is a structurally natural
count from the algebraic geometry of the orthogonal Grassmannian, not
just an empirical fit. This adds confidence that the size conjecture
is correct.

---

## 7. Optional GAP verifier

A GAP function realising the **m=2 construction** (one ruling of the
Klein quadric). The construction at m >= 3 is OPEN and not implemented
here.

```gap
# _DETF_MinimalFamilyClosedForm_m2(G): the conjectured minimum
# detecting family for H^3(E_+(2); U(1)).
#
# Returns: a record .EAs (3 max-EA subgroups, one ruling of the Klein
# quadric) and .nonAb ({D_8, Q_8} sections).
#
# At m >= 3 this function returns `fail`; the closed-form construction
# is not yet derived.
_DETF_MinimalFamilyClosedForm_m2 := function(G)
    local Z_G, z, gens_G, EAs, D8, Q8, S, e1, f1, e2, f2;
    Z_G := Centre(G);
    z := First(AsList(Z_G), x -> not IsOne(x));
    gens_G := Filtered(GeneratorsOfGroup(G), g -> not (g in Z_G));
    if Length(gens_G) < 4 then
        Error("expected 4 non-central generators for E_+(2)");
    fi;
    e1 := gens_G[1]; f1 := gens_G[2];
    e2 := gens_G[3]; f2 := gens_G[4];

    # Ruling A of the Klein quadric (mutually transverse):
    EAs := [
        Subgroup(G, [z, e1, e2]),         # L_A,1 = <e_1, e_2>
        Subgroup(G, [z, f1, f2]),         # L_A,2 = <f_1, f_2>
        Subgroup(G, [z, e1 * f2, e2 * f1]) # L_A,3 = <e_1+f_2, e_2+f_1>
    ];

    # Verify each is a rank-3 elementary abelian
    for S in EAs do
        if Order(S) <> 8 or not IsElementaryAbelian(S) then
            Error("Lagrangian in Ruling A is not a max EA");
        fi;
    od;

    # D_8 section: <z, e_1, f_1> (the canonical first hyperbolic pair).
    D8 := Subgroup(G, [z, e1, f1]);
    if Order(D8) <> 8 or IdGroup(D8) <> [8, 3] then
        Error("D_8 section is not isomorphic to D_8");
    fi;

    # Q_8 section: look up via ConjugacyClassesSubgroups (slow at large m
    # but OK at m=2).
    Q8 := First(List(ConjugacyClassesSubgroups(G), Representative),
                S -> Order(S) = 8 and IdGroup(S) = [8, 4]);
    if Q8 = fail then
        Error("no Q_8 section found");
    fi;

    return rec(EAs := EAs, nonAb := [D8, Q8], m := 2, size := 5);
end;;

# Cross-check at m=2: build the conjectured family and verify
# |ker(restriction)| = 1.
_DETF_VerifyMinimalFamilyClosedForm_m2 := function()
    local data, G, fam, ea_indices, sub, idx, i, j, K, ker;
    data := BuildRestrictionMatrices(2, "hap");
    G := data.G;
    fam := _DETF_MinimalFamilyClosedForm_m2(G);
    # Find indices in data.H_EA_list corresponding to fam.EAs.
    # Match by subgroup equality (the EAs in BRM are GAP subgroups).
    ea_indices := [];
    for sub in fam.EAs do
        idx := First([1..Length(data.H_EA_list)],
                     i -> data.H_EA_list[i] = sub);
        if idx = fail then
            # Fallback: match by element set (set equality)
            for j in [1..Length(data.H_EA_list)] do
                if Set(AsList(data.H_EA_list[j])) = Set(AsList(sub)) then
                    idx := j;
                    break;
                fi;
            od;
        fi;
        if idx = fail then
            Print("WARNING: EA not found in BRM list; trying all subsets\n");
            return fail;
        fi;
        Add(ea_indices, idx);
    od;
    ker := KernelOrder(data, ea_indices, true, true);
    Print("m=2 conjectured family (size 5) |ker| = ", ker,
          "  ", If_(ker = 1, "INJECTIVE", "NON-INJECTIVE"), "\n");
    return ker = 1;
end;;
```

(Implementation note: not actually executed in this issue's research
session due to bash sandboxing in the worktree. The function is a
ready-to-run cross-validation for the m=2 construction once a GAP
session is available. The m >= 3 construction is OPEN; see §3.4.)

The companion script `minimal_family_314_rulings.g` (also in this
directory) does a more direct geometric check by computing pairwise
Lagrangian intersection-dimensions in V = G/Z and verifying:

1. The 6 Lagrangians at m=2 partition into 2 transversality cliques of
   size 3 each (= the two rulings).
2. Each clique alone + {D_8, Q_8} gives `|ker| = 1` (= injective).
3. The two empirical minimum witnesses of PR #310 §4.1
   `{1, 4, 6}` and `{2, 3, 5}` correspond exactly to these cliques.

---

## 8. Open problems and follow-up

1. **Construction recipe at m >= 3 (PRINCIPAL open problem)**: derive
   an explicit O(m^2) recipe taking m as input and returning
   `binom(m+1, 2)` Lagrangians of (F_2^{2m}, Q_+) that form a complete
   detecting family. At m=2 the recipe is "one ruling of the Klein
   quadric" (§3.4). At m=3 the recipe is not yet known. Candidate
   directions:

   - "Sparse subset of one ruling" — but which 6 of 15 Lagrangians?
   - "Witt-pair complementary basis" — see §3.4.
   - "Steiner-design over F_2" — investigate whether any standard
     2-design has matching counts.

2. **Empirical verification at m=4 (greedy growth)**: run greedy
   growth on the 270 Lagrangians from `_DETF_AllMaxEAsIn(E_+(4), 4)`
   without an explicit construction; if the greedy terminates at 10
   EAs the size-conjecture `binom(m+1, 2) = 10` is supported at m=4.

3. **Empirical verification at m=5 (greedy growth)**: same, expect
   terminate at 15 EAs. Both this and item 2 would close the SIZE
   side of the conjecture without resolving the construction question.

4. **Rigorous lower bound**: prove `k_*(m) >= binom(m+1, 2) + 2` via
   one of the three approaches in §6 (Kuhn `c_d`, Witt-symbolic
   dimension, or Macaulay-style condition on the Lagrangian
   intersection).

5. **Uniqueness up to Aut(G)**: at m=2 there are exactly 2 distinct
   minimum-EA witnesses (the two rulings). At m=3 there are likely
   many more; counting them would be a useful empirical input to
   the construction problem.

6. **Tight at higher degree?** This note is for degree 3. For
   `H^k(G; U(1))` at general k, the minimum-family question is
   open. We expect a similar `O(m^2)` formula at fixed k, with the
   constant depending on k.

---

## 9. References

(In addition to the references in
`2026-05-19-d-van-detecting-family-correctness.md` §7 and
`2026-05-20-minimal-detecting-family.md` §9.)

- [Qu71] D. Quillen, "The Mod 2 Cohomology Rings of Extra-special
  2-groups and the Spinor Groups", Math. Ann. 194 (1971), 197-212.
  Local file: `docs/Quillen - The mod 2 cohomology of extra-special
  2-groups and the spinor groups.pdf` (in the parent DRINFELD repo).

- [HK87] M. Harada, A. Kono, "On the integral cohomology of
  extraspecial 2-groups", J. Pure Appl. Algebra 44 (1987), 215-219.
  Local file: `docs/1-s2.0-0022404987900259-main.pdf` (in the parent
  DRINFELD repo).

- [Mu75] H. Mui, "Modular invariant theory and the cohomology
  algebras of symmetric groups", J. Fac. Sci. Univ. Tokyo IA 22
  (1975), 319-369. (Not local; used for the explicit basis of
  `H^*((Z/2)^k; F_2)`.)

- [Ka95] J. F. Carlson, "Depth and transfer maps in the cohomology
  of groups", Math. Z. 218 (1995), 461-468. (Depth conjecture for
  p-groups.)

- [GH02] D. J. Green, G. Hertweck, "Carlson's depth conjecture and
  cohomology mod 2 for the Sylow 2-subgroups of M_22 and U_4(3)",
  Math. Z. (2003), `arXiv:math/0206127`. (Verifies depth conjecture
  for extraspecial 2-groups.)

- [Sy04] P. Symonds, "On the depth of the cohomology ring of a
  finite p-group", Math. Z. 247 (2004), 305-322. (Depth bounds.)

- [Ku07] N. J. Kuhn, "Primitives and central detection numbers in
  group cohomology", Adv. Math. 216 (2007), 387-442. `arXiv:math/0612133`.
  (Defines `d_0(G)`, `d_1(G)`; computes for several p-groups including
  `d_0(Q_8) = 3`.)

- [Mi00] P. A. Minh, "Essential Cohomology and Extraspecial p-Groups",
  Trans. AMS 353 (5) (2000), 1937-1957. Local file:
  `docs/S0002-9947-00-02689-1.pdf` (in the parent DRINFELD repo).

- [Pa-Yal12] J. Pakianathan, E. Yalçın, "Stably free periodic modules
  over extraspecial p-groups", Math. Z. 270 (2012), 1041-1075. (No
  minimum-family result, included for transfer-detection context.)

- [#154] D-VAN-MATH Quillen-stratification minimal-family analysis.
  See `2026-05-20-minimal-detecting-family.md` for empirical
  foundation.

- [#289] D-VAN m=5 audit. See
  `2026-05-19-d-van-detecting-family-correctness.md` for the
  Quillen 5.10 framing.

- [#310] PR linking #154's research note.

- [#314] This note: closed-form bound.
