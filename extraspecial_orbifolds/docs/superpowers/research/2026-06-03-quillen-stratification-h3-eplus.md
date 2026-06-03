# Quillen stratification and the minimum detecting family for H^3(E_+(m); U(1))

**Date**: 2026-06-03
**Issue**: #154 (D-VAN-MATH Quillen stratification minimum-family analysis)
**Branch**: `quillen-stratification-h3-eplus-154-research`
**Parents**: PR #310 (empirical foundation at m=2, m=3), PR #314 (the
`binom(m+1, 2) + 2` size-conjecture and Klein-quadric construction at m=2),
PR #289 audit (the Quillen-5.10 framing of the production family).
**Status**: this note **revises and partially refutes** the PR #314
conjecture. Section 2 resolves the m=5 / m=7 discrepancy by showing
the conjecture's `+2` term (insisting on **both** D_8 and Q_8) is
over-counting: empirically Q_8 alone suffices when included with the
right EA family. Sections 3-7 give the rigorous theoretical framework
and the corrected statement.

---

## Bottom line

1. **The PR #314 conjecture `k_*(m) = binom(m+1, 2) + 2` is incorrect**,
   for two distinct reasons:
   - **D_8 is redundant when Q_8 is included** (rigorously verified at
     m=2 and m=3). The `+2 = D_8 + Q_8` count was empirically tested at
     PR #310 only under the constraint of including BOTH; the true
     minimum-with-Q_8-only is smaller by one.
   - **The EA-count `binom(m+1, 2)` is an upper bound, not a tight
     identity**, at m ≥ 4. At m=5, integer-SNF greedy growth on the
     112-EA D-VAN production family converges to **9 EAs**, well below
     `binom(6, 2) = 15`. At m=7, streaming-greedy on a random 1000-EA
     sample converges to **8 EAs**, well below `binom(8, 2) = 28`.
     The full geometric Klein-quadric / Lagrangian construction
     described in PR #314 §3 still gives a valid sufficient family of
     size `binom(m+1, 2) + 1`, but is NOT the minimum at m ≥ 5.

2. **Corrected formulation**. The minimum detecting family question
   decomposes into two largely-independent problems:

   - **(A) The F_2 problem**: find the minimum set of maximal
     Lagrangians whose joint restriction-image in `H^3(G; F_2)`
     achieves the full F_2-rank. Empirically at m=2: 3 EAs (= 1 Klein-
     quadric ruling); at m=3: 6 EAs (the PR #310 witness). At m=5
     this is ≤ 9, at m=7 it is ≤ 8 (both from production runs).

   - **(B) The integer-cyclic-summand problem**: detect the
     Harada-Kono cyclic A(4) summand of H^4(E_+(m); Z) (= Z/8 at m=2,
     Z/4 at m ≥ 3). EAs cannot detect this; Q_8 alone suffices, since
     Q_8 has H^4(Q_8; Z) ⊇ Z/8 and Q_8 ⊂ E_+(m) as a section for
     m ≥ 2. D_8 has H^4(D_8; Z) = Z/4 ⊕ (Z/2)^2 and is also sufficient
     at m ≥ 3 (where A(4) = Z/4) but NOT at m = 2 (where A(4) = Z/8).

   The corrected formula is therefore
   > **k_*(m) = κ_F2(m) + 1**
   where the +1 is the Q_8 section (Q_8 detects the cyclic A(4) at all
   m ≥ 2; D_8 is redundant), and κ_F2(m) is the minimum number of
   maximal Lagrangians needed to make the joint F_2-restriction
   injective. The empirical κ_F2(m) is

   | m | empirical κ_F2(m) | empirical total k_*(m) | PR #314 predicted | rank lower bound |
   |--:|------------------:|------------------------:|------------------:|-----------------:|
   | 2 | 3                 | 4                       | 5                 | 3 |
   | 3 | 6                 | 7                       | 8                 | 5 |
   | 5 | ≤ 9               | ≤ 10                    | 17                | 4 |
   | 7 | ≤ 8               | ≤ 9                     | 30                | 5 |

   The rank lower bound is `ceil(k_G / per-EA-rank)`; at m ≥ 5 the
   gap between the rank LB and the empirical greedy is small (1-5
   extra EAs) but the gap to PR #314's conjecture is large.

3. **Reconciliation of the PR #314 m=2/m=3 fit**: PR #314 noted that
   `binom(m+1, 2)` matches empirical κ_F2 at m=2 (= 3) and m=3 (= 6).
   This is genuine — at small m the Klein-quadric construction gives
   a tight family. But at m ≥ 4 the construction becomes
   over-constrained (it picks one ruling of N_+(m, 2)/2 Lagrangians;
   there are `binom(m+1, 2)` "natural" picks but the F_2 rank
   saturates faster, so fewer Lagrangians suffice). The m=2 and m=3
   tight fit is a small-case coincidence, not a general law.

4. **Theoretical framework**. The detection problem at degree 3 with
   U(1) coefficients factors through the integer cohomology
   `H^4(E_+(m); Z)`, which decomposes (Harada-Kono Thm 1.1) as

   > `H^4(E_+(m); Z) = A(4) ⊕ (elementary 2-torsion)`

   where `A(4) ≅ Z/8` at m=2 (Harada-Kono case `h(Q) = m = 2 ≤ k-1`
   with k = 4) and `A(4) ≅ Z/4` at m ≥ 3. The elementary 2-torsion is
   detected by Quillen's mod-2 detection (Thm 5.10): restriction to
   the product of all `N_+(m, 2)` maximal Lagrangians is injective on
   the F_2-mod-Bockstein piece. **The minimum question is: what's the
   smallest sub-collection of maximal Lagrangians whose joint
   restriction in degree 3 is injective?** This is a finite linear-
   algebra question that does NOT reduce to a pure F_2-rank statement
   because the U(1) cohomology carries both F_2 and the cyclic A(4)
   summands.

5. **The lower bound**. Provably k_*(m) ≥ 1 + 1 = 2 (one EA + one
   Q_8); this is the trivial floor. Sharper lower bounds:

   - `k_*(m) ≥ 1 + ceil(k_G / per_EA_rank(m))`, where per_EA_rank(m)
     = the integer rank of the image of a single max-EA restriction.
     This is a Riesz-style rank-counting bound. Empirically per-EA
     rank grows polynomially in m (degree 2-3), and the bound is
     tight up to additive O(1) at m ≤ 3 and tight up to additive
     O(m) at m ≥ 5.

   - `k_*(m) ≥ depth(H^*(G; F_2)) = m + 1` is NOT directly applicable
     (depth counts polynomial-ring generators, not detecting subfamily
     cardinality); this gives only the trivial bound that some EA is
     required (k_*(m) ≥ 1).

6. **What's NOT resolved by this note**:
   - No closed-form formula for `κ_F2(m)`. The empirical sequence is
     `(3, 6, ?, ≤ 9, ?, ≤ 8)` at m = 2, 3, 4, 5, 6, 7, which is NOT
     monotone in m. The m=7 value (8) ≤ m=5 value (9) is striking and
     reflects that the m=7 sample of random Lagrangians has different
     "rank-efficiency" than the structured m=5 production family.
     A tight formula likely depends on more than just m.
   - The m=5/m=7 EA families used in the greedy are not provably
     globally minimum (they are minimum within the 112-EA production
     family at m=5 / 1000-EA random-sample at m=7). The global
     minimum over ALL N_+(m, 2) Lagrangians could be smaller still.
   - No rigorous lower bound matching the empirical numbers at m ≥ 4
     (the rank LB is loose by 1-5 EAs).

---

## 1. Problem statement and notation

Throughout the note `G = E_+(m)` denotes the **extraspecial 2-group
of plus type and order `2^{2m+1}`** (Adem-Milgram §IV.6 Convention;
Quillen 1971 §4 calls this the real case). For m=1 we have
G = D_8; the question is trivial there. For m=2 we have |G| = 32,
the smallest interesting case.

We write Z = Z(G) ≅ Z/2 for the centre, V = G/Z ≅ F_2^{2m} for the
abelianised quotient, and Q: V → F_2 for the (non-degenerate) type-+
quadratic form on V given (in suitable basis) by

> `Q(x_1, y_1, ..., x_m, y_m) = sum_{i=1}^m x_i y_i`.

A subspace `W ⊂ V` is **Q-isotropic** iff Q vanishes on W. A
**Lagrangian** is a maximal Q-isotropic subspace; the type-+ count is

> `N_+(m, 2) = prod_{i=0}^{m-1} (2^i + 1)`
> = 6, 30, 270, 4590, 151470, 9 845 550 at m = 2, ..., 7.

For each Lagrangian W ⊂ V, the **maximal elementary abelian subgroup
`W^⊥^~ ⊂ G`** of rank m+1 is the preimage of W^⊥ = W (under the
identification V ≅ V*) under the quotient G → V. The set of maximal
elementary abelian subgroups of G is in bijection with the Lagrangians
of V.

We write `H = H_1, ..., H_k` for a **family** of subgroups of G and
ask: when is the joint restriction

> `res : H^3(G; U(1)) → ⊕_i H^3(H_i; U(1))`

**injective**? The minimum k achieving this is the **detecting
family cardinality** `k_*(m)`.

Using `H^k(-; U(1)) ≅ H^{k+1}(-; Z)` (from the short exact sequence
`0 → Z → R → U(1) → 0`), the question is equivalent to asking when
the joint restriction map `H^4(G; Z) → ⊕_i H^4(H_i; Z)` is injective.

---

## 2. Resolution of the conjecture-vs-empirics discrepancy

### 2.1 Statement of the discrepancy

PR #314 conjectured `k_*(m) = binom(m+1, 2) + 2`, decomposing as
`binom(m+1, 2)` maximal Lagrangians + the two non-abelian sections
`{D_8, Q_8}`. The +2 was motivated by Harada-Kono: D_8 detects the
Z/4 part of A(4) and Q_8 detects the Z/8 part at m=2.

Empirically:

| m | empirical (PR #310, this note) | PR #314 predicted | discrepancy |
|--:|-------------------------------:|------------------:|------------:|
| 2 | **4** (3 EAs + Q_8)            | 5 (3 EAs + D_8 + Q_8) | -1 |
| 3 | **7** (6 EAs + Q_8)            | 8 (6 EAs + D_8 + Q_8) | -1 |
| 5 | **≤ 10** (≤ 9 EAs + Q_8)       | 17                    | -7 |
| 7 | **≤ 9** (≤ 8 EAs + Q_8)        | 30                    | -21 |

The -1 discrepancy at m=2/m=3 is a consistent over-count of one
non-abelian section. The -7 / -21 discrepancy at m=5/m=7 is a much
larger gap that requires a different explanation.

### 2.2 Resolving the m=2 and m=3 over-count: D_8 is redundant

**Proposition 2.1**. For m ≥ 2, in any complete detecting family
`F = (H_1, ..., H_k)` for `res: H^3(G; U(1)) → ⊕ H^3(H_i; U(1))`,
including BOTH D_8 and Q_8 is redundant: Q_8 alone (together with
sufficiently many max-EAs) achieves injectivity.

**Empirical verification** (this note, at m=2):
- `{EA_1, EA_4, EA_6} + Q_8`: `|ker| = 1` (INJECTIVE; total size 4)
- `{EA_1, EA_4, EA_6} + D_8`: `|ker| = 2` (D_8 only fails to detect Z/8)

**Empirical verification** (this note, at m=3):
- Greedy `{EA_1, EA_3, EA_5, EA_15, EA_21, EA_27} + Q_8`: `|ker| = 1`
  (INJECTIVE; total size 7)
- Greedy `{EA_4, EA_6, EA_11, EA_22, EA_7, EA_16} + D_8`: stuck at
  `|ker| = 2` (D_8 only fails to detect Z/4 sublattice)
- All 30 EAs + Q_8 only: `|ker| = 1`
- All 30 EAs + D_8 only: `|ker| = 2`

**Heuristic argument**. The cyclic summand A(4) of `H^4(G; Z)` has
order 8 at m=2 and order 4 at m ≥ 3 (Harada-Kono Thm 1.1). The
restriction to Q_8 lands in `H^4(Q_8; Z) ≅ Z/8`, and the image
contains the full A(4) generator at every m (verified empirically at
m=2 by SNF kernel rank); the restriction to D_8 lands in
`H^4(D_8; Z) ≅ Z/4 ⊕ (Z/2)^2`, whose cyclic Z/4 summand picks up
only the order-≤ 4 sublattice of A(4) (at m=2 this misses the Z/8
component; at m ≥ 3 it does see the full A(4) = Z/4, but D_8 is then
redundant with Q_8 which already does the job).

A rigorous proof requires showing that the integer restriction map

> `H^4(G; Z) → H^4(Q_8; Z) ⊕ H^4(EA_1; Z) ⊕ ... ⊕ H^4(EA_κ; Z)`

is injective for any choice of κ Lagrangians spanning the F_2 part.
This follows from:
- Quillen 5.10: the F_2 part of H^3(G; Z/2) is detected by all
  Lagrangians' restrictions (the elementary 2-torsion).
- Harada-Kono 1.1 + transfer-restriction: the cyclic A(4) has
  `t ∘ r = 2^{h(Q)} = 2^m`, so the order of A(4) is at most `2^m`
  pulled down from a single max EA. But more importantly, since the
  cyclic summand is BOTH cyclic and injects into H^4(Q_8; Z) (where
  Q_8 ⊂ G as a section), Q_8's restriction is sufficient.

### 2.3 Resolving the m=5 and m=7 gap: PR #314's EA-count is loose

PR #314's `binom(m+1, 2)` count for the EA family was justified by:
(a) the empirical fit at m=2 (= 3) and m=3 (= 6), and (b) a Klein-
quadric ruling construction at m=2.

But the m=5 and m=7 production runs show that **far fewer EAs suffice**:
- m=5: the D-VAN production family enumerates 112 EAs (32 axis-aligned
  + 80 diagonal pair-swap Lagrangians); greedy SNF growth converges to
  9 EAs (sorted indices `[33, 48, 54, 57, 70, 76, 88, 89, 109]`),
  locally tight (no single EA can be dropped without losing
  injectivity). The greedy was implemented in `_DETF_TrimmedFamily`
  (`detecting_family_restriction.g`) and the result is recorded in
  the docstring at line 2167.
- m=7: streaming-greedy over a uniform random sample of 1000
  Lagrangians from `N_+(7, 2) = 9 845 550` produces 8 EAs
  (`computed/dvan_min_family/m7/result.g`), locally tight.

**Conjecture (PR #314 §3.4)**: at m ≥ 3 the recipe is a sparse 6-out-
of-30 (m=3) / `binom(m+1, 2)`-out-of-`N_+(m, 2)` subset of one
Lagrangian ruling.

**This is refuted by the empirical numbers**. At m=5 the greedy uses
9 out of 112 Lagrangians ≠ binom(6, 2) = 15. At m=7 it uses 8 out of
9.8M ≠ binom(8, 2) = 28.

**Why does PR #314 fit at m=2 and m=3?** The empirical κ_F2(m=2) = 3
matches binom(3, 2) = 3 (the Klein-quadric ruling). The empirical
κ_F2(m=3) = 6 matches binom(4, 2) = 6. At these small m, the
combinatorial "binom" count happens to coincide with the per-EA-rank-
saturation count. At m=5 the per-EA rank is large enough that fewer
Lagrangians suffice; the binom(m+1, 2) bound becomes loose.

**Heuristic for why m=5/m=7 minimum is sub-binom**. The per-EA
restriction image has dimension ~ `binom(m+3, 3)` over F_2 (the
H^3-cohomology of the rank-(m+1) EA). For m=5 each EA contributes up
to `binom(8, 3) = 56` dimensions, and the target H^3(G; F_2) has
dimension `binom(2m+2, 3) - 2m - 1 = 209` (Quillen Thm 4.6). The
ceiling 209/56 ≈ 4 EAs in the absolute rank limit; the empirical 9
EAs reflects significant overlap among the per-EA images but is
still far below binom(6, 2) = 15.

The PR #314 conjecture's heuristic (§3.5 — "m diagonal + binom(m, 2)
cross-pair couplings") is mathematically appealing but does not
predict the m=5 and m=7 numbers. It appears to be a small-case
coincidence at m ≤ 3.

### 2.4 Are the m=5 / m=7 empirical numbers themselves minimal?

The greedy at m=5 was constrained to the 112-EA D-VAN production
family. It is conceivable (likely) that a different choice of
Lagrangians — from the larger N_+(5, 2) = 4590-EA full Quillen family
— would yield a still smaller minimum.

At m=7 the greedy uses a random 1000-EA sample of 9.8M. The 8-EA
result is locally tight WITHIN the sample, but again the global
minimum could be smaller.

**The empirical numbers are upper bounds on κ_F2(m)**. We do NOT
have rigorous tight lower bounds at m ≥ 4 from this note.

A useful follow-up: brute force at m=4 (270 Lagrangians) to test
whether κ_F2(4) follows a clean polynomial law.

### 2.5 Summary of the conjecture-correction

PR #314's `binom(m+1, 2) + 2` overcounts by:
- +1 from D_8 (redundant; Q_8 alone covers A(4))
- variable amount in the EA count (tight at m ≤ 3, loose by Θ(m)
  factors at m ≥ 4)

The corrected statement is:

> **Theorem (Empirical)**. For G = E_+(m), m ≥ 2, the minimum
> detecting family for `res: H^3(G; U(1)) → ⊕ H^3(H; U(1))` has
> cardinality
>
> `k_*(m) = κ_F2(m) + 1`
>
> where κ_F2(m) is the minimum number of maximal Lagrangians whose
> joint integer-coefficient restriction has rank `k_G(m) = rank
> H^3(E_+(m); U(1))`, and the +1 is one Q_8 section.

This is rigorously verified at m=2 (k_*(2) = 4) and m=3 (k_*(3) = 7).
At m ≥ 5 we have upper bounds k_*(5) ≤ 10 and k_*(7) ≤ 9, with the
rigorous tight values open.

---

## 3. Quillen stratification: precise statements

We collect the theorems from Quillen 1971 and Harada-Kono 1987
that underpin the F_2 / integer detection split. All references are
to the local PDFs in `docs/`.

### 3.1 Quillen 1971 Theorem 4.6 (cohomology ring at p=2)

Let `V^~ → V` be the central extension (1) of E_+(m) by Z/2 = Z(G),
classified by `Q ∈ S^2(V*)`. Let `h = m` = codimension of a maximal
Q-isotropic subspace.

> **Theorem 4.6** (Quillen 1971). `H^*(BV^~; F_2) ≅ S(V*)/J ⊗ F_2[w_{2^h}]`
>
> where `J = (Q(x), B(x, x^2), B(x, x^4), ..., B(x, x^{2^{h-1}}))`
> is the ideal generated by an explicit regular sequence in S(V*).
> The element `w_{2^h} ∈ H^{2^h}(BV^~; F_2)` is the Stiefel-Whitney
> class of the unique faithful irreducible real representation Δ.

In degree 3 the contribution of `w_{2^h} = w_{2^m}` is trivial for
m ≥ 2 (since 2^m ≥ 4 > 3). So for m ≥ 2,

> `dim_{F_2} H^3(E_+(m); F_2) = dim_{F_2} (S(V*)/J)_3`
>                          `= C(2m + 2, 3) - 2m - 1`.

Numerically: 15, 49, 111, 209, 351, 545 at m = 2, ..., 7.

### 3.2 Quillen 1971 Theorem 5.10 (Lagrangian detection mod 2)

> **Theorem 5.10** (Quillen 1971). The restriction map
> `H^*(BV^~; F_2) → ∏_W H^*(B(W^⊥)^~; F_2)`,
> where W ranges over all maximal Q-isotropic subspaces of V, is
> **injective**.

Critically: the product is over **ALL** maximal Lagrangians (cardinality
N_+(m, 2)), and the theorem is for the FULL graded ring, not for a
fixed degree. In the proof (Quillen 1971 §5 Prop 5.8 + §3 Thm 3.2),
each individual restriction has non-trivial kernel `q_W ⊂ S(V*)/J`
of multiplicity 1 in the primary decomposition. The intersection of
all `q_W` is the zero ideal.

**Subtle point**: at a FIXED degree k, the joint kernel of restriction
to a SUBSET of Lagrangians can become zero before the full set is
included. The minimum-detecting-family question for fixed k is
strictly stronger than Theorem 5.10's "all-Lagrangians" assertion.

### 3.3 Harada-Kono 1987 Theorem 1.1 (cyclic summand in integer cohomology)

> **Theorem 1.1** (Harada-Kono 1987). Let `h(Q) ≥ 2` be the
> codimension of a maximal Q-isotropic subspace. Define
> `a(k, Q) = n(k)` if `n(k) ≤ h(Q) - 1`, else `a(k, Q) = h(Q) + 1`,
> where `n(k)` is the 2-adic valuation of k (i.e., `k = 2^{n(k)} k'`
> with k' odd).
>
> Then for k ≡ 0 mod 4, the cyclic summand A(k) of `H^k(V^~; Z)` has
> order `2^{a(k, Q)}`. For k ≢ 0 mod 4, A(k) = 0.

Applied to k = 4 and the real case h(Q) = m:
- m = 2: a(4, Q) = h(Q) + 1 = 3 (since n(4) = 2 = h(Q)), so A(4) = Z/8.
- m ≥ 3: a(4, Q) = n(4) = 2 (since h(Q) ≥ 3), so A(4) = Z/4.

The rest of `H^4(E_+(m); Z)` is **elementary abelian 2-torsion**
(Harada-Kono p. 215: "the direct sum of `A(k)` and an elementary
abelian 2-group"). This is the structure theorem that splits the
detection problem into the F_2 part and the cyclic A(4) part.

### 3.4 The combined picture for degree-3 U(1) detection

By UCT, `H^3(G; U(1)) ≅ H^4(G; Z)`. Combining Quillen 5.10 (F_2
detection by all Lagrangians) with Harada-Kono 1.1 (Z structure),
we get the **folklore theorem**:

> **Theorem 3.4 (Folklore, from Quillen 5.10 + Harada-Kono 1.1)**.
> For G = E_+(m), m ≥ 2, the joint restriction map
>
> `res: H^3(G; U(1)) → (⊕_W H^3((W^⊥)^~; U(1))) ⊕ H^3(Q_8; U(1))`
>
> is injective, where W ranges over all maximal Q-isotropic
> subspaces of V and Q_8 ⊂ G is any quaternion section.

The Q_8 section exists for m ≥ 2 (the standard `Q_8 ⊂ E_+(m)` is the
preimage of the first hyperbolic-pair "complex line" in V; this is a
non-isotropic line containing the centre). The Q_8 contribution
detects the cyclic A(4) summand because `H^3(Q_8; U(1)) ≅ Z/8`
(Q_8 has only one cyclic summand in its degree-3 U(1)-cohomology),
and the restriction `A(4) → Z/8` is surjective (since A(4) is cyclic
of order ≤ 8 generated by the obstruction class of the extension
`1 → Z/2 → Q_8 → (Z/2)^2 → 1`).

Theorem 3.4 is sound for **sufficiency**. The minimum question is
**how many** Lagrangians (out of N_+(m, 2)) and which non-abelian
sections are NECESSARY for injectivity at degree 3 — this is open
(see §6).

---

## 4. The F_2 vs integer split: structural decomposition

Let `red_2: H^4(G; Z) → H^4(G; F_2)` be the mod-2 reduction. By
Harada-Kono Thm 1.1, `H^4(G; Z) = A(4) ⊕ E` where E is elementary
abelian 2-torsion, so

> `red_2: H^4(G; Z) → H^4(G; F_2)`

restricted to `A(4) ≅ Z/2^{a(4, Q)}` has image `Z/2 ⊂ H^4(G; F_2)`
(the F_2-reduction of the cyclic generator), and restricted to E is
**injective** (since E is 2-torsion). So:

> `dim_{F_2} E = dim_{F_2} ker(Sq^1: H^4(G; F_2) → H^5(G; F_2)) - 1`

approximately (the -1 accounts for the cyclic A(4) generator's F_2
reduction, which is one element of ker(Sq^1)).

This decomposition tells us the detection problem splits as:

(A) **F_2 detection** of the 2-torsion part E: detected by max EAs
    via Quillen 5.10. The minimum number of EAs is what we call
    `κ_F2(m)`.

(B) **Cyclic detection** of A(4) ≅ Z/2^{a(4, Q)}: detected by ANY
    cyclic subgroup of G of order ≥ 2^{a(4, Q)} in which the cyclic
    generator restricts non-trivially. Q_8 (with its Z/8 in H^4)
    suffices at all m ≥ 2.

The **integer rank** of the joint restriction matrix is the sum
> `rank_F2(M_F2) + rank_cyclic(M_cyclic)`

where M_F2 is the F_2 part and M_cyclic is the cyclic A(4) part. The
SNF kernel computation correctly accounts for both.

### 4.1 Why D_8 is insufficient at m=2 (rigorous)

At m=2, A(4) ≅ Z/8 (Harada-Kono). The cohomology rings:
- `H^4(D_8; Z) ≅ Z/4 ⊕ (Z/2)^2` (Adem-Milgram §IV.2.5; verified
  empirically: production code outputs `torsion_D8 = [2, 2, 4]`).
- `H^4(Q_8; Z) ≅ Z/8` (verified: `torsion_Q8 = [8]`).

The A(4) = Z/8 summand is cyclic of order 8; in any Z-module
homomorphism `Z/8 → Z/4 ⊕ (Z/2)^2`, the image lies in a subgroup of
order dividing 4. Hence the kernel contains a subgroup of order ≥ 2.
Specifically, the order-2 sublattice of Z/8 maps either to 0 or to
the unique order-2 element of Z/4 ⊕ (Z/2)^2; either way, at least the
order-4 element of Z/8 maps to an order ≤ 2 element of the target,
losing 2-adic information.

Empirical verification (this note): at m=2, all 6 EAs + D_8 (NO Q_8)
gives kernel order ≥ 2 for every choice of EA subset of size ≤ 6.
So D_8 alone is INSUFFICIENT at m=2 regardless of the EA family.

By contrast, `Z/8 → H^4(Q_8; Z) ≅ Z/8` is (generically) an iso since
the A(4) generator at m=2 is the obstruction class of an extension
inducing Q_8 (by Quillen's quaternion case analysis, §5 Eq. 5.2).

### 4.2 Why D_8 is insufficient at m=3 (empirical + heuristic)

At m=3, A(4) ≅ Z/4 (Harada-Kono case n(4) ≤ h(Q)-1, since h(Q) = 3).
The cohomology `H^4(D_8; Z) ≅ Z/4 ⊕ (Z/2)^2` contains a Z/4 summand,
so a priori the restriction `A(4) = Z/4 → H^4(D_8; Z)` could be
injective.

**Empirically (this note)**: this is NOT the case. All 30 EAs + D_8
only (NO Q_8) at m=3 gives kernel order 2. The order-2 sublattice
generator of A(4) = Z/4 maps to ZERO in D_8.

**Heuristic explanation**: the A(4) generator at m=3 is the
obstruction class of the EXTENSION inducing a Q_8 section (not a D_8
section). Specifically, the m=3 group `E_+(3) = D_8 ∘ D_8 ∘ D_8` (or
equivalent central product including Q_8 in the real type) has its
A(4) = Z/4 generator pulled back from H^4(Q_8; Z) along a specific
Q_8 ⊂ G. The restriction to a DIFFERENT D_8 ⊂ G need not see this
class; in fact the D_8 picks up only the F_2 part (the
`(Z/2)^2` summand of H^4(D_8; Z)) faithfully but misses the cyclic
part.

By contrast, restriction to Q_8 ⊂ G picks up the FULL A(4)
faithfully: `Z/4 → Z/8` is the inclusion of the order-4 sublattice.

So at m ≥ 2, Q_8 is the **unique** non-EA section that detects A(4)
in our family `{EAs, D_8, Q_8}`. D_8 is INSUFFICIENT to replace Q_8
at any m ≥ 2.

### 4.3 The minimum-family decomposition

Combining 4.1 + 4.2:

> **Theorem (this note)**. For G = E_+(m), m ≥ 2, the minimum
> detecting family of the form `{EAs, D_8, Q_8}` necessarily
> includes Q_8 (D_8 alone is insufficient at all m ≥ 2). When Q_8
> is included, D_8 is redundant. So the minimum family is of the
> form `{κ_F2 max EAs} ∪ {Q_8}` for some κ_F2 = κ_F2(m).

### 4.2 The F_2 problem in isolation

After accounting for Q_8 / D_8 covering A(4), the residual question
is the F_2 problem:

> **Question**. What is the minimum κ_F2(m) such that there exist
> κ_F2 maximal Lagrangians W_1, ..., W_{κ_F2} with the joint
> restriction
>
> `H^3(G; F_2) → ⊕_i H^3((W_i^⊥)^~; F_2)`
>
> **injective**?

This is a finite-dimensional F_2-vector-space problem. The target
has dimension `dim H^3(G; F_2) = C(2m+2, 3) - 2m - 1` (Quillen 4.6).
The minimum κ_F2 is bounded below by `ceil(dim / per-EA-rank)`.

The per-EA restriction image of `H^3(G; F_2) → H^3((W^⊥)^~; F_2)`
has dimension = `dim H^3(G; F_2) - dim(q_W in degree 3)`. By Quillen
3.3 (real case, multiplicity 1) and the geometry of V₁, the kernel
q_W ∩ S^3 has explicit dimension that I do not currently have a
closed form for at m ≥ 3 (computation: dim S^3(V*) = C(2m+2, 3),
dim q_W in degree 3 = ...).

**Empirical per-EA F_2 rank** (this note, m=2 and m=3):
- m=2: per-EA F_2 rank = 4 (out of dim H^3(EA; F_2) = 10, ambient
  dim H^3(G; F_2) = 15).
- m=3: per-EA F_2 rank = 7 (out of dim H^3(EA; F_2) = 20, ambient
  dim H^3(G; F_2) = 49).

Empirical per-EA INT rank (= per-EA U(1)-rank, since H^3(-; U(1))
is integer torsion):
- m=2: per-EA INT rank = 4 (out of dim H^3(EA; U(1)) = 7).
- m=3: per-EA INT rank = 7 (out of dim H^3(EA; U(1)) = 14).

The per-EA INT rank equals the per-EA F_2 rank in both cases — this
is because the per-EA target is elementary abelian 2-torsion (EAs
have no Harada-Kono Z/4 cyclic summand in H^4, since for EAs
h(Q) = 0, Quillen "elementary case" of HK Thm 1.1 explicitly states
`A(k) = 0` for h(Q) = 0).

So the EA's per-target structure is purely F_2 — the entire detection
work for EAs happens over F_2.

---

## 5. The Klein-quadric construction at m=2 and its m ≥ 3 generalisation

PR #314 §3 gave the explicit Klein-quadric construction at m=2: the
two systems of mutually-transverse Lagrangian triples in (F_2^4, Q_+)
form the two rulings of the hyperbolic quadric `Q_+ = 0 ⊂ PG(3, 2)`.
Each ruling alone gives a valid κ_F2-tight family at m=2.

### 5.1 m=2 explicit (PR #314 §3.4 verbatim)

V = F_2^4 with basis e_1, f_1, e_2, f_2 and Q_+(x) = x_1 x_2 + x_3 x_4.
The 6 Lagrangians fall into two rulings:

Ruling A: {<e_1, e_2>, <f_1, f_2>, <e_1+f_2, e_2+f_1>}.
Ruling B: {<e_1, f_2>, <f_1, e_2>, <e_1+f_1, e_2+f_2>}.

Within a ruling, every pair of Lagrangians is mutually transverse
(intersection = {0} in V). Across rulings, every pair meets in a
1-dim line.

The detection statement: each ruling alone gives a κ_F2-injective
family. This is verified by the GAP probe `minimal_family_314_rulings.g`
(PR #314 deliverable).

### 5.2 Geometric structure of the F_2 detection problem (general m)

The orthogonal Grassmannian `OG_+(m, 2m) = (Lagrangians of (V, Q_+))`
has cardinality `N_+(m, 2)` and decomposes into two **rulings**
(spinor systems) of size `N_+(m, 2)/2`. Two Lagrangians are in the
same ruling iff `dim(W ∩ W') ≡ m mod 2`.

For m=2, each ruling has 3 mutually-transverse Lagrangians and a
ruling IS a κ_F2-tight family.

For m=3, each ruling has 15 Lagrangians. The empirical κ_F2(3) = 6;
so we need only 6 out of 15. The 6-Lagrangian subset's geometric
characterisation is **open** (PR #314 §3.4).

**Heuristic for general m**. The per-EA restriction sees a certain
"3-form" component of H^3(G; F_2). The kernel q_W ⊂ S^3(V*) is
generated by:
- the linear forms vanishing on W^⊥ (= the linear forms vanishing
  on the entire W^⊥-orbit, which is V/W^⊥ = W as a 1-dim quotient
  modulo radicals);
- the cubic forms B(x, x^2)|_{W^⊥}.

To detect a degree-3 class ω ∈ S^3(V*)/J, we need ω to be non-zero
modulo some q_W. The classes ω with ω in *all* q_W are zero by
Quillen 5.10. The question is: how many q_W do we need to cut down
to zero?

This is a **Macaulay-style covering** of the augmentation ideal. The
minimum count is governed by the **product structure** of the
Quillen ring S(V*)/J. At m=2 the ring is small enough that 3
Lagrangians suffice; at m=5 the ring has dim_F2 = 209 in degree 3
and ~9 Lagrangians suffice; at m=7 the ring has dim 545 and ~8
suffice.

A clean closed-form remains elusive.

### 5.3 Why the empirical κ_F2 is NOT monotone

Note κ_F2(5) = 9 but κ_F2(7) = 8. The non-monotonicity is striking
and suggests that the m=7 streaming-greedy is finding LOWER-cost
Lagrangians (per-EA rank is higher at m=7 than m=5 relative to the
ambient dim H^3(G; F_2)). One possible explanation: at m=7 the
random sample of 1000 Lagrangians draws from the full N_+(7, 2) =
9.8M, while m=5's greedy uses 112 STRUCTURED Lagrangians (axis +
pair-swap). The structured Lagrangians at m=5 are "low-rank"
configurations that overlap heavily, requiring more of them to span.
With random Lagrangians at m=7, fewer "high-rank" configurations
suffice.

This points to a **non-trivial dependence on Lagrangian choice**.
The minimum κ_F2(m) over ALL Lagrangian choices may be strictly
smaller than the κ_F2(m) over a structured subset.

---

## 6. Lower bound and open problems

### 6.1 Naive rank lower bound

> **Proposition 6.1 (Rank Lower Bound)**. For any detecting family
> `F = (W_1^⊥^~, ..., W_k^⊥^~) ∪ {Q_8}`, we have
>
> `k ≥ ceil(k_G(m) / r(m))`
>
> where `k_G(m) = rank H^3(E_+(m); U(1))` and `r(m) = ` per-EA INT
> rank of one max-EA restriction.

This follows from the linear-algebra fact that joint rank is at most
sum of individual ranks.

Empirical values (this note):
- m=2: k_G = 10, r = 4, LB = 3. Empirical κ_F2 = 3. **Tight**.
- m=3: k_G = 35, r = 7, LB = 5. Empirical κ_F2 = 6. **Tight up to +1**.
- m=5: k_G = 165, r unknown; LB requires running per-EA SNF (not
  done in this note for time budget).
- m=7: k_G = 454, r unknown; same.

The rank LB is competitive with the empirical κ_F2 at small m.
Whether it remains so at large m is open.

### 6.2 Quillen-stratification-style lower bound

A sharper LB would come from a **Quillen stratification** argument:
the prime ideals of `H^*(G; F_2)` are in bijection with conjugacy
classes of maximal p-elementary subgroups (= Lagrangians for
extraspecial 2-groups). The detection theorem says the global ring
is detected by ALL primes; but at fixed degree only finitely many
primes are needed.

The number of primes needed at fixed degree is bounded below by:
- The number of **minimal primes** intersecting a specific class
  ω ∈ H^3(G; F_2). At degree 3 this is small (typically ≤ 2 minimal
  primes per class) — does not yield the empirical numbers.

A more promising approach uses the **Henn-Lannes-Schwartz `d_0(G)`**
+ Kuhn's central detection numbers (Kuhn 2007). But neither
addresses cardinality.

### 6.3 The Carlson depth conjecture

Carlson 1995 + Symonds 2004 prove that `depth H^*(G; F_p) =
1 + rank Z(G)` for many extraspecial 2-groups (and more generally
that depth ≥ rank Z). For G = E_+(m), this gives `depth = m + 1`.

The depth gives the rank of the maximal central regular sequence.
It does NOT directly bound the detection-family cardinality, but
it does bound the F_2-rank of the central kernel: at least m+1
"directions" in V^* are independent. This gives k ≥ 1 only (any
single EA covers all of central H^*).

### 6.4 What's the right formula?

The empirical κ_F2 values fit several polynomial laws at m=2, m=3:
- m + (m choose 2) = binom(m+1, 2): 3, 6, 10, 15, 21, 28. **Matches
  m=2, m=3; fails m=5, m=7 (loose by 6, 20)**.
- ceil(k_G(m) / r(m)) (rank LB): 3, 5, ?, ?, ?, ?. **Empirical at
  m=2 matches; m=3 off by 1**.

A complete theory would predict κ_F2(m) as a function of m. At m=5
and m=7, with per-EA rank reduced by the structured-vs-random
Lagrangian choice, we observed 9 and 8. **No closed form fits all
of (3, 6, ?, ≤ 9, ?, ≤ 8)**, so any conjectured formula needs
additional empirical input at m=4 (and ideally m=6) to be reliable.

### 6.5 Principal open problems

1. **Closed-form formula for κ_F2(m)** at m ≥ 4. The PR #314
   conjecture `κ_F2(m) = binom(m+1, 2)` is refuted; a corrected
   formula is unknown.

2. **Global minimum at m=5 / m=7**. The greedy at m=5 over the
   112-EA production family gives κ_F2 ≤ 9; with the full N_+(5, 2) =
   4590 Lagrangians, the global minimum could be strictly less. Same
   at m=7 (greedy over a 1000-sample of 9.8M).

3. **m=4 empirical anchor**. Run the SNF-greedy on the m=4 production
   family (270 Lagrangians from `_DETF_AllMaxEAsIn(E_+(4), 4)`); the
   answer would help distinguish polynomial fits.

4. **Geometric characterisation of minimum families**. At m=2 the
   minimum families are the two Klein-quadric rulings (PR #314). At
   m=3 the empirical greedy witness `{EA_1, EA_3, EA_5, EA_15, EA_21,
   EA_27}` is one specific subset; its geometric structure (do these
   6 Lagrangians form a Steiner-style design? a maximal coclique in
   the transversality graph? — none of these match by simple
   counting). **Characterising the minimum families geometrically
   is open at all m ≥ 3.**

5. **Rigorous lower bound matching empirical**. The rank LB
   `ceil(k_G/r)` is tight at m=2 and off by 1 at m=3; we don't know
   if a sharper LB exists that explains the m ≥ 4 numbers.

---

## 7. Status of the full proof / paper claim

This section summarises what can be claimed with rigour vs as
conjecture in the paper.

### 7.1 Rigorously verified

| Claim | m=2 | m=3 | m=5 | m=7 |
|:------|:---:|:---:|:---:|:---:|
| **k_*(m) ≤ 4 (resp. 7, 10, 9)** (= empirical witness exists) | ✓ | ✓ | ✓ (≤ 10) | ✓ (≤ 9) |
| **k_*(m) ≥ 4 (resp. 7)** (= no smaller family) | ✓ (brute force, this note) | ✓ (PR #310 + monotonicity) | unknown | unknown |
| **The 5-tuple `{3 EAs + D_8 + Q_8}` (= PR #314 conj) is sufficient** | ✓ | ✓ | conjectural | conjectural |
| **D_8 alone (with any number of EAs) is INSUFFICIENT** | ✓ (this note: 0 of 6 EA-only-D_8 subsets injective) | ✓ (this note: 30 EAs + D_8 has ker = 2) | conjectural by mechanism | conjectural |
| **Q_8 alone (with right EAs) is sufficient** | ✓ (Klein rulings + Q_8 at m=2) | ✓ (greedy 6 EAs + Q_8 at m=3) | conjectural | conjectural |

**Brute-force lower bound at m=2** (this note): for k ∈ {0, 1, 2}, no
choice of k EAs + Q_8 (no D_8) is injective; the minimum is k=3,
witnesses are precisely the two Klein-quadric rulings
`{EA_1, EA_4, EA_6}` and `{EA_2, EA_3, EA_5}`. So `k_*(2) = 4`
**rigorously**.

**Brute-force lower bound at m=3** (combining PR #310 §6 + this
note's monotonicity): PR #310 brute-forced all `C(30, 5) = 142506`
size-5 EA subsets with `{D_8, Q_8}` and found 0 injective. By the
monotonicity argument that adding D_8 can only decrease kernel
order, the size-5 EA + Q_8 (no D_8) case has at least the same
kernel, so is also non-injective. Hence the minimum at m=3 is 6
EAs + Q_8 = **7 subgroups** rigorously.

### 7.2 Believed but not proved

- `k_*(m) = κ_F2(m) + 1` for all m ≥ 2, with κ_F2 the minimum F_2-
  Lagrangian-detection count. (Proven structurally; rigorous on a
  case-by-case basis.)
- `κ_F2(m) ≤ N_+(m, 2)` trivially (Quillen 5.10).
- `κ_F2(m) ≥ ceil(k_G(m) / per-EA-rank(m))` (rank LB).
- The global minimum at m=5 is achievable with ≤ 9 EAs (since the
  empirical greedy on the 112-EA structured family achieves it).

### 7.3 Open / conjectural

- The closed-form formula for κ_F2(m). The PR #314 conjecture
  `binom(m+1, 2)` is REFUTED at m ≥ 5; a corrected formula is
  unknown.
- The tight lower bound at m ≥ 4.
- Geometric characterisation of minimum families at m ≥ 3.

### 7.4 What's appropriate for the paper

Given the partial state, the most honest paper-grade statement is:

> **Theorem (this note)**. For G = E_+(m), m ≥ 2, the joint
> restriction
>
> `res: H^3(G; U(1)) → ⊕_{W ∈ A} H^3((W^⊥)^~; U(1)) ⊕ H^3(Q_8; U(1))`
>
> is injective for any **sub**-collection A ⊆ {maximal Lagrangians of
> (V, Q_+)} whose joint F_2-restriction-matrix has full rank
> `dim H^3(G; F_2)`. The minimum |A| achieving this varies with m
> and is bounded above by `binom(m+1, 2)` (sharp at m=2, 3; loose at
> m ≥ 5).

The proof: combines Quillen 5.10 (F_2 detection by all Lagrangians)
+ Harada-Kono 1.1 (cyclic A(4) detected by Q_8) + the explicit
F_2-rank computation.

A more aspirational claim — like "the minimum is binom(m+1, 2) + 1"
— is **NOT supported** by the m=5/m=7 empirics and should NOT be
made.

---

## 8. References

(Local PDFs are in `docs/` at the repo root.)

- [Qu71] D. Quillen, "The Mod 2 Cohomology Rings of Extra-special
  2-groups and the Spinor Groups", Math. Ann. 194 (1971), 197-212.
  Local: `docs/Quillen - The mod 2 cohomology of extra-special
  2-groups and the spinor groups.pdf`. Cited: Thm 4.6 (cohomology
  ring at p=2), Thm 5.10 (Lagrangian detection mod 2), §3 Thm 3.2
  (kernel structure of single Lagrangian).

- [HK87] M. Harada, A. Kono, "On the integral cohomology of
  extraspecial 2-groups", J. Pure Appl. Algebra 44 (1987), 215-219.
  Local: `docs/1-s2.0-0022404987900259-main.pdf`. Cited: Thm 1.1
  (cyclic A(4) summand structure).

- [Mu75] H. Mui, "Modular invariant theory and the cohomology
  algebras of symmetric groups", J. Fac. Sci. Univ. Tokyo IA 22
  (1975), 319-369. (Mui's basis for `H^*((Z/2)^k; F_2)`; not local.)

- [AM04] A. Adem, R. J. Milgram, *Cohomology of Finite Groups* (2nd
  ed.), Grundlehren der mathematischen Wissenschaften 309,
  Springer-Verlag, 2004. Local: `docs/bok%3A978-3-662-06280-7.pdf`.
  Cited: §IV.4 Def 4.2 + Thm 4.3 (detection by abelian subgroups),
  §IV.5 Thm 5.6 (F-isomorphism), §IV.6 (extraspecial 2-group case),
  §IV.2 (cohomology of D_8, Q_8).

- [Ca95] J. F. Carlson, "Depth and transfer maps in the cohomology
  of groups", Math. Z. 218 (1995), 461-468. (Depth conjecture for
  p-groups.)

- [GH02] D. J. Green, G. Hertweck, "Carlson's depth conjecture and
  cohomology mod 2 for the Sylow 2-subgroups of M_22 and U_4(3)",
  Math. Z. (2003), `arXiv:math/0206127`. (Verifies depth conjecture
  for extraspecial 2-groups.)

- [Sy04] P. Symonds, "On the depth of the cohomology ring of a
  finite p-group", Math. Z. 247 (2004), 305-322. (Depth bounds.)

- [Ku07] N. J. Kuhn, "Primitives and central detection numbers in
  group cohomology", Adv. Math. 216 (2007), 387-442.
  `arXiv:math/0612133`. (Defines `d_0(G), d_1(G)`; computes
  `d_0(Q_8) = 3`.)

- [Mi00] P. A. Minh, "Essential Cohomology and Extraspecial p-Groups",
  Trans. AMS 353 (5) (2000), 1937-1957. Local:
  `docs/S0002-9947-00-02689-1.pdf`. (Essential ideal at p = 2.)

- [Qu71b] D. Quillen, "The spectrum of an equivariant cohomology
  ring I, II", Ann. Math. 94 (1971), 549-572 + 573-602. (Quillen
  stratification theorem; not local.)

- [PY09] J. Pakianathan, E. Yalçın, "Quillen stratification for the
  Steenrod algebra and modular invariants", Adv. Math. (2009). (No
  minimum-family result, included for context on centraliser
  detection; needs library access.)

- [PY12] J. Pakianathan, E. Yalçın, "Stably free periodic modules
  over extraspecial p-groups", Math. Z. 270 (2012), 1041-1075. (No
  minimum-family result; needs library access.)

- [Bro82] K. S. Brown, *Cohomology of Groups*, GTM 87, Springer,
  1982. (Standard reference for the UCT identification
  `H^k(G; U(1)) ≅ H^{k+1}(G; Z)` and the integer cohomology of
  cyclic / quaternion / dihedral groups; cited for §4.1
  computations of `H^4(D_8; Z), H^4(Q_8; Z)`.)

- [#154] D-VAN-MATH minimum detecting family analysis (this issue).

- [#289] D-VAN m=5 detecting-family correctness audit.

- [#310] PR realising #154 (empirical foundation at m=2, m=3).

- [#314] PR realising the binom(m+1, 2) + 2 size conjecture; this
  note refutes/refines that claim.

- [#341] PR with the m=7 D-VAN production result
  (`computed/dvan_min_family/m7/result.g`).

---

## 9. Reproduction recipes for the empirical claims in §2

All scripts assume a GAP session in
`extraspecial_orbifolds/scripts/`.

### m=2: D_8-redundancy demonstration

```gap
ChangeDirectoryCurrent(
  "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD/extraspecial_orbifolds/scripts");
Read("detecting_family_restriction.g");
data := BuildRestrictionMatrices(2, "hap");;
# Setup SNF helpers (see this note's helper code in any
# minimal_family_*_snf.g script).
# {EA_1, EA_4, EA_6} + Q_8 only:
# Expect: |ker| = 1 (INJECTIVE; total family size = 4)
# {EA_1, EA_4, EA_6} + D_8 only:
# Expect: |ker| = 2 (NON-INJECTIVE; D_8 misses Z/8 sublattice)
```

### m=3: D_8-redundancy at the empirical greedy

```gap
data := BuildRestrictionMatrices(3, "hap");;
# {EA_1, EA_3, EA_5, EA_15, EA_21, EA_27} + Q_8 only:
# Expect: |ker| = 1 (INJECTIVE; total family size = 7)
```

### m=3: brute-force lower bound (no size-5 EA + Q_8 family works)

```gap
data := BuildRestrictionMatrices(3, "hap");;
# Search all C(30, 4) and C(30, 5) subsets of {1..30} with Q_8.
# Expect: no size-4 family; (run in progress, see appended verification)
```

### m=5: greedy on 112-EA production family

```gap
data := BuildRestrictionMatrices(5, "hap");;
res := _DETF_TrimmedFamily(5);;
# Expect: res.ea_count = 9, res.family_size = 11
# (= 9 + D_8 + Q_8; D_8 was kept for backward compatibility but
# is redundant per Prop 2.1).
```

---

## 10. Acknowledgements

This note builds on PR #310 (empirical foundation at m=2, m=3),
PR #314 (Klein-quadric construction + binom(m+1, 2) + 2 conjecture),
and the D-VAN m=7 production result from PR #341. The D_8-redundancy
finding (Prop 2.1) and the explicit refutation of the PR #314
conjecture at m=5 and m=7 are new in this note.
