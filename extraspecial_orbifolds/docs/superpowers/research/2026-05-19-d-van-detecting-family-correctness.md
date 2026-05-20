# D-VAN m=5 detecting-family correctness audit

**Date**: 2026-05-19
**Issue**: #289
**Branch**: `dvan-math-audit-112-lagrangians`
**Parent fix**: #287 (branch `dvan-m5-direct-subgroup-construct`, commit 051d1aa)
**Status**: complete (subject to GAP probe limited to m <= 3 by the CPU cap)

## Bottom line

1. The **Aut(G)-orbit count of maximal elementary abelians in E_+(m)
   is 1** for m = 2, 3 (computed in GAP), and is **conjecturally 1 for
   all m >= 2**. So "one rep per Aut-orbit" = a single max EA — which
   the empirical m=2 probe shows is INSUFFICIENT (2 of 10 unit
   generators have zero restriction to a single max EA but are
   detected by another max EA).

2. The detecting-family theorem from **Quillen 1971 Theorem 5.10**
   states that H*(E_+(m); F_2) is detected by the product over **ALL**
   maximal Q-isotropic subspaces, not Aut-orbit reps. The "mod Aut(G)"
   reading from the R-1 lit survey (its "Step 3") is technically
   incorrect: Aut-equivariance is enough to identify cocycles up to
   coboundary (the D-VAN modular-data quotient), but is NOT enough to
   identify subgroups for restriction purposes. The kernel of res to a
   single max EA is generally non-trivial even after Aut quotienting.

3. The **m=5 agent fix uses 112 of 4590 G-conjugacy classes** of max
   EAs in E_+(5). The choice is structural (32 axis-aligned +
   80 diagonal-pair-swap Lagrangians) but is NOT proven from
   Quillen 5.10 / Harada-Kono 1.1. It is **empirically sufficient**
   (0/165 erroneous trivials) but the math soundness has not been
   established. The 112-Lagrangian fix is therefore *empirically*
   valid at m=5 but *theoretically* under-justified.

4. The **m=7 prediction** is: 9 845 550 total Lagrangians, 1 Aut-orbit,
   and the same "axis-aligned + diagonal-pair-swap" extension would
   give 296 representatives (128 axis + 168 pair-swap). At 454
   generators of H^3(E_+(7); U(1)), this requires careful validation
   before relying on it.

The 112-Lagrangian m=5 fix **is mathematically sound conditional on
the empirical 0/165 finding**, but the underlying soundness argument
is incomplete. Section 6 below records the errata.

---

## 1. Background: the question

D-VAN (issue #148, parent #142) computes the kernel of
res: H^3(E_+(m); U(1)) -> H^3(E; U(1)) ⊕ H^3(D_8; U(1)) ⊕
H^3(Q_8; U(1)) and uses vanishing on this kernel as the "is this
modular data trivial" verdict for twisted Drinfeld doubles. The
correctness of D-VAN depends on this restriction being **injective**
on H^3(G; U(1)).

The current `detecting_family_restriction.g` (at origin/main =
2b0ac00) uses `ConjugacyClassesSubgroups(G)` to enumerate the
detecting family. At m=5 this OOMs at 32 GB. The fix on
`dvan-m5-direct-subgroup-construct` (commit 051d1aa, issue #287)
replaces the enumeration with a direct construction of 112
maximal-EA subgroups (32 axis-aligned + 80 diagonal pair-swap
Lagrangians in F_2^{10}). Empirically: 0/165 erroneous trivials at
m=5.

Two surprising empirical findings need reconciliation against the
AM04 / Quillen / Harada-Kono literature:

* **At m=2 with one EA + D_8 + Q_8, 2/10 unit generators erroneously
  reported trivial**. The fix at m=2 uses all 6 G-conj-class reps of
  max EAs (cured); but the question stands: why does "one of each"
  fail?

* **The 112-Lagrangian m=5 enumeration covers 112/4590 of the total
  Lagrangians; it is empirically sufficient but its theoretical
  sufficiency is unclear**.

This audit reconciles both findings.

---

## 2. Theorem statements (with citations)

### 2.1 Quillen 1971, Theorem 5.10

Source: D. Quillen, "The Mod 2 Cohomology Rings of Extra-special
2-groups and the Spinor Groups", Math. Ann. 194 (1971), 197-212.

Local file: `docs/Quillen - The mod 2 cohomology of extra-special 2-groups
and the spinor groups.pdf`, p. 208.

**Theorem 5.10**: Let V be an F_2-vector space, Q a (possibly
degenerate) quadratic form on V, and V^~ the central extension
0 -> Z/2 -> V^~ -> V -> 0 classified by Q. Then the homomorphism

> H*(BV^~) -> ∏_W H*(B(W^⊥)^~)

is **injective**, where the product is over **all** maximal
Q-isotropic subspaces W ⊂ V, and (W^⊥)^~ is the preimage in V^~ of
W^⊥ ⊂ V (the maximal elementary abelian of rank dim(W^⊥) = m+1 in
E_+(m), where m = codim of W).

**Coefficient ring**: F_2 only.

**Hypotheses**: V finite-dimensional F_2; Q with hyperbolic-pair Witt
decomposition; the theorem applies to E_+(m) and E_-(m) without
restriction.

**Detection set**: "all maximal Q-isotropic subspaces". Not
G-conjugacy classes (which are the same as Lagrangians since the
extraspecial centre acts trivially on V); not Aut(G)-orbits. The
literal reading is **every Lagrangian**.

For E_+(m) (real type, + sign): the count of Lagrangians is
`N_+(m, 2) := prod_{i=0}^{m-1} (2^i + 1)`:

| m | N_+(m, 2) |
|---:|----------:|
| 1 | 2         |
| 2 | 6         |
| 3 | 30        |
| 4 | 270       |
| 5 | 4 590     |
| 6 | 151 470   |
| 7 | 9 845 550 |

(These match the GAP-computed counts of G-conj-classes of maximal EAs
in E_+(m) at m=2, 3.)

### 2.2 Quillen 1971, Theorem 4.6 (ring structure)

Same source, p. 205.

H*(BV^~; F_2) ≅ S(V*)/J ⊗ F_2[w_{2^h}] where J = (Q(x), B(x, x^2), …,
B(x, x^{2^{h-1}})) is the ideal generated by an iterated regular
sequence. Here h = codim of maximal Q-isotropic = m for E_+(m).

This is the explicit polynomial-ring structure that lets us *check*
Theorem 5.10 computationally — the maximal isotropic restrictions
collectively annihilate the ideal J.

### 2.3 AM04 §IV.4 Definition 4.2 + Theorem 4.3

Source: Adem-Milgram, *Cohomology of Finite Groups*, 2nd ed., Springer
2004.

Local file: `docs/bok%3A978-3-662-06280-7.pdf`, p. 138.

**Definition 4.2** (verbatim): "Let G be a finite group. We say that
H*(G; F_p) is *detected by abelian subgroups* if there is a *family*
of abelian subgroups H_i ⊂ G so that

> ⊔_i (res^G_{H_i})*: H*(G; F_p) -> ⊔_i H*(H_i; F_p)

is an injection."

**Theorem 4.3** (Quillen, p. 138): If H*(G; F_p) is detected by
abelian subgroups, then so is H*(G ≀ Z/p; F_p).

**Coefficient ring**: F_p (not Z).

**"Family"**: AM04 uses "family", not "conjugacy class set". The
family can be any sufficient collection; for E_+(m) the canonical
choice is the full set of maximal Q-isotropic preimages (by Quillen
5.10), which has cardinality N_+(m, 2) above. A single Aut(G)-orbit
representative is NOT a valid family in the AM04 sense unless that
single subgroup detects all of H*.

### 2.4 AM04 §IV.5 Theorem 5.6 (F-isomorphism)

Same source, p. 142.

The map φ: H*(G; F_p) -> lim_{A ∈ A_p(G)} H_A* has **nilpotent kernel
and cokernel**. Here A_p(G) is the category of non-trivial
p-elementary abelian subgroups of G, with morphisms = inclusion +
conjugation.

This is weaker than 5.10: the kernel is non-zero in general, only
nilpotent. So 5.6 does NOT give degree-3 injectivity directly. The
sharper 5.10 (specialised to extraspecial 2-groups) DOES give
injectivity in all degrees over F_2.

**Combined**: AM04 IV.5 + Quillen 5.10 give injectivity at F_2;
Harada-Kono lifts to Z; UCT lifts to U(1).

### 2.5 Harada-Kono 1987, Theorem 1.1

Source: Harada-Kono, "On the integral cohomology of extraspecial
2-groups", J. Pure Appl. Algebra 44 (1987), 215-219.

Local file: `docs/1-s2.0-0022404987900259-main.pdf`, p. 215.

**Theorem 1.1**: For E_+(m) with h(Q) >= 2, the cyclic summand A(k)
of H^k(E_+(m); Z) is of order 2^{a(k, Q)} for k ≡ 0 mod 4 and is
zero for k ≢ 0 mod 4. Here

> a(k, Q) = n(k) if n(k) ≤ h(Q) - 1, else h(Q) + 1.

For our target degree k = 4 (= H^3 with U(1) coefficients via UCT):
n(4) = 2.

| m (= h(Q)) | a(4, Q)        | A(4) of E_+(m) |
|:----------:|:--------------:|:--------------:|
| 2          | h(Q)+1 = 3     | Z/8            |
| ≥ 3        | n(k) = 2       | Z/4            |

The rest of H^4(E_+(m); Z) is elementary abelian 2-torsion, captured
by Quillen 5.10 via restriction to max EAs.

**Coefficient ring**: Z. Crucially the only source in the local lit
that does the integer-cohomology computation.

### 2.6 Pham 2000 / Adem-Karagueuzian 1997 (essential cohomology)

Source: P. A. Minh, "Essential Cohomology and Extraspecial p-Groups",
Trans. AMS 353 (5) (2000), 1937-1957.

Local file: `docs/S0002-9947-00-02689-1.pdf`, p. 1937.

The p = 2 case (quoted in Pham's introduction, attributed to Quillen
1971): "for p = 2 ... H*(G) is Cohen-Macaulay and Ess(G) = {0}, except
for the case G = Q_8". So Q_8 is the UNIQUE 2-group of order 8 with
non-zero essential cohomology — equivalently, the only 2-group of
order 8 in which every order-2 element is central. This is what
makes Q_8 mandatory in any detecting family for groups *containing*
Q_8 as a section (such as E_+(m) for m >= 2).

### 2.7 Synthesis for D-VAN at degree 3

Combining 5.10 + 1.1 + UCT (compatible with restriction):

> **Theorem (folklore)**: For G = E_+(m), m >= 2, the restriction
> map
>
>   res: H^3(G; U(1)) -> ⊕_{W ∈ ML} H^3((W^⊥)^~; U(1))
>                       ⊕ H^3(Q_8; U(1))
>
> is **injective**, where ML = the set of all maximal Q-isotropic
> subspaces of V = G/Z(G), and Q_8 is any quaternion section of G.
> (Adding D_8 is redundant by Q_8 but cheap.)

**Critical caveat**: "ML" is the FULL set of Lagrangians, cardinality
N_+(m, 2). Restricting to a single Lagrangian, or to a single Aut(G)
orbit, does NOT suffice.

---

## 3. Aut(G)-orbit counts of maximal EAs

Computed via GAP (`dvan_math_audit_orbits.g` in this directory);
results in `dvan_math_audit_orbits.out`. Empirical counts:

| m | \|G\|  | G-conj classes of max EA | Aut(G)-orbits | Orbit sizes |
|---|--------|--------------------------|---------------|-------------|
| 2 | 32     | 6                        | **1**         | [6]         |
| 3 | 128    | 30                       | **1**         | [30]        |

(m = 5, 7 are not directly computed due to the CPU cap and the
expense of `ConjugacyClassesSubgroups` at m >= 5 — the very problem
that motivated the m=5 fix. But the closed-form count gives
N_+(5, 2) = 4590, N_+(7, 2) = 9 845 550. Empirically at m = 2, 3 the
Aut(G)-orbit count is 1; by the same structural argument — Aut(G)
projects onto O^+(2m, 2) which acts transitively on Lagrangians of
the + type — we expect 1 Aut-orbit at every m >= 2.)

### 3.1 G-conj-class count matches the Lagrangian count

The G-conj-class count of max EAs equals N_+(m, 2). This is because:

* Inner automorphisms of E_+(m) act trivially on V = G/Z (since V is
  abelian); so G-conjugacy of subgroups preimage-lifts to V-equality.
* Distinct maximal Q-isotropic W, W' ⊂ V give distinct preimages
  (W^⊥)^~, (W'^⊥)^~ ⊂ G, and these are NOT G-conjugate (G acts
  trivially on V/{centre}).
* So G-conj-class count = number of maximal Q-isotropic subspaces
  = N_+(m, 2).

Verified at m=2 (count 6 = 1·3·... actually 2·3) and m=3 (count
30 = 2·3·5). Identification is exact.

### 3.2 Aut(G)-orbit count = 1 (at m = 2, 3 confirmed)

The full Aut(E_+(m)) projects onto O^+(2m, 2) (the orthogonal group
preserving the quadratic form). O^+(2m, 2) acts **transitively** on
maximal Q-isotropic subspaces of + type (standard, Wilson "The Finite
Simple Groups" §3.7 or Taylor "Geometry of Classical Groups" Ch. 11),
so it acts transitively on the G-conj-classes. Hence
1 Aut-orbit at every m >= 2. Empirically confirmed at m = 2, 3.

### 3.3 The "single rep per Aut-orbit" approach FAILS

If we pick one rep per Aut-orbit, we get **1 max EA** (independent of
m >= 2). The m=2 empirical probe (`dvan_math_audit_m2_anomaly.g` in
this directory; results in `dvan_math_audit_m2_anomaly.out`) confirms
that
restriction to a single max EA + D_8 + Q_8 reports trivial for
generators 1 and 5 of H^3(E_+(2); U(1)), but these classes are NOT
trivial under the full 6-EA family: their restriction to OTHER max
EAs is non-zero. This is the 2/10 erroneous-trivials finding.

**Why does "Aut-orbit reduction" fail?** Aut(G) acts on subgroup
*set*s, and on the cohomology H^*(G; U(1)) (since cocycles are
Aut(G)-equivariant up to the standard Aut-action on coefficients).
But the kernel of `res: H^* -> H^*(H_1)` is generally NOT preserved
by the Aut-action: an automorphism φ sends `ker(res_{H_1})` to
`ker(res_{φ(H_1)})`, not to itself. So even if Aut acts transitively
on {H_i}, the union of kernels is strictly larger than the kernel of
any single restriction, and the intersection of kernels (which is
what 5.10 says is zero) requires the full set.

**Aut-equivariance is only useful at the cocycle-mod-coboundary
level**, not at the subgroup level. For D-VAN's "is this class
trivial up to Aut(G)?" question, the relevant kernel is

> ker_{Aut} := { ω : Aut(G) · ω ∩ (zero class) ≠ ∅ }

This is the *image* of Aut(G) in H^3, not the kernel of any single
restriction; and it is properly handled by the existing
`AutomorphismOrbits` machinery in `modular_data.g`. The detecting-
family question is orthogonal to it: we need ω to vanish in the FULL
restriction sum (so it's truly the zero class), not just up to Aut.

---

## 4. The 112-Lagrangian audit at m=5

### 4.1 Counts

* **N_+(5, 2) = 4590** maximal Q-isotropic Lagrangians in F_2^{10}.
* **G-conj-class count of max EAs in E_+(5) = 4590** (by §3.1).
* **Aut(E_+(5))-orbit count = 1** (by §3.2).
* **Agent's enumeration = 112** (= 32 axis-aligned + 80 diagonal
  pair-swap).

### 4.2 Soundness assessment

The agent's 112 enumeration is a structured **subset** of the 4590
Lagrangians. It is:

* **Sound** in the sense of "no false trivials by over-quotienting":
  restricting to 112 max EAs + D_8 + Q_8 can only IMPOSE constraints,
  not REMOVE them. Any class detected as non-trivial under the 112-EA
  family is genuinely non-trivial.

* **Empirically sufficient**: at m=5 with 165 generators, the
  m=5-fix run shows 0 erroneous trivials. Equivalently, every generator
  has non-zero restriction to at least one of the 112 EAs (or to D_8
  or Q_8). Verified by the agent in #287.

* **Theoretically under-justified**: there is no published theorem
  saying "112 specifically structured Lagrangians suffice for degree-3
  injectivity at m=5". The Quillen-Theorem-5.10 / Harada-Kono-1.1
  framework requires ALL 4590 in principle. The 112 is a heuristic
  enumeration; it works at m=5 only by virtue of the specific
  degree-3 structure of H^3(E_+(5); U(1)).

### 4.3 Why 112 works empirically (conjecture)

H^3(E_+(m); U(1)) is a quotient of H^3(E_+(m); Z) ≅ H^4(E_+(m); Z)
(via UCT) by the cyclic A(4) summand of order Z/4 (m >= 3) plus the
elementary abelian 2-torsion piece. The elementary abelian 2-torsion
sits inside H^3(E_+(m); F_2), and the F_2 cohomology has 165
generators in degree 3 at m=5 (matching the U(1) count up to a
factor).

The "axis-aligned" Lagrangians (32 of them) correspond to choices of
{a_i or b_i} from each symplectic pair (a_i, b_i) of the standard
basis of F_2^{2m}. These detect the rank-3 sub-multilinear pieces of
H^3 that decompose along the symplectic-pair structure.

The "diagonal pair-swap" Lagrangians (80 of them) correspond to
"mixing" two pairs (i, j) by an off-axis substitution. These detect
the cross-pair structure that pure axis-aligned cannot see.

These 112 generate (conjecturally) the **full image** of res in
deg-3 because the H^3 generators are sparse: they are bounded above
by C(2m+1, 3) = C(11, 3) = 165 (matching the empirical count), and
each generator has a "support" inside F_2^{2m} that is captured by
some axis-aligned or pair-swap Lagrangian.

**This is a conjecture**. A proof would require showing that
res|_{112 EAs}: H^3(G; F_2) -> ⊕ H^3(EA; F_2) is injective and then
lifting via UCT + Harada-Kono. The agent's empirical 0/165 is
*evidence* for the conjecture at m=5 but not a proof.

### 4.4 Risk at m=7

At m=7 with the same scheme (128 axis + 168 pair-swap = 296 EAs of
9 845 550 total, ~0.003% coverage), the conjecture extrapolation is
**riskier**:

* H^3(E_+(7); U(1)) has 454 generators (per #289), vs. C(15, 3) = 455
  upper bound — so the H^3 structure is still essentially "sparse
  multilinear" plus the cyclic A(4) = Z/4.
* The 128 axis-aligned Lagrangians still cover all degree-3
  monomials in a_i or b_i only.
* The 168 pair-swap Lagrangians cover C(7, 2) = 21 pairs × 8
  swap-variants = 168 cross-pair detections.
* But there are higher-order "triple-swap" / "quadruple-swap"
  configurations at m=7 that don't appear at m=5 due to the smaller
  number of pairs. These could potentially detect H^3 classes that
  the (1, 2)-pair-swap heuristic misses.

**Recommendation**: at m=7, either (a) extend to a full
{1-swap, 2-swap, 3-swap, ...} hierarchy and verify 0/454 erroneous
trivials, or (b) use the **Witt-decomposition machinery from
§7 of the methodology paper** to enumerate Lagrangians
**systematically up to a parametrised "depth"** and confirm
detection of every generator. The latter is the cleaner option.

---

## 5. m=7 recommendation

### 5.1 Aut-orbit count

By the same Aut(G) → O^+(2m, 2) projection argument as §3.2,
**Aut(E_+(7))-orbit count = 1**.

### 5.2 Enumeration strategy

**Recommendation**: do NOT extrapolate "112" naively to "296" at m=7.
Instead:

1. **Use the Witt-decomposition machinery (§7 of methodology paper)**
   to enumerate Lagrangians systematically. The Witt decomposition
   gives a CANONICAL parametrisation of Lagrangians of + type as
   (symplectic basis, Arf-zero choices) pairs.

2. **Cross-validate** at m=5 by running the Witt-decomposition
   enumeration against the agent's 112 and confirming that the 112
   correspond to a "depth-1 or depth-2 Witt slice" (whatever the
   correct formalisation is).

3. **Run depth-1, depth-2, ..., depth-d_max** at m=7 and watch for
   the "0 erroneous trivials" criterion to stabilise. Take the depth
   at which it stabilises as the m=7 enumeration.

4. **Theoretical confirmation**: if "depth-d" suffices at m=5, prove
   (via the Witt-decomposition / H^3 dual basis argument) that
   "depth-d'" suffices at m=7. This proof is OPEN and would be a
   genuine contribution to the methodology.

### 5.3 Numerical estimate

If "depth-2" suffices, the count at m=7 is:
* 128 axis-aligned (depth 1, no swaps).
* C(7, 2) * 8 = 168 single-swap (depth 2).
* Total: 296.

If "depth-3" is needed (one extra swap):
* + C(7, 3) * 8^2 = 35 * 64 = 2240 triple-swaps.
* Total: 2536.

If "depth-d" is needed for d up to 7:
* The full count is 9 845 550.

**Cost estimate**: for 296 Lagrangians + D_8 + Q_8 at m=7, with
`RestrictionMatrixViaHAP` at ~1-10 minutes per Lagrangian × 296 ≈
5-50 hours. Tractable in a single sweep with `subagent-driven-
development`. For 2536: ~40-400 hours, much harder; for the full
count, untractable.

---

## 6. Errata for the current code

### 6.1 R-1 lit survey "Step 3" is technically incorrect

File: `docs/superpowers/research/2026-05-17-detecting-family-literature.md`,
"Synthesis" section, Step 3.

The current text reads:

> "However: for E_+(m) every maximal elementary abelian is conjugate
> to a single one in Aut(G), so the restriction to one E (= "the"
> maximal elementary abelian of rank m+1) is injective on V modulo
> Aut(G), which is what we need at U(1)-coefficient level since
> cocycles up to coboundary are Aut(G)-equivariant."

**This is wrong**. Aut-transitivity does NOT imply "single rep
suffices" for injectivity. The kernel of `res_{EA_1}` is non-trivial
in general, and Aut(G) does NOT preserve it (it sends
`ker(res_{EA_1})` to `ker(res_{EA_2})`, not back to itself). The
empirical 2/10 finding at m=2 (this audit, §3.3) refutes this
reading.

The correct statement is: Quillen 5.10 requires the FULL set of
Lagrangians. The Aut-orbit reduction is valid only at the
*cocycle-mod-coboundary* level, not at the subgroup level.

**Fix**: rewrite Step 3 of the lit survey to (a) drop the "single
EA suffices modulo Aut" claim, (b) clarify that "all max EAs" is the
Quillen 5.10 requirement, and (c) cross-reference the empirical 2/10
finding.

### 6.1.bis Methodology paper §3.2 makes the same mis-statement

File: `writeup/methodology.md`, line 172 (in §3.2 "Proof sketch
(Quillen + Harada-Kono + UCT)").

Current text:

> "The summand V ⊂ H^4(G; Z) is detected by the integral-to-mod-2
> reduction inside H^4(G; F_2); restriction to ANY ONE maximal
> elementary abelian E (rank m+1) is then injective on V, since for
> E_+(m) the action of Aut(G) is transitive on maximal elementary
> abelians of given rank (a structural consequence of the
> orthogonal-group action on V)."

**The claim "restriction to any ONE maximal elementary abelian is
injective on V" is incorrect**: empirically refuted by the m=2 probe
above (§3.3 of this audit). Aut-transitivity does not imply
single-EA injectivity; Quillen 5.10 explicitly requires the FULL
product over all maximal Q-isotropic subspaces.

**Fix**: rewrite §3.2 of the methodology paper to use the FULL set of
G-conj-class reps of max EAs (i.e. the literal Quillen 5.10
statement), and explain that the Aut-transitivity is relevant only
for the *cocycle-mod-coboundary* quotient (handled separately by
`AutomorphismOrbits`), not for the restriction injectivity.

This is the SAME error as §6.1 (R-1 lit survey Step 3), propagated
to the methodology paper. Both need updating.

### 6.2 `quillen_detecting_subgroup.g` header comments

File:
`extraspecial_orbifolds/scripts/quillen_detecting_subgroup.g`,
lines 17-20:

> "[AM04, §IV.4-§IV.5 (Thm 4.3, Thm 5.6)] gives a detecting family
> consisting of:
>   * the m+1 conjugates of a maximal elementary abelian subgroup
>     (rank m+1 — the centre z together with m commuting σ_{a,1}); and
>   * one D_8 = E_+(1) section..."

The "m+1 conjugates" parenthetical is misleading. There are
N_+(m, 2) max EA G-conjugacy classes, not "m+1 conjugates". Also AM04
IV.4-IV.5 do NOT give the explicit detecting family; the actual
source is Quillen 1971 Theorem 5.10. AM04 IV.4 is the abstract
definition ("detected by abelian subgroups"); IV.5 is the nilpotent
kernel (F-isomorphism).

**Fix**: update the docstring to cite Quillen 1971 Thm 5.10 + Harada-
Kono 1987 Thm 1.1 + Pham 2000 (for the Q_8 essential class) as the
combined justification, with AM04 IV.4-IV.5 as the framework
reference only.

### 6.3 Soundness comment in the 112-Lagrangian m=5 fix

File (on `dvan-m5-direct-subgroup-construct` branch — not in this
worktree, but should be added before merging):

The fix should include a docstring acknowledging that:

1. The 112 enumeration is a **structured subset** of 4590 total
   Lagrangians.
2. Its sufficiency at m=5 is **empirical** (0/165 erroneous
   trivials) not theoretical.
3. The Aut-orbit count is 1, so "one rep per Aut-orbit" reduction is
   inapplicable; the 112 is justified by the "axis + pair-swap"
   heuristic, not by Quillen 5.10's "all Lagrangians" requirement.
4. At m=7 the same heuristic gives 296 of ~10M Lagrangians, ~0.003%
   coverage; sufficiency should be re-verified empirically before
   relying on it for production.

### 6.4 Future work: prove the "depth-d Witt-slice suffices" conjecture

This audit identifies the math gap: the agent's heuristic
"axis-aligned + diagonal pair-swap" enumeration empirically works at
m=5 but lacks theoretical justification. A genuine proof — using the
Witt-decomposition (methodology paper §7) and the explicit Harada-Kono
+ Quillen ring structure — would establish that, e.g., depth-2 (=
axis + single-pair-swap) Lagrangians suffice for degree-3 detection
at all m. This is open work.

Such a proof would also let us *compute* the correct enumeration
depth at m=7 (e.g. depth-3 may be needed there) without empirical
trial-and-error.

---

## 7. References

* [Quillen71] D. Quillen, "The Mod 2 Cohomology Rings of Extra-special
  2-groups and the Spinor Groups", *Math. Ann.* **194** (1971),
  197-212. Local file: `docs/Quillen - The mod 2 cohomology of
  extra-special 2-groups and the spinor groups.pdf`.
* [AM04] A. Adem and R. J. Milgram, *Cohomology of Finite Groups*,
  2nd ed., Springer GMW 309 (2004). Local file:
  `docs/bok%3A978-3-662-06280-7.pdf`.
* [HK87] M. Harada and A. Kono, "On the integral cohomology of
  extraspecial 2-groups", *J. Pure Appl. Algebra* **44** (1987),
  215-219. Local file: `docs/1-s2.0-0022404987900259-main.pdf`.
* [Pham00] P. A. Minh, "Essential Cohomology and Extraspecial
  p-Groups", *Trans. AMS* **353** (5) (2000), 1937-1957. Local file:
  `docs/S0002-9947-00-02689-1.pdf`.
* [Wilson09] R. A. Wilson, *The Finite Simple Groups*, Springer GTM
  251 (2009), §3.7 (orthogonal groups O^+(2m, q), Witt's theorem,
  Lagrangian counts).
* R-1 lit survey:
  `docs/superpowers/research/2026-05-17-detecting-family-literature.md`.
* Methodology paper §7: `writeup/section_7_witt_decomposition.md`
  (Witt-decomposition machinery + F_2 Gauss sums).
* Issues: #287 (the fix), #289 (this audit), #142 (D-VAN EPIC),
  #148 (D-VAN-7), #154 (D-VAN-MATH), #193 (R-1).

## 8. GAP probe artefacts

The following are the live GAP outputs that anchor this audit. They
are reproducible by re-running the scripts (copies persisted alongside
this note for convenience).

* `dvan_math_audit_orbits.g` + `.out`: Aut(G)-orbit and G-conj-class
  counts of max EAs at m = 2, 3. Confirms 1 Aut-orbit at both, with
  G-conj-class counts 6 and 30 respectively, matching the closed form
  N_+(m, 2) = prod_{i=0}^{m-1} (2^i + 1).

* `dvan_math_audit_m2_anomaly.g` + `.out`: the m=2 empirical probe
  confirming 2 of 10 unit generators (specifically gens 1 and 5) have
  zero restriction to a single max EA + D_8 + Q_8 but are detected by
  another max EA. Confirms the issue #289 anomaly is a genuine
  Quillen-5.10 requirement, not a bug.

* `dvan_math_audit_lagrangians.g` + `.out`: closed-form Lagrangian
  counts at m = 1 through 7, and the prediction
  N_+(7, 2) = 9 845 550.

Note: `dvan_math_audit_lagrangians.out` contains an additional
"TotalLagrangians = 2 * N_+" exploratory block that was a wrong-track
hypothesis during the audit. The correct G-conj-count = N_+(m, 2)
identification is documented in §3.1 of this note; the closed-form
values used here (6, 30, 270, 4590, 151470, 9845550) are the
N_+(m, 2) values from the first block of `.out`.

