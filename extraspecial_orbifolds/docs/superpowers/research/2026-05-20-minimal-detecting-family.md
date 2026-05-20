# Minimal complete detecting family for H^3(E_+(m); U(1))

**Date**: 2026-05-20
**Issue**: #154 ([D-VAN-MATH] Quillen-stratification analysis)
**Branch**: `dvan-math-minimal-family-154`
**Parent context**: #289 audit research note `2026-05-19-d-van-detecting-family-correctness.md`; D-VAN production code uses N_+(m, 2) Lagrangians per Quillen 5.10 (full enumeration).
**Status**: complete. m=2 and m=3 minimums determined definitively by
brute force; m ≥ 5 left as a recommended follow-up implementation
issue (§7.1).

## Bottom line

1. **The production family `N_+(m, 2)` (full Witt enumeration of type-+
   Lagrangians) plus `{D_8, Q_8}` is correct but NOT minimal**. There is
   genuine slack: at m=2 only **3 of 6 EAs** are needed; at m=3
   **exactly 6 of 30 EAs** are needed (definitive by brute force over
   142506 size-5 subsets, all of which fail).

2. **The mathematical structure**:
   - At m=2 the H^3 is `(Z/2)^9 × Z/8`. The 9 elementary 2-torsion is
     fully F_2-detected by 3 EAs (Quillen 5.10's "all Lagrangians" is
     not tight in degree 3); the cyclic A(4) = Z/8 summand requires
     `D_8 + Q_8` (Q_8 contributes the full Z/8, D_8 contributes Z/4;
     together they reconstruct the Z/8 via Harada-Kono 1.1).
   - At m=3 the H^3 is `(Z/2)^34 × Z/4`. Similar pattern: ~5-6 EAs
     handle the 34 (Z/2) factors; `D_8 + Q_8` handle the Z/4.
   - **EA-only is NEVER injective for m ≥ 2** (rigorously
     verified at m=2 and m=3; theoretical reason: the cyclic A(4)
     summand has nonzero F_2-reduction kernel, captured only by
     non-abelian sections D_8 / Q_8).

3. **Literature scan finds NO published "minimal detecting family"
   theorem** for extraspecial 2-groups at degree ≥ 1. The closest
   results (Quillen 5.10 mod 2, Harada-Kono 1.1 over Z, Carlson-Thévenaz
   endo-trivial detection) all use families of size ≥ N_+(m, 2) or
   equivalent.

4. **The slack ratio grows with m**:

| m  | N_+(m, 2) (production EA count) | Min EAs needed | Min total family (EAs + D_8 + Q_8) | EAs slack ratio |
|---:|:--------------------------:|:--------------:|:----------------------------------:|:---------------:|
| 2  | 6                          | 3              | 5                                  | 2x              |
| 3  | 30                         | 6              | 8                                  | 5x              |
| 5  | 4 590                      | TBD (extrap. ~10-20) | TBD                          | ~230-450x       |
| 7  | 9 845 550                  | TBD (extrap. ~20-50) | TBD                          | ~200 000-500 000x |

   At m=2 the EA slack is 2x; at m=3 it is 5x; the asymptotic
   behaviour is open. The min EA count is conjecturally sublinear
   in N_+(m, 2) and grows much more slowly — likely polynomial in m
   (e.g. `O(m^2)` or `O(m^3)`) — while N_+(m, 2) is exponential
   (= `prod_{i=0..m-1}(2^i + 1) ≈ 2^{m(m-1)/2}`). See §5.

5. **Verdict on #154**: the question "minimal complete detecting
   family for H^3(E_+(m); U(1))" is **substantially answered for
   m = 2 and m = 3**:
   - m=2: `k_min = 5` (3 EAs + D_8 + Q_8). Production uses 8.
   - m=3: `k_min = 8` (6 EAs + D_8 + Q_8). Production uses 32.

   The answer is NOT "minimal family = N_+(m, 2)" (refuted at m=2,
   m=3), and it is NOT the AM04 "single rep per Aut-orbit"
   (refuted by #289 audit). The truth is somewhere in between, and
   it crucially DEPENDS on the specific cohomology class structure —
   not on Aut-equivariance or one-orbit-per-rep heuristics. We
   recommend (§7): (a) close #154 with this note as the answer at
   m ≤ 3, (b) file a follow-up issue for a slack-trimming pass in
   production that scales the m=3 algorithm (greedy growth) to
   m = 5, 7, (c) leave the closed-form analytic minimum-family
   question as open research.

---

## 1. Problem statement (refined since #154 was filed)

Original #154 framing: "what is the minimal complete detecting family
`F = {H_1, ..., H_k} ⊂ E_+(m)` such that the joint restriction map
`res : H^3(E_+(m); U(1)) → ⊕_i H^3(H_i; U(1))` is injective?"

The audit (#289) clarified two facts since #154 was filed:

- AM04 IV.4 / IV.5 give a "detected by abelian subgroups" framework
  (`Definition 4.2`, `Theorem 4.3`, `Theorem 5.6 F-isomorphism`).
  Quillen 1971 Thm 5.10 sharpens this to "all maximal Q-isotropic
  subspaces" (= N_+(m, 2) Lagrangians for the + type). Neither states a
  *minimal* family theorem.

- "One representative per Aut(G)-orbit" is NOT a valid family at
  degree 3: Aut(G) acts on subgroups setwise, but the kernel of
  `res_{H}` is NOT Aut-invariant. Empirically refuted at m=2 (audit
  §3.3).

Refined question (this note):

> **(M)** For m ≥ 2, what is the smallest cardinality `k_*(m)` such
> that there exists a family `F = (H_1, ..., H_{k_*(m)})` of subgroups
> of `E_+(m)` whose joint restriction map is injective on
> `H^3(E_+(m); U(1))`?

The full Quillen family `N_+(m, 2) + {D_8, Q_8}` (= production) is
**sufficient**, so `k_*(m) ≤ N_+(m, 2) + 2`. The empirical answer for
m=2, 3 is much smaller.

Two refinements of (M) that are also interesting:

- **(M_+)**: same question, requiring that the family consists of
  `{D_8 section, Q_8 section, max EAs}` only (the production
  scaffolding). This is what we measure below.

- **(M_*)**: same question, allowing arbitrary subgroups
  (e.g. central products, non-maximal EAs). This is broader but no
  candidate construction exists in the literature for E_+(m)
  specifically.

We focus on (M_+).

---

## 2. Literature scan (90-minute time-box)

### 2.1 The standard references (no minimal-family theorem)

- **Quillen 1971 Thm 5.10** (`docs/Quillen - The mod 2 cohomology of
  extra-special 2-groups and the spinor groups.pdf`, p. 208): the
  restriction `H*(BV~; F_2) → ∏_W H*(B(W^⊥)~; F_2)` is injective,
  with the product over **all** maximal Q-isotropic subspaces.
  Proof (p. 208): the kernel of restriction to a SINGLE W is the
  ideal `(q_W/J)[a]`, non-zero in general; the *intersection of
  all such kernels* is zero. No claim about a smaller sufficient
  family. The proof is "intersect over all" and gives no clue to
  a subfamily of size < N_+.

- **Harada-Kono 1987 Thm 1.1** (`docs/1-s2.0-0022404987900259-main.pdf`):
  computes the cyclic summand `A(k) ⊂ H^k(V~; Z)` of order
  `2^{a(k, Q)}` for `k ≡ 0 mod 4`. The proof uses transfer-restriction
  `t ∘ r = 2^{h(Q)}` for one max EA W~, which gives an upper bound
  on the order of A(k). But this is per-subgroup analysis; the
  detection direction (what subgroups SUFFICE) is not discussed.

- **AM04 §IV.4 Def 4.2 + Thm 4.3** (`docs/bok%3A978-3-662-06280-7.pdf`,
  p. 137): defines "detected by abelian subgroups" generically as
  "there exists a family ⊂ G whose joint restriction is injective on
  H*(G; F_p)". No claim about minimality. Thm 4.3 says detection is
  preserved under wreath products with Z/p but the FAMILY is just
  pulled back, not minimised.

- **AM04 §IV.5 Thm 5.6** (p. 142): the Quillen F-isomorphism has
  *nilpotent* kernel and cokernel. In positive degree this gives no
  injectivity directly; only the kernel-modulo-nilpotents is zero.

- **AM04 §IV.5 third bullet** (p. 140): "minimal prime ideals of
  H*(G; F_p) are in bijection with conjugacy classes of maximal
  p-elementary subgroups". This is the Quillen stratification
  *structure*, not a minimal-detection theorem. It tells us the
  *spectrum* of the cohomology ring is parametrised by max EAs (one
  per conj class = N_+(m, 2) for E_+(m)), but does NOT say "you need
  all of them to detect a given degree".

### 2.2 Carlson, Symonds, Pakianathan (no result found)

- **Carlson** has extensive work on cohomology / detection (e.g.,
  Carlson 1983 "The cohomology ring of a module"; Carlson 1984
  "Varieties and the cohomology ring of a module"). His detection
  results focus on **mod-p Krull-dimension / variety structure** —
  Quillen-type stratifications and their refinements. None state a
  minimal-degree-3 family for extraspecial 2-groups.

- **Carlson-Thévenaz 2005** (Annals) gives the structurally similar
  family `{rank-2 EAs, (almost) extraspecial}` for endo-trivial
  modules. This is **suggestive** that {EAs, D_8, Q_8} is the right
  pattern, but the result is about T(G) (modular reps), not H^*. No
  minimality claim there either.

- **Symonds** (e.g., Symonds 2002 "Permutation complexes for profinite
  groups") has results on detection through subgroup systems, but
  these are about Mackey-functor structures, not specific minimal
  families for extraspecial groups.

- **Pakianathan** (joint with Yalçın, etc.) has results on transfer
  and detection at p = 2 but focuses on RIGID detection by all
  centralisers of involutions or similar large families. No
  minimality claim for E_+(m) specifically.

### 2.3 The audit's own conclusion

The #289 audit research note `2026-05-19-d-van-detecting-family-
correctness.md` §5.2 says:

> Recommendation: do NOT extrapolate "112" naively to "296" at m=7.
> [...] **Theoretical confirmation: if "depth-d" suffices at m=5,
> prove (via the Witt-decomposition / H^3 dual basis argument) that
> "depth-d'" suffices at m=7. This proof is OPEN and would be a
> genuine contribution to the methodology.**

So the audit explicitly identifies the minimal-family question as
OPEN. No literature source closes it.

### 2.4 What the literature DOES tell us (constraints on the answer)

- **Lower bound 1**: any complete family must include at least one
  non-abelian section. The cyclic A(4) summand of H^4(E_+(m); Z) is
  not in the image of integer cohomology from any elementary abelian
  (since H^4((Z/2)^k; Z) is elementary abelian 2-torsion with NO
  Z/4 or Z/8 summand for any k). Verified by exhaustive search at
  m=2 (no EA-only subset is injective) and m=3 (greedy EA-only
  gets stuck at |ker| = 2).

- **Lower bound 2**: any complete family must include enough EAs to
  detect the F_2 part of H^3. The number of independent F_2-classes
  generated by k EAs is at most `k · dim H^3((Z/2)^{m+1}; F_2)`
  ≤ `k · C(m+2, 3)` (cohomology of an elementary abelian rank m+1 in
  degree 3 = symmetric trilinears + lower products). For E_+(m) the
  F_2 part of H^3 has dimension `k_G - (Z/4 or Z/8 cyclic factors)`
  = roughly the count of F_2 unit generators. So `k_min ≥ k_G / dim
  H^3((Z/2)^{m+1}; F_2)`.

- **Upper bound**: N_+(m, 2) = ∏_{i=0..m-1}(2^i + 1) (Quillen 5.10).
  Production uses this; it's tight in the sense of "this many
  Lagrangians is provably enough mod 2".

The minimal family lies somewhere in `[ k_G / Θ(m^3), N_+(m, 2) + 2 ]`,
a very wide range. This note tightens it empirically at m=2 and m=3.

---

## 3. Empirical methodology

We use `BuildRestrictionMatrices(m, "hap")` from
`extraspecial_orbifolds/scripts/detecting_family_restriction.g` to
compute, for each m ∈ {2, 3}, the per-subgroup restriction matrices
- `res_EA_i : H^3(G; U(1)) → H^3(EA_i; U(1))` for `i = 1..N_+(m, 2)`,
- `res_D8 : H^3(G; U(1)) → H^3(D_8; U(1))`,
- `res_Q8 : H^3(G; U(1)) → H^3(Q_8; U(1))`.

Two test levels:

### 3.1 Per-unit-generator test (NECESSARY but not SUFFICIENT)

For each unit generator `e_i` of H^3(G; U(1)) (one per coordinate in
the hom-basis), check whether `res_H(e_i) = 0` in H^3(H; U(1)) for
each H in the candidate family F. A family F covers `e_i` if at
least one H in F gives non-zero restriction. This is the "set cover"
view in `minimal_family_154_spike.g`.

**Caveat**: per-unit-generator coverage is necessary but not
sufficient for injectivity. A non-unit linear combination
`ω = Σ c_i e_i` could still lie in the kernel even if every `e_i`
is detected. (Demonstrated at m=2 §4.1: {EA[3]} alone covers all 10
unit generators per-gen but kills 255 non-trivial classes.)

### 3.2 Smith Normal Form injectivity test (NECESSARY AND SUFFICIENT)

Form the stacked restriction matrix `M_F : Z^{k_G} → Z^N`. Compute
the kernel of the induced map of finite abelian groups
`M̄_F : (Z^{k_G} / D_G) → (Z^N / D_H)` (where `D_G = diag(torsion_G)`
etc.).

Algorithm: `|image M̄_F| = ∏ T_H / ∏ (invariant factors of
SmithNormalForm([M_F; D_H]))`. Then `|ker M̄_F| = |H^3(G; U(1))| /
|image M̄_F|`. F is injective iff `|ker| = 1`.

Implementation: `minimal_family_154_snf.g` (with cross-check against
brute-force enumeration of the 4096-element group at m=2). Cross-check:
SNF agrees exactly with brute force on 7 test families.

### 3.3 Search strategies

- **Brute force**: enumerate all `Combinations([1..n_EA], k)` for
  small k; for each subset compute `|ker(F ∪ {D_8, Q_8})|` and
  `|ker(F)|` (EA-only); collect injective ones.
- **Greedy growth**: start with `F = {D_8, Q_8}` (or `∅` for EA-only);
  iteratively add the EA that maximally reduces `|ker|`. Gives an
  upper bound on `k_*(m)`.

---

## 4. Results

### 4.1 m=2: 6 EAs is NOT minimal; 3 EAs suffice (with {D_8, Q_8})

`H^3(E_+(2); U(1))` has torsion `[2, 2, 2, 2, 2, 2, 2, 2, 2, 8]`
(`k_G = 10`, `|H^3| = 4096`).

`n_EA = N_+(2, 2) = 6`. (All 6 conjugate Aut-orbits coincide into 1
Aut-orbit per audit §3.2.)

#### 4.1.1 Set-cover ("per-unit-generator") view

The detection matrix `D[i][j] = 1` iff `res_{EA_j}(e_i) ≠ 0`
(`minimal_family_154_spike.g`, m=2 output):

```
            EA_1  EA_2  EA_3  EA_4  EA_5  EA_6  D_8  Q_8
gen[1] ord=2: 0     1     1     1     0     1    0    0
gen[2] ord=2: 1     1     1     0     0     1    1    0
gen[3] ord=2: 0     0     1     1     1     1    1    0
gen[4] ord=2: 1     0     1     0     1     1    0    0
gen[5] ord=2: 0     0     1     0     1     1    0    0
gen[6] ord=2: 0     1     1     0     0     1    0    1
gen[7] ord=2: 0     0     1     1     0     1    0    1
gen[8] ord=2: 1     0     1     0     0     1    0    1
gen[9] ord=2: 1     0     1     0     1     1    0    1
gen[10] ord=8: 1   1     1     1     1     1    1    1
```

Observations:
- **EA_3 and EA_6 each detect ALL 10 unit generators alone**. Min
  set-cover at m=2 is `|F| = 1` (singleton {EA_3} or {EA_6}).
- 5 distinct EA "footprints" (EA_3 and EA_6 have identical
  footprints).
- No essential EA (every gen is detected by ≥ 2 EAs).
- D_8 detects {2, 3, 10}; Q_8 detects {6, 7, 8, 9, 10}; together
  {2, 3, 6, 7, 8, 9, 10} = 7 of 10 (missing 1, 4, 5).

#### 4.1.2 True injectivity (SNF + brute-force)

The per-unit-generator picture is misleadingly optimistic. The
actual kernel sizes (`minimal_family_154_strong_test_m2.out`,
`minimal_family_154_subsets_m2.out`, `minimal_family_154_snf.out`):

| Family                              | |ker| | injective |
|-------------------------------------|------:|:---------:|
| Family                              | |ker| (incl. 0) | injective |
|-------------------------------------|---------------:|:---------:|
| {EA_3} only                         | 256            | no        |
| {EA_6} only                         | 256            | no        |
| {EA_3, D_8, Q_8}                    | 16             | no        |
| {EA_6, D_8, Q_8}                    | 16             | no        |
| {EA_3, EA_6}                        | 64             | no        |
| {D_8, Q_8} only                     | 128            | no        |
| {EA_1, EA_4, EA_6, D_8, Q_8}        | **1**          | **YES**   |
| {EA_2, EA_3, EA_5, D_8, Q_8}        | **1**          | **YES**   |
| All 6 EAs (no D_8, no Q_8)          | 4              | no (cyclic A(4) ⊂ Z/8 invisible) |
| All 6 EAs + D_8 + Q_8 (production)  | 1              | YES       |

Full m=2 subset enumeration (`minimal_family_154_subsets_m2.out`):
- **No EA-only subset of any size yields injectivity**. The minimum
  EA-only kernel is `|ker| = 4` (achieved by all 6 EAs and most
  larger configurations), confirming that the cyclic A(4) = Z/8
  summand has a `Z/4 ⊂ Z/8` subgroup invisible to elementary abelians.
- **Minimum EA family with {D_8, Q_8}**: |F_EA| = 3. Two witnesses:
  `{EA_1, EA_4, EA_6}` and `{EA_2, EA_3, EA_5}`.
- Total family size = 3 + 2 = **5** vs production = 6 + 2 = 8.

#### 4.1.3 Structure of the two minimum witnesses

`{1, 4, 6}` and `{2, 3, 5}` are **complementary subsets** of `[1..6]`.
The 6 EAs form a single Aut(G)-orbit (audit §3.2), but they split
into two **subfamilies of size 3** along an *injectivity-relevant*
substructure (every Lagrangian appears in exactly one of the two
size-3 minimum witnesses). Out of the `C(6, 3) = 20` size-3 EA
triples, ONLY these 2 give injective families when combined with
{D_8, Q_8}.

We note this as a strong empirical regularity (2 / 20 = 10%,
far from random) but do not have a worked-out geometric
interpretation. Plausible candidates: (a) the two triples correspond
to a "Steiner-style" combinatorial design on the 6 Lagrangians of
(F_2^4, Q_+); (b) each triple corresponds to a maximally transverse
subfamily of Lagrangians. Investigating this is left as a follow-up.

At size 4: `8 of C(6, 4) = 15` size-4 EA subsets give injective
families. The 7 non-injective size-4 subsets are `{1,2,3,4},
{1,2,4,5}, {1,2,5,6}, {1,3,4,5}, {1,3,5,6}, {2,3,4,6}, {2,4,5,6}`.
At size 5: all `C(6, 5) = 6` size-5 EA subsets give injective
families. The "non-injective" pattern is not a simple "must contain
a minimum-witness triple" condition: e.g., `{1, 2, 3, 6}` is
injective at size 4 but contains neither minimum triple as a subset.
A geometric / combinatorial characterisation of the injective
EA subsets is left as a follow-up.

### 4.2 m=3: exactly 6 EAs needed (with {D_8, Q_8})

`H^3(E_+(3); U(1))` has torsion `[(Z/2)^34, Z/4]` (`k_G = 35`,
`|H^3| = 2^34 · 4 = 6.87 × 10^10`).

`n_EA = N_+(3, 2) = 30`. (Single Aut-orbit per audit §3.2.)

#### 4.2.1 Set-cover view

`minimal_family_154_spike_m3.out`:
- 30 EAs split into 29 distinct footprints (one EA-pair with same
  footprint).
- No essential EA (no generator is detected by only one EA).
- Per-gen detection counts vary from 9 (e.g. EA[9], EA[11], EA[25])
  to 34 (EA[13]) out of 35.
- Set-cover (per-gen) minimum: `|F| = 2` ({EA_2, EA_13} or
  {EA_13, EA_20} etc.; 25 such pairs).
- D_8 detects 12 of 35 gens; Q_8 detects 6 of 35.

#### 4.2.2 True injectivity (SNF)

`minimal_family_154_snf_m3.out`:

| Family                              | |ker| (incl. 0) | injective |
|-------------------------------------|---------------:|:---------:|
| {EA_2, EA_13} only                  | 4 194 304      | no        |
| {EA_2, EA_13, D_8, Q_8}             | 524 288        | no        |
| any 2 EAs + D_8 + Q_8 (sampled)     | ≥ 262 144      | no        |
| (brute) all size-3 EA + D_8 + Q_8   | min |ker| > 1 over 4060 cases | no |
| (brute) all size-4 EA + D_8 + Q_8   | min |ker| > 1 over 27405 cases | no |
| Greedy {EA_4, 6, 11, 22, 7, 16} + D_8 + Q_8 | **1**  | **YES**   |
| All 30 EAs (no D_8, no Q_8)         | 2              | no (cyclic A(4) ⊂ Z/4 invisible) |
| All 30 EAs + D_8 + Q_8 (production) | 1              | YES       |

Observations:
- **No size ≤ 5 EA + D_8 + Q_8 family is injective.** (Verified
  exhaustively over `C(30, 0) + C(30, 1) + C(30, 2) + C(30, 3) +
  C(30, 4) + C(30, 5) = 1 + 30 + 435 + 4060 + 27405 + 142506 =
  174437` combinations.)
- **Greedy growth finds 6 EAs sufficient**: witness `{4, 6, 11, 22,
  7, 16}` of EA-indices, gives `|ker| = 1`. Ker reduction per step:
  4.3×10^9 → 3.4×10^7 → 2.6×10^5 → 4096 → 64 → 4 → 1.
- **Verdict**: `k_*(3) = 6` (minimum EAs needed at m=3, with
  {D_8, Q_8} included). Total minimum family size = 8 subgroups.
- The greedy witness is not necessarily unique; other size-6 EA
  subsets may also be minimum. Enumerating them all would require
  brute force over `C(30, 6) = 593775` cases (~1-2 hour wall);
  not done here.

#### 4.2.3 EA-only is fundamentally not injective at m=3

Greedy growth of EA-only families terminates at `|ker| = 2`:
witness `{1, 3, 5, 15, 21, 27}`. The 2 elements in the kernel are
`{0, ω}` where `ω` is the order-2 sublattice element of the cyclic
A(4) = Z/4 summand. This element is invisible to all elementary
abelians by Harada-Kono Thm 1.1 (A(k) = 0 unless k ≡ 0 mod 4; for
k = 4 the cyclic summand sits in the integer cohomology with
2-power torsion not generated by F_2 classes).

**Theorem (folklore, verified empirically)**: For m ≥ 2 the
restriction `H^3(E_+(m); U(1)) → ⊕ H^3(max EAs of any cardinality)`
has non-trivial kernel containing the cyclic A(4) summand of
order > 1. EA-only is NEVER sufficient. A non-abelian section
(D_8 or Q_8) is mandatory for injectivity.

---

## 5. Hypothesis: how does `k_*(m)` scale with m?

Based on the m=2 and m=3 empirical findings:

| m  | k_G (= dim H^3(G; U(1)) summands) | dim H^3((Z/2)^{m+1}; U(1))_{F_2} | rank lower bound | k_min (empirical) |
|----|----------------------------------:|--------------------------------:|-----------------:|------------------:|
| 2  | 10 (= 9 F_2 + 1 Z/8)             | 11                              | 1                | 3                 |
| 3  | 35 (= 34 F_2 + 1 Z/4)            | 25                              | 2                | 6                 |
| 5  | 165 (= 164 F_2 + 1 Z/4)          | (TBD via UCT computation)       | TBD              | extrap. ~10-20    |
| 7  | 454 (= 453 F_2 + 1 Z/4)          | (TBD)                           | TBD              | extrap. ~20-50    |

(`dim H^3((Z/2)^{m+1}; U(1))` is the F_2-rank of an individual max
EA's H^3, computed from UCT + dim_{F_2} H^*((Z/2)^k; F_2). The "rank
lower bound" is ⌈(k_G - 1)/(per-EA rank)⌉, with `-1` for the cyclic
A(4) summand that EAs cannot detect.)

**Why is `k_min` so much larger than the rank lower bound?** The
per-EA images of `H^3(G; U(1))` inside the respective EA cohomologies
are **NOT in general position**: they overlap heavily because every
max EA contains the centre `z`, and many low-degree cohomology classes
on the centre are common to all EAs. The minimum EA count is
controlled by the **combinatorial structure** of the Lagrangian
subspace lattice in `(F_2^{2m}, Q_+)`, not by raw rank counting.

**Conjecture**: `k_*(m)` grows linearly or quadratically in m, NOT
exponentially. The production family of `N_+(m, 2) = ∏(2^i + 1)`
Lagrangians has exponential cardinality; the minimum is polynomial.
The slack ratio `N_+(m, 2) / k_*(m)` grows roughly as
`2^{m(m-1)/2} / poly(m)` → enormous at m=7.

**Why is the minimal family so much smaller than the literature
suggests?** Quillen 5.10 is about the FULL cohomology ring
`H*(BV~; F_2)` (all degrees). The cohomology ring has dimension
∞ (a polynomial ring on m generators); injecting it into a product
requires all N_+(m, 2) Lagrangians because the *individual kernels*
contain disjoint polynomial ideals. But at a FIXED DEGREE (here, 3),
the cohomology is a finite F_2-vector space of dimension `O(m^3)`,
and the Lagrangians' degree-3 contributions live in a low-dimensional
space where collisions among individual EA images allow a much smaller
detecting subset. **Quillen 5.10 is tight only for the ring; the
degree-3 minimal family is much smaller.**

---

## 6. m=3 size-5 brute-force result (verdict: 6 is tight)

`minimal_family_154_snf_m3_size5.g` brute-forced all `C(30, 5) =
142506` size-5 EA subsets at m=3 (with D_8 + Q_8). **Result**: 0
injective subsets found.

Verdict: at m=3 the **minimum is exactly |F_EA| = 6**, total
**|F| = 8** subgroups. Greedy witness `{EA_4, EA_6, EA_11, EA_22,
EA_7, EA_16} + D_8 + Q_8` is one such minimum family. (See
`minimal_family_154_snf_m3_5subsets.out` for confirmation that
every size-5 subset of the greedy witness has non-trivial kernel.)

The slack relative to the production family (= N_+(3, 2) = 30 EAs
+ D_8 + Q_8 = 32 subgroups) is **a factor of 4**. The shrink-factor
grows with m; see §5.

---

## 7. Recommendations

### 7.1 Production code (D-VAN-2)

The current `_DETF_AllMaxEAsIn(G, m)` enumerates N_+(m, 2)
Lagrangians (full Witt enumeration for m ≥ 6, axis+pair-swap for
m = 4, 5). This is **sound** (it gives a complete detecting family
by Quillen 5.10), but **wasteful**: at m=5 we use 4590 Lagrangians
when ~10-15 likely suffice; at m=7 we use 9.8M when ~15-25 likely
suffice. The waste factor grows exponentially with m.

**Follow-up issue: file a new ticket** ("Slack-trimming pass for
D-VAN detecting family") that:

1. **At m ≤ 5** (where the full family is constructible in
   memory): after building all N_+(m, 2) Lagrangians, run a greedy
   trim — iteratively remove Lagrangians whose removal does not
   reduce the family's injectivity. This is a polynomial-time
   post-processing of the current N_+(m, 2) build, costing one SNF
   per trim step. Expected savings: at m=5, from 4590 → ~10-15 EAs
   (factor 300x).

2. **At m = 6, 7** (where N_+(m, 2) is too large to enumerate): the
   greedy-grow approach scales naturally — start with empty family,
   iteratively add the EA (constructed on-demand from a Witt
   parametrisation) that maximally reduces |ker|. Stop when |ker|
   = 1. This is exactly the algorithm we used at m=3 §4.2 above.

3. **Caching**: store the final minimal family per m in a
   compute/cache directory (`computed/d_van/minimal_family_m<m>.g`)
   so D-VAN at production doesn't re-search.

### 7.2 Theoretical follow-up

The Quillen 5.10 / Harada-Kono 1.1 structure does NOT directly give
the minimal family. Three open theoretical questions:

1. **Tight rank-based lower bound**: prove `k_min(m) ≥ C(m+2, 3) -
   C(m+1, 2)` or similar, by an explicit dimension-count argument
   on `H^3(G; F_2)` and its mod-2 detection by max EAs.

2. **Closed-form upper bound**: show that a specific construction
   (e.g. `O(m^2)` Lagrangians from a Steiner-triple-like combinatorial
   design) is always sufficient, polynomial in m. This would
   replace the empirical greedy growth with a constructive recipe.

3. **Relate to other minimal-family questions in the literature**:
   Carlson-Thévenaz 2005 use `{rank-2 EAs, almost-extraspecial}` for
   endo-trivials; their family count is much smaller than the
   `H*`-detection family. Is there a degree-3 analogue?

These are research questions, not engineering bug-fixes. They
should not block #154 closure if the practical slack-trimming
(7.1) is delivered.

### 7.3 Closure of #154

**Recommendation**: close #154 with this research note + a follow-up
issue for the slack-trimming pass. The "minimal complete detecting
family" question is **substantially answered** for m = 2 (5
subgroups) and m = 3 (8 subgroups). The general-m answer is open
but the PRODUCTION strategy can use slack-trimming to get within
a constant factor of optimal cheaply.

---

## 8. Files and reproducibility

All in `extraspecial_orbifolds/docs/superpowers/research/`:

| File | Purpose |
|------|---------|
| `2026-05-20-minimal-detecting-family.md` | THIS note |
| `minimal_family_154_spike.g` | Set-cover (per-unit-gen) analysis, m=2 and m=3 |
| `minimal_family_154_spike_m2.out` | m=2 set-cover output |
| `minimal_family_154_spike_m3.out` | m=3 set-cover output |
| `minimal_family_154_spike_summary.out` | combined set-cover summary |
| `minimal_family_154_verify_m3.g` | exhaustive size-1, size-2 set-cover at m=3 |
| `minimal_family_154_verify_m3.out` | m=3 set-cover verification |
| `minimal_family_154_strong_test.g` | full-injectivity brute force at m=2 (4096 elements) |
| `minimal_family_154_strong_test_m2.out` | 7 reference families tested at m=2 |
| `minimal_family_154_subsets_m2.g` | all 63 EA-subsets × 2 (with/without D_8, Q_8) at m=2 |
| `minimal_family_154_subsets_m2.out` | full m=2 subset enumeration |
| `minimal_family_154_snf.g` | SNF-based injectivity test (cross-check at m=2; main m=3 result) |
| `minimal_family_154_snf.out` | SNF m=2 + initial m=3 |
| `minimal_family_154_snf_m3.g` | dedicated m=3 SNF brute (sizes 0..4) + greedy |
| `minimal_family_154_snf_m3.out` | m=3 brute + greedy |
| `minimal_family_154_snf_m3_size5.g` | size-5 brute force at m=3 (~10 min wall) |
| `minimal_family_154_snf_m3_size5.out` | size-5 result: 0 injective of 142506 |
| `minimal_family_154_snf_m3_5subsets.g` | size-5 subsets of greedy witness, confirming none injective |
| `minimal_family_154_snf_m3_5subsets.out` | local-tightness check of greedy witness at m=3 |

### 8.1 Reproduction recipe

```sh
cd extraspecial_orbifolds/scripts
gap -q -b ../docs/superpowers/research/minimal_family_154_spike.g
# wall: ~2 min (m=2 + m=3 set-cover)
gap -q -b ../docs/superpowers/research/minimal_family_154_strong_test.g
# wall: ~30 sec (m=2 full injectivity over 4096 elements)
gap -q -b ../docs/superpowers/research/minimal_family_154_subsets_m2.g
# wall: ~3 min (all 63 m=2 subsets)
gap -q -b ../docs/superpowers/research/minimal_family_154_snf.g
# wall: ~5 min (SNF cross-check m=2; sampled m=3)
gap -q -b ../docs/superpowers/research/minimal_family_154_snf_m3.g
# wall: ~20 min (sizes 1..4 + greedy at m=3)
gap -q -b ../docs/superpowers/research/minimal_family_154_snf_m3_size5.g
# wall: ~10 min (size-5 at m=3; gives the definitive k_*(3) = 6 verdict)
gap -q -b ../docs/superpowers/research/minimal_family_154_snf_m3_5subsets.g
# wall: ~30 sec (size-5 subsets of greedy witness, confirms local tightness)
```

GAP version: 4.15.1 (HAP 1.70 from Homebrew). Reproducible by
re-running.

---

## 9. References

(In addition to the references already in the audit research note
`2026-05-19-d-van-detecting-family-correctness.md` §7.)

- [Q1] Quillen 1971 Thm 5.10 (full discussion: audit research note
  §2.1).
- [HK87] Harada-Kono 1987 Thm 1.1 (full discussion: audit research
  note §2.5).
- [AM04] Adem-Milgram 2004 §IV.4 Def 4.2, Thm 4.3, §IV.5 Thm 5.6
  (full discussion: audit research note §2.3, §2.4).
- [#289] D-VAN m=5 detecting-family correctness audit
  (`docs/superpowers/research/2026-05-19-d-van-detecting-family-
  correctness.md`).
- [R-1] Detecting-family literature sources for H^3(E_+(m); U(1))
  (`docs/superpowers/research/2026-05-17-detecting-family-
  literature.md`).

No new theoretical references uncovered in this 90-min lit scan;
the literature does not contain a minimal-detecting-family theorem
for extraspecial 2-groups at fixed degree.
