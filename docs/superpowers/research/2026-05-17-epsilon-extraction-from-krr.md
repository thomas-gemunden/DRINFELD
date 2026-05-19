# Extracting ε_a from KRR's lattice intertwiners

**Date.** 2026-05-17
**Issue.** #196 (K-4a-T4a). Parent: #188 (K-4a), #187 (K-4 EPIC).
**Status.** Derivation note for the K-4a-T4b implementation.

---

## TL;DR (for the impatient)

For the Barnes-Wall orbifold of E(m) (m ∈ {3, 5, 7}) with conjectured trivial
3-cocycle ω = 0, KRR show that the lattice 2-cocycle `c_g` (= CGR's `β_g`)
is **trivial as a cochain**. CGR call this the **CT (cohomologically trivial)
case** and parametrise the modular data by a 1-cocycle `ε_a : C_G(a) → U(1)`,
which in our case is automatically a **character** of C_G(a).

The crucial CGR observation (after their eq 5.21): **the modular data
(S^α, T^α) is independent of the choice of ε_a up to relabelling
characters**. That is, ε_a can be set to the trivial character without
loss of generality — different choices just permute which projective
character χ̃ is paired with which group element.

**Therefore: for K-4a-T4b, ε ≡ 1 (the trivial character) is a mathematically
correct choice.** No extraction from T_h matrix entries is required for ε
itself. The non-trivial work is making `trace_on_W` reflect the
**linear-character decomposition of Ω_0 under the commuting family
{T_h : h ∈ C_G(a)}**, which is the CGR character χ.

This is the principal conclusion; sections 2–4 below justify it. Section 5
states the function spec for K-4a-T4b. Section 6 records the obstacles
this conclusion leaves on the table (chiefly: how to compute χ when
ε_a is fixed to trivial).

---

## 1. Setup recap

### 1.1 The KRR construction

Following Keller–Roberts–Roberts (arXiv:2411.13646, hereafter KRR) and
Bakalov–Kac (BK04), for each lifted automorphism `ĝ ∈ Aut(V_L)` of a
lattice VOA there is a unique `ĝ`-twisted module `W_ĝ`. The centraliser
`C_{Ê(m)}(ĝ)` carries a **projective representation φ_ĝ** on `W_ĝ` with
2-cocycle `c_ĝ ∈ H²(C_{Ê(m)}(ĝ); U(1))` (KRR eq 1.2.6, eq 2.1.3):

```
φ_ĝ(h_1) · φ_ĝ(h_2) = c_ĝ(h_1, h_2) · φ_ĝ(h_1 h_2).
```

The 3-cocycle ω ∈ H³(E(m); U(1)) that classifies the orbifold MTC controls
all the c_ĝ via the standard CGR/Evans-Gannon formula

```
c_g(h_1, h_2) = ω(g, h_1, h_2) · ω(h_1, h_2, h_2⁻¹ h_1⁻¹ g h_1 h_2)
                    · ω(h_1, h_1⁻¹ g h_1, h_2)*                        (KRR 1.3.1)
```

For ω trivial in H³, every c_ĝ is trivial in H² — equivalently the φ_ĝ
become genuinely linear after a gauge fix.

### 1.2 The g = z = -I sector and Ω_0

For `g = z = -I` (the unique central involution in E(m)), `L_g⊥ = L` and
`N := L_g⊥ / L(1 − g) = L / 2L`. As an F_2-vector space, `N ≅ F_2^{2^m}`
(NB: the paper's "(Z/2Z)^{2m}" on p.12 is a typesetting glitch for
"(Z/2Z)^{2^m}"; the code in `defect_rep_minus_id.g` uses `n = 2^m` and
`k = n/2 = 2^{m-1}` throughout).

The Bakalov–Kac **defect representation** (ρ, Ω_0) is an irreducible
projective rep of N. Writing `d := dim_F2(N)/2 = 2^{m-1}`, KRR eq 4.2.1 picks
a symplectic basis `{α_i, β_i : 1 ≤ i ≤ d}` of N and writes
`α ∈ N` in coordinates `α = (a, ǎ) ∈ F_2^d × F_2^d`. Then `Ω_0` is the
`2^d = 2^{2^{m-1}}`-dimensional space with basis `{e_č : č ∈ F_2^d}`, and
(KRR eq 4.2.2):

```
ρ(α)(e_č) = (-1)^{a · č} · e_{č + ǎ}.                                  (1.2.1)
```

So dim Ω_0 = 16 at m = 3; 65 536 at m = 5; ≈ 1.8 × 10^19 at m = 7. The
last is why entries of T_h are computed in closed form rather than
enumerated.

### 1.3 The intertwiners T_h

For each `h ∈ C_E(m)(g) = E(m)` (since g = z is central), `ρ_h := ρ ∘ h`
is again a projective rep of N (with cocycle `P_h`). KRR §4.1 construct
intertwiners `T_h : Ω_0 → Ω_0` via **Schur averaging** (eq 4.1.5):

```
T_h := (1/√|N|) Σ_{α ∈ N} B_h(α)⁻¹ · ρ(α)⁻¹ · t · ρ_h(α),               (1.3.1)
```

where `t` is a linear map of choice (the identity, or an elementary
matrix `t_{ě,f̌}`), and `B_h(α)` is a particular coboundary of `P_h / P`
(KRR eq 4.2.8).

KRR eq 4.1.1 then guarantees `T_h ρ_h(α) T_h⁻¹ = B_h(α) ρ(α)`, and from
Schur's lemma (KRR eq 4.1.4) the T_h's compose projectively:

```
T_g T_h = λ(g, h) · T_{gh}                                               (1.3.2)
```

with a scalar `λ : C_G(a) × C_G(a) → C^×`. This `λ` is exactly the lattice
2-cocycle `c_g` of φ_ĝ pulled to Ω_0 via the restriction trick of
KRR §2.3 (last paragraph).

### 1.4 What KRR's §4.4 verifies

For `m ∈ {3, 5, 7}` (KRR §4.4), the authors construct explicit `s_h` so
that the lifted intertwiners T_{ar} (one for each generator Σ_{ar} of
E(m)) satisfy the **identity-on-the-nose** relations of E(m)/⟨z⟩:

```
T_ar² = I,           T_ar T_bs = T_bs T_ar.                              (1.4.1)
```

(KRR eqs 4.4.1, 4.4.2.) Read in the language of (1.3.2): the scalar λ is
identically 1 on the generator set (so `λ ≡ 1` on all of E(m) by
multiplicativity). Hence `c_g ≡ 1` as a **cochain** (not just as a
cohomology class). This is the central technical achievement of KRR §4.

In our optim port (`defect_rep_minus_id_optim.g`), the
`HardCodeShortComputeInterTwineref` and `HardCodeShortComputeProductCoordinateef`
machinery computes (T_h)_{c,d} and (T_{h_1} T_{h_2})_{c,d} entry-by-entry
in O(2^{m-1})-sized linear algebra. The verification at m = 5 (Test 3) and
m = 7 (Test 4) of `test_defect_rep_optim.g` confirms (1.4.1) for our
choice of symplectic basis (which differs from KRR's — see §6.4 below —
but the substantive claims survive).

### 1.5 The CGR CT formulas

CGR (hep-th/0001158) §5.2 give the modular data of a CT-twisted
finite-group theory in terms of any 1-cochain ε_a satisfying CGR eq 5.18:

```
β_a(h, g) = (δε_a)(h, g) = ε_a(h) · ε_a(g) · ε_a(hg)⁻¹.                  (CGR 5.18)
```

When β_a ≡ 1 cochain-level (our case), δε_a ≡ 1 — i.e. **ε_a is a
1-cocycle, i.e. a homomorphism ε_a : C_G(a) → U(1) = a linear character**.

The modular data is (CGR 5.20, 5.21):

```
S^α_{(a,χ),(a',χ')} = (1/(|C_G(a)| |C_G(a')|)) Σ_{g ∈ G(a, a')}
                        χ*(g a' g⁻¹) · χ'*(g⁻¹ a g) · σ*(a | g a' g⁻¹),    (1.5.1)

T^α_{(a,χ),(a',χ')} = δ_{a, a'} δ_{χ, χ'} · (χ(a)/χ(e)) · ε_a(a),         (1.5.2)
```

with `σ(h | g) := ε_h(g) · ε_g(h)` (CGR 5.22) and `G(a, a') := {g ∈ G :
g a' g⁻¹ ∈ C_G(a)}` (equivalently `g⁻¹ a g ∈ C_G(a')`).

The **critical** observation, stated in CGR immediately after eq 5.22:
> "It is easy to see that (5.20), (5.21) are (essentially, i.e. up to a
> relabelling of the characters χ) independent of the choice of 1-cochains
> ε_a in (5.18), (5.19)."

That is: any choice of ε_a satisfying (5.18) gives **the same modular
data** up to a permutation of the χ-labels. So the only invariant of
ε_a is its cohomology class. When β_a is trivial as a cochain, the only
ambiguity-free representative is the trivial 1-cochain ε_a ≡ 1.

---

## 2. The canonical vacuum vector

### 2.1 Statement and consequence

**Claim.** There is no canonical 1-dimensional invariant subspace of Ω_0
under the C_G(g) action that pins ε_a without additional data. In
particular, the natural basis vector `e_0` (= `e_{č=0}`, the "first
basis vector" of Ω_0) is **not** a simultaneous eigenvector of all T_h.

**Justification (m = 3, by hand).** From KRR eqs 4.4.3–4.4.8 (with their
normalisation):

| h        | T_h(e_0) |
|----------|----------|
| T_{1,1}  | e_0      |
| T_{1,2}  | e_0      |
| T_{2,1}  | e_0      |
| T_{2,2}  | e_0      |
| T_{3,1}  | ½ (e_0 + e_{(0,0,0,1)}) + ½ (e_{(0,1,1,0)} − e_{(0,1,1,1)}) |
| T_{3,2}  | e_0      |

So `T_{3,1}` does **not** preserve the line through e_0; it maps e_0 to
a 4-vector. The matrix entry `(T_{3,1})_{0,0} = 1/2`. Hence
`(T_h)_{0,0}` is not multiplicative across h: it equals 1 for five
generators and 1/2 for the sixth, which is incompatible with being a
character of E(m).

**Consequence.** The Rayleigh-quotient hypothesis from the issue
description — `ε_a(h) := ⟨e_0, T_h e_0⟩ / ⟨e_0, e_0⟩` — does **not**
yield a homomorphism. So this naive recipe is wrong, and a more
careful analysis is required.

### 2.2 What e_0 actually is

The basis vector e_0 = e_{č=0} comes from KRR's chosen identification
of Ω_0 with `C[Ǎ]` (KRR eq 2.3.5): pick subgroups A, Ǎ < N with
A ⊕ Ǎ = N (a Lagrangian decomposition) and identify `e_ψ ↔ |ψ⟩` for
`ψ ∈ Ǎ`. Then e_0 = |trivial character of A⟩, i.e. the "constant
function 1" on A. This is **not** an L²-norm-minimising vacuum; it's a
combinatorial choice of basis.

What does the actual conformal "lowest weight state" of W_{−I} look
like? In the BK04 / Lepowsky-induction picture, the lowest-weight
component of W_{−I} is Ω_0 (a finite-dim space), the lowest-weight
**vector** is a state of conformal weight ρ_g (the vacuum anomaly,
KRR (3.2.1)). But Ω_0 itself is not 1-dim: it's a representation of
the **finite Heisenberg group** N (and hence has dim √|N| = 2^d), so
the "vacuum" of W_{−I} is the **whole space Ω_0**, not a single vector
inside it. That's why ρ doesn't act trivially.

**So the "vacuum" of W_a is a representation of C_G(a), not a vector.**
This is the crux: any ε_a "pinning" recipe needs to choose a particular
χ ∈ Irr(C_G(a)) inside Ω_0's decomposition. And that choice is exactly
the labelling ambiguity CGR mention.

### 2.3 Spectral decomposition of Ω_0

The unnormalised T_h returned by `HardCodeShortComputeInterTwineref`
satisfies `(T_h^2)_{0,0} = 2^{2k}` where k = 2^{m-1} (see Appendix A-bis).
So the **normalised** intertwiner is `\hat{T}_h := T_h / 2^k`; it
satisfies `\hat{T}_h^2 = I` literally. (Equivalent rescaling per
Test 3 / Test 4 of `test_defect_rep_optim.g`: divide each (i, j) of
the relation matrix by `RootInt(diag_i · diag_j)`.)

Since the `\hat{T}_h`'s for h running over the 2m generators {Σ_ar} of
E(m) all commute and have order 2 (KRR eqs 4.4.1, 4.4.2), they generate
an abelian group of involutions, faithfully representing E(m)/⟨z⟩ ≅
F_2^{2m}. Hence Ω_0 decomposes as

```
Ω_0 = ⊕_{χ ∈ Irr(F_2^{2m})} Ω_0(χ),     dim Ω_0 = 2^d = 2^{2^{m-1}},     (2.3.1)
```

where Irr(F_2^{2m}) has |F_2^{2m}| = 2^{2m} linear characters. For m = 3:
2^d = 16 and |Irr| = 64, so at most 16 characters appear in Ω_0 with
non-zero multiplicity (perhaps each with multiplicity 1 — this is
empirical, to be checked by T4c via per-character trace formulas).

**Each simple (a = −I, χ) of D^ω(E(m)) corresponds to one χ that
appears in (2.3.1).** That's the K-1 / CGR-(5.20) interface: χ
indexes the simples in the central sector.

---

## 3. The ε_a formula

### 3.1 ε_a is gauge

Combining §1.5 (the CGR gauge freedom) and §2.1 (no canonical 1-dim
vacuum), we arrive at:

**There is no recipe `ε_a(h) := f(T_h)` that produces a canonical
character of C_G(a) without additional structure.** Any character of
C_G(a) is a valid choice; different choices permute the χ-labels of
simples but leave the modular data invariant.

### 3.2 The simplest gauge choice: ε ≡ 1

The trivial 1-cochain ε_a ≡ 1 satisfies (CGR 5.18) precisely when
β_a ≡ 1, which is KRR's verified condition for m ∈ {3, 5, 7}. So
**ε_a := the trivial character of C_G(a)** is a mathematically valid,
gauge-fixing choice.

Under this choice:
- σ(h | g) = ε_h(g) · ε_g(h) = 1 · 1 = 1 always.
- (CGR 5.20) simplifies to the standard (untwisted-form) S formula.
- (CGR 5.21) gives T^α_{(a, χ)} = (χ(a)/χ(e)) · 1 = χ(a)/χ(e).

The remaining content of the BW orbifold's modular data lives in the
**characters χ** themselves (the irreps of C_G(a) decomposing Ω_0
under {T_h}). That is: **the only nontrivial input to `ProjectorFormula`
from the lattice is `trace_on_W`, NOT `epsilon`.**

### 3.3 What would ε ≠ 1 buy us?

Two reasons one might want non-trivial ε:

1. **Sanity check / cross-validation.** If we *had* a canonical vacuum
v_a, then `ε_a(h) := ⟨v_a, T_h v_a⟩` (with T_h's eigenvalue, if v_a
is a simultaneous eigenvector) would let us double-check σ(a|b)
against the (S, T) reproduction at m=3 (the K-3 anchor).

2. **Generalising to ω ≠ 0.** For non-trivial ω, β_a ≠ 1 as a
cochain (in general), and the CGR formulas need a specific ε_a
representing the cohomology class. But in that setting we'd compute
ε_a from ω directly (V-1, issue #14), not from the T_h matrices.

For K-4a's job at m ∈ {3, 5, 7} with KRR's conjectured ω = 0, **(1) is
the only motivation**, and it's not on the critical path.

### 3.4 What if KRR's lattice gave ω ≠ 0?

KRR conjecture but do not prove ω = 0. If ω ≠ 0, then by (KRR 1.3.1)
some c_g would be non-trivial in H². But KRR's §4.4 verifies c_g ≡ 1
**as a cochain** for g = −I, Σ_{11}, Σ_{11}Σ_{12} (the three
non-trivial classes; the latter two are even easier because the
centraliser acts trivially on N, see KRR p.13 last paragraph).

Cochain-level β_g ≡ 1 is **stronger** than cohomology-level β_g ≡ 0.
So KRR's evidence is for cochain-level CT, which automatically gives
ε_a = (some 1-cocycle = character). KRR don't compute which character.

**My read of CGR's gauge remark**: the choice doesn't affect the
modular data, so we can ignore it and set ε ≡ 1. KRR don't compute
ε_a because there is no canonical one to compute. The character that
appears in T^α_{(a, χ)} = (χ(a)/χ(e)) · ε_a(a) is, when ε_a = 1, just
χ(a)/χ(e); and χ runs over the linear characters of C_G(a) that appear
in Ω_0's decomposition.

---

## 4. Verifications

Because we are choosing ε ≡ 1 (Section 3), the verification protocol
is **about χ, not about ε**.

### 4.1 Verification at m = 3 against K-3 anchor

The decisive test is K-3 (issue #40): the central-row entries of
S^Keller at m = 3 must match the dense untwisted S central row computed
by `untwisted_modular_data.g` byte-for-byte (cyclotomic equality).

**Under the ε ≡ 1 hypothesis**: K-4a-T4b's `BuildKRRIntertwinerData(3,
E(3))` should reproduce K-3's central-row anchor immediately, with
`trace_on_W` falling back to the centraliser-character functional (the
ω = 0 ground truth) and `epsilon ≡ 1`. This is the acceptance criterion
of K-4a (issue #188).

**Worked-out central-row case for a = −I, m = 3**:

- C_G(−I) = E(3), |E(3)| = 32. The class [−I] = {−I} (size 1).
- For the central row, χ_1 is taken to be the regular character of E(3)
  (or any character; for the "vacuum" simple (−I, trivial), χ_1 ≡ 1
  on E(3)).
- The CGR formula (1.5.1) with χ_1 ≡ 1, ε_1 ≡ 1 simplifies to the
  Dijkgraaf-Witten ω = 0 untwisted S central row, by standard character
  manipulations.

So at m = 3, ε ≡ 1 passes the K-3 anchor trivially. (More precisely: it
passes by construction, because `BuildIntertwinerDataUntwisted` already
does exactly this. So K-4a's job is to reproduce the same answer through
the lattice machinery.)

### 4.2 Homomorphism check (vacuous for ε ≡ 1)

Setting ε_a ≡ 1 makes `ε_a(h_1 h_2) = 1 = 1 · 1 = ε_a(h_1) · ε_a(h_2)`
trivially. No computation needed.

### 4.3 Conjugation transport (vacuous for ε ≡ 1)

CGR eq 5.19: `ε_{x a x⁻¹}(x h x⁻¹) = β_a(x, x⁻¹hx) / β_a(h, x) · ε_a(h)`.
For β_a ≡ 1 cochain-level (our case), this collapses to `ε_{x a x⁻¹}(x h x⁻¹) = ε_a(h)`.
With ε ≡ 1 it is trivially true (1 = 1).

### 4.4 What's NOT vacuous and IS critical

The non-trivial verification at m = 3 is that the **K-3 central-row
match holds**. This in turn requires that the χ's of (2.3.1) are
correctly extracted from the T_h's. That's the K-4a-T4b implementation
job — not part of T4a (this note).

### 4.5 Negative consistency check (sanity)

If the K-3 anchor were to **fail** with ε ≡ 1, that would indicate one
of two things:
- ε ≡ 1 is the wrong gauge (some specific non-trivial χ is being
  implicitly chosen by the lattice, against CGR's gauge-freedom claim).
- The bug is elsewhere (e.g. in `trace_on_W` or in transports).

Per CGR's gauge remark, only the second option is mathematically
possible. So a K-3 failure with ε ≡ 1 would unambiguously point at
`trace_on_W`.

---

## 5. Function specification for K-4a-T4b

This is the K-4a-T4b deliverable spec — readable standalone.

### 5.1 Inputs

`BuildKRREpsilon(setup) → epsilon_callable` where `setup` is a record
with fields:

```gap
setup := rec(
    m := <integer in {3, 5, 7}>,
    G := <EmGroup(m)>,
    idx := BuildSimpleIndex(G),
    # T_h matrix-entry oracle — already exists in the optim pipeline:
    # for h ∈ G, mh = MhHalfefMat(h, m), A = Kernef(h, m), s = zero shift vec,
    # B = BasisForN(m), R = TwoCocycleForN(m).
    # The entry (T_h^{0,0})_{c, d} is
    #   HardCodeShortComputeInterTwineref(h, 0_k, 0_k, c, d, 0_n, mh, A, B, R, m)
);
```

### 5.2 Output (concrete)

A GAP callable `epsilon : (g1, g2, a, b) -> cyclotomic` matching the
K-1 interface signature (krr_projector.g eq 5.20 wrapper):

```gap
epsilon := function(g1, g2, a, b)
    return 1;     # the trivial CGR phase σ*(a | b)
end;
```

That's it. Per Section 3, ε_a ≡ 1 for all a is a mathematically valid
gauge choice for KRR's CT case, and CGR's eq 5.22 then gives
σ(a | b) = ε_a(b) ε_b(a) = 1 · 1 = 1.

The K-4a-T4b implementation should **not** read any T_h matrix entries
to produce ε. ε is a constant function 1.

### 5.3 Why no T_h is needed

The entirety of the lattice-orbifold information needed by K-1's
`ProjectorFormula` for the BW orbifold lives in `trace_on_W`, **not in
ε**. The trace `trace_on_W(class_idx, irrep_idx, h)` must return the
character value χ_{class_idx, irrep_idx}(h) where χ ranges over the
**linear characters of C_G(a) that appear in the decomposition of Ω_0
under the T_h-action**.

This is what K-4a-T4c (a separate sub-task) implements; T4a (this note)
only deals with ε.

### 5.3a Caveat: χ-labelling alignment

The ε ≡ 1 choice is correct **provided** K-4a-T4c's `trace_on_W` and
K-1's `EvalIrr` use the **same** labelling of characters of C_G(a). The
existing `BuildIntertwinerDataUntwisted` (krr_projector.g lines 74-87)
uses GAP's `Irr(C_G(a))` ordering (via `EvalIrr` → `BuildSimpleIndex`).

So K-4a-T4c must:
1. Read the joint eigenspaces of {T_h : h ∈ C_G(a)-generators} on Ω_0.
2. Identify which character χ ∈ Irr(C_G(a)) each eigenspace carries
   (by matching eigenvalues against GAP's character-table entries).
3. Return the dimension of the corresponding eigenspace as the simple's
   dim, and the character value as `trace_on_W(class_idx, k, h) := dim · χ_k(h)`
   (or, more carefully, `Tr(T_h | Ω_0(χ_k))` which equals `mult_k · χ_k(h)`
   where `mult_k` is the multiplicity of χ_k in Ω_0).

If T4c uses a **different** labelling (e.g., natural-ordering-on-joint-
eigenvalues rather than GAP's `Irr`), then we'd need a non-trivial
ε_a to compensate. But it's strictly simpler to fix the labelling
upstream (in T4c) and keep ε ≡ 1.

### 5.4 Optional refinement: ε_a from eigenvalues

For sanity-checking, a hypothetical "computed ε_a" using the lattice
data could be defined as follows (NOT required for T4b, but useful
diagnostic):

```
ε_a(h) := the eigenvalue of \hat{T}_h := T_h / 2^k on the
          trivial-character isotypic component of Ω_0 under
          {\hat{T}_h : h ∈ C_G(a)}.
```

Since on the trivial-character component each T_h acts as +1, this
gives ε_a(h) = +1 always, recovering the trivial character. (This is
consistent with §3.2.)

If KRR's lattice secretly carried a non-trivial canonical character
(an unlikely scenario, given CGR's gauge-freedom argument), this
eigenvalue extraction would detect it: ε_a(h) would land in {±1, ±i}
without all values being 1.

A concrete realisation: at m = 3, for each h ∈ E(3), compute the trace
of T_h on Ω_0. The 16-dim Ω_0 decomposes under the 6 commuting
involutions {T_{ar}} into joint eigenspaces. Each joint eigenspace
carries a single character χ : F_2^6 → {±1}. The "ε_a-character" would
be one specific χ among the (at most 16) characters appearing — and
under CGR's gauge freedom, **any** of them is a valid ε. The simplest
gauge choice is the trivial character.

### 5.5 The full K-4a record

For completeness, the K-4a record fed to `ProjectorFormula` is:

```gap
BuildKRRIntertwinerData(m, G) := rec(
    group       := G,
    idx         := BuildSimpleIndex(G),
    transport   := BuildTransports(idx),

    # Non-trivial: per K-4a-T4c, this uses HardCodeShortComputeInterTwineref
    # to extract the eigen-decomposition of Ω_0 and project onto the
    # k-th linear character of C_G(g_i).
    trace_on_W  := function(class_idx, irrep_idx, h)
        # ... lattice-derived χ_{class_idx, irrep_idx}(h) ...
    end,

    # T4a output: trivial.
    epsilon     := function(g1, g2, a, b) return 1; end
);
```

K-4a-T4b is exactly the boilerplate of providing the
`epsilon := function(g1, g2, a, b) return 1; end` plug — a one-line
implementation.

---

## 6. Open questions / risks

### 6.1 Did I read CGR correctly?

The pivotal claim in §3 is CGR's "modular data is independent of the
choice of ε_a up to relabelling of characters" (CGR p.25 line after
eq 5.22). I have read this as: any choice satisfying (5.18) gives the
same (S, T) up to a character-permutation.

**Risk.** If CGR's statement is weaker than I'm reading it (e.g.,
"independent" might mean only "independent of the gauge ε_a within a
fixed cohomology class", not "independent of which cocycle class
within Z²"), then ε ≡ 1 might still be one specific gauge choice that
needs to match what KRR's lattice computes.

**Mitigation.** The K-3 anchor at m = 3 is the empirical check: if
ε ≡ 1 fails K-3, that's strong evidence that the gauge is not as
free as CGR seem to claim. Given that the existing K-1 implementation
with ε ≡ 1 already targets K-3 as its acceptance test (issue #20,
krr_projector.g lines 30–35), if K-3 passes then ε ≡ 1 is empirically
the right choice.

### 6.2 The "trivial character of which C_G(a)"?

For a = −I, C_G(−I) = E(m) (the whole group). Setting ε_{−I} ≡ 1 is
unambiguous.

For non-central a (e.g. a = Σ_{11} or Σ_{11}Σ_{12} in m = 3),
C_G(a) = Z_2 × E(m−1) or Z_4 ∘ E(m−1). The trivial character of these
groups is also unambiguous. So no obstacle.

### 6.3 KRR's "trivial centraliser action" cases

KRR p.13 last paragraph: "Somewhat surprisingly, we found that for
m = 3, 5, 7 the centralizer groups Z_2 × E(m − 1) and Z_4 ∘ E(m − 1)
act trivially on N. Their intertwiner representations are thus trivial
and automatically have vanishing 2-cocycle."

So for a = Σ_{11} and a = Σ_{11}Σ_{12}, T_h = I for all h ∈ C_G(a) (up
to overall normalisation). Then β_a ≡ 1 trivially, ε_a ≡ 1 is the
unique gauge.

This means K-4a-T4b only has substantive work to do for the central
class a = −I, AND it's vacuous (ε ≡ 1) per §3.

### 6.4 Symplectic-basis dependence

Our `SymplecticBasisF2` (in `defect_rep_minus_id.g`) produces a
*different* symplectic basis of N than KRR's Magma `WittDecomposition`,
so the literal T_h matrices and their (0,0) entries do not match
KRR's eqs (4.4.3)–(4.4.8). However:

- The intertwiner representation φ_ĝ on W_ĝ is basis-independent up to
  conjugation, so the **characters** χ that appear in Ω_0 are
  unaffected by the symplectic basis choice.
- Both bases give cochain-level trivial β_a, so ε_a ≡ 1 is correct in
  both.
- The verification at m = 5 and m = 7 (Tests 3, 4 of
  `test_defect_rep_optim.g`) confirms diag = 1 and symmetric, i.e.
  λ ≡ μ ≡ 1, in our basis.

**Risk.** If T4c (the trace_on_W implementation) needs to identify
specific characters by name (e.g. "the sign character of E(3)"), the
basis difference may shuffle labels. The fix is to identify characters
by their action on the C_G(a) generators (basis-independent), not by
name.

### 6.5 Is ω actually trivial?

KRR's evidence (KRR §5.3) is restricted to two necessary conditions:
- ω restricts trivially to all cyclic subgroups (type-0 condition).
- All c_g have trivial cocycle (i.e. CT condition), per their §4.

These are necessary but not sufficient. **If ω turns out to be
non-trivial after all**, the entire K-4 epic's premise needs revisiting,
not just T4a/T4b. The H-restriction approach (K-4b) is what tests this
empirically.

### 6.6 What does "ε ≡ 1" buy us, really?

In some sense this note's conclusion is anticlimactic: "ε = 1, no work
to do". The substantive math of the K-4 epic happens in `trace_on_W`,
not in ε. **All the technical complexity of KRR §4 (the optim pipeline,
the closed-form Schur sums, the relation matrix verification) feeds into
`trace_on_W`, not into ε.**

That's because KRR's §4 effort *establishes that ε can be trivial* —
the projective rep is already a linear rep on the nose. Once you have
a linear rep, the character is just the (suitably normalised) trace, and
ε disappears. The hard work was in showing the rep is linear, not in
computing ε.

This is consistent with the fact that K-1's existing `BuildIntertwiner
DataUntwisted` (krr_projector.g) already uses `epsilon ≡ 1` and is
expected to pass the K-3 anchor.

---

## Appendix A: Worked-out (T_h)_{0,0} table at m = 3 (this codebase's basis)

Because our `SymplecticBasisF2` differs from KRR's Magma basis, the
m = 3 T_h matrices in our code do not literally match KRR (4.4.3)–
(4.4.8). For diagnostic purposes only, the (T_h)_{0,0} entries that
HardCodeShortComputeInterTwineref returns at m = 3 with (e, f) = (0, 0),
(c, d) = (0, 0), shift s = 0 are reproducible via:

```gap
Read("defect_rep_minus_id.g");
Read("defect_rep_minus_id_optim.g");
m := 3;;
for a in [1..3] do for r in [1, 2] do
    h := UnimodSigma(m, a, r);
    val := HardCodeShortComputeInterTwineref(
        h, F2_ZeroVec(4), F2_ZeroVec(4),
        F2_ZeroVec(4), F2_ZeroVec(4),
        F2_ZeroVec(8),
        MhHalfefMat(h, m), Kernef(h, m),
        BasisForN(m), TwoCocycleForN(m), m);
    Print("T_", a, r, ": (0,0) entry = ", val, "\n");
od; od;
```

Expected output: each T_h^{0,0}_{0,0} value is an integer ±2^j for some
j ≤ k = 4 (at m = 3). After normalisation by 2^k = 16, the (T_h)_{0,0}
values lie in {±1, ±1/2, ±1/4, ±1/8, ±1/16} (rational, denominators
powers of 2). Six values, six different patterns depending on which
generator and what s_h happens to be.

This is NOT a "Rayleigh ε_a" computation in the homomorphism sense
(see §2.1 for why); it is just a diagnostic to confirm the entries
come out as the relation matrix demands. The actual ε_a is the
trivial character per §3.

## Appendix A-bis: How the relation matrix relates to T_h^2

In `test_defect_rep_optim.g` Test 3 (m=5), `M5raw[i][j]` is the
**(c1 = 0, d2 = 0) entry of the product matrix `T_{h_i}^{0,0} · T_{h_j}^{0,0}`**.
For i = j, this gives `(T_{h_i}^2)_{0,0}`.

A computation reveals (and the code verifies):
- `(T_h^{0,0})^2_{0,0} = 2^{2k}` for every generator h (NB: this is
  `2^{2 · 2^{m-1}}`, NOT `2^k`).
- After dividing by `RootInt(diag_i · diag_j) = 2^k`, the diagonal is 1.

So the **fully-normalised** intertwiner is `\hat{T}_h := T_h / 2^k`; it
satisfies `(\hat{T}_h^2)_{0,0} = (T_h^2)_{0,0} / 2^{2k} = 1`. Combined
with the fact that `\hat{T}_h^2 = scalar · I` (by Schur, from KRR's
λ ≡ 1), we get `\hat{T}_h^2 = I` literally. The diagonal-1 claim of
the relation matrix is exactly this normalisation.

**To be safe about normalisations**, the T4c implementation should:
1. Compute the diagonal `diag_h := (T_h^{0,0} \cdot T_h^{0,0})_{0,0}`
   (call `HardCodeShortComputeProductCoordinateef(h, ..., h, ..., 0, 0)`).
2. Use `\hat{T}_h := T_h / RootInt(diag_h)` as the normalised
   linear-rep matrix.
3. Compute Tr(\hat{T}_h | Ω_0) and per-isotype traces by sums of
   `\hat{T}_h` entries on appropriate sub-bases.

For ε ≡ 1 (this note's conclusion), normalisation details don't matter
since ε is a constant.

---

## Appendix B: References

- **KRR**: C.A. Keller, A.W. Roberts, J. Roberts, *CFTs with large gap
  from Barnes-Wall lattice orbifolds*, arXiv:2411.13646. Relevant
  sections: §2.1 (orbifold theory), §2.3 (defect rep), §4 (intertwining
  rep and Schur averaging), §5.3 (the ω conjecture).
- **CGR**: P. Coste, T. Gannon, P. Ruelle, *Finite group modular data*,
  Nucl. Phys. B581 (2000) 679, hep-th/0001158. Relevant: §5.1, §5.2
  (CT-twist formulas eqs 5.18–5.22).
- **BK04**: B. Bakalov, V. Kac, *Twisted modules over lattice vertex
  algebras*, in Lie theory and its applications in physics V, 2004
  (originally cited in KRR for the defect rep construction).
- **DRX17**: C. Dong, L. Ren, F. Xu, *On orbifold theory*, Adv. Math.
  321 (2017) 1.
- **Evans-Gannon**: D.E. Evans, T. Gannon, *Reconstruction and local
  extensions for twisted group doubles, and permutation orbifolds*,
  arXiv:1804.11145.

---

## Appendix C: Glossary of variables

- `m` ∈ {3, 5, 7}: rank parameter of E(m) = 2^{2m+1}_+.
- `n := 2^m`: dim of N as F_2-space.
- `k := n/2 = 2^{m-1}`: half-dim of N; also exponent in dim Ω_0 = 2^k.
- `d := k = 2^{m-1}`: dim of A and Ǎ in N's Lagrangian decomp.
- `Ω_0`: defect representation space, dim 2^k.
- `W_g`: g-twisted module of V_L, dim infinite. Lowest-weight
  component is Ω_0 (at weight ρ_g).
- `N` (for g = z = −I): L/2L, F_2-rank 2^m.
- `c_g = β_g`: 2-cocycle of φ_ĝ resp. CGR's β_a.
- `ε_a`: 1-cochain such that δε_a = β_a (CGR 5.18). Our claim: ε ≡ 1.
- `σ(h | g) := ε_h(g) ε_g(h)` (CGR 5.22). With ε ≡ 1, σ ≡ 1.
- `χ`: linear character of C_G(a) (a 1-cocycle since β_a ≡ 1 cochain).
- `T_h`: KRR's intertwiner Ω_0 → Ω_0 (unnormalised: (T_h²)_{0,0} = 2^{2k}).
- `\hat{T}_h := T_h / 2^k`: normalised intertwiner (\hat{T}_h² = I).
- `(T_h)_{c, d}` or `(T_h^{e, f})_{c, d}`: matrix entry returned by
  `HardCodeShortComputeInterTwineref(h, e, f, c, d, s, mhh, A, B, R, m)`.
