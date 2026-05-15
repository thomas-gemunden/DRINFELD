# Integer Cohomology of Extraspecial 2-Groups — Literature Synthesis

**Date:** 2026-05-15
**Triggered by:** D-VAN-FIX investigation (PR #155). Empirical evidence that
no D_8 subgroup of E_+(3) detects the Z/4 summand of H^3(E_+(3); U(1))
with full resolution — see #153, #154 for the issue trail.

## Primary references

- **Harada & Kono 1987**, *J. Pure Appl. Algebra* 44:215-219. *On the integral
  cohomology of extraspecial 2-groups*. Local copy: `docs/1-s2.0-0022404987900259-main.pdf`.
- **Pham Anh Minh 2001**, *Trans. AMS* 353:1937-1957. *Essential cohomology and
  extraspecial p-groups*. Local copy: `docs/S0002-9947-00-02689-1.pdf`.
  Primarily about odd primes but cites Quillen's p=2 result.
- **Quillen 1971**, *Math. Ann.* 194:197-212. *The mod 2 cohomology rings of
  extra-special 2-groups and the spinor groups*. Local copy:
  `docs/Quillen - The mod 2 cohomology of extra-special 2-groups and the spinor groups.pdf`.

## Notation

- V is an F_2-vector space; Q ∈ S^2(V^*) is a quadratic form.
- V^- is the extraspecial 2-group classified by Q (central extension
  `0 → Z/2 → V^- → V → 0`).
- `h(Q)` = codimension of a maximal Q-isotropic subspace of V.
- For E_+(m) (plus type), `h(Q) = m`.
- `n(k)` = 2-adic valuation of integer k.

## Quillen 1971 (p = 2, mod-2 cohomology)

**Essential cohomology vanishes** for E_+(m) with m ≥ 1, with the single
exception of Q_8 (which is the only group of order 2^3 with every element
of order ≤ 2 central).

**Consequence.** The family of conjugacy class representatives of maximal
elementary abelian subgroups of E_+(m) **detects all of `H*(E_+(m); F_2)`**
(not just modulo nilpotents).

This is the **F_2 side** of detection. For our purposes it confirms that the
F_2 part of H^3 IS captured by EA restriction — matches our empirically
verified Gate 1A after the D-VAN-FIX partial repair.

## Harada-Kono 1987 (integer cohomology)

### Theorem 1.1

For h(Q) ≥ 2:

```
H^k(V^-; Z)  =  A(k)  ⊕  (elementary abelian 2-group)
```

with `A(k)` **cyclic of order `2^{a(k,Q)}`** if `k ≡ 0 (mod 4)`, and `A(k) = 0`
otherwise. The exponent is

```
a(k, Q)  =  n(k)        if  n(k) ≤ h(Q) − 1
          =  h(Q) + 1    if  n(k) ≥ h(Q)
```

### Applied to our case (H^3(G; U(1)) ≅ H^4(G; Z), so k = 4, n(k) = 2)

| m  | h(Q) | branch                  | A(4) order        | Empirical confirmation                      |
|----|------|-------------------------|-------------------|---------------------------------------------|
| 2  | 2    | n(k) = h(Q) → 2nd       | `2^{h+1} = 8`     | ✓ HAP gives `[(Z/2)^9, Z/8]` for E_+(2)     |
| 3  | 3    | n(k) ≤ h-1 → 1st        | `2^{n(k)} = 4`    | ✓ A-3a gives `[(Z/2)^34, Z/4]` for E_+(3)   |
| 5  | 5    | n(k) ≤ h-1 → 1st        | `Z/4`             | **Prediction.** A-5b empirical check pending. |
| 7  | 7    | n(k) ≤ h-1 → 1st        | `Z/4`             | **Prediction.** No HAP-route check available. |

The **rank of the elementary abelian part** is determined by Quillen's F_2
cohomology and Section 3's Bockstein spectral sequence calculation; we
have the empirical values at m ≤ 3 and will get m=5 from A-5b.

### Proof tool: transfer-restriction formula

For any Q-isotropic subspace W ⊂ V with preimage W^- ⊂ V^-:

```
t ∘ r  =  2^{h(Q)}  · id    on H^*(V^-; Z)
```

where `r: H^*(V^-; Z) → H^*(W^-; Z)` is restriction, `t: H^*(W^-; Z) →
H^*(V^-; Z)` is transfer.

## Implication for D-VAN

D-VAN's architecture is **restriction to detecting subgroups**. The transfer
formula forces a structural ceiling on what restriction can detect for
integer cohomology:

- **At m = 2** (h = 2, transfer-restriction is mult-by-4): the order-2 element
  of A(4) = Z/8 satisfies `4 · gen ≠ 0`, so it survives the transfer
  composition. Subgroup detection partially works — empirically, our partial
  fix's Gate 1B catches the Z/8 generator AND its order-4 half-vector.
- **At m = 3** (h = 3, transfer-restriction is mult-by-8): the cyclic
  A(4) = Z/4 has max torsion 4 < 8, so `8 · y = 0` for every y in H^4(V^-; Z).
  Restriction is "lossy" relative to the cyclic summand — no subgroup
  detects the Z/4 generator with full Z/4 resolution.
- **At m ≥ 3 in general**: A(4) is always `Z/4`, and `t ∘ r = 2^m` annihilates
  it (for m ≥ 3 we have `2^m ≥ 8 > 4`). The cyclic summand is structurally
  invisible to subgroup restriction at degree 4.

### Mapped to D-VAN's empirical results (#155)

- **Gate 1A at m=2 and m=3 PASSES**: matches the F_2 detection theorem; all
  unit basis generators have non-trivial F_2 restriction.
- **Gate 1B at m=2 PASSES**: the Z/8 generator's order-4 half-vector is
  detected. This is the "lucky" m=2 case where transfer-restriction = 4 is
  compatible with the Z/8 cyclic summand.
- **Half-vector at m=3 fails (#153)**: the order-2 sub-element of A(4) = Z/4
  is NOT detected. This is the predicted m≥3 failure mode.
- **8/8 D_8 spike at m=3**: every sampled D_8 gives res_D8[exp_idx][3] ∈ {0, 2}.
  This is consistent with the structural ceiling — no D_8 can give the odd
  Z/4 coord that would faithfully resolve the cyclic summand.

## What this rules out

- **Adding more D_8 sections** won't close the gap at m ≥ 3. The empirical
  spike already showed 8/8 give the bad outcome; the structural argument
  predicts all 280 conj classes will too. (Worth confirming exhaustively
  if/when D-VAN-MATH continues.)
- **Adding Q_8 sections** at m = 3: Q_8 has H^3 = Z/8, which could
  potentially capture order-4 elements. But Q_8 is order 8 with all
  elements of order 2 central — restriction to Q_8 from E_+(3) follows
  similar transfer constraints. Worth empirical check; the math suggests
  it won't help fundamentally.
- **Larger sections at m = 3**: each section H has its own `t ∘ r = 2^{h(Q|H)}`
  bound; bigger H means bigger 2^h means stronger annihilation of small
  torsion. Doesn't help.

## What could work (out of scope for current PR)

1. **Direct BSS evaluation on G**: compute ω's image in `H^*(G; F_2)` via the
   Bockstein spectral sequence and check the differential structure. Bypasses
   subgroup restriction. Would need an explicit BSS implementation —
   feasible per Harada-Kono's Section 3.
2. **Cocycle-level test**: build the bar 3-cocycle from ω (already done in
   D-VAN's `f_E`, `f_D8`) and test exactness directly via integer linear
   algebra on `B^3(G; Z)`, not through subgroups. Approximately the existing
   `IsCoboundary3` work, but on G itself rather than its subgroups.
3. **Accept the partial detection contract**: as documented in PR #155, use
   D-VAN as a one-way filter (non-triviality detector). For Keller, this is
   genuinely useful — it gives a CHEAP NECESSARY condition for triviality.

## Connection to Q-int A2 (#136)

Harada-Kono Theorem 1.1 **solves the cyclic-summand prediction** for Q-int
Stage A2:

- m=5: `A(4) = Z/4`
- m=7: `A(4) = Z/4`

The remaining ranks of the elementary-abelian parts come from Section 3's
BSS calculation, which can be re-derived from Quillen's F_2 cohomology
(`QuillenCanonicalPresentation` + `BasisInDegree` from Q-2a / Q-1).

So **Q-int A2 collapses to**: compute the F_2 dimensions of H^3, H^4, H^5
of E_+(m) for m ∈ {5, 7}; combine with Theorem 1.1 to read off the
torsion. No from-scratch BSS implementation needed.

## Next research targets (deferred)

- **Yagita** — cohomology theory of extraspecial p-groups. May provide
  additional structural tools.
- **Adem-Milgram IV.7** — original source of the brainstorm's `{E, D_8}`
  detection-family claim. Worth verifying we read it correctly originally;
  the empirical and theoretical evidence above strongly suggests the
  original brainstorm misquoted or over-extended it.
