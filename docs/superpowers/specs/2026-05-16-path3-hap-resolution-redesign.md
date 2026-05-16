# Path 3 Redesign: Z/4 3-Cocycle Construction on HAP's Compact Resolution

**Date:** 2026-05-16
**Issue:** #137 (Q-int C). Supersedes the bar-resolution approach (#160-#162, kept as m=1 reference implementations).
**Status:** Spec / new B3 workstream.

## Why this redesign

The bar-resolution approach (#160 Steenrod cup-1, #161 Pontryagin square, #162 linear-solve integration) is **mathematically correct** but **fundamentally infeasible** beyond m=1. The bar resolution at degree 5 has |G^5| cells:

| m | \|G\| | \|G^5\| | feasible? |
|---|---|---|---|
| 1 (D_8) | 8 | 3.3×10⁴ | dense ok (≈100 min) |
| 2 (E_+(2)) | 32 | 3.4×10⁷ | sparse only (~hours) |
| 3 (E_+(3)) | 128 | 3.4×10¹⁰ | infeasible |
| 5 (E_+(5)) | 2048 | 3.6×10¹⁶ | astronomical |
| 7 (E_+(7)) | 32768 | 3.6×10²² | impossible |

Sparse linear algebra alone doesn't change this — the bar resolution itself is the wrong substrate for m ≥ 3.

## The new substrate: HAP's compact resolution

HAP's `ResolutionFiniteGroup(G, n)` builds a free ZG-resolution with cells of count `O(|G| × poly(n))` — orders of magnitude smaller than the bar resolution at the same degree. E.g., the A-5a result (`#138`): `ResolutionFiniteGroup(E_+(5), 4)` succeeds at **1.2 GB / 9 min** vs. the bar-resolution's 10¹⁶ cells.

For m=7 specifically, HAP's `ResolutionFiniteGroup` OOMs at ~60 GB (#137). The replacement is `ResolutionFiniteExtension`: build R(E_+(m)) from R(V) and R(Z/2) via Lyndon-Hochschild-Serre perturbation. V = (F_2)^{2m} is elementary abelian and has minimal-size resolution; Z/2 has trivial resolution; their twisted product gives a small resolution of E_+(m).

## The new chain-level operations

HAP exposes the building blocks we need but doesn't bundle them as a Pontryagin-square pipeline:

- **`IntegralCupProduct(R, vec1, n1, vec2, n2)`** — integer cup product on cocycle vectors.
- **`HAP_PHI(G, N)`** — the chain map `R(C_2 × G) → R(G × G)` underlying Steenrod operations; the cup-i products are built from this.
- **`Sq` method** — cohomology-level Steenrod squares; built on top of `HAP_PHI`.
- **`HAP_chain_bockstein(C, n, p)`** — mod-p Bockstein, returns a hom of cohomology groups.
- **`ConnectingCohomologyHomomorphism`** — connecting hom for an SES; this is the algebraic side of `δ_4: H^3(Z/4) → H^4(Z)`.

What's missing for our use case:
- An **explicit cochain-level cup-1 product** `α ∪₁ β` on HAP's resolution (cohomology-level Sq isn't enough — we need the underlying cochain to plug into `α̃ ∪ α̃ + δα̃ ∪₁ α̃`).
- An **explicit cochain-level Pontryagin square** `P(α)` = Z/4-valued 2n-cocycle from F_2 n-cocycle α.
- An **integration step**: given the Z/4 2n-cocycle, find the corresponding (2n-1)-cocycle representative of the connecting-hom preimage class.

## Workstream B3: HAP-resolution Path 3

### B3-1 (issue #171 below): Cup-1 product on HAP resolutions
- File: `extraspecial_orbifolds/scripts/hap_steenrod_cup1.g`.
- API: `HAP_SteenrodCup1(R, alpha_vec, p, beta_vec, q)` returns the cup-1 product cocycle vector (degree p+q-1) on HAP's resolution R.
- Built from HAP_PHI or by direct construction. Verify the defining cup-1 coboundary identity at D_8 (mirror of #160's test).

### B3-2 (issue #172): Pontryagin square on HAP resolutions
- File: `extraspecial_orbifolds/scripts/hap_pontryagin_square.g`.
- API: `HAP_PontryaginSquare(R, alpha_F2_vec, n)` returns a Z/4-valued 2n-cocycle vector on R.
- Formula: `P(α) = α̃ ∪ α̃ + δα̃ ∪₁ α̃ mod 4` — same as #161, but using HAP's `IntegralCupProduct` and our B3-1 cup-1.
- Verify bar 2n-cocycle equation mod 4 on R's `dimension(2n)` cells.

### B3-3 (issue #173): Integration → Z/4 (2n-1)-cocycle on HAP resolutions
- File: `extraspecial_orbifolds/scripts/hap_integrate_to_z4_cocycle.g`.
- API: `HAP_IntegrateToZ4Cocycle(R, F_z4_vec, n)` returns f, a Z/4 (2n-1)-cocycle vector with `δ_4([f]) = [F]` in H^{2n}(Z).
- Two-stage linear solve same as #162 but on `R!.dimension(p)` × `R!.dimension(p+1)` matrices instead of `|G^p|` × `|G^{p+1}|`. Sizes drop drastically — at m=5, HAP's R has cells in the hundreds, not 10¹⁶.

### B3-4: m=3 anchor for B3 pipeline (retargets old #164)
- Run the B3 pipeline at m=3 using HAP's `ResolutionFiniteGroup(E_+(3), 4)`.
- Verify the resulting Z/4 3-cocycle is cohomologous to HAP's empirical ω_4 from `StandardCocycleOf`.
- Class equality test in H^3(G; Z/4).

### B3-5: m=5 anchor for B3 pipeline (retargets old #165)
- Run at m=5 using the same resolution A-5a built (cached on disk?).
- Cross-check against A-5b's empirical kernel.g once available.

### B3-6: m=7 production (retargets old #166)
- Build R(E_+(7)) via `ResolutionFiniteExtension(generators_E, generators_V, R_V, 4, ...)` — the central extension perturbation route.
- Run the B3 pipeline end-to-end.
- Output `computed/transgression/7/kernel.g`. Closes #137.

## What's preserved from the bar-resolution work

- **Steenrod cup-1 mathematics** (#160 merged): the formula and identities are universal. We're rewriting the implementation on a different chain complex, not changing the math.
- **Pontryagin square formula** (#161 merged): identical formula `α̃ ∪ α̃ + δα̃ ∪₁ α̃`, just evaluated on HAP's chain complex.
- **Two-stage linear-solve algorithm** (#162 merged): identical logic, smaller matrices.
- **m=1 (D_8) regression** stays as the algorithmic correctness check.

The bar-resolution files (`steenrod_cup1.g`, `pontryagin_square.g`, `integrate_to_3cocycle.g`) are kept as **reference m=1 implementations** with cleaner semantics than HAP's, used for cross-checking the HAP-resolution versions during B3-1/B3-2/B3-3 development.

## Out of scope for this redesign

- A direct cochain formula (#163, closed): not found in the literature; remains an open question.
- Sparse Z linear algebra over bar resolutions: parked alongside Path 3 bar.
- Z/8 cocycles (m=2 cyclic A(4) = Z/8 per H-K): different formula (P²), separate problem if pursued.

## Why this should work for m=7

R(E_+(7)) via `ResolutionFiniteExtension` is conjectured tractable. V = (F_2)^14 has resolution of size O(deg^14), but for our degree-5 needs that's polynomial-bounded. The perturbation construction adds the central Z/2 extension cleanly. End result: chain modules in degrees 0..5 each of size O(thousands), well within memory.

Empirical confirmation gap: nobody's actually built R(E_+(7)) via ResolutionFiniteExtension yet. **First experimental risk** is B3-6 setup; the rest follows mathematically.

## References

- `docs/superpowers/specs/2026-05-15-path3-pontryagin-square-design.md` (bar-resolution spec; superseded by this doc).
- HAP `lib/CohomologyOperations/mycupi.gi`, `chainbockstein.gi`, `connecting_homomorphism.gi`.
- HAP `lib/Perturbations/resExtension.gi`, `resFiniteExt.gi`.
- Steenrod 1947, Brumfiel-Morgan 1973 (for the underlying math, unchanged).
