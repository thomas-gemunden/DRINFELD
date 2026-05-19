# Chain-level diagonal Δ : R → R⊗R on HAP's compact resolution

> Follow-up to Q-int B3-2 (#171). Discovered while implementing the
> Pontryagin square on HAP's `ResolutionFiniteGroup` / `ResolutionPrimePowerGroup`.

## Problem

HAP exposes `IntegralCupProduct(R, u, v, p, q)` for cohomology-class
cup products. Under the hood it builds a "cup-with-α" chain map via
`CR_ChainMapFromCocycle(R, u, p, q)`. **That chain map is built
assuming `u` is a cocycle** — for a non-cocycle `u` (in particular
the {0,1}-integer lift `α̃` of an F_2 cocycle, which is *not* a
Z-cocycle), the resulting cup product:

- is bilinear in both arguments ✓
- but does NOT satisfy the Leibniz rule:
  `d(α̃ ∪ α̃) ≠ cup(δα̃, α̃) + cup(α̃, δα̃)` ✗

Direct verification at D_8 = `SmallGroup(8, 3)` on the
`ResolutionPrimePowerGroup(D_8, 6)` resolution
(`R!.dimension = [1,2,3,4,5,6]`) with α = `[0, 0, 1]` (a non-trivial
F_2 2-cocycle whose integer lift α̃ has `δα̃ = [2, 4, 0, 2] ≠ 0`):

```
α̃ ∪ α̃          = [14, 13, 12, 0, 3]
d(α̃ ∪ α̃)      = [54, 128, 86, 24, 0, 6]
cup(δα̃, α̃)    = [86, 210, 104, 24, 0, 10]
cup(α̃, δα̃)    = [2854, 5306, 5048, 1228, 0, 742]
sum            = [2940, 5516, 5152, 1252, 0, 752]    ≠ d(α̃∪α̃)
```

So the Brumfiel-Morgan formula `P(α) = α̃ ∪ α̃ + δα̃ ∪₁ α̃ mod 4` does
not produce a Z/4 cocycle when computed this way. At D_8, our
implementation gives `P(α) = [0, 3, 2, 0, 3]` with `d(P) mod 4 =
[2, 0, 2, 0, 0, 2]` — 3 of 6 cocycle equations fail.

Additionally, HAP_PHI (the other candidate for cup-1) builds an
internal `ResolutionPrimePowerGroup` and `AlgebraicReduction`s mod 2.
Its output is correct **mod 2** but its signs are not integer-meaningful,
so it cannot produce a Z-coefficient cup-1 either.

## Goal

Implement a true chain-level diagonal

  Δ : R → R⊗R

on HAP's compact resolution `R = ResolutionFiniteGroup(G, N)` (or
`ResolutionPrimePowerGroup(G, N)`), together with the level-1 cup-1
homotopy

  h_1 : R → (R⊗R)[+1]    with    d h_1 + h_1 d = τΔ − Δ

(where τ swaps tensor factors). Both should be **integer-valued** so
that the Brumfiel-Morgan formula yields a proper Z/4 cocycle.

## Approach

Standard inductive construction. R is acyclic over ZG; R⊗R is a free
resolution of G via the diagonal embedding `Δ_G: G → G×G`. We build Δ
generator-by-generator using R⊗R's contracting homotopy.

### Step 1: data structure for R⊗R chains over ZG

We avoid HAP's `EquivariantChainMap` because its internals call
`ImagesRepresentative` on group homomorphisms in ways that fail at
degree ≥ 1 for our G (verified). Instead, use a direct representation:

A chain in (R⊗R)_n is a list of records (or 6-tuples)
`[sign, p, q, j_p, j_q, g]` where:

- `(p, q)` is the bidegree, `p + q = n`
- `j_p ∈ [1..R!.dimension(p)]`, `j_q ∈ [1..R!.dimension(q)]` are
  generator indices
- `sign ∈ {+1, −1}` is the integer coefficient sign (combine
  duplicates by adding integer coefficients)
- `g` is a position in `R!.elts` (the diagonal `(g, g)` acts on both
  factors since we view R⊗R as a ZG-module via the diagonal)

Helper operations:
- `_Boundary_RR(chain)`: ∂ of an `(R⊗R)_n`-chain, returning an
  `(R⊗R)_{n−1}`-chain. Uses `R!.boundary`:

      ∂(e_p^j ⊗ e_q^k)·g
        = (∂_R e_p^j)·g ⊗ e_q^k + (−1)^p e_p^j ⊗ (∂_R e_q^k)·g

- `_Homotopy_RR(chain)`: contracting homotopy
  `s: (R⊗R)_n → (R⊗R)_{n+1}` with `∂s + s∂ = id − aug`. Standard
  tensor-product formula:

      s(e_p^j ⊗ e_q^k)·g
        = h_R(e_p^j)·g ⊗ e_q^k                          (if p ≥ 1)
        + (−1)^p (aug e_p^j) · h_R(e_q^k)·g             (if p = 0)

  where `h_R` is `R!.homotopy`. This relies on R having a contracting
  homotopy that's a Z-module map (not necessarily ZG-equivariant); HAP
  resolutions provide this.

### Step 2: inductive Δ

`Δ_data[n][i]`: cached `(R⊗R)_n`-chain for the i-th generator of R
at degree n.

- `n = 0`: `Δ(e_0^1) = [(+1, 0, 0, 1, 1, IDEN)]` (diagonal embedding
  of the unique generator at degree 0).
- `n > 0`:

      let bdr = R!.boundary(n, i)        # in (R)_{n−1}
      c = sum over (sgn_j, g) in bdr of sgn_j · g · Δ_data[n−1][|j|]
      # (apply g via diagonal: shift the `g` field in each term by g)
      # c is an (R⊗R)_{n−1}-cycle (since ∂_RR ∘ Δ = Δ ∘ ∂_R on the
      # lower-degree data, and ∂_R∂_R = 0)
      Δ_data[n][i] = _Homotopy_RR(c)

Sanity invariants to check:
1. `∂_RR(Δ_data[n][i]) = Δ_data[n][i]_bdr`, computed both ways.
2. Δ commutes with the ZG-action (via diagonal): `g · Δ(e) = Δ(g · e)`.
3. Δ projects to e_n ⊗ aug at first factor and aug ⊗ e_n at second
   (Alexander–Whitney boundary conditions).

### Step 3: cup product from Δ

For α a p-cochain, β a q-cochain on R:

    (α ∪ β)[i] = sum over (sgn, p', q', j_p', j_q', g) in Δ_data[p+q][i] of
                 [if (p', q') = (p, q): sgn · α[j_p'] · β[j_q'] else: 0]

Note: g doesn't enter because we're evaluating cochains (linear over
ZG up to coboundary; the chain-level cup ignores g for cochain
evaluation).

### Step 4: inductive h_1 (cup-1 homotopy)

τΔ is `Δ` with factors swapped: `(sgn, p, q, j_p, j_q, g) ↦
(sgn · (−1)^{pq}, q, p, j_q, j_p, g)` (Koszul sign).

For each generator e_n of R, the chain `τΔ(e_n) − Δ(e_n)` is a cycle
(both Δ and τΔ are chain maps). Define `h_1(e_n)` so that `∂ h_1(e_n)
= τΔ(e_n) − Δ(e_n) − h_1(∂e_n)`, by the same homotopy-lift trick:

- `n = 0`: `h_1(e_0) = 0` (both Δ and τΔ agree at degree 0; cycle is 0).
- `n > 0`:

      let lhs = τΔ(e_n) − Δ(e_n) − h_1(∂_R e_n)
      h_1(e_n) = _Homotopy_RR(lhs)

### Step 5: integer cup-1 from h_1

For α a p-cochain, β a q-cochain on R:

    (α ∪₁ β)[i] = sum over (sgn, p', q', j_p', j_q', g) in h_1_data[p+q−1][i] of
                  [if (p', q') = (p, q): sgn · α[j_p'] · β[j_q'] else: 0]

### Step 6: replace HAP_ChainCupProduct_Int and HAP_SteenrodCup1_Int

Use the new Δ-based and h_1-based functions throughout. Drop the
HAP_PHI dependence except for F_2 cup-1 (which still works on
ResolutionPrimePowerGroup, but we won't need it once integer cup-1 is
available).

## Acceptance tests

At D_8 on `R = ResolutionFiniteGroup(D_8, 5)`:

1. **Δ chain-map property**: for each (n, i) with n ∈ [0..4]: 
   `∂_RR(Δ_data[n][i]) = (Δ ∘ ∂_R)(e_n^i)`. Zero violations.
2. **Leibniz of integer cup**: for each (p, q) ∈ {(2,2), (2,3), (3,2), (3,3)}
   and each (α, β) cochain pair (use small support):
   `d(α∪β) = (dα)∪β + (−1)^|α| α∪(dβ)`. Zero violations.
3. **h_1 chain-homotopy property**: for each (n, i) with n ∈ [0..4]:
   `∂_RR(h_1[n][i]) = (τΔ − Δ)(e_n^i) − h_1(∂_R e_n^i)`. Zero
   violations.
4. **Cup-1 coboundary identity**: for α an F_2 n-cocycle and β an
   F_2 n-cocycle (n ∈ {1, 2}):
   `d(α∪₁β) = α∪β + β∪α (mod 2)`. Zero violations.
5. **Pontryagin square Z/4 cocycle**: at D_8 for the chosen α F_2
   2-cocycle, `d(P(α)) mod 4 = 0`. **0 of 6 violations** (currently
   3/6 — the failing case).
6. **Pontryagin square non-triviality**: `P(α)` has at least one
   non-zero entry mod 4. ✓ (already passes).
7. **Mod-2 reduction**: `P(α) mod 2 = (α ∪ α) mod 2`. ✓ (already passes).

## Out of scope (next-tier issues)

- E_+(2), E_+(3) anchor tests (#164, #165).
- Integration of `P(α)` to a Z/4 3-cocycle (B3-3 / #172).
- Performance optimisation for E_+(5+).

## References

- Brumfiel & Morgan, *Quadratic functions, the index mod 8, and a
  Z/4-Hirzebruch formula*, Topology 12 (1973), 105–122. Local copy:
  `docs/main.pdf`. Lemma 3.5(b) is the relevant formula.
- HAP source: `lib/Rings/cocycleChainMap.gi`,
  `lib/Rings/cupProduct.gi`, `lib/CohomologyOperations/mycupi.gi`,
  `lib/Functors/equiChainMap.gi`. The Δ construction here parallels
  the bar-resolution version in `extraspecial_orbifolds/scripts/pontryagin_square.g`
  (#161) but at the chain level on HAP's compact resolution.
- HAP_PHI in `mycupi.gi` is structurally analogous but mod-2 only and
  on its own `RG = ResolutionPrimePowerGroup`, so cannot be reused.
