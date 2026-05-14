# Quillen Integration: Replace HAP `ResolutionFiniteGroup` in `SetupCohomology3`

> **For agentic workers:** This is a multi-session research plan. Stage A is implementable in a single focused session; Stage B is research-grade and may take 3-5 sessions. Use this document as the scope-of-work contract.

**Goal:** Make `SetupCohomology3(E_+(m))` work for m=7 without OOM. The current HAP path (`ResolutionFiniteGroup(E_+(7), 4)` → `TensorWithIntegers` → `UniversalCoefficientsTheorem`) consumes 60 GB and dies.

**Architecture.** Two pieces of HAP work are being replaced:

1. **H^3 structure** (`torsion, exponent, num_generators`) — analytical via Quillen's [Q4] Theorem 4.6 + Bockstein spectral sequence on the canonical presentation from Q-2a (issue #133).
2. **Cocycle evaluation** (`StandardCocycleOf(setup, vec)` returning a callable `ω : G^3 → Z/exp`) — explicit closed-form bar 3-cocycles per Quillen H^3 generator, eliminating the dependence on HAP's `StandardCocycle` (which has the V-4a bar-equation bug as a side issue).

**Tech stack:** GAP 4.15.1, HAP 1.70 (compiled), Q-2a canonical presentation (issue #133 in PR review).

---

## Stage A: `QuillenH3Structure(m)` — analytical H³ shape

**Scope:** For m ≥ 1, return `(torsion, exponent, num_generators)` matching HAP on m = 1, 2, 3 byte-for-byte; provide values for m = 5, 7 derivable from Quillen + Bockstein.

**Known values** (anchored from `computed/transgression/2/kernel.g` and the just-completed E_+(3) kernel.g):
- m = 1 (D_8): `torsion = [2, 2, 4]`, exp = 4, k = 3.
- m = 2 (E_+(2)): `torsion = [2, 2, 2, 2, 2, 2, 2, 2, 2, 8]`, exp = 8, k = 10.
- m = 3 (E_+(3)): `torsion = [2 (×34), 4]`, exp = 4, k = 35.
- m = 5, 7: to derive from Quillen + Bockstein (this Stage's research output).

**Method.** From Quillen's theorem 4.6:
`H*(E_+(m); F_2) = F_2[x_1, ..., x_{2m}] / J  ⊗  F_2[w]` with `deg(w) = 2^m`,
J = (Q, B(x, x^2), ..., B(x, x^{2^{m-1}})).

Bockstein β: H^n(G; F_2) → H^{n+1}(G; F_2) acts as a derivation with `β(x_i) = x_i^2`, `β(w) = ?`. Iterated Bocksteins determine the integral cohomology torsion structure. For H^4(E_+(m); Z) ≅ H^3(E_+(m); U(1)):
- Image of β at degree 3 gives 2-torsion classes (Z/2 contributions).
- Kernel of β at degree 4 not in image of β: lift to Z/4 (or higher) — the "honest higher-order" classes.

**Implementation plan.**

### Task A1: Document Bockstein action on Quillen generators

**Files:** Create `extraspecial_orbifolds/scripts/quillen_bockstein.g`.

- [ ] Provide `BocksteinOnGenerator(m, gen_name)` returning the F_2 image of β.
- [ ] For x_i (deg 1): β(x_i) = x_i².
- [ ] For w (deg 2^m): β(w) = ? (derive from Quillen — likely 0 or a specific polynomial).
- [ ] Test against HAP-computed Bockstein at m = 1 on a few classes.

### Task A2: Compute integral H^4(E_+(m); Z) torsion

**Files:** `extraspecial_orbifolds/scripts/quillen_h3_structure.g`.

- [ ] Implement `QuillenH3Structure(m)` using the F_2 cohomology data + Bockstein from Task A1.
- [ ] Algorithm: enumerate F_2 basis of H^3 and H^4, compute β, find kernel/image to determine torsion factors.
- [ ] Acceptance: for m ∈ {1, 2, 3}, output equals HAP's `UCT.torsion`. Test in `tests/test_quillen_h3_structure.g`.

### Task A3: Predict m = 5, 7

- [ ] Run `QuillenH3Structure(5)`, `QuillenH3Structure(7)`. Document outputs.
- [ ] Cross-check m = 5 against HAP if HAP can handle it (E_+(5) at 512 elements may be tractable).
- [ ] m = 7 is the unlock: predicted torsion should be derivable from the F_2 computation we already have via Q-2a.

---

## Stage B: `QuillenBarCocycle(m, vec)` — explicit bar 3-cocycles

**Scope:** For each H^3(E_+(m); U(1)) coordinate vector vec, return a callable `ω: E_+(m)^3 → Z/exp` that is a STRICT bar 3-cocycle (satisfies the bar 3-cocycle equation, unlike HAP's `StandardCocycle`).

**This is research-grade math.** The derivation requires:
- Explicit bar 3-cocycle formulas for each Quillen H^3 generator of E_+(m).
- For the 2-torsion (Z/2) generators: cup-products of degree-1 classes via the standard simplicial cup product formula.
- For the Z/4 / Z/8 generators: lift via the Pontryagin square or iterated Bockstein.

**Implementation plan.**

### Task B1: Bar 3-cocycle for cup products

**Files:** `extraspecial_orbifolds/scripts/bar_cocycle.g`.

- [ ] `CupProduct1x1x1(x, y, z)` — for three deg-1 classes interpreted as homomorphisms G → F_2, compute the bar 3-cocycle (g, h, k) ↦ x(g)·y(h)·z(k).
- [ ] `BarCocycleFromMonomial(m, mon_exps)` — for a Quillen monomial like x_1² x_3, build the bar 3-cocycle by combining cup products and Bockstein lifts.
- [ ] Verify each builder's output satisfies the bar 3-cocycle equation on small groups.

### Task B2: Bockstein lifts for higher-torsion generators

- [ ] Implement the Pontryagin square or iterated Bockstein at the cocycle level to produce Z/4-valued bar cocycles from Z/2 bar cocycles.
- [ ] Use this for the order-4 generator of D_8 and the order-4 generator of E_+(3); for E_+(2), the order-8 generator.

### Task B3: Putting it together

- [ ] `QuillenBarCocycle(m, vec)` linear-combines the per-generator bar cocycles with coefficients from `vec`.
- [ ] Reduces mod `exp` to give a callable `G^3 → Z/exp`.

### Task B4: Cross-check against HAP at m = 1, 2

- [ ] For each kernel vec in the verified `computed/transgression/2/kernel.g`, build the Quillen bar cocycle and verify it produces the same transgression-kernel verdict (in-kernel / not-in-kernel) as HAP.
- [ ] Acceptance: E_+(1) kernel = `{[0,0,0], [0,1,2], [1,0,0], [1,1,2]}`. E_+(2) `|ker Tr| = 2048` from `computed/transgression/2/kernel.g`.

---

## Stage C: Wire into `SetupCohomology3`

**Scope:** Add a `setup.cocycle_source` field in `SetupCohomology3` that can be `"hap"` (default) or `"quillen"`. Route `StandardCocycleOf` through the chosen source.

**Implementation plan.**

### Task C1: Refactor `SetupCohomology3`

- [ ] Modify `transgression_kernel.g`'s `SetupCohomology3(G, [optional source])` to support a Quillen path.
- [ ] When `source = "quillen"`, populate `torsion, exponent, num_generators` from `QuillenH3Structure(m)` instead of HAP UCT.
- [ ] Override `StandardCocycleOf(setup, vec)` to use `QuillenBarCocycle(m, vec)` when Quillen-routed.

### Task C2: Verify m = 1, 2, 3 byte-for-byte

- [ ] Re-run D_8 regression: `|ker Tr| = 4`, exact kernel vecs match.
- [ ] Re-run E_+(2) anchor: `|ker Tr| = 2048`.
- [ ] Re-run E_+(3) driver: `|ker Tr| = 2^36`, total wall ≤ 10 min (cross-check against HAP-routed baseline).

### Task C3: Unlock m = 7

- [ ] Run the full A-3a-style driver on E_+(7) via the Quillen path.
- [ ] Persist `computed/transgression/7/kernel.g`.
- [ ] Document timing and memory.

---

## Acceptance gates

1. **Stage A gate** (this session): `QuillenH3Structure(m)` matches HAP at m = 1, 2, 3. Outputs documented for m = 5, 7.
2. **Stage B gate** (research): Quillen bar cocycles pass the bar 3-cocycle equation on Q_8 / D_8 (closes V-4a as a side benefit).
3. **Stage C gate** (integration): Byte-for-byte match for E_+(2) and E_+(3) ker Tr via the Quillen path. m = 7 produces a kernel within memory budget (< 16 GB).

## Out of scope (for now)

- Performance optimisation of Quillen cocycle evaluation.
- Generalisation beyond extraspecial 2-groups (the Quillen formula is specific to E_+(m); other groups would need their own treatment).
- The full Stage 2 verification of mixed-kernel-combinations at m = 7.
