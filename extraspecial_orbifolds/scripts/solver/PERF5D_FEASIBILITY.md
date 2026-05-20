# A-7 perf-5d feasibility assessment (#283)

## Verdict: **Intractable** within the 3-4 hour budget. Phase 1 ABORTED, no prototype code pushed.

The minus-I central element gives a 2-cocycle `c_{-I}(omega_i)` on E_+(m) whose **cohomology class** factors through V := E_+(m)/⟨z⟩ ≅ F_2^{2m}. However, HAP's specific cocycle representative does NOT factor through V at the cocycle level, has no clean low-degree algebraic structure, and cannot be reproduced bit-identically without HAP. The "cohomology-equivalent" weakening — produce ANY cocycle in the same H² class — is also blocked, because identifying the V-class symbolically without HAP requires Quillen-presentation infrastructure (Q-int workstream) that is not yet in production.

## What the existing infrastructure does (refresher)

`solver/snf_wrapper.g :: BuildPerClassCocycleBasis(setup, gRep, C)` builds an integer (n² × k) table where row `(a-1)*n + b` gives the values
- `c_{omega_i}(gRep, elts[a], elts[b]) = omega_i(gRep, a, b) - omega_i(a, gRep, b) + omega_i(a, b, gRep)`

across `i ∈ [1..k]`. Each row entry is `Syzygy(R, [...]) · UCT.cocyclebasis[i]`. The dominant cost at m≥3 is the `Syzygy` chain walks (`3·n² = 12·n²` length-2 sub-syzygies, plus the `Homotopy(2, _)` accumulator). The current implementation already includes A-7 perf-5 Route A (`#281`) and perf-5b Route B (`f8542cc`) optimisations.

For `gRep = -I`, the centraliser is the full group E_+(m). The natural hope is that the resulting 2-cocycle on E_+(m) has SPECIAL closed-form structure exploiting the central extension `1 → ⟨z⟩ → E_+(m) → V → 1`. Phase 1 here tested that hope and reports back.

## What we tried in Phase 1 (m=2: |G|=32, k=10, exp=8)

The empirical bootstrap was a single one-shot `BuildPerClassCocycleBasis(setup, zG, G)` call (~0.4 s wall), then characterisation of the resulting 1024 × 10 integer table.

### 1. Per-column structural inspection

| col i | non-zero rows / 1024 | distinct values (mod 8) | order of class in Z/8 |
|-------|---------------------|-------------------------|-----------------------|
| 1     | 482                 | {0, 4}                  | 2                     |
| 2     | 498                 | {0, 4}                  | 2                     |
| 3     | 0                   | {0}                     | 1 (identically 0)     |
| 4     | 0                   | {0}                     | 1 (identically 0)     |
| 5     | 288                 | {0, 4}                  | 2                     |
| 6     | 360                 | {0, 4}                  | 2                     |
| 7     | 404                 | {0, 4}                  | 2                     |
| 8     | 0                   | {0}                     | 1 (identically 0)     |
| 9     | 490                 | {0, 4}                  | 2                     |
| 10    | 820                 | {0..7}                  | 8                     |

Cols 3, 4, 8: trivially coboundary. Cols 1, 2, 5, 6, 7, 9: order-2 classes (values in {0, 4} = {0, exp/2}). Col 10: order-8 class (the Z/8 invariant factor).

### 2. Does the cocycle factor through V at the cocycle level?

**No.** Picking V := G/⟨z⟩ and the natural projection π : G → V, we tested whether `c_{-I}(ω_i)(h, k)` depends only on (π(h), π(k)). For all non-zero columns, the table value differs across the z-fiber. Specifically, for column 1 at (π(h)=e, π(k)=f1), the (t_h, t_k)-indexed block is

```
  block[t_h+1][t_k+1] = [[0, 0], [4, 4]]
```

which means `c(z, f1) = 4, c(e, f1) = 0` — distinct values at different z-shifts. The non-zero cocycles **do NOT factor through V cell-by-cell at the cocycle level**, only at the cohomology level.

### 3. Pure-symplectic fit (the issue's hypothesis)

Tested `c_{-I}(ω_i)(h, k) =? α_i · B(π(h), π(k)) · (exp/2)` where B is the F_2-symplectic commutator form on V. **Only the zero columns fit**; all non-zero columns reject this ansatz.

### 4. Affine bilinear fit in (v, t) coordinates

With each element g ↦ (v_g_1, v_g_2, v_g_3, v_g_4, t_g) ∈ F_2^5 (PC-basis v-coords + z-shift), tried fitting
```
  c(g, h) = c_0 + Σ_i α_i · g_i + Σ_j β_j · h_j + Σ_{ij} γ_{ij} · g_i · h_j
```
(36 coefficients, vs 1024 data points). **Only zero columns fit.**

### 5. Full multilinear Möbius expansion (the unique canonical polynomial form)

The 10-binary-variable function space has 2^{10}=1024 monomial degrees of freedom, and the function table has exactly 1024 data points (32 × 32), so the multilinear expansion is uniquely determined. Counting non-zero monomial coefficients:

| col i | non-zero monomials | max degree |
|-------|-------------------|------------|
|  1    | 104               | 6          |
|  2    | 170               | 6          |
|  3    | 0                 | 0          |
|  4    | 0                 | 0          |
|  5    | 52                | 4          |
|  6    | 84                | 5          |
|  7    | 128               | 5          |
|  8    | 0                 | 0          |
|  9    | 170               | 6          |
| 10    | 592               | 9          |

These are **not clean low-degree forms**. HAP's representative encodes high-degree multilinear data tied to its specific bar-resolution + Syzygy + Homotopy choices.

### 6. Cohomology-equivalence attempts

Replacing HAP's table with a "section-sampled" or "inflated-from-V" table (c'(g, h) := c_HAP(sec(π(g)), sec(π(h))) for a fixed PC-canonical section sec : V → G) was tested as a cohomology-equivalent fast path:

- The section-sampled c' is **not even a 2-cocycle on V** for non-zero columns (the section is not a homomorphism — E_+(m) is a non-trivial central extension of V).
- The inflated table differs from HAP's by something that is **not a coboundary on G** for any non-zero column.
- Random-vec sweep on IsCoboundary2 verdicts: 30/64 agree, 34/64 **disagree**.

So substituting the section-sampled cocycle breaks the kernel computation. Inflation-from-V is not a valid cohomology equivalence on its own without a proper class-level lift.

## Why this is intractable in the budget

A correct cohomology-equivalent fast path would need:

1. A canonical algorithm to identify the H²(V; Z/exp) class of `c_{-I}(ω_i)` **without computing the slant on G first**. This requires the Quillen-presentation interpretation of `UCT.cocyclebasis[i]` (the Q-int workstream — partially landed via #234, #238, #244 per the issue brief; not yet in production for arbitrary m).

2. Given a V-class, construct a canonical 2-cocycle on G in that class — i.e. a representative of the inflation. This requires a controlled section + section-cocycle treatment of the central extension, plus a class-correction step to land in the desired class.

3. Verify the resulting table gives the same `IsCoboundary2Split` answer as HAP's table on the kernel.

Step 1 is the blocker. Without Q-int's symbolic interpretation of `cocyclebasis[i]`, the V-class can only be identified by running HAP's slant — which is the very cost we wanted to avoid.

The alternative — replicating HAP's specific cocycle representative directly via a closed form — was the original goal. Phase 1 has shown that HAP's representatives have degree-up-to-9 multilinear support with no clean algebraic structure, so this avenue is also infeasible.

## Files inspected (no edits)

- `extraspecial_orbifolds/scripts/transgression_kernel.g` — slant-product structure, `SetupCohomology3`, `StandardCocycleOf`, `IsCoboundary2`.
- `extraspecial_orbifolds/scripts/solver/snf_wrapper.g` — `BuildPerClassCocycleBasis`, the (n², k) integer table, the slant-product formula.
- `extraspecial_orbifolds/scripts/quillen_detecting_subgroup.g` — `EPlusGroup(m)`, the symplectic structure on V.
- `extraspecial_orbifolds/scripts/em_construction.g` — explicit matrix realisation of E_+(m).
- `extraspecial_orbifolds/scripts/qforms_f2.g` — F_2 linear algebra helpers.

## Investigation artefacts (not committed; live at /tmp/a7p5d_work/)

- `phase1_m2_bootstrap.g`, `phase1_m2.txt` — initial column statistics.
- `phase1_m2_analysis.g`, `phase1_m2_analysis.txt` — proof that the raw cocycle does NOT factor through V cell-by-cell.
- `phase1_m2_deviation.g`, `phase1_m2_deviation.txt` — z-shift dependence per column; second-difference table.
- `phase1_m2_fit.g`, `phase1_m2_fit.txt` — failed 25-coefficient bilinear regression.
- `phase1_m2_fit2.g`, `phase1_m2_fit2.txt` — failed 36-coefficient affine+bilinear regression.
- `phase1_m2_multilin.g`, `phase1_m2_multilin.txt` — full Möbius/Fourier expansion showing high-degree support.
- `phase1_m2_cohom_equiv_test.g`, `phase1_m2_cohom_equiv_test.txt` — section-sampled "cleansed" table fails as a cohomology equivalent.
- `phase1_m2_inflate.g`, `phase1_m2_inflate.txt` — section-sampled c_V isn't a V-cocycle; inflated diff isn't a G-coboundary; 34/64 vec verdicts disagree.

## Recommendations for follow-up

Two viable directions:

### A. Optimise HAP's chain layer (perf-5c continuation, #282)

The perf-5b feasibility doc identified the real bottleneck as `AddFreeWords`'s quadratic linear-scan `Position` inside `Homotopy(2, ...)`. A dictionary-keyed `AddFreeWords` is expected to give 3-10x on the dominant cost. **This lever is independent of central-class structure** and helps every orbit, not just orbit 2.

### B. Build out Q-int symbolic interpretation of UCT.cocyclebasis

If Q-int provides a symbolic-polynomial representation of each `cocyclebasis[i]` in the Quillen presentation, then:
- The class of `c_{-I}(ω_i)` on V is readable directly from the polynomial (slant by z corresponds to a specific operation on the Quillen ring — e.g. partial derivative).
- A canonical V-cocycle in that class can be built from V's much smaller `BuildPerClassCocycleBasis` (|V|² = 256 at m=2, 1024 at m=3, ~10⁶ at m=5 — comparable to G's, so not a free win for m=5).

Even Direction B does not obviously give a HUGE speedup over the optimised HAP path at m=5 (the V-level cocycle build is the same order of work). The main win would be at the kernel-detection layer where the V-cohomology data is consumed.

### C. Pragmatic: cache HAP's central-class tables across runs

Less elegant but immediately useful: persist the c_{-I} table to disk after the first slow build, then load from disk on subsequent runs. Saves ~30s (m=3) / ~1 hour (m=5) per re-run with the same (G, exp) signature.

## Time spent

~90 min of Phase 1 wall. Hit the user-instruction signal ("If Phase 1 takes more than 90 min, that's a signal to either narrow the scope or abort with the feasibility doc."). Choosing to abort: the closed-form does not exist for HAP's representative, and the cohomology-equivalent alternative is blocked on Q-int.

## Open caveats

- The `c_{-I}(ω_i)` cocycle on E_+(m) is determined **up to coboundary** by its H²(V; Z/exp) class. The COCYCLE-level representative is, however, **canonically chosen by HAP** based on its bar/Syzygy infrastructure — and is intrinsically non-V-factorisable.
- Even if one could replicate HAP's representative bit-identically, the speedup would only apply to the central element class (orbit 2 in the perf-1 BRW orbit structure). Other orbits would still pay full HAP cost.
- The cohomology-equivalence path becomes viable if and only if the downstream `IsCoboundary2Split` and `PerVecTransgressionShared` driver paths formally accept the equivalence (they do, as documented in `BuildPerClassCocycleBasisForOrbit`'s "mod 2-coboundary on C(g')" caveat). The block is purely on the side of identifying V-classes without HAP.
