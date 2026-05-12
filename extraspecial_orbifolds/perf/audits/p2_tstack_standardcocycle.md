# P-2 audit: T-stack `StandardCocycle` callsites

Goal: find other instances of the PR #108 hoist pattern — `Syzygy(R, [g, h, k])` redundantly computed across cocycle vectors with a fixed triple.

## Callsites inspected

| File | Line | Context | Verdict |
|---|---|---|---|
| `src/modular_data.g` | 702 | `SaveModularDataParallel` driver loop: per-orbit `omega := StandardCocycle(R, vector, 3, exp); ComputeModularData(...)` | **No intra-call hoist** (closure built ONCE per orbit). See "cross-orbit" note below. |
| `src/modular_data.g` | 905 | `ComputeNonAbelianDataForeverParallel` driver loop: same pattern as 702. | Same as 702. |
| `src/modular_data.g` | 969 | `ComputeALittleData`: single-cocycle entry point, one StandardCocycle call. | Trivially fine. |
| `extraspecial_orbifolds/scripts/fsi_wrapper.g` | 147 | `FSIContext(G, omega_vec)` builds `f := StandardCocycle(...)` once per context. | Already optimal — `FSIContext` is constructed once per (G, omega) and reused across all `FSIAllAtClass` calls; P-3 (#120) further caches `pi_values_cache` inside the same context. |
| `extraspecial_orbifolds/scripts/fsi_agt_wrapper.g` | 87 | Same pattern as fsi_wrapper.g. | Same verdict. |
| `extraspecial_orbifolds/scripts/standard_bar_cocycle.g` | 57, 90 | Thin pass-through wrappers around HAP `StandardCocycle`. | Trivially fine — no internal loop. |

**Summary:** all six current callsites build the `StandardCocycle` closure exactly once per `(R, vector, n, exp)` tuple. The PR #108 hoist (Syzygy out of the per-generator i-loop) does not apply at this layer because none of these callsites call `omega(g, h, k)` for VARYING cocycle vectors over a FIXED triple — they all hold the cocycle vector fixed and call `omega` for many different triples.

## Cross-orbit Syzygy memoisation (filed as follow-up)

The deeper hoist opportunity at modular_data.g lines 702/905 is **cross-orbit**: the driver loops over hundreds of cocycle orbits, each computing `ComputeModularData(G, omega, ...)` that calls `omega(g, h, k)` on many triples derived from $G$. The set of triples is determined by $G$ (and the conjugacy-pair enumeration in `GenerateSimpleObjects` / `GenerateModularData`), not by the cocycle vector. Caching `Syzygy(R, [g, h, k])` results across orbits would save a factor proportional to the orbit count.

**Out of scope here** because:

1. The fix requires wrapping HAP's `StandardCocycle` with a memoised chain-encoder + dot-product helper — a structural change, not the local hoist pattern P-2 was scoped to.
2. The A-3a driver (`run_e_plus_3_kernel.g`) does NOT use `ComputeModularData`; it uses `transgression_per_generator_brw.g` whose hot path was P-5's target (PR #119). Fixing this layer would benefit `SaveModularDataParallel`-style modular-data sweeps, not the A-3a kernel run.

Filed as a P-EPIC follow-up to revisit when the modular-data sweep cost becomes a bottleneck.

## Acceptance per #111

- [x] All 6 callsites in the listed files have a documented verdict.
- [x] No hoist found at this layer that wasn't already addressed by PR #108 / #119 / #120.
- [x] Cross-orbit Syzygy memoisation noted as a follow-up.
