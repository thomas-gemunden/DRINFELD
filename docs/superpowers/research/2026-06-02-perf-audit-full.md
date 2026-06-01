# Full-codebase perf audit — 2026-06-02 (issue #387)

## Trigger

Post-audit-2 (PR #386 merged audit-1 P1/P2/P3 + 8-pattern taxonomy from
the audit-2 doc on main), Step 4 of the A-5b m=5 production sweep remains
the dominant wall (per the latest sample, ~58% of CPU in
`ProdListScl + ProdVectorVector`, the interpreted integer matvec path).
Issue #387 commissions a thorough tier-3 sweep across the whole in-scope
codebase, covers all 15 named patterns (P1..P15), runs an empirical probe
of whether `ConvertToMatrixRep(M)` (without a field arg) actually engages
GAP's compiled `PROD_MAT_VEC_INT` on integer matrices, and produces a
prioritised punch list. Source-code modifications are out of scope; the
deliverable is this report + a docs-only PR.

## Sample evidence (post-#386)

The freshest available sample is `/tmp/gap_2026-06-01_215344_WI6e.sample.txt`
(taken at 2026-06-01 21:53). Header reports PID **72680** (not 79240 — the
sample target was a different live process). The `sample` binary is denied
from the audit harness, so this is the latest pre-existing sample and the
methodology adapts to it. The sample covers 8422 stack snapshots at 1 ms
intervals.

Top hot symbols (sort-by-top-of-stack, when ≥5 samples):

| Rank | Symbol | Count | % of 8422 | Pattern hit |
|----:|---|---:|---:|---|
| 1 | `ProdVectorVector` | 2425 | 28.8% | P2 (interpreted int matvec) |
| 2 | `PositionPRec` | 1152 | 13.7% | Type recheck during matvec |
| 3 | `DoExecFunc1args` | 765 | 9.1% | Interpreter closure dispatch (P3) |
| 4 | `EvalElmList` | 363 | 4.3% | Per-element interpreter |
| 5 | `FuncPROD_GF2MAT_GF2VEC` | 337 | 4.0% | Mod2 fast path (working) |
| 6 | `KTNumPlist` | 215 | 2.6% | Type recheck on plist matrix rows |
| 7 | `EvalMod` + `ModInt` | 308 | 3.7% | Rational mod (was P1) |
| 8 | `ProdIntFFE` | 171 | 2.0% | Int × FFE coercion |
| 9 | `EvalProd` + `EvalSum` | 145 | 1.7% | Per-cell arithmetic |
| 10 | `Solution<unsigned char>` | 21 | 0.25% | Mod2 SolutionMat (fast) |

Top tier interpretation: the 2425 `ProdVectorVector` samples (28.8%) are
in a single nested call stack (line 1307–1308 of the sample): an
`ExecAssLVar → ProdObject → ProdListScl → ProdVectorVector` chain inside
`ExecForRange` loop bodies, with the matmul/matvec operand being an
INTEGER matrix in plain plist-of-plist representation. This is the
"interpreted integer matvec" pattern (P2) that #382 attempted to fix.

The 1152 `PositionPRec` samples (13.7%) plus 215 `KTNumPlist` and 211
`TypePlistHomHelper` samples are all GAP's per-call list-type recheck —
the cost of NOT having an `IsMatrixObj`-tagged matrix. They cluster
directly above the `ProdListScl` frames, confirming the dispatch is
falling through the generic operation table per matvec.

Stack-trace cross-reference: the dominant matvec at this scale matches
`basis_cache.table * vec_target` in
`run_e_plus_m_kernel_hap.g:590` (Path A integer column rebuild — only on
the rare `vec_target[exp_index] != 0` branch, but each call iterates a
full n²×k matvec), `cache_orbit.table * vec_target_exp` in
`solver/transgression_matrix_reduced.g:1335` / `:1400` (fallback fail-
column hot path), and `H3MatrixForOrbitMember`'s `M_step * M_y` in
`solver/transgression_matrix_reduced.g:906`. All operate on plain integer
plist-of-plist matrices.

## P2 verification result

Probe (`/tmp/probe.g`), run via `gap -q -b /tmp/probe.g`:

```
BEFORE ConvertToMatrixRep:
  TNUM_OBJ(M) = 26               (T_PLIST_HOM)
  TNUM_OBJ(M[1]) = 54            (T_PLIST_CYC)
  IsMatrix(M) = true
  1000 matvec wall: 29 ms
AFTER ConvertToMatrixRep:
  TNUM_OBJ(M) = 26               (UNCHANGED — no-op!)
  TNUM_OBJ(M[1]) = 54            (UNCHANGED)
  1000 matvec wall: 29 ms        (UNCHANGED — no speedup)
AFTER ImmutableMatrix(Integers, ...):
  TNUM_OBJ(M2) = 27              (T_PLIST_HOM + IMMUTABLE)
  TNUM_OBJ(M2[1]) = 55           (T_PLIST_CYC + IMMUTABLE)
```

Follow-up probe (`/tmp/probe2.g`) sized to match the production matvec
(n=165, integer entries mod 4, 1000 matvec iterations):

```
Baseline (plist of plist):             29 ms  (TNUM 26 / 54)
ImmutableMatrix(Integers, M):          25 ms  (TNUM 49 / 55)   speedup ≈ 1.16x
```

**HEADLINE FINDING.** `ConvertToMatrixRep(M)` called WITHOUT a field
argument on an integer matrix is silently a NO-OP. TNUM unchanged,
matvec walltime unchanged. The fix landed in PR #382 ("tag matrix as
IsMatrixRep so downstream `M * v` dispatches to compiled
PROD_MAT_VEC_INT") DOES NOT do what its comments claim. This call appears
in **at least 9 production code sites** (see P2 findings below) and
silently confers no speedup at any of them.

The alternative `ImmutableMatrix(Integers, M)` does flip TNUM (26 → 49 =
IsRectangularList + integer-attr) and gives a small (~16%) matvec
speedup. But the underlying issue is more fundamental: GAP does not ship
a dense compiled `PROD_MAT_VEC_INT` for plain integer matrices the way
it does `PROD_MAT_VEC_GF2`. Matvec on plain integer plist-of-plist falls
through generic `ProdListScl → ProdVectorVector`, which IS the C-level
implementation but goes one element at a time with type dispatch each
cell. This is fundamental to GAP and cannot be cured by a flag change
alone. The right fixes are either (a) batch via GF(2) when possible, or
(b) move to native code via custom kernels or HAP wrappers (e.g.
`MultRowMatrix` for row-vector form).

## Findings by pattern

(Files marked **HIGH** are on the dominant hot path per the sample.
**MEDIUM** = hot file, hot function, but not in this sample's top
stack. **LOW** = setup, identity-class branch, or rare fallback.)

### P1: SolutionMat/SolutionIntMat IsRat propagation

| Line | File | Code | Risk | Notes |
|---|---|---|---|---|
| 230 | `solver/iterated_bockstein.g` | `sol := SolutionMat(A_F2_T, residual);` | LOW | Inside `IsCoboundary2Mod2WithLiftWitness` enumeration — but cached via `_GetCachedAF2T(C)`. Witness path, not Vec-path. |
| 269 | `solver/transgression_matrix_reduced.g` | `sol := SolutionIntMat(M_aug_T_full, c_vec);` | MEDIUM | Inside `project_full` closure of `BuildPCWithBockstein`. Per-class once. |
| 302 | `solver/transgression_matrix_reduced.g` | `sol := SolutionIntMat(P_C_rec.M_aug_T, c_vec_mod);` | MEDIUM | `ProjectVectorViaP_C` per-c_g call — n² × n² matrix at m=5. Comment at line 314 calls it "minutes per column". |
| 436 | `solver/transgression_matrix_reduced.g` | `sol := SolutionIntMat(fproj.M_aug_T_cached, c_vec_mod);` | MEDIUM | `FastProjectVector` — cached `M_aug_T_cached` but fresh SolutionIntMat each call. |
| 95, 97, 127, 134 | `brw_h3_action.g` | `SolutionMat(Z, ...)` / `SolutionIntMat(...)` fallback | LOW | One-time BRW setup. Already optimised (#329). |
| 268, 283 | `abelian_e_form_check.g` | `SolutionMat(TransposedMat(BC_2_F), alpha_vec_F);` / int variant | LOW | Out-of-hot-loop diagnostic; not in m=5 sweep. |
| 202, 402 | `cocyclebasis_quillen_bridge*.g` | `SolutionMat(A, b_vec);` | LOW | Quillen bridge, not on A-5b m=5 path. |

The previous SolutionMat→IsRat→QuoRat propagation chain is no longer
visible in the sample top — looks like #381's per-row `Int` cast on
`brw_h3_action.g:157` is engaged. P1 is mostly handled.

### P2: integer matrix not in IsMatrixObj rep (the dominant pattern post-#386)

VERIFIED via probe (above): `ConvertToMatrixRep(M)` without field arg is
a NO-OP on integer matrices. Every site below confers no measurable
speedup at the production scale.

| Line | File | Code | Risk | Notes |
|---|---|---|---|---|
| **165** | `brw_h3_action.g` | `ConvertToMatrixRep(M_y);` | **HIGH** | "tag matrix as IsMatrixRep so downstream M*v dispatches to compiled PROD_MAT_VEC_INT" — claim disproved by probe. The h3_matrices entries are used by H3VecAtTarget / H3MatrixForOrbitMember / ApplyH3Endomorphism per target in the fail-column sweep. |
| **276** | `brw_h3_action.g` | `ConvertToMatrixRep(result);` | **HIGH** | `ComposeH3Endomorphism` (used in `H3MatrixForOrbitMember` line 906 per Schreier step). |
| 289 | `brw_h3_action.g` | `ConvertToMatrixRep(M);` | LOW | `IdH3Endomorphism` — once per BRW setup. |
| 306 | `detecting_family_restriction.g` | `ConvertToMatrixRep(res_mat);` | MEDIUM | Restriction matrix; per-G build (LOW frequency). |
| **461** | `solver/orbit_cache_persist.g` | `ConvertToMatrixRep(table);` (load path) | **HIGH** | `basis_cache.table` — n²×k integer matrix used by `table * vec_target` in `run_e_plus_m_kernel_hap.g:590` (Path Z column) and `transgression_matrix_reduced.g:1335` (fail-column axis sweep). Comment claims compiled matvec; probe says no-op. |
| **699** | `solver/snf_wrapper.g` | `ConvertToMatrixRep(table);` (fresh build) | **HIGH** | Same `table` matrix as above, the freshly-built path. Same comment, same no-op. |
| 502 | `run_e_plus_m_kernel_hap.g` | `ConvertToMatrixRep(cache_table);` (identity orbit) | LOW | Identity class only; cache_table is all-zero. |
| 93 | `perf5b_measure_m3_cache.g` | `ConvertToMatrixRep(cache_table);` | LOW | One-off measurement script. |
| 572, 682 | `solver/snf_wrapper.g` | `ConvertToMatrixRep(basis_T);` / `(contrib_row);` | MEDIUM | Inside the basis-cache build. The product `(contrib_row * basis_T) mod exp` on line 684 IS the n×n×k integer matmul that builds the table; the surrounding ConvertToMatrixRep calls on operands are no-ops. |

**Other matrices NOT promoted that should be considered**:

| Line | File | Code | Risk | Notes |
|---|---|---|---|---|
| **906** | `solver/transgression_matrix_reduced.g` | `prod := M_step * M_y;` | **HIGH** | Inside `H3MatrixForOrbitMember` per-Schreier-step loop. Both M_step (h3_matrices[k_step]) and M_y are 165×165 integer matrices in plist-of-plist form. The matmul falls through to ProdListList. |
| **590** | `run_e_plus_m_kernel_hap.g` | `c_g_table := basis_cache.table * vec_target;` | **HIGH** | n² × k integer matvec at m=5: n²=4M, k=165. This is the per-target call inside PerVecTransgressionShared. |
| **1335** | `solver/transgression_matrix_reduced.g` | `c_g_table_exp := cache_orbit.table * vec_target_exp;` | **HIGH** | Same matvec shape as 590, in the fail-column axis enumeration loop (4-level nesting: fc × exp_axis_vec × orbit × target). |

### P3: closure form in arithmetic / hot path

Many hits; this is the highest-volume pattern. The dominant new finding
is on the closure that builds `vec_target_exp` for the fail-column sweep:

| Line | File | Code | Risk | Notes |
|---|---|---|---|---|
| **1326** | `solver/transgression_matrix_reduced.g` | `vec_target_exp := List([1..k], jj -> (M_y_j_exp[jj][fc] * exp_axis_vec) mod h3_torsion[jj]);` | **HIGH** | In the 4-level nested fail-column loop. k=165 closures per call. Should be `(M_y_j_exp{[1..k], [fc]} * exp_axis_vec) mod h3_torsion` or, since this is a single-column slice with a per-row mod, two compiled list ops. |
| **1396** | `solver/transgression_matrix_reduced.g` | `vec_target_exp := List([1..k], jj -> (M_y_j_exp[jj][exp_index] * 2) mod h3_torsion[jj]);` | **HIGH** | Same pattern, half-vec branch. |
| **144** | `solver/iscoboundary2_split.g` | `c_prime_vec := List(c_g_vec, x -> (((x mod setup.exponent) / r) mod 2));` | **HIGH** | Path A sweep entry; at m=5 c_g_vec has length n² = 4M. 4M closure dispatches per Path Z call. Should be `(((c_g_vec mod setup.exponent) / r) mod 2)`. |
| 540 | `solver/transgression_matrix_reduced.g` | `col_i_gf2 := List(table_gf2, row -> row[i]);` | MEDIUM | Per order-2 generator. k=165 closures, but only k×|order_2_gens| ≈ 165² total. |
| 645 | `solver/mod2_solver.g` | `row := List(c_g_vec, x -> (x mod 2) * one);` | MEDIUM | `_StackBVectorsForBatch`. Already batched but inner closure remains. n² per batch row. Should be `((c_g_vec mod 2) * one)` then `ConvertToVectorRep`. |
| 796, 836 | `solver/transgression_matrix_reduced.g` | `v := List([1..k_dim], j -> If_(M_y[j][i] mod 2 = 0, zero_gf2, one_gf2));` | MEDIUM | `UpdateColumnDispositionFromMBarGF2` GF(2) column-extract closures. k_dim=165 closures × k_dim columns. |
| 271, 305, 438 | `solver/transgression_matrix_reduced.g` | `a_coords := List([1..r_full], k_b -> sol[k_b] mod torsion_full[k_b]);` etc. | LOW | r_full ≤ 165 closures, called per c_g. |
| 1418 | `solver/transgression_matrix_reduced.g` | `half_vec := List([1..k], j -> If_(j = exp_index, 2, 0));` | LOW | Once per kernel call. |
| 875, 894 | `solver/transgression_matrix_reduced.g` | identity matrix `List([1..k_dim], l -> List([1..k_dim], i -> If_(l = i, 1, 0)))` | LOW | Each `H3MatrixForOrbitMember` start; would be `IdentityMat(k_dim)`. Once per call. |
| 213 | `solver/orbit_cache_persist.g` | `elts_exps := List(cache.elts, x -> ExponentsOfPcElement(pcgs, x));` | LOW | Per-cache save. n closures, but called O(n_orbits) only. |

The Path A sub-pattern `(vec_target mod 2) * one_gf2; ConvertToVectorRep(...)` 
on `run_e_plus_m_kernel_hap.g:614` (post-#381) is already vectorised
(no per-element closure). That fix worked and is the model for the rest.

### P4: symmetric / outer-product List builds

| Line | File | Code | Risk | Notes |
|---|---|---|---|---|
| 425 | `solver/mod2_solver.g` | `v := KroneckerProduct([alpha_vals], [alpha_vals])[1];` | — | Already fixed in #186/#221/#225 (was the n²-closure outer product). Documented as such. |
| 311 | `solver/iterated_bockstein.g` | `return KroneckerProduct([alpha], [alpha])[1];` | — | Same pattern, same fix landed. |

No new P4 hits in scope. The pattern is well-cleaned.

### P5: trivial-init `List([1..n], i -> 0)`

| Line | File | Code | Risk |
|---|---|---|---|
| 263, 456 | `solver/mod2_solver.g` | `b := List([1..n*n], i -> 0);` | **HIGH** at m=5 (4M closure dispatches per call inside `IsCoboundary2Mod2` slow-path adapter and `IsCoboundary2Mod2WithLift`). Fix: `ListWithIdenticalEntries(n*n, 0)`. Note: the Vec-API variants on line 294/343/504 already use `ListWithIdenticalEntries`. |
| 88 | `solver/cohomology_class.g` | `c_vec := List([1..n*n], i -> 0);` | MEDIUM (this file isn't on the A-5b m=5 path but is on test/spike paths). |
| 244, 263 | `solver/transgression_matrix_reduced.g` | `row_int := List([1..n*n], i -> 0);` / `c_vec := List([1..n*n], q -> 0);` | MEDIUM. Inside `BuildPCWithBockstein` per-Bockstein-row + per-c_func call. |
| 358 | `solver/transgression_matrix_reduced.g` | `B_T := List([1..n*n], i -> List([1..r], k_b -> 0));` | **HIGH** at m=5: n²×r allocation, ~660M closures (n²=4M × r ≈ 165). |
| 372 | `solver/transgression_matrix_reduced.g` | `M_small := List([1..r + n], rowidx -> List([1..n*n], colidx -> 0));` | **HIGH** at m=5. Should be `NullMat(r + n, n*n)`. |
| 403 | `solver/iterated_bockstein.g` | `result := List([1..n_eq], i -> 0);` | MEDIUM. `IB_DivBy2`, called per IB_RecCob level. n_eq = n². |
| 671 | `solver/transgression_matrix_reduced.g` | `M_bar := List([1..r_full], l -> List([1..k], i -> 0));` | MEDIUM. Only when r_full × k ≤ 4e6 cells (else fail). |
| 746 | `solver/transgression_matrix_reduced.g` | `result := List([1..r], l -> List([1..k], i -> 0));` | LOW. `ApplyH3MatrixToMatBar`, only used by legacy callers (`r=0` returns early at m=5). |
| 926, 947 | `solver/snf_wrapper.g` | `sigma := List([1..n_sib], a -> 0);` / `table_sib := List([1..n_sib * n_sib], r_idx -> 0);` | LOW. Sibling transport, not used by current m=5 driver per the comments at line 442. |
| 143, 355, 592, 751 | `cocyclebasis_quillen_bridge.g` | `v := List([1..n_gens], i -> 0);` etc. | LOW. Quillen bridge, not on A-5b m=5 path. |

### P6: per-row `x mod c` closures

| Line | File | Code | Risk |
|---|---|---|---|
| **301, 435** | `solver/transgression_matrix_reduced.g` | `c_vec_mod := List(c_g_vec, x -> x mod exp_local);` | **HIGH** at m=5 (n²=4M closures per `ProjectVectorViaP_C` / `FastProjectVector` call). Fix: `c_g_vec mod exp_local`. |
| 908 | `solver/transgression_matrix_reduced.g` | `prod[l] := List(prod[l], x -> x mod h3_torsion[l]);` | **HIGH** inside Schreier loop. Per-row mod per step. k=165 closures × (path_length × orbit × axis × fc). Fix: `prod[l] mod h3_torsion[l]` (since `mod` distributes over lists). |
| 270, 250 | `brw_h3_action.g` | `result[j] := result[j] mod torsion[j];` (in `ComposeH3Endomorphism` / `ApplyH3Endomorphism`) | LOW. Already the compiled list-mod form. |
| 961 | `solver/snf_wrapper.g` | `table_sib := List(table_sib, row -> List(row, x -> x mod exp));` | LOW. Sibling transport (unused on m=5 hot path per comment at line 442). |
| 287 | `abelian_e_form_check.g` | `beta_mod := List(beta_int, x -> x mod m);` | LOW. Test/spike file. |
| 124, 134 (closures in callees) | `brw_h3_action.g` | — | LOW. Already noted at line 126: `(hombasis[i] * autmat) mod exp` is compiled. |

### P7: SolutionMat inside loops where SemiEchelon cache would amortise

The mod2 path has been thoroughly cached:
- `_GetCachedSemForAT(A)` and `_GetLiftSemForC(C)` in `mod2_solver.g`.
- `_GetCachedAF2T(C)` in `iterated_bockstein.g`.

No remaining HIGH-risk hits. The `IsCoboundary2Mod2WithLiftWitness`
witness path on `iterated_bockstein.g:230` does call `SolutionMat(A_F2_T,
residual)` inside the mask enumeration, but A_F2_T is cached and the
mask loop is bounded by 2^num_basis ≤ 2^6 = 64 — not the dominant cost.

### P8: TransposedMat in hot loops

Hot-path TransposedMat calls are all cached:
- `_BoundaryMatrixGF2_cache` keys raw boundary matrices on H (`mod2_solver.g:28`).
- `_IsCoboundary2Mod2_SemCache` holds `SemiEchelonMatTransformation(TransposedMat(A))` (`mod2_solver.g:109`).
- `_LiftSemCache` holds `TransposedMat(BoundaryMatrixGF2(C))` (`mod2_solver.g:470`).
- `_ItBock_AF2T_CACHE` holds `TransposedMat(BoundaryMatrixGF2(C))` for IB (`iterated_bockstein.g:91`).
- `Y_full_T := TransposedMat(Y_full)` is built once at cache time (`mod2_solver.g:216`).

No remaining HIGH-risk uncached TransposedMat in the in-scope hot path.

Outside-scope: `detecting_family_restriction.g:339, 352, 1443, 1466,
1546` have TransposedMat calls but those are per-G or per-orbit, not
per-target.

### P9: Sum(List(...))

Zero hits in the in-scope tree. (Negative finding.)

### P10: Append/Concatenation inside loops

No HIGH-risk hits. The `Concatenation` calls under `for` loops are all
in error-string builders (e.g. `dp_i_dispatch.g:44`, `quillen_algebra.g:529`)
or one-shot bookkeeping. The `Append(results, chunk_results)` in
`mod2_solver.g:802` is once per chunk (256 RHSes), not per-element.

### P11: Set(List(...))

Zero hits in the in-scope tree.

### P12: NewDictionary inside hot loops

The `NewDictionary(elts[1], true, elts)` pattern is well-cached:
- `_BoundaryMatrixGF2_raw` builds it once per H, hot but inside the per-H cache (`mod2_solver.g:64`).
- `_GetCachedMultTable` builds it once per C in IB (`iterated_bockstein.g:125`).
- `LoadOrbitCache` builds it on cache load only (`orbit_cache_persist.g:440`).
- `BuildPerClassCocycleBasis` builds it once per orbit rep (`snf_wrapper.g:690`).

The remaining hit is `IsCoboundary2[Vec](H, c, m)` in
`transgression_kernel.g:173, 213` — this is the slow Z/exp path,
unwrapped per call. **NOT a HIGH risk** because the production path is
the Vec API via the iterated-Bockstein cache; the Z/exp path triggers
only when `setup.exponent` is not a power of 2 (never at m ∈ {2, 3, 5, 7}).

### P13: Centralizer/Pcgs/Image() inside hot loops

Centralizer calls are all out of the inner loop:
- `KernelOfTransgressionViaMBar:981` — once per orbit rep.
- `transgression_matrix_reduced.g:1314` reuses captured `cache_orbit.C` (per comment).
- `centraliser_cache.g:40` is keyed on IdGroup.

The `Image(phi, g)` calls in `IB_F2HomBasis` (`iterated_bockstein.g:262`)
are inside an `elts` traversal — n × IndependentGeneratorExponents lookups
per call. **MEDIUM risk** at m=5 n=2048: ~2K Image+IGE calls per IB
invocation × every IB level recursion. Cheap relative to the matvec but
not free.

### P14: ForAll / Filtered in loops

`non_pivot_cols := Difference([1..ncols], pivot_cols)` in
`transgression_matrix_reduced.g:510` is the only Difference in scope
and it's cache-time only.

`Filtered([1..k], i -> h3_torsion[i] = 2)` in
`transgression_matrix_reduced.g:514, 530` — called once per orbit rep.

No HIGH-risk hits.

### P15: GAP-callback `If_` strict-eval bombs

The user shim `If_(cond, a, b)` is in active use across
`transgression_kernel.g:245`, `transgression_matrix_reduced.g`, etc. The
known bug (per `transgression_matrix_reduced.g:1013` comment) is that
`If_` evaluates BOTH branches eagerly, so passing a `fail` value via
`If_` explodes downstream. Comment-documented and audited.

The pattern `If_(j = i, 1, 0)` etc. is also expensive when iterated:
each call is two extra ExecAssLVar + EvalRefHVar dispatches. Not the
top bottleneck but a noise floor under hot loops.

### P16 (new): `cache_orbit.table * vec` matvec on un-promoted integer matrix

Adding pattern: `M * v` where M is a plist-of-plist integer matrix and
the comment-claimed `ConvertToMatrixRep(M)` (no field arg) is a no-op.
This is the dominant Step 4 bottleneck per the sample's
`ProdVectorVector` count (28.8% of total CPU). Listed under P2 above
for grouping convenience, but it deserves its own pattern label because
the fix is NOT `ConvertToMatrixRep`. Candidate fixes (none of which were
explored in #381/#382):
- `ImmutableMatrix(Integers, M)` flips TNUM but gives only ~16% speedup at n=165 (per probe2).
- Restructure the call to a row-vector form: build `M^T` once and do `v * M^T` if GAP's compiled `PROD_VEC_LIST_INT` is faster than `PROD_LIST_LIST`. Empirically untested in this audit.
- For binary-shaped intermediate columns (Path A's bit-extraction), batch
  via GF(2) matvec — already done at `run_e_plus_m_kernel_hap.g:616` for
  Path A. The fail-column path at `transgression_matrix_reduced.g:1335`
  could potentially use the same trick when modulus is 2-power and the
  `vec_target_exp` is sparse.

## Prioritised punch list

Ranked by expected wall-time impact at m=5 (the production scale):

| Rank | File:line | Pattern | Risk | Expected gain |
|---:|---|---|---|---|
| **1** | `solver/transgression_matrix_reduced.g:1326, 1396` | P3 (n=165 closure per call, in 4-level nested fail-column loop) | HIGH | Likely 10–30% wall reduction on Step 4 fail-column branch. Fix: replace `List([1..k], jj -> ...)` with a compiled list-mod expression on a sliced column. The cost is multiplied by the orbit and Schreier-path lengths. |
| **2** | `solver/iscoboundary2_split.g:144` | P3 (4M closures per Path Z call) | HIGH | This is the entry-point chunk for every Path Z call; closure-free vectorisation should drop closure dispatch cost from ~5–15% to ~1%. Fix: `c_prime_vec := (((c_g_vec mod setup.exponent) / r) mod 2);`. |
| **3** | `solver/transgression_matrix_reduced.g:908` | P6 (`prod[l] := List(prod[l], x -> x mod h3_torsion[l])`) inside the H3MatrixForOrbitMember Schreier loop | HIGH | `List(...) -> compiled list-mod-int` per row. Per Schreier step ~k=165 closure → 1 list-mod-int per row × k rows. Combined with the matmul shape, ~5–10% wall savings. Fix: `prod[l] := prod[l] mod h3_torsion[l];`. |
| **4** | `solver/transgression_matrix_reduced.g:301, 435` | P6 (`c_vec_mod := List(c_g_vec, x -> x mod exp_local)`) | HIGH at m=5 | 4M closures per call. Fix: `c_g_vec mod exp_local`. Called inside ProjectVectorViaP_C / FastProjectVector. |
| **5** | `brw_h3_action.g:165, 276; solver/orbit_cache_persist.g:461; solver/snf_wrapper.g:699` | P2 (the no-op `ConvertToMatrixRep(M)`) | HIGH (mislabelled as fix) | These calls confer NO speedup per the probe. Comments are misleading and steer future audits the wrong way. Recommendation: replace with either `ImmutableMatrix(Integers, M)` (small but real speedup) or delete the no-op call and update the comment to reflect the limitation. Investigate moving to row-vec convention (`v * M`) or pre-transposed matrices. |
| **6** | `solver/transgression_matrix_reduced.g:358, 372` | P5 (n²-scale zero-init) | HIGH at m=5 | n²×r and n²×(r+n) zero-init using closure form. Fix: `NullMat(n*n, r)`, `NullMat(r+n, n*n)`. Inside `FastProjectionMatrixSetup` — runs once per centraliser type. Not on the Step 4 hot per-vec path but a noticeable setup cost. |
| 7 | `solver/mod2_solver.g:263, 456` | P5 (n²-scale zero-init in slow-path adapters) | LOW (production uses Vec API) | Slow-path-only; fix is cheap (`ListWithIdenticalEntries`) but rarely engaged. |
| 8 | `solver/iterated_bockstein.g:403` | P5 (`result := List([1..n_eq], i -> 0)`) in `IB_DivBy2` | MEDIUM | n_eq = n² = 4M closures per IB level. Fix: `ListWithIdenticalEntries`. |
| 9 | `solver/transgression_matrix_reduced.g:540` | P3 column-extract closure | LOW | k × |order_2_gens| total, capped at k². The pattern is fine for that size. |
| 10 | `solver/transgression_matrix_reduced.g:796, 836` | P3 GF(2) column-extract closures | LOW | k × k_dim total, capped. |

## Methodology notes / what's not covered

**Sample limitation**: The user-requested `sample 79240 10 -mayDie` call
was denied by the harness sandbox. The most recent pre-existing sample
(`/tmp/gap_2026-06-01_215344_WI6e.sample.txt`, 2026-06-01 21:53) was used
instead. It targets PID 72680, not 79240. The dominant hot-symbol
signature (`ProdVectorVector` 28.8%, `PROD_GF2MAT_GF2VEC` 4%, `EvalMod`
3.7%, `ProdIntFFE` 2%) matches the post-#386 production profile the
task brief described, so the analysis remains representative; however, a
fresh PID-79240 sample taken on the actual A-5b m=5 production process
would harden the row-1 prediction. **Recommend re-sampling PID 79240 (or
its successor) and validating the rank-1 fix lands the predicted gain
before sinking engineering time.**

**Coverage**: Patterns P1–P15 all swept. Added P16 (the
`ConvertToMatrixRep` no-op on integer matrices) because the empirical
probe surfaced a systematic mis-fix across 9 production sites. All
in-scope files under `extraspecial_orbifolds/scripts/` were grepped;
`tests/*.g`, `src/modular_data.g`, and one-off research scripts were
out of scope per the brief. The `keller/` subdirectory was swept and
contains only two short files (`keller_s_entry.g`, `keller_twist_is_trivial.g`)
that exercise the Path A/Path Z dispatch via the same wrappers, no
unique hot patterns.

**Not yet audited (time-bound)**: 
- Detailed cost model for how much of the 28.8% `ProdVectorVector` is
  attributable to `transgression_matrix_reduced.g:1335` (fail-column)
  versus `H3MatrixForOrbitMember:906` (Schreier-step matmul) versus
  `run_e_plus_m_kernel_hap.g:590` (Path A integer matvec). A
  per-frame `sample -dispwords` of PID 79240 would resolve this.
- Empirical timing on whether `ImmutableMatrix(Integers, M)` vs
  pre-transposed `v * M^T` is the better workaround for the no-op
  `ConvertToMatrixRep`. Probe2 measured the operand swap-only.
- The fusion_oracle.g `ConvertToMatrixRep(S_int, Integers)` form (with
  the `Integers` field arg) — this DOES change behaviour (per GAP docs
  the field-aware form CAN flip TNUM for integer mats), and it's the
  only site in scope that uses the field-aware form. Out-of-scope for
  the current Step 4 question but worth flagging as the model for any
  P2 fix attempt.
