# Thorough perf audit — 2026-06-01

## Trigger

After PR #382 merged (ConvertToMatrixRep on h3_matrices + closure-free
Path A bit-extract) we observed:
- **Step 1 perf-4' path: 2× speedup** (2700 s → 1358 s) ✓
- **Step 4 per-vec wall: NO improvement** (270 s → 270 s) ✗

A fresh `sample` of PID 72680 (10 sec, mid-Step-4 at vec ~3/100) shows:

| Symbol | Count | % CPU | Path |
|--------|---:|----:|---|
| ProdListScl + ProdVectorVector | 4863 | ~58% | matvec, interpreted |
| TypePlistHomHelper + KTNumPlist | 2873 | ~34% | list type recheck |
| EvalMod + QuoRat + GcdInt | 1295 | ~15% | rational mod |
| ProdIntFFE | 171 | ~2% | Int × FFE (GF(2)) |
| FreeLVarsBag + NewLVarsBag | 396 | ~5% | closure allocations |

(Sums >100% because they nest.)

Read: #381+#382 fixes did NOT engage on Step 4's hot path. The hot path
in Step 4 is **Path Z** (iterated Bockstein for the order-4 column),
which lives in files the audit didn't sweep: `solver/iterated_bockstein.g`
and `solver/mod2_solver.g`.

## Anti-pattern taxonomy

| Code | Pattern | Why slow | Fix idiom |
|---|---|---|---|
| **P1** | `SolutionMat → mod` with IsRat-tagged result | `EvalMod → QuoRat → GcdInt` instead of `MOD_INT` | `Int` cast each row |
| **P2** | Plain-plist matrices used in `M*v` | `ProdListScl + ProdVectorVector` instead of `PROD_MAT_VEC_INT` | `ConvertToMatrixRep(M)` |
| **P3** | `List(L, x -> f(x))` closures in arithmetic hot paths | NewLVarsBag/FreeLVarsBag per element + dispatch overhead | Vectorise: `f(L)` |
| **P4** | `List([1..n], i -> List([1..n], j -> a[i][j] + a[j][i]))` symmetric build | O(n²) closures | `(a + TransposedMat(a)) mod 2` |
| **P5** | `List([1..n], i -> 0)` zero init | per-element closure | `ListWithIdenticalEntries(n, 0)` or `0 * [1..n]` |
| **P6** | `List(L, x -> x mod c)` per row in a loop | closure × hot | `L mod c` |
| **P7** | Repeated `SolutionMat` per call where SemiEchelon cache would amortise | Gauss redo per call | Cache SemiEchelonMatTransformation |
| **P8** | `TransposedMat` on packed GF2 matrix in a hot loop | 1 GB of bits moved | Cache transposed view |

## Audit by file

### `solver/iterated_bockstein.g` — **HIGHEST RISK (Path Z core)**

Called once per orbit-target where `vec_target[exp_index] != 0`. At
m=5: ~25% × 1024 targets × 100 vecs ≈ **25,000 calls per Step 4**.

| Line | Pattern | Code | Fix |
|---|---|---|---|
| 127 | P5 | `mult := List([1..n], i -> List([1..n], j -> 0))` | `NullMat(n, n)` |
| 173 | P5 | `c_F2 := List([1..n*n], i -> zero)` | `ListWithIdenticalEntries(n*n, zero)` then `ConvertToVectorRep(..., GF(2))` |
| 227 | P7 | `sol := SolutionMat(A_F2_T, residual)` — inside loop | Re-use cached SemiEchelon |
| 277 | **P3 — HOT** | `alpha := List([1..n], i -> (alpha[i] + hom_basis[k][i]) mod 2)` | `alpha := (alpha + hom_basis[k]) mod 2` |
| 359 | **P3 — HOT** | `List([1..n*n], i -> c_table[i] mod 2)` (n² closures!) | `c_table mod 2` |
| 383 | **P3 — HOT** | same as 359 | `c_table mod 2` |
| 480 | P5 | `c_table := List([1..n*n], i -> 0)` | `ListWithIdenticalEntries(n*n, 0)` |
| 526 | **P3 — HOT** | `c_table := List(c_g_vec, x -> x mod modulus)` | `c_g_vec mod modulus` |

**At m=5, n=2048, n²=4,194,304.** Lines 359/383 each fire 4M closure
calls per IB invocation × 25k invocations per Step 4 = **~10^11 closure
dispatches**. This is almost certainly where the 58% `ProdListScl` time
is going.

### `solver/mod2_solver.g`

Called via `IsCoboundary2Mod2WithLiftVecBatch` once per orbit (4× per
vec on m=5). Less hot than IB but still material.

| Line | Pattern | Code | Fix |
|---|---|---|---|
| 294 | P3 | `b := List(c_g_vec, x -> (x mod 2) * one)` | `b := (c_g_vec mod 2) * one` |
| 343 | P3 | same as 294 | same |
| 504 | P3 | same as 294 (in cached SemiEchelon variant) | same |
| 645 | **P3 — HOT inside per-row loop** | `row := List(c_g_vec, x -> (x mod 2) * one)` | `(c_g_vec mod 2) * one` |

### `solver/snf_wrapper.g`

`BuildPerClassCocycleBasis` builds the `table_gf2` view at orbit-cache
build time. Hot at SETUP but called once per orbit.

| Line | Pattern | Code | Fix |
|---|---|---|---|
| 720 | P3+P6 | `List(row, x -> (QuoInt(x, r_half) mod 2) * one_gf2)` | `((row mod (2*r_half)) - (row mod r_half)) / r_half * one_gf2` (vectorised) |
| 961 | P6 | `List(table_sib, row -> List(row, x -> x mod exp))` | `table_sib mod exp` (matrix mod scalar) |
| 968 | P3+P6 | same as 720 | same fix |

### `solver/transgression_matrix_reduced.g`

The perf-4' path. Already partially touched in PR #383.

| Line | Pattern | Code | Fix |
|---|---|---|---|
| 271 | P3 (semi) | `List([1..r_full], k_b -> sol[k_b] mod torsion_full[k_b])` | `sol{[1..r_full]} mod torsion_full` IF torsion_full is a list (need to check) |
| 301 | P3 | `c_vec_mod := List(c_g_vec, x -> x mod exp_local)` | `c_g_vec mod exp_local` |
| 435 | P3 | same as 301 | same |
| 438 | P3 (semi) | same as 271 | same |
| 796 | P3+If_ | `List([1..k_dim], j -> If_(M_y[j][i] mod 2 = 0, zero_gf2, one_gf2))` | column extraction; needs care with M_y rep |
| 908 | P6 | `prod[l] := List(prod[l], x -> x mod h3_torsion[l])` | `prod[l] := prod[l] mod h3_torsion[l]` |

### `brw_h3_action.g`

Lines 123, 264 already fixed in PR #383. No further hits.

### Hidden cost (P2 follow-up): why didn't ConvertToMatrixRep engage?

`H3MatrixOfAutomorphism` now ends with:
```gap
for j in [1..k] do
    M_y[j] := List(M_y[j], Int);
od;
ConvertToMatrixRep(M_y);
```

But the **assignment** `M_y[j] := List(M_y[j], Int)` REPLACES each
row with a *fresh* plist. `ConvertToMatrixRep` may then promote the
outer list but **the inner rows could still be `IsPlistRep` rather than
the compressed representation expected for `PROD_MAT_VEC_INT`**.

Verification needed: in a GAP session, after the cast + ConvertToMatrixRep,
check `IsMatrixObj(M_y)` and `TNUM_OBJ(M_y)` and `RepresentationsOfObject(M_y)`.
If the matrix is not flagged as `IsMutableMatrix and IsCyclotomicCollColl`,
the compiled matvec method doesn't get selected.

Hypothesis: the correct fix is
```gap
M_y := ImmutableMatrix(Integers, M_y);
```
which returns a properly-tagged matrix (not in-place conversion).

## Prioritised punch list

(Lines × estimated occurrence-rate-per-vec × impact)

| Rank | File:line | Fix | Expected Step-4 wall reduction |
|---|---|---|---|
| 1 | `iterated_bockstein.g:359,383` (P3, n² closure) | `c_table mod 2` | **HIGH** — most likely 30-50% of Step 4 CPU |
| 2 | `iterated_bockstein.g:277` (P3 in IB inner loop) | `alpha := (alpha + hom_basis[k]) mod 2` | MEDIUM-HIGH |
| 3 | `brw_h3_action.g::H3MatrixOfAutomorphism` (P2 follow-up): verify ConvertToMatrixRep actually promoted to compiled-matvec dispatch; if not, switch to `ImmutableMatrix(Integers, M_y)` | engages compiled PROD_MAT_VEC_INT on h3_matrices everywhere | HIGH |
| 4 | `iterated_bockstein.g:526`, `mod2_solver.g:294,343,504,645` (P3 closure in inner loops) | `c_g_vec mod 2 * one` | MEDIUM |
| 5 | `snf_wrapper.g:720,968` (P3+P6 closure in basis_table_gf2 build) | vectorised arithmetic | LOW-MEDIUM (setup, runs once per orbit cache build) |
| 6 | `transgression_matrix_reduced.g:301,435,908` (P3 closure-mod) | `c_g_vec mod exp_local`, `prod[l] mod h3_torsion[l]` | LOW (already in perf-4' path which is now 2× faster) |
| 7 | `iterated_bockstein.g:127,173,480` (P5 zero init) | `ListWithIdenticalEntries` | LOW |
| 8 | `iterated_bockstein.g:227` (P7 SolutionMat in loop) | reuse cached SemiEchelon | MEDIUM |

## What this audit missed (and a TODO sweep tier-3)

Files I haven't audited but contain Path Z / Path A code reachable
from Step 4:

- `src/modular_data.g` (per CLAUDE.md "treat as reference, do not Read
  twice") — the parent UCT machinery. May contain anti-patterns shared
  by transgression_kernel.g.
- `brw_simples_action.g` — BRW orbit construction. Not hot for Step 4
  but used at setup.
- `hap_pontryagin_square.g`, `hap_integrate_to_z4_cocycle.g` — Pontryagin
  Z/4 generator helpers. May be on Quillen-route hot path.
- `defect_rep_minus_id_optim.g` — K-4a Q_8 dispatch. PR #383 fixed the
  symmetric-matrix builds but not all closure patterns; ~3 more sites
  remain at lines 153, 230, 231 (column-access closures, harder to
  vectorise).

## Next step

Land the top 3 in a stacked PR (proposed `a5b-perf-iterbock-385`):
- Fix `iterated_bockstein.g:359,383,277,526` (4 lines, vectorised
  closures over n²-length lists).
- Verify the `H3MatrixOfAutomorphism` matrix is genuinely tagged
  for compiled dispatch — if not, switch to `ImmutableMatrix(Integers, M_y)`.
- m=2 / m=3 regression smoke-test.
- Kill PID 72680 + restart with the patches engaged.

Expected: per-vec Step 4 wall from 270s to ~50-80s. Total Step 4 from
~22h to ~3-5h.
