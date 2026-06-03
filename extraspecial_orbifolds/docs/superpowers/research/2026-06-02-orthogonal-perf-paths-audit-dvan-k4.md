# Orthogonal Perf-Path Siloing Audit — D-VAN + K-4 follow-up — 2026-06-02

**Audit branch:** `audit-dvan-k4-perf-397`
**Scope:** D-VAN code paths (`detecting_family_restriction.g`, `detecting_family_vanish.g`, `fsi_wrapper.g`, `quillen_detecting_subgroup.g`) plus K-4a / K-4b orchestrators and trace machinery (`keller/`, `k4a_classify.g`, `krr_spectral_characters_sparse.g`, `restrict_to_subgroup.g`, `em_eplus_translate.g`).
**Trigger:** PR #396 explicitly scoped these out. The user wants follow-up because K-4a/K-4b have multiple dispatch paths (abelian closed-form vs general spectral; sparse trace vs dense; per-irrep mult-scaling vs unscaled) and K-4a-T4c (#220) layered sparse-trace on top of #208's original spectral path — classic siloing risk.

## TL;DR

| # | Instance | Tier | Confidence | Composition gap |
|---|---|---|---|---|
| A-K4-1 | `_TraceEntry` (per-c hot loop) uses `F2_Dot` / `F2_QuadDot` interpreted manual loops; `F2_Mul` / `F2_VMul` are overridden to compiled. Overrides are siloed at the helper boundary. | A | HIGH | Override `F2_Dot` / `F2_QuadDot` to compiled `*` + Sum (matches sibling overrides). |
| A-K4-2 | `_BuildTraceCtx` / `_BuildGaussCtx` row-reduces a 2n×2n F_2 matrix via manual `for c in [1..n] do A[j] := List(...)` per pivot; bypasses compiled GF(2) `TriangulizeMat` / `SemiEchelonMat`. | A (Gauss only-A at m=7; Batch at m=5: B) | NEEDS-REVIEW | Use `TriangulizeMat` on a GF(2)-tagged matrix; recover `solveMap` / `feasMat` via standard echelon back-sub. |
| A-K4-3 | `TraceOnOmega0Batch`'s P3+P6 anti-pattern: 8 sites of `List(M * V, row -> List(row, x -> x mod 2))` on n²/n³-shape GF(2) products. | A (m=5 K-4b production) | HIGH | Single per-row compiled `row mod 2`; or do whole-matrix `mod 2` if supported. |
| A-DVAN-1 | `ResIsTrivialOnDetectingFamily` builds restriction images via `Sum(List(...))` per entry (P9) — n_EA × k_H × k_G manual sums where compiled `hom * res_mat` would work. | A (D-VAN production at m≤5) | HIGH | Replace per-(i,j)-entry `Sum(List)` with compiled matvec `hom_omega * res_EA_i`; reduce mod row-wise. |
| A-DVAN-2 | D-VAN m=7 streaming `Step 4` (per-sample restriction-matrix builds) calls `RestrictionMatrixViaHAP` k=1000 times against the SAME `setup_G`/`R_G`; the `EquivariantChainMap` build is per-EA, not amortised. | A (D-VAN m=7) | NEEDS-REVIEW | EA centralisers don't share `R_H`, but `R_G`-side TensorWithIntegers + UCT setup is identical across calls — verify HAP caches them; if not, hoist. |
| A-K4-4 | `_CTComputeSBlock` calls `intertwiner_data.trace_on_W(i, k, b_tilde)` in the innermost (a, b, k) loop — Ni × #commuting-pairs × Nj evaluations. At m=5 the `trace_on_W` from the sparse builder dispatches per-call through `EvalIrr` + central-class lookup. No per-class trace_on_W batching. | B | NEEDS-REVIEW | Pre-evaluate `trace_on_W(i, *, b_tilde)` once per (i, b_tilde) into a length-Ni vector; cache by (i, b_tilde) within the block. |
| B-DVAN-1 | `_DETF_F2RrefStateAddBlockMut` exposes columns of M_block_F2 via `TransposedMat` per call — m=7 streaming Pass 1 calls this O(n_EA × #passes) times per sample, each `TransposedMat` is over a k_G × k_H GF(2) matrix that doesn't change between calls. | B | HIGH | Precompute and cache `TransposedMat(data!.res_EA_list_F2[j])` once per j (alongside the existing `res_EA_list_F2` cache). |
| B-K4-1 | K-4a m=5 dispatch on `_K4A_GetDVANEAFamily(m) <> fail`: when fail, m≥5 routes via TranslateSpectralDataToEPlus + RestrictTraceOnWToSubgroupHonourParent; when not-fail, multi-EA via direct `ComputeModularData`. These two paths exist side-by-side with NO composition — under `opts.omega_vec != 0`, the multi-EA path skips the spectral/translate path entirely even though both engage at non-zero ω. | C | NEEDS-REVIEW | This is a CORRECTNESS dispatch (mult-scaling reconciliation #275, #333), not a perf dispatch. Negative finding. |
| C-K4-1 | `BuildCentralExtension` in `fsi_wrapper.g` builds each `b_perms` by closure `b_img := List([1..n], function(k) ... end)` — per-element interpreted code on |G|*o entries. | C | HIGH | Compiled list comprehension is rarely faster in GAP for this kind of permutation build; main issue is the algorithmic O(|G|² · |gens|) cost. Likely not on a hot path (only fsi at small G). |

D-VAN audit verdict: ORTHOGONAL SILOING FOUND. A-DVAN-1 (Sum(List(...)) inside D-VAN's restriction-image build) is a P9 anti-pattern in production code at m ≤ 5; A-DVAN-2 (per-EA HAP setup duplication) is a NEEDS-REVIEW for the m=7 streaming rerun. B-DVAN-1 (per-call `TransposedMat`) is an orthogonal-paths instance where the GF(2) cache exists but its transpose doesn't — exactly the pattern PR #396 A-5 flagged for the integer table_T case.

K-4 audit verdict: ORTHOGONAL SILOING FOUND. A-K4-1 is the highest-impact instance — F2_Mul/Trans/VMul/Add got compiled GAP-native overrides in `defect_rep_minus_id_optim.g` but F2_Dot / F2_QuadDot were NOT overridden. The K-4b m=5 hot path goes through `_TraceEntry` → F2_QuadDot, paying the manual-loop cost on every per-c invocation. A-K4-2 (manual F_2 RREF) and A-K4-3 (P3+P6 in TraceOnOmega0Batch) are P-class anti-patterns sitting inside the K-4b m=5 production trace builder.

The report below documents each instance with file:line refs, current shape, why the paths are orthogonal, and a composition sketch. **No code changes** were made by this audit.

---

## Tier A: in production hot paths

### A-K4-1 — `F2_Dot` / `F2_QuadDot` not overridden by `defect_rep_minus_id_optim.g`. (HIGH-CONFIDENCE)

**Location:** `extraspecial_orbifolds/scripts/defect_rep_minus_id.g:219-235` (defines `F2_Dot`, `F2_QuadDot` as manual loops). `defect_rep_minus_id_optim.g:48-74` (overrides `F2_Mul`, `F2_VMul`, `F2_Trans`, `F2_Add` to use compiled `*`, `TransposedMat`). **No override for F2_Dot / F2_QuadDot.**

**Current shape:**

```gap
# defect_rep_minus_id.g:
F2_Dot := function(u, v)
    local s, i;
    s := 0;
    for i in [1..Length(u)] do s := s + u[i] * v[i]; od;
    return s mod 2;
end;;

F2_QuadDot := function(u, Q, v)
    local n, s, i, j;
    n := Length(u);
    s := 0;
    for i in [1..n] do
        for j in [1..n] do s := s + u[i] * Q[i][j] * v[j]; od;
    od;
    return s mod 2;
end;;

# defect_rep_minus_id_optim.g (overrides only these four):
F2_Mul := function(A, B)
    ...
    p := A * B;   # GAP integer matrix multiplication
    return List(p, row -> List(row, x -> x mod 2));
end;;
F2_VMul := function(v, M)
    ...
    p := v * M;
    return List(p, x -> x mod 2);
end;;
F2_Trans := ...
F2_Add  := ...
```

The hot path in `krr_spectral_characters_sparse.g:223-276` (`_TraceEntry`, called 2^k times per trace at m=5: 65 536 times) calls:

```gap
gammaConst := F2_QuadDot(x, Mhh, x);        # manual O(n²) interpreted loop
t1 := F2_VMul(F2_VMul(x, H), R);
gammaConst := (gammaConst + F2_Dot(t1, ic)) mod 2;   # manual O(n) interpreted loop
```

At m=5: n=32, so F2_QuadDot is 32² = 1024 interpreted multiply-adds per call × 65 536 calls per trace × 1025 classes per central-class build = ~70 billion interpreted ops *just* for F2_QuadDot, even before any other arithmetic.

**Why the paths are orthogonal:**

- **F2_Mul / F2_VMul / F2_Trans / F2_Add** were sped up by PR (issue #208 or earlier) to use GAP's compiled integer matmul + a `List(row, x -> x mod 2)` reduce-mod-2 trailing pass. That gives a ~10-100× speedup at n=32.
- **F2_Dot / F2_QuadDot** were left at the manual interpreted loop. The composition between the two would be trivial: `F2_Dot(u, v) := (u * v) mod 2` (GAP has compiled vector-dot), `F2_QuadDot(u, Q, v) := ((u * Q) * v) mod 2` (two compiled matvecs).
- The two perf families don't compose at the function-boundary level because the dot/quad-dot path was never updated. Anyone reading the optim file would assume "the optim file overrides all the slow ones" — but actually two of the most-frequently-called helpers were missed.

The `TraceOnOmega0Batch` function on the same hot path (line 328-448) avoids F2_QuadDot by doing the work as compiled matmul + List-closure-mod-2 (instance A-K4-3 below), so the slowdown of F2_QuadDot is only paid in `_TraceEntry` / `TraceOnOmega0Naive` (currently called for m=3, 4 only at production but historically the m=5 path too).

**At m=7:** `TraceOnOmega0Gauss` uses `_BuildGaussCtx` which calls F2_Mul (overridden, fast) extensively for the per-h Q matrix build; F2_Dot / F2_QuadDot are NOT on the m=7 critical path (only inside `_TraceEntry` which is m≤5).

**Composition sketch:**

WRONG (current — manual loops):
```gap
F2_Dot := function(u, v) ... O(n) GAP-level loop ... end;;
F2_QuadDot := function(u, Q, v) ... O(n²) GAP-level loop ... end;;
```

RIGHT (compiled, matching the F2_Mul override style):
```gap
F2_Dot := function(u, v)
    return (u * v) mod 2;   # compiled vector dot, single MOD_INT trailing.
end;;
F2_QuadDot := function(u, Q, v)
    return ((u * Q) * v) mod 2;   # two compiled matvecs.
end;;
```

**Impact:** Tier A. The m=5 K-4b production rerun (currently blocked on A-5b's kernel.g per task description) finalises through `BuildKRRSpectralCharactersSparse(5)` which exercises `TraceOnOmega0` per central-class element. At m=5 today the dispatch routes to `TraceOnOmega0Batch` (which already does compiled matvec), so F2_QuadDot is NOT exercised on the m=5 production hot path — but it IS on the m=3 anchor path and the `_TraceEntry`/`TraceOnOmega0Naive` regression tests, and would become A-Tier hot if anyone switched the m=5 dispatch back to the diagonal-sum entry point (e.g. for memory reasons, since TraceOnOmega0Batch materialises a 65 536 × 32 matrix).

**Re-categorisation:** A for "F2_QuadDot in any path that consumes _TraceEntry"; B in practice because m=5 production routes around it via TraceOnOmega0Batch. Still flag as Tier-A because the override gap is a trap for anyone adding new sparse-trace consumers.

**Cross-reference:** `krr_spectral_characters.g:74-77` warns "defect_rep_minus_id_optim.g overrides several functions defined in defect_rep_minus_id.g (F2_Mul, F2_VMul, F2_Trans, F2_Add, MatOfBilForm) with faster versions" — explicitly enumerates the 5 functions, confirming F2_Dot / F2_QuadDot were intentionally or accidentally excluded.

---

### A-K4-2 — `_BuildTraceCtx` / `_BuildGaussCtx` does manual F_2 RREF instead of compiled `TriangulizeMat`. (NEEDS-REVIEW)

**Location:** `extraspecial_orbifolds/scripts/krr_spectral_characters_sparse.g:133-153` (`_BuildTraceCtx`'s row-reduction loop). Same pattern in `_F2_AffineSolveCols:519-571`.

**Current shape:**

```gap
# _BuildTraceCtx (line 133):
BPiT := F2_Trans(BPi);  # n x n   (fast: compiled TransposedMat)
A2 := List([1..n], i -> Concatenation(BPiT[i], IdentityMat(n)[i]));
r := 1;
pivCols := [];
pivRows := [];
for c in [1..n] do
    if r > n then break; fi;
    i := r;
    while i <= n and A2[i][c] = 0 do i := i + 1; od;
    if i > n then continue; fi;
    if i <> r then A2{[r, i]} := A2{[i, r]}; fi;
    for j in [1..n] do
        if j <> r and A2[j][c] = 1 then
            A2[j] := List([1..2 * n],
                          i -> (A2[j][i] + A2[r][i]) mod 2);   # P3 closure!
        fi;
    od;
    Add(pivCols, c);
    Add(pivRows, r);
    r := r + 1;
od;
```

This is a manual GF(2) RREF on a 2n×2n integer matrix at m=5 (n=32: a 64×64 matrix; m=7: 128×128). The inner-most row update uses a P3 closure `List([1..2*n], i -> (A2[j][i] + A2[r][i]) mod 2)`.

**Why the paths are orthogonal:**

The wider K-4 codebase has TWO families of GF(2) primitives:

1. **`defect_rep_minus_id_optim.g`'s F2_* operations**: compiled integer matmul + List-closure-mod-2.
2. **GAP's built-in GF(2) compiled operations** (`ConvertToMatrixRep(M, GF(2))`, `TriangulizeMat`, `RankMat`, `SolutionMat` over GF(2)): packed-bit representation, ~100× faster than even the integer-compiled F2 path.

The D-VAN m=7 streaming code (`_DETF_F2RrefStateAddBlockMut` in `detecting_family_restriction.g:1539-1571`) uses option 2 — explicitly `ConvertToMatrixRep(M, GF(2))` and `AddRowVector` on packed GF(2) rows. The K-4b m=5 / m=7 sparse trace code uses option 1 (integer-matmul). Both engage compiled C primitives but at different speeds.

Within `_BuildTraceCtx` specifically:
- The F_2 RREF on the 2n×2n integer matrix could be done by tagging the matrix `ConvertToMatrixRep(A2, GF(2))` and calling `TriangulizeMat(A2)` — single compiled call, ~50-100× faster at n=32.
- The result back-substitutes via `A2[i]{[n+1..2*n]}` for `solveMap` / `feasMat`. These row slices work identically for GF(2)-typed matrices, so the migration would be a 3-line change.

**Why "NEEDS-REVIEW":** The RREF here is called once per centraliser element h (~1025 calls per m=5 central-class build), then cached via `_traceHKeys`/`_traceHVals`. Cost is small compared to the per-c inner loop (which doesn't touch this). Confidence in HIGH MATH (the speedup is real); confidence in HIGH WALL IMPACT depends on profiling — needs verification.

**Composition sketch:**

WRONG (current):
```gap
A2 := List([1..n], i -> Concatenation(BPiT[i], IdentityMat(n)[i]));   # integer matrix
# ... manual GF(2) RREF via for c in [1..n], for j in [1..n], List(...) mod 2 ...
```

RIGHT:
```gap
A2 := List([1..n], i -> Concatenation(BPiT[i], IdentityMat(n)[i]));
ConvertToMatrixRep(A2, GF(2));   # tag as packed-bit GF(2) matrix
A2 := MutableCopyMat(A2);
TriangulizeMat(A2);   # compiled GF(2) RREF, ~50-100× faster
# Then read pivot columns + back-sub structure from A2's triangulised form.
```

**Impact:** Tier-B (sub-call to _BuildTraceCtx, called once per h, cached). Effort: ~30 lines of refactoring inside _BuildTraceCtx + _BuildGaussCtx. Flag as A because if the RREF cost ever becomes hot (e.g. m=7 with n=128 and a Gauss-sum call per class × 16K classes), this would dominate.

---

### A-K4-3 — `TraceOnOmega0Batch` reduces mod 2 via closure-over-row × per-cell mod (P3 + P6). (HIGH-CONFIDENCE)

**Location:** `extraspecial_orbifolds/scripts/krr_spectral_characters_sparse.g:362-447` (`TraceOnOmega0Batch`).

**Current shape:**

```gap
# Line 362-369:
fmat_diag := List(targetMat * TransposedMat(feasMat),     # compiled matmul (good)
                  row -> List(row, x -> x mod 2));         # P3+P6: row closure + per-cell mod
infeasMask := List(fmat_diag, row -> ForAny(row, e -> e <> 0));

# Line 396-398:
XHR := List(XH * ctx.R, row -> List(row, x -> x mod 2));

# Line 417-420:
term1 := List(XMhhSym * ctx.AT, row -> List(row, x -> x mod 2));
icRT := icMat * ctx.RT;
icRTHT := List(icRT * ctx.HT, row -> List(row, x -> x mod 2));
icRTHTAT := List(icRTHT * ctx.AT, row -> List(row, x -> x mod 2));

# Line 424:
betaTilde := List(betaMat * ctx.sht.ShT, row -> List(row, x -> x mod 2));
```

Eight sites, each pattern `List(M * V, row -> List(row, x -> x mod 2))`. At m=5 with dim = 65 536 and inner dimensions 32-128, each closure dispatches 32 × 65 536 = 2 million times per call site. With 8 sites this is ~16 million closure dispatches per trace × 1025 traces per central-class build at m=5 ≈ 16 billion closure dispatches in the m=5 K-4b spectral build.

**Why the paths are orthogonal:**

- **Compiled matmul** (`targetMat * TransposedMat(feasMat)`) — already in compiled C (PROD_MAT_MAT_INT). Good.
- **Per-row mod-2** — closure-over-row × closure-over-cell. Two layers of P3 / P6 anti-pattern.

The compiled-matmul win is silently undone by the trailing mod-pass — same pattern as `_BuildSiblingTableViaTransport` from PR #396 instance B-7, except here it appears 8 times in the same function. The per-row mod is exactly the P6 fix:

```gap
# RIGHT:
for r in [1..Length(M)] do
    M[r] := M[r] mod 2;   # compiled list-mod-int per row
od;
```

Or in some matrix-context-dependent way, the whole matrix `mod 2` may dispatch correctly.

**Composition sketch:**

WRONG (current, 8 sites):
```gap
fmat_diag := List(targetMat * TransposedMat(feasMat),
                  row -> List(row, x -> x mod 2));
```

RIGHT:
```gap
fmat_diag := targetMat * TransposedMat(feasMat);
for r in [1..Length(fmat_diag)] do
    fmat_diag[r] := fmat_diag[r] mod 2;   # compiled list-mod-int
od;
# (or, if applicable: fmat_diag := fmat_diag mod 2;)
```

Alternatively, the entire function would benefit from `ConvertToMatrixRep(targetMat, GF(2))` and using GF(2) compiled matmul + zero check, which composes more cleanly with the per-c feasibility check (`ForAny(row, e -> e <> 0)`).

**Impact:** Tier-A — this is the m=5 K-4b production trace builder, called 1025 times per `BuildKRRSpectralCharactersSparse(5)`. Each `TraceOnOmega0Batch` call has 8 closure-mod-row sites with O(2 million) closure dispatches each. Composition is mechanical (the P6 fix; 8 sites to change).

**Proposed follow-up issue:** "Replace 8× `List(M, row -> List(row, x -> x mod 2))` in TraceOnOmega0Batch with compiled per-row `mod 2`."

---

### A-DVAN-1 — `ResIsTrivialOnDetectingFamily` builds restriction images via `Sum(List(...))` per entry (P9). (HIGH-CONFIDENCE)

**Location:** `extraspecial_orbifolds/scripts/detecting_family_vanish.g:140-176` (`ResIsTrivialOnDetectingFamily`).

**Current shape:**

```gap
for i in [1..Length(rec_m.res_EA_list)] do
    torsion_EA_i := rec_m.torsion_EA_list[i];
    res_EA_i := rec_m.res_EA_list[i];
    vec_int := List([1..Length(torsion_EA_i)], j ->
        Sum([1..Length(hom_omega)], k ->
            hom_omega[k] * res_EA_i[k][j]));   # P9 anti-pattern!
    vec_modH := List([1..Length(vec_int)], j ->
        vec_int[j] mod torsion_EA_i[j]);
    ...
od;

# D_8 restriction (same shape):
res_D8_vec_int := List([1..Length(rec_m.torsion_D8)], j ->
    Sum([1..Length(hom_omega)], i ->
        hom_omega[i] * rec_m.res_D8[i][j]));   # P9!
res_D8_vec := List([1..Length(res_D8_vec_int)], j ->
    res_D8_vec_int[j] mod rec_m.torsion_D8[j]);

# Q_8 restriction (same shape):
res_Q8_vec_int := List([1..Length(rec_m.torsion_Q8)], j ->
    Sum([1..Length(hom_omega)], i ->
        hom_omega[i] * rec_m.res_Q8[i][j]));   # P9!
```

Three sites, all the **P9 anti-pattern** from CLAUDE.md (line 446: "`Sum(List(L, f))` instead of compiled inner product"). At m=5, k_G = 165, n_EA = 112, k_H ≈ 30 for max EAs — that's 112 × 30 × 165 ≈ 555 000 manual Sum-of-List ops per `ResIsTrivialOnDetectingFamily` call.

`ResIsTrivialOnDetectingFamily` is the **D-VAN vanishing test entry point** invoked by:
- `KellerTwistIsTrivial(m, omega_vec)` (the Keller-namespace wrapper)
- `KellerSEntry(m, omega_vec, i, j)` (the K-2 S-matrix dispatcher's trivial-twist check)
- `k4b_xcheck_d_van.g` (K-4b cross-validation harness)

Each of these is called many times during a K-4b production run; even at m=3 the routine is in the K-4a regression test loop.

**Why the paths are orthogonal:**

`res_EA_i` is a k_G × k_H integer matrix; `hom_omega` is a length-k_G integer vector. The intended math is the matvec `hom_omega * res_EA_i`, which GAP compiles to `PROD_VEC_MAT_INT` (compiled C primitive, ~50-100× faster than the Sum-of-List).

Two perf families are siloed:
- **Per-restriction-matrix** (already updated): `RestrictionMatrixViaHAP` casts `res_mat[i] := List(res_mat[i], Int)` then `ConvertToMatrixRep(res_mat)` to tag as IsMatrixRep (PR #381+#382 lines 297-306). This makes the matrix ready for compiled matvec.
- **Per-restriction-image** (this site): the consumer of those matrices does `Sum(List(..., k -> v[k] * M[k][j]))` per entry, bypassing the compiled path entirely.

The composition would replace 3 × 2 = 6 nested-List+Sum sites with `hom_omega * res_EA_i` (one compiled matvec each), then a single row-mod-row vector of torsions.

**Composition sketch:**

WRONG (current):
```gap
vec_int := List([1..Length(torsion_EA_i)], j ->
    Sum([1..Length(hom_omega)], k ->
        hom_omega[k] * res_EA_i[k][j]));
vec_modH := List([1..Length(vec_int)], j ->
    vec_int[j] mod torsion_EA_i[j]);
```

RIGHT:
```gap
vec_int := hom_omega * res_EA_i;   # compiled PROD_VEC_MAT_INT
# Per-entry mod by torsion (the moduli are per-column, can't batch into one `mod`):
vec_modH := List([1..Length(vec_int)], j -> vec_int[j] mod torsion_EA_i[j]);
# (Could batch if torsion is constant per matrix, but in general it varies.)
```

The per-entry mod loop is fine — that's the unavoidable per-column-different-modulus case (see CLAUDE.md N-4: `ApplyH3Endomorphism` has the same pattern and is correct).

**Impact:** Tier-A in two senses:
1. D-VAN production m≤5 runs through this per ω evaluation.
2. K-4b m=5 finalisation (after A-5b kernel.g lands) will run this for cross-validation.

The wall is currently small (the call is rare per K-4a run), but it sits in any future D-VAN omega-sweep (e.g., "verify A-5b's kernel is detected-trivial on every basis vector"), and the speedup composes with PR #381+#382's IsMatrixRep tagging.

**Proposed follow-up issue:** "Replace 6× Sum(List) matvec patterns in `ResIsTrivialOnDetectingFamily` with compiled `hom_omega * res_*` matvec."

---

### A-DVAN-2 — D-VAN m=7 streaming Step 4 builds N=1000 restriction matrices each pulling in a fresh `EquivariantChainMap` against the same setup_G. (NEEDS-REVIEW)

**Location:** `extraspecial_orbifolds/scripts/detecting_family_restriction.g:1841-1855` (the per-sample restriction-matrix build loop in `_DETF_TrimmedFamily_m7_streaming`).

**Current shape:**

```gap
ea_subs := [];
ea_ctxs := [];
ea_ress := [];
for i in [1..Length(sample_basis_tuples)] do
    H_i := Subgroup(G, sample_basis_tuples[i]);
    ctx_i := SubgroupCohomologyContext(H_i);
    phi_i := SubgroupInclusion(H_i, G);
    res_i := RestrictionMatrixViaHAP(setup_G, ctx_i, phi_i);   # *** hot ***
    Add(ea_subs, H_i);
    Add(ea_ctxs, ctx_i);
    Add(ea_ress, res_i);
    if verbose and i mod 100 = 0 then
        Print("[_DETF_TrimmedFamily_m7]   built ", i, " / ",
              Length(sample_basis_tuples),
              " restriction matrices (wall = ",
              Runtime() - t0, " ms)\n");
    fi;
od;
```

Each `RestrictionMatrixViaHAP(setup_G, ctx_i, phi_i)` (defined at `:201-308`) does:

```gap
chainmap := TensorWithIntegers(EquivariantChainMap(R_H, R_G, phi_HG));
gcf := _FastGroupCohomologyFunctor(UCT_H, UCT_G, chainmap, 3);
```

The `UCT_H`/`R_H` is different per EA (rank-(m+1) elementary abelian, with its own HAP resolution). The `UCT_G`/`R_G` is the SAME per call (LHS-resolution from `_DETF_BuildSetupG_LHS(7)`, built once).

`EquivariantChainMap(R_H, R_G, phi)` is a HAP call. Per `_FastGroupCohomologyFunctor`'s docstring (line 122-150), the previous bottleneck `UniversalCoefficientsTheorem(K_G)` (called inside the original `GroupCohomologyFunctor`) was eliminated by passing pre-computed UCT records (issue #329). But `EquivariantChainMap` itself — which is `chainmap.mapping(...)` called inside `_FastGroupCohomologyFunctor` — still does per-call work.

**Why the paths are orthogonal:**

- **The R_G / UCT_G side** is computed once via `_DETF_BuildSetupG_LHS(7)` and re-used. Good.
- **The R_H side** is per-EA (necessary; different abelian groups).
- **The chain map** `EquivariantChainMap(R_H, R_G, phi_HG)` is built per call. Necessary because phi depends on the specific H_i and its embedding into G.

There's no obvious siloing here. The `EquivariantChainMap` build is genuinely per-EA work, and there's no obvious cache that could amortise it across the 1000 samples (each H_i is structurally different).

**However** — issue #329's `_FastGroupCohomologyFunctor` only addressed the UCT recomputation. There's a separate question: does `EquivariantChainMap` itself amortise anything when called repeatedly against the SAME `R_G`? Per HAP's source (not audited here), this is unclear. The per-EA wall in production (1000 EAs × ~5 s each, per the docstring estimate at line 1671-1677) suggests ~80 min just for Step 4 at m=7. If even 50% of that is the R_G-side chain-map setup work that COULD be cached, it would be Tier-A.

**Why NEEDS-REVIEW:** verification would require running m=7 with profiling. The user's task description says "D-VAN m=7 production rerun is imminent (Agent ready brief in flight)" — that's the natural place to measure. The audit cannot determine speedup without that data.

**Possible composition:**

If HAP's `EquivariantChainMap` doesn't cache R_G-side work, the perf win is:

1. Pre-build the per-R_G data once (whatever is invariant across the 1000 H_i's).
2. Per-EA, build only the R_H-side data + the homomorphism phi.

But this requires modifying HAP or vendoring its internals — out of scope for "no code changes" audit.

**Impact:** Tier-A if confirmed; deferred to NEEDS-REVIEW pending m=7 production profiling.

**Proposed follow-up issue:** Profile m=7 Step 4 walls; if the per-EA cost is dominated by R_G-side chain-map work, file an issue to vendor HAP's per-EA chain-map setup.

---

### A-K4-4 — `_CTComputeSBlock` per-(a, b, k) `trace_on_W` calls; no per-class trace_on_W batching. (NEEDS-REVIEW)

**Location:** `extraspecial_orbifolds/scripts/ct_modular_data.g:115-189` (`_CTComputeSBlock`).

**Current shape:**

```gap
for ai in [1..Length(elts_i)] do
    a := elts_i[ai];
    t_a := ts_i[ai];
    for bi in [1..Length(elts_j)] do
        b := elts_j[bi];
        if a * b <> b * a then continue; fi;
        s_b := ts_j[bi];
        b_tilde := t_a^-1 * b * t_a;     # in C_H(g_i)
        a_tilde := s_b^-1 * a * s_b;     # in C_H(g_j)
        eps := intertwiner_data.epsilon(g_i, g_j, a, b);
        for k in [1..Ni] do
            eps_chi_b := eps * ComplexConjugate(
                intertwiner_data.trace_on_W(i, k, b_tilde));
            for l in [1..Nj] do
                chi2_val := ComplexConjugate(
                    intertwiner_data.trace_on_W(j, l, a_tilde));
                M[k][l] := M[k][l] + eps_chi_b * chi2_val;
            od;
        od;
    od;
od;
```

`trace_on_W` is called Ni × #(commuting a, b pairs) times per block at the inner-k loop, and Nj × same times per block at inner-l. For a Q_8 / D_8 branch at m=5 with Ni=Nj=8, this is 64 × #(commuting pairs) trace_on_W evaluations per block × #(class pairs)² blocks. The trace_on_W is the K-4 m=5 sparse spectral builder's per-element character evaluation.

**Why the paths are orthogonal:**

The K-4a m=5 routing in `k4a_classify.g:770-849` builds `sparse_data := BuildKRRSpectralCharactersSparse(5)` (the K-4a-T4c sparse trace path, issue #220). This sparse data feeds `TranslateSpectralDataToEPlus` → `RestrictTraceOnWToSubgroupHonourParent` → the H-level `trace_on_W` closure.

For the central class on G (where the sparse builder has computed actual multiplicities), the H-level `trace_on_W` then calls `multiplicity_lookup(k_H, j_H)` which does a sum over `mat[j_H_arg][j_G] * mults[j_G]`. For non-central classes (which is the entire D_8 / Q_8 branch), the H-level `trace_on_W` falls back to `EvalIrr` — a character-table lookup.

The per-(i, k, b_tilde) calls in `_CTComputeSBlock` could be batched into a per-(i, b_tilde) call returning a length-Ni vector of trace values:
```gap
trace_vec_b_tilde := [];
for k in [1..Ni] do trace_vec_b_tilde[k] := trace_on_W(i, k, b_tilde); od;
```
But this is internal to `_CTComputeSBlock`; the `trace_on_W` callable itself has signature `(i, k, h) -> cyclotomic` and would need a parallel `trace_on_W_batch(i, h) -> List(cyclotomic, length Ni)` version to compose.

**Why NEEDS-REVIEW:**
1. The trace_on_W for non-central classes routes to `EvalIrr`, which is a column lookup in the character table. The per-(i, k) cost is amortised by the character-table cache — so batching may not help.
2. At the central class on G, `trace_on_W = mult * chi_val` where `mult` doesn't depend on h. So pre-computing `mult` once per (i, k) and reusing it across all b_tilde calls is the natural optimization — currently done implicitly via the multiplicity_lookup cache.
3. The current shape (per-call k loop) suggests the author already structured this for clarity vs perf. Verifying that an Ni-length batched version would actually help requires profiling on m=5 K-4b production data, which is not yet available.

**Impact:** NEEDS-REVIEW. The orthogonal-perf question here is: when `trace_on_W` is a cheap character-table lookup (non-central), there's no slot for batching to help; when it's a multiplicative wrapper around character data, the wrapper might be expensive enough to want batching, but the multiplicity is already cached. Flagged for follow-up if m=5 K-4b production wall analysis shows _CTComputeSBlock dominates.

---

## Tier B: driver setup / streaming pre-compute

### B-DVAN-1 — `_DETF_F2RrefStateAddBlockMut` calls `TransposedMat` per call on cached per-EA F_2 matrices. (HIGH-CONFIDENCE)

**Location:** `extraspecial_orbifolds/scripts/detecting_family_restriction.g:1539-1571` (`_DETF_F2RrefStateAddBlockMut`).

**Current shape:**

```gap
_DETF_F2RrefStateAddBlockMut := function(state, M_block_F2)
    local M_T, r, i, pivot, j_clear;
    # Columns of M_block_F2 are vectors in F_2^{k_G}; expose them
    # as mutable rows via TransposedMat ...
    M_T := MutableCopyMat(TransposedMat(M_block_F2));   # *** per call ***
    for r in M_T do
        ...
    od;
end;;
```

Called by:
- `_DETF_F2RankGain(state, M_block_F2)` — line 1617-1626. Used in the m=7 Pass 1 inner loop at line 1947-1949:
  ```gap
  gains := List(eligible, j -> [j, _DETF_F2RankGain(f2_state, data!.res_EA_list_F2[j])]);
  ```
- `_DETF_F2RrefStateAdd(state, M_block_F2)` — used to commit a chosen EA at line 1965.

At m=7 Pass 1 with 1000 candidate EAs, each pass through the while loop evaluates `_DETF_F2RankGain` for every remaining candidate (eligible). If pass1_steps ≈ 10 with 1000 candidates initially, that's ~10 000 invocations of `_DETF_F2RrefStateAddBlockMut`, each doing a fresh `TransposedMat` on the same `data!.res_EA_list_F2[j]` matrix.

**Why the paths are orthogonal:**

- **The cached GF(2) matrix** `data!.res_EA_list_F2[j]` (built lazily at `:1580-1591` and `:1416-1431`) is correctly tagged via `ConvertToMatrixRep(M, GF(2))` — composes nicely with compiled GF(2) arithmetic.
- **The transpose** is computed per-call. The matrix doesn't change between calls (it's a fixed restriction matrix), so the transpose could be pre-cached alongside it.

This is the **same pattern as PR #396 instance A-5** (integer column-major `basis_cache.table_T`) applied to the D-VAN m=7 streaming path's GF(2) restriction-matrix family. The PR #396 audit explicitly flagged: "Add INTEGER column-major view too: `table_T := TransposedMatMutable(table)`" — this is the GF(2) counterpart, where the cache is `res_EA_list_F2_T`.

Memory cost: at m=7, `res_EA_list_F2[j]` is k_G × k_H = ~91 × ~few-hundred = ~50 KB per matrix × 1000 EAs = ~50 MB. Doubling for the transpose cache: ~100 MB. Within budget for the m=7 streaming-greedy path (which has ~600 MB peak per the docstring at line 1675).

**Composition sketch:**

WRONG (current):
```gap
# Cache build (line 1580-1591): only forward direction.
data!.res_EA_list_F2 := List(data.res_EA_list, M -> M * One(GF(2)));
for j in [1..Length(data!.res_EA_list_F2)] do
    ConvertToMatrixRep(data!.res_EA_list_F2[j], GF(2));
od;

# Per-call (1546): re-transpose.
M_T := MutableCopyMat(TransposedMat(M_block_F2));
```

RIGHT:
```gap
# Cache build: forward + transpose.
data!.res_EA_list_F2 := List(data.res_EA_list, M -> M * One(GF(2)));
data!.res_EA_list_F2_T := [];
for j in [1..Length(data!.res_EA_list_F2)] do
    ConvertToMatrixRep(data!.res_EA_list_F2[j], GF(2));
    data!.res_EA_list_F2_T[j] := MutableCopyMat(
        TransposedMat(data!.res_EA_list_F2[j]));
    ConvertToMatrixRep(data!.res_EA_list_F2_T[j], GF(2));
od;

# Per-call: look up the cached transpose. The caller needs to pass
# both directions, or expose a separate _AddBlockTransposed entry.
_DETF_F2RrefStateAddBlockMut_FromCache := function(state, M_block_F2_T)
    local r, i, pivot, j_clear;
    for r in M_block_F2_T do  # already row-major over k_H
        # ShallowCopy may still be needed if state's mutations conflict;
        # but the per-call TransposedMat + MutableCopyMat goes away.
        ...
    od;
end;;
```

Caveat: `_DETF_F2RrefStateAddBlockMut` mutates rows of `M_T` (via `AddRowVector(r, state.basis[i])`). If the cache rows are shared across calls, that's a correctness bug — need `ShallowCopy(M_T[r])` to preserve. Alternatively, snapshot the cached transpose and let GAP's packed GF(2) `AddRowVector` work on the copy (still cheaper than a fresh transpose).

**Impact:** Tier-B. The wall at m=7 Pass 1 is bounded by 1000 × (transpose cost + RREF cost). The transpose dominates for sparse matrices; the RREF for dense ones. Profiling would clarify.

**Proposed follow-up issue:** "Cache `data!.res_EA_list_F2_T` (GF(2) transposes) alongside `data!.res_EA_list_F2` to amortise the `TransposedMat` cost across `_DETF_F2RankGain` evaluations in m=7 Pass 1."

---

### B-K4-1 — K-4a m=5 dispatch on `_K4A_GetDVANEAFamily`: paths exist but don't compose (negative finding re-cat). (NEEDS-REVIEW)

**Location:** `extraspecial_orbifolds/scripts/k4a_classify.g:884-902`.

**Current shape:**

```gap
if opts.lattice_source
   and (not _K4A_OmegaIsZero(opts.omega_vec))
   and _K4A_GetDVANEAFamily(m) <> fail then
    # Multi-EA path (D-VAN's minimum family). Uses ComputeModularData
    # directly per EA, NOT via TranslateSpectralDataToEPlus +
    # RestrictTraceOnWToSubgroupHonourParent.
    E_class := _K4A_ClassifyEBranchMulti(opts, m, _K4A_GetDVANEAFamily(m));
elif m >= 5 then
    # Spectral translation path (m=5 K-4b production). Uses sparse spectral
    # data + TranslateSpectralDataToEPlus + RestrictTraceOnWToSubgroupHonourParent.
    data_E := TranslateSpectralDataToEPlus(sparse_data, ea_rec.parent);
    restricted_E := RestrictTraceOnWToSubgroupHonourParent(
        data_E, ea_rec.subgroup);
    E_class := _K4A_ClassifyAbelianBranch(restricted_E, ea_rec.subgroup);
else
    # Legacy single-EA path (m <= 3).
    data_E := _K4A_BuildBranchData(opts, m, ea_rec.parent);
    restricted_E := _K4A_RestrictForBranch(opts, data_E,
                                            ea_rec.subgroup);
    E_class := _K4A_ClassifyAbelianBranch(restricted_E, ea_rec.subgroup);
fi;
```

This is a 3-way dispatch on (opts.lattice_source, opts.omega_vec, m). The three paths:

1. **Multi-EA at ω ≠ 0** (any m, when D-VAN family available): direct `ComputeModularData` per EA. Bypasses the spectral builder entirely.
2. **Spectral-translate single-EA at m ≥ 5** (ω = 0): `BuildKRRSpectralCharactersSparse(5)` + `TranslateSpectralDataToEPlus`. The sparse spectral builder runs but its data only feeds the single-EA branch.
3. **Legacy single-EA at m < 5** (any ω): K-1 untwisted-baseline.

**Why this is not orthogonal-perf siloing:**

The three paths address DIFFERENT MATH PROBLEMS, not different perf opts of the same problem:
- Path 1 was added (issue #333) because the spectral-translate path mis-classifies at single-EA when ω ≠ 0 (kernel of the single-EA restriction is non-trivial).
- Path 2 is the K-4a-T4c path that genuinely needs the spectral builder at ω = 0 (per K-4b semantics).
- Path 3 is the legacy K-4a-T7 anchor for m ≤ 3.

Composing them WOULD be wrong: the multi-EA path's E_class is a conjunction over D-VAN's minimum family, the spectral-translate path's E_class is a single match. They're answering different questions.

**Why NEEDS-REVIEW:** at m=7 the multi-EA path (Path 1) and spectral-translate path (Path 2) BOTH need to engage — Path 1 for correctness at ω ≠ 0, Path 2 for the spectral data on G's central twist. Currently they don't compose: under (Path 1)'s condition, `sparse_data` is computed (Step 1, line 770-863) but never USED by Path 1's `_K4A_ClassifyEBranchMulti`. The sparse spectral computation runs as side-effect but its result is discarded.

This is a **dispatch siloing in a correctness-driven way** — not a perf issue per se, but the wasted spectral build at m=5/m=7 with non-zero ω is a real cost (∼30 min at m=5 per the spectral_data.wall_seconds field). At m=7, with #236 unblocked, the sparse spectral build is ~hours.

**Composition sketch:**

WRONG (current — sparse build runs but is discarded under Path 1):
```gap
if m = 5 then
    sparse_data := BuildKRRSpectralCharactersSparse(5);   # ~30 min
    spectral_data := rec(...);
fi;
...
if opts.lattice_source and ω != 0 and DVANFamily != fail then
    E_class := _K4A_ClassifyEBranchMulti(opts, m, ea_family);   # uses ω, not sparse
elif m >= 5 then
    data_E := TranslateSpectralDataToEPlus(sparse_data, ea_rec.parent);   # uses sparse
    ...
fi;
```

RIGHT:
```gap
# Defer sparse build until we know it's needed:
need_sparse := opts.lattice_source AND m >= 5 AND _K4A_OmegaIsZero(opts.omega_vec);
if need_sparse then
    sparse_data := BuildKRRSpectralCharactersSparse(m);
fi;
...
if opts.lattice_source and ω != 0 and DVANFamily != fail then
    E_class := _K4A_ClassifyEBranchMulti(opts, m, ea_family);
elif need_sparse then
    data_E := TranslateSpectralDataToEPlus(sparse_data, ea_rec.parent);
    ...
fi;
```

**Re-categorisation:** This isn't orthogonal-perf siloing as PR #396 defined it (two perf wins for the same problem that don't compose). It's wasted-work due to eager computation. Flag as a negative finding with a TODO for the dispatch to skip the spectral build when not needed. **Not Tier-A in the perf sense.**

**Impact:** Tier-C as a perf issue (it's correctness-shape, not perf-shape). But ~30 min wasted at m=5 with non-zero ω is real.

---

## Tier C: outside production hot path

### C-K4-1 — `BuildCentralExtension` in `fsi_wrapper.g` builds permutations via per-element closures. (HIGH-CONFIDENCE)

**Location:** `extraspecial_orbifolds/scripts/fsi_wrapper.g:220-283` (`BuildCentralExtension`).

**Current shape:**

```gap
t_perm := PermList(List([1..n], function(k)
    local gIdx, a;
    a := ((k - 1) mod o);
    gIdx := QuoInt(k - 1, o) + 1;
    return embed(gIdx, a + 1);
end));
...
for b in GeneratorsOfGroup(G) do
    b_img := List([1..n], function(k)
        local gIdx, a, g, gb, gbIdx, exp;
        a := (k - 1) mod o;
        gIdx := QuoInt(k - 1, o) + 1;
        g := elemsG[gIdx];
        gb := g * b;
        gbIdx := Position(elemsG, gb);
        exp := alpha(g, b);
        return embed(gbIdx, a + exp);
    end);
    Add(b_perms, PermList(b_img));
od;
```

Each `List([1..n], function(k) ... end)` invocation dispatches a fresh `NewLVarsBag`/`FreeLVarsBag` per element — the **P3 anti-pattern** but with multi-line closures (more LVarsBag work than the typical x -> expr form). At n = |G| × o where |G|=8 and o=8 for the Q_8 example, n=64 — small. At larger G (D_8 at m=2 with central order 8: n=64; D_8 at m=5 with central order ≥8: n=64), still small.

**Why orthogonal:**

The closure pattern here is the P3 anti-pattern, fixable with a plain `for k in [1..n] do b_img[k] := ... od;` (compiled local-var assignment instead of closure call). But the algorithmic cost is O(|G|² · |gens|) (`Position(elemsG, gb)` is linear in |G|), which dominates at any non-trivial G — the P3 fix would not be a meaningful speedup.

**Why Tier-C:** `BuildCentralExtension` is only called by `ProjectiveCharactersDirect`, which is in turn called by `FSIProjAt`. The fsi_wrapper.g path is used by the D-VAN-FIX (#81) regression tests and the F-S indicator computations — none of which is on the A-5b or D-VAN m=7 hot path.

**Impact:** Tier-C. Recording for completeness. Not urgent.

---

## Negative findings (places examined; siloing not found)

### N-DVAN-1 — `_DETF_F2RrefState` correctly composes lazy F_2 cache with incremental RREF.

`detecting_family_restriction.g:1577-1606`. The F_2 cache (`data!.res_EA_list_F2`, `data!.res_D8_F2`, `data!.res_Q8_F2`) is built once per `data` record; the RREF state accumulates over per-call adds. The `data!` mutation marker (using GAP's bang-syntax for mutable record fields) is intentional. The lazy build is correctly memoised — IsBound check at line 1579 + 1416. No siloing.

### N-DVAN-2 — `_DETF_KernelOrderSNF` correctly delegates to `SmithNormalFormIntegerMat` on stacked block matrix.

`detecting_family_restriction.g:1448-1490`. The integer SNF is the right primitive for kernel-order over Z. The function caches results indirectly through `_DETF_F2RrefState` (the F_2 prescreen). No orthogonal-perf opportunity in the SNF call itself — that's compiled HAP/GAP code.

### N-DVAN-3 — `BuildRestrictionMatrices`'s m-dependent dispatch is correct.

`detecting_family_restriction.g:1183-1332`. The (hap | lhs | quillen) source dispatch at lines 1199-1220 is correctness-shape (each source produces a different `R_G`); not perf-shape. Errors at m=7+hap are deliberate guards against `ResolutionFiniteGroup(E_+(7), 4)` OOM. No siloing.

### N-DVAN-4 — `_DETF_LagrangiansViaWitt_streaming` correctly streams via consumer callback.

`detecting_family_restriction.g:868-877`. The streaming variant is the OOM fix for the m=7 case (9.8M Lagrangians × ~5 GB peak otherwise). The recursion-with-consumer pattern is standard and the streaming/eager dichotomy is a memory-trade, not orthogonal perf.

### N-K4-1 — `K4aClassify`'s 3-branch (E, D_8, Q_8) is correctness-shape, not perf-shape.

`k4a_classify.g:865-945`. Each branch addresses a different injectivity gap (E covers F_2 torsion, D_8 covers Z/4 cyclic at m=2, Q_8 covers Z/4 at m≥3). The AND aggregation at line 953-966 is the AM04 detecting-family conjunction. No orthogonal-perf siloing.

### N-K4-2 — `KellerTwistIsTrivial` is a thin wrapper.

`keller/keller_twist_is_trivial.g:26-28`. Just `return ResIsTrivialOnDetectingFamily(m, omega_vec).trivial;`. The perf issue is in `ResIsTrivialOnDetectingFamily` (A-DVAN-1), not in the wrapper.

### N-K4-3 — `KellerSEntry`'s `lattice_source := true` dispatch is correctness-shape.

`keller/keller_s_entry.g:60-112`. The `if lattice_source then ... else ... fi;` at line 83 dispatches between SKellerLattice (the K-4a-T4b path for non-zero ω with V-1 epsilon) and SKeller (the K-2 untwisted-baseline). At ω = 0 the two agree numerically (K-3 anchor). This is the same kind of correctness dispatch as N-K4-1, not perf-shape.

### N-K4-4 — `q8_classifier.g::ClassifyOnQ8` correctly iterates LoadModularData.

`q8_classifier.g:115-172`. The 8-class iteration is small and bounded; LoadModularData has its own caching in `src/modular_data.g`. No orthogonal-perf opportunity here.

### N-K4-5 — `RestrictTraceOnWToSubgroupHonourParent`'s short-circuit at `parent_data.multiplicities[k_G_idx] = fail` is correct.

`restrict_to_subgroup.g:650-678`. The short-circuit at line 650-653 avoids building the restriction-decomposition matrix at non-central classes (where the sparse builder marks mults as `fail`). This is intentional and not a siloing. Comment at line 644-649 explicitly notes "At m=5 the parent has 1025 classes and only one (the central) carries a real mults list, so this short-circuit is the difference between O(1) class touches and O(num_classes) for the restriction-decomposition build."

### N-K4-6 — `RestrictTraceOnWToSubgroupProjective`'s delegate-to-untwisted at `omega_vec = 0` is correct.

`restrict_to_subgroup.g:919-937`. When `omega_vec` is all-zero, the projective path delegates to `RestrictTraceOnWToSubgroup` (byte-for-byte identical output per acceptance criterion 1 of #328). This is intentional dispatch, not siloing.

### N-DVAN-5 — `RestrictionMatrixViaHAP` post-#329 `_FastGroupCohomologyFunctor` is composed correctly.

`detecting_family_restriction.g:201-308`. The integration of `_FastGroupCohomologyFunctor` (which skips UCT recomputation per #329) with the existing rescale+augment+solve pipeline correctly threads the pre-computed UCT records. The P1/P3 fixes from #381+#382 (per-row mod-loop closure-free; SolutionMat int-cast) are already in place. The downstream `ConvertToMatrixRep(res_mat)` at line 306 tags the result for compiled matvec. No further siloing.

---

## Open questions / NEEDS-REVIEW items

1. **A-K4-1 (F2_Dot / F2_QuadDot override) impact at m=7.** The Gauss-sum path at m=7 (`_BuildGaussCtx`, `_F2_QuadGaussSum`) uses `QFormEval` and other ops that internally call `F2_Dot` or matrix arithmetic. Does the m=7 production path actually hit F2_QuadDot? Verify by tracing through `TraceOnOmega0Gauss` and confirming F2_QuadDot is or isn't called. If not, demote to Tier-B for the m=5 K-4b production line.

2. **A-K4-2 (manual RREF in _BuildTraceCtx) wall.** Profile m=5 K-4b production to see whether the RREF cost matters at all next to the per-c trace loop. If RREF is <1% of trace cost, demote to Tier-C.

3. **A-K4-3 (TraceOnOmega0Batch P3+P6) total impact.** 8 sites × O(2M closure dispatches) per call × 1025 traces per m=5 build = ~16B dispatches. At ~50-200 ns per dispatch (GAP overhead) this is 800-3200 seconds. The K-4b m=5 result file (`k4b_m5_result.g`) records `E_class.wall_seconds = 586 s` — could be a substantial chunk. Worth measuring on the next K-4b production rerun.

4. **A-DVAN-2 (per-EA HAP chain-map setup) HAP internals.** Whether `EquivariantChainMap(R_H, R_G, phi)` actually recomputes R_G-side data per call is a HAP-internals question. The fast `_FastGroupCohomologyFunctor` already addressed UCT recomputation; the remaining question is whether the chain-map body itself has shared cost. Profile the m=7 production rerun and see whether per-EA wall is bounded below by a hard cost (R_H-side; expected) or has an R_G-side component that could be hoisted.

5. **B-DVAN-1 (cached `TransposedMat` for res_EA_list_F2).** Per-call `TransposedMat` cost on small (k_H × k_G ≈ 91 × 200 at m=7) GF(2) matrices vs caching ~50 MB. Likely a clear win but should be verified on m=7 Pass 1 wall.

6. **B-K4-1 (m=5 wasted sparse build under multi-EA at ω ≠ 0).** The K-4a orchestrator currently runs `BuildKRRSpectralCharactersSparse(5)` (~30 min, ~700 s observed) even when its result is discarded by the multi-EA path at ω ≠ 0. Verify by inspecting the actual K-4a m=5 omega-sweep run logs; if the eager build is a noticeable fraction of total K-4a wall, gate it behind the need_sparse condition.

---

## Methodology

**Approach:** Read every file in `extraspecial_orbifolds/scripts/keller/` plus the D-VAN core files (`detecting_family_restriction.g`, `detecting_family_vanish.g`, `fsi_wrapper.g`, `quillen_detecting_subgroup.g`), the K-4 orchestrators (`k4a_classify.g`, `k4b_xcheck_d_van.g`), the trace machinery (`krr_spectral_characters.g`, `krr_spectral_characters_sparse.g`), and the bridge/translate files (`restrict_to_subgroup.g`, `em_eplus_translate.g`, `ct_modular_data.g`). Looked specifically for:

1. `if perf_A then ... else perf_B` dispatch shapes (orthogonal-perf siloing).
2. P3 closures `List(L, x -> f(x))` in hot loops.
3. P6 per-row mod via closure inside a for-loop.
4. P9 `Sum(List(L, f))` instead of compiled inner product / matvec.
5. P5 `List([1..n], i -> 0)` zero-init instead of `ListWithIdenticalEntries`.
6. P8 `TransposedMat` on cached matrices.
7. Two perf families on the SAME math (e.g. integer-matmul vs GF(2)-matmul) being applied in separate places without composition.
8. Helpers overridden by `*_optim.g` files — and helpers that should have been overridden but weren't.
9. Caches that exist for one representation but not another.

**Files read in full:**
- `extraspecial_orbifolds/scripts/keller/keller_s_entry.g` (114 lines)
- `extraspecial_orbifolds/scripts/keller/keller_twist_is_trivial.g` (30 lines)
- `extraspecial_orbifolds/scripts/k4a_classify.g` (996 lines)
- `extraspecial_orbifolds/scripts/detecting_family_restriction.g` (2350 lines, in three passes)
- `extraspecial_orbifolds/scripts/detecting_family_vanish.g` (202 lines)
- `extraspecial_orbifolds/scripts/fsi_wrapper.g` (359 lines)
- `extraspecial_orbifolds/scripts/quillen_detecting_subgroup.g` (732 lines, in two passes)
- `extraspecial_orbifolds/scripts/krr_spectral_characters_sparse.g` (1209 lines, in three passes)
- `extraspecial_orbifolds/scripts/restrict_to_subgroup.g` (key sections at 270-787, 791-1050)
- `extraspecial_orbifolds/scripts/em_eplus_translate.g` (key section 375-580)
- `extraspecial_orbifolds/scripts/ct_modular_data.g` (289 lines)
- `extraspecial_orbifolds/scripts/brw_construction.g` (161 lines)
- `extraspecial_orbifolds/scripts/krr_spectral_characters.g` (first 120 lines, dependency notes)
- `extraspecial_orbifolds/scripts/defect_rep_minus_id.g` (F2_* primitive definitions, lines 120-235)
- `extraspecial_orbifolds/scripts/defect_rep_minus_id_optim.g` (F2_* overrides, lines 40-105; usage examples 200-500)
- `extraspecial_orbifolds/scripts/qforms_f2.g` (first 200 lines of F_2 helpers)
- `extraspecial_orbifolds/scripts/q8_classifier.g` (key dispatcher at 100-172)
- The original audit report at `extraspecial_orbifolds/docs/superpowers/research/2026-06-02-orthogonal-perf-paths-audit.md`.

**Files partially read (skimmed for perf-relevant sections):**
- `extraspecial_orbifolds/scripts/brw_simples_action.g` (~100 lines around perf-relevant primitives)
- `extraspecial_orbifolds/scripts/k4b_xcheck_d_van.g` (~120 lines harness only)
- `extraspecial_orbifolds/scripts/k4b_m5_result.g` (header + RESULT shape; rest is matrix data)

**Grep queries used:**
- `grep -rnE "List.*-> "` to find closures (P3 in CLAUDE.md)
- `grep -rnE "Sum\(List|SolutionMat|TransposedMat"` to find P9 and P8
- `grep -rn "F2_Dot\|F2_QuadDot\|F2_Mul"` to find override gaps
- `grep -nE "if perf_A then|^TraceOnOmega0\|^F2_"` to find dispatch entries
- `grep -nE "TraceOnOmega0" extraspecial_orbifolds/scripts/*.g` to enumerate the trace dispatch tree
- `grep -nE "RestrictTraceOnWToSubgroup"` to find the variant family (Subgroup, HonourParent, Projective)

**Cross-references checked:**
- For each function found via grep, traced callers to confirm whether the function is on the m=5 K-4b production hot path (Tier A), D-VAN m=7 streaming path (Tier A), or driver setup (Tier B).
- Cross-referenced findings against PR #396's negative findings (N-1 through N-7) to avoid duplicating.
- Cross-referenced findings against CLAUDE.md's P1-P10/P16 anti-pattern catalog.
- Confirmed `defect_rep_minus_id_optim.g` does NOT override F2_Dot / F2_QuadDot via explicit `grep -nE "^F2_Dot|F2_Dot :=|^F2_QuadDot|F2_QuadDot :="`.

**What this audit did NOT check:**
- HAP-internal performance (per the same scope-out as PR #396).
- The detailed K-1 / krr_projector.g / untwisted_modular_data.g pipeline — those are upstream consumers but are not the "orthogonal-perf siloing" target.
- `build_krr_intertwiner_data.g` (only header-skimmed for K-4a-T4b context).
- Tests under `tests/`. Per task constraint (production code only).
- `defect_rep_other.g` (non-central twist; not on K-4 production hot path).
- `untwisted_modular_data.g` (very large, only the public surface read).
- `brw_h3_action.g` (already audited by PR #396 as N-4).
- `brw_construction.g` / `brw_simples_action.g` more than the first ~100 lines (header confirms they're BRW glue, not perf-critical).

---

## Summary by impact tier

**Tier A (D-VAN m=7 or K-4 m=5 production hot path; fix soon):**
- A-K4-1: Add `F2_Dot` and `F2_QuadDot` overrides in `defect_rep_minus_id_optim.g` to match the existing `F2_Mul`/`F2_VMul`/`F2_Trans`/`F2_Add` family. (HIGH)
- A-K4-3: Replace 8× `List(M, row -> List(row, x -> x mod 2))` in `TraceOnOmega0Batch` with compiled per-row `mod 2`. (HIGH)
- A-DVAN-1: Replace 6× `Sum(List)` matvec patterns in `ResIsTrivialOnDetectingFamily` with compiled `hom_omega * res_*` matvec. (HIGH)
- A-K4-2: Migrate manual F_2 RREF in `_BuildTraceCtx` / `_BuildGaussCtx` to `TriangulizeMat` on GF(2)-tagged matrix. (NEEDS-REVIEW: confirm wall impact via m=5/m=7 profiling)
- A-DVAN-2: Verify HAP's `EquivariantChainMap` doesn't waste R_G-side setup per-call at m=7 streaming Step 4. (NEEDS-REVIEW: pending m=7 production profiling)
- A-K4-4: Consider per-(i, b_tilde) batched trace_on_W in `_CTComputeSBlock`. (NEEDS-REVIEW: confirm `_CTComputeSBlock` dominates K-4b m=5 wall)

**Tier B (driver setup / pre-compute; fix when convenient):**
- B-DVAN-1: Cache `data!.res_EA_list_F2_T` (GF(2) transposes) for m=7 streaming Pass 1. (HIGH)
- B-K4-1: Defer `BuildKRRSpectralCharactersSparse(m)` build to only when actually consumed (lattice_source ∧ ω = 0 ∧ m ≥ 5). (NEEDS-REVIEW: not a perf-paths siloing, more a wasted-work issue)

**Tier C (cleanup / negligible impact; track only):**
- C-K4-1: P3 closures in `BuildCentralExtension` (fsi_wrapper.g). (HIGH math, negligible impact)
