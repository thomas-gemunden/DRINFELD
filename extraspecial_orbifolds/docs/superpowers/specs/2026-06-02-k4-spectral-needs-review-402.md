# Spec: A-K4-2 + A-K4-4 (K-4 spectral trace NEEDS-REVIEW items from PR #402)

**Date:** 2026-06-02
**Status:** NEEDS-REVIEW — both items deferred pending K-4 m=5 / m=7
production timing data.
**Refs:** Issue #409. PR #402 audit (D-VAN + K-4 perf paths).
Companion HIGH-CONFIDENCE fixes A-K4-1 (PR #413), A-K4-3 (PR #405).

## TL;DR

Two K-4 spectral-trace findings from the PR #402 audit are flagged
NEEDS-REVIEW because they require either a math correctness check
(A-K4-2) or a non-trivial refactor with uncertain payoff (A-K4-4).
Neither is on the active production critical path today:

* **A-K4-2** — replace the manual F_2 RREF in `_BuildTraceCtx` /
  `_BuildGaussCtx` with `ConvertToMatrixRep(GF(2)) + TriangulizeMat`.
  Expected speedup 50-100×, but the manual code returns auxiliary
  state (pivot columns + back-substitution matrix) that the compiled
  primitive does not expose; we'd need to recover those from the
  GAP RREF output. Verdict: implement when K-4 m=5 production builds
  are profiled and prove `_BuildTraceCtx` is the bottleneck.

* **A-K4-4** — batch `_CTComputeSBlock`'s per-(a, b, k) `trace_on_W`
  evaluations. Current code does Ni × Nj × #pairs scalar evaluations
  per block; could pre-compute per-i / per-b_tilde once. Expected
  speedup is bounded by the fraction of trace_on_W's per-call setup
  cost that survives in batched form. Verdict: defer until profile
  data justifies the refactor.

**Recommendation: DEFER both** until K-4 m=5 production reruns with
PR #408 / #405 / #413 land and profile data is available.

## A-K4-2 — _BuildTraceCtx / _BuildGaussCtx manual F_2 RREF

### Location

`extraspecial_orbifolds/scripts/krr_spectral_characters_sparse.g`:
* `_BuildTraceCtx(h, m)` at line 103.
* `_BuildGaussCtx(h, m)` at line 592 (wraps `_BuildTraceCtx`).

### Current shape

```gap
# Row-reduce BPi. Solve x * BPi = target by reducing the
# augmented matrix [BPi^T | I_n]; pre-reduce the BPi^T side.
BPiT := F2_Trans(BPi);  # n x n
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
                          i -> (A2[j][i] + A2[r][i]) mod 2);
        fi;
    od;
    Add(pivCols, c);
    Add(pivRows, r);
    r := r + 1;
od;
# After RREF: A2[1..r-1] are pivot rows, A2[r..n] are zero on the
# BPi^T side (free directions). pivCols tracks the columns where
# pivots landed. The right-hand n columns store P such that
# P · BPi^T = RREF(BPi^T).
```

This is a manual `O(n^3)` row reduction over `F_2` with bookkeeping for
pivot columns + back-substitution matrix. At m=5, n = 32, so n^3 = 32K;
at m=7, n = 128, so n^3 = 2M. The interpreter loops are interpreted
GAP code (no compiled-primitive dispatch).

### Proposed alternative

```gap
BPiT := F2_Trans(BPi);                        # n x n integer matrix in {0, 1}
BPiT_gf2 := BPiT * One(GF(2));                # promote to GF(2) entries
ConvertToMatrixRep(BPiT_gf2, GF(2));          # packed-bit representation

# Compute RREF via TriangulizeMat (in place). Returns the row rank
# and mutates BPiT_gf2 to be the row-echelon form.
rank := TriangulizeMat(BPiT_gf2);

# Recover pivCols + back-substitution matrix:
#   - For each pivot row r, pivCols[r] is the leftmost non-zero
#     column of BPiT_gf2[r].
#   - The back-substitution matrix P satisfies P · BPiT = RREF.
#     We need to track this separately (TriangulizeMat doesn't
#     return it).
```

### Risk and math considerations

1. **Auxiliary state recovery (HIGH)**: The manual code maintains the
   augmented `[BPi^T | I_n]` matrix so that after RREF the right half
   yields `P` with `P · BPi^T = RREF(BPi^T)`. `TriangulizeMat` does not
   return `P`; we'd need to either:
   * (a) Augment the matrix manually with `IdentityMat(n)` and pass
         `[BPi^T | I_n]` to `TriangulizeMat`, then split. This works
         but doubles the matrix width (still cheap).
   * (b) Re-derive `P` from pivot positions. Requires solving
         `P · BPi^T = RREF(BPi^T)` row-by-row, which defeats the speedup.

   Option (a) is the right choice. The compiled `TriangulizeMat` on
   the augmented matrix produces both the RREF and the `P` block in
   one call.

2. **Pivot column ordering (MEDIUM)**: The downstream code in
   `_TraceEntry` (line 282+) uses `pivCols` to map RREF rows back to
   column positions. `TriangulizeMat` produces RREF with pivots in
   ascending column order (left-to-right), which is the same
   convention as the manual code. No change needed.

3. **Numerical / F_2 correctness (LOW)**: Standard `TriangulizeMat`
   over `GF(2)` is identical math to the manual mod-2 row reduction.
   Bit-identical results expected; only the implementation differs.

4. **Caching compatibility (LOW)**: The `_traceHKeys` /
   `_traceHVals` cache lookups at the top of `_BuildTraceCtx` are
   unaffected — they cache the whole context record, not individual
   matrices.

### Expected speedup

The audit estimated 50-100×. Grounded in CLAUDE.md performance notes:

* `TriangulizeMat` over `GF(2)` with `ConvertToMatrixRep(GF(2))` engages
  the compiled `TRIANGULIZE_LIST_GF2VECS` primitive — operates on
  packed-bit `Char(2)` matrices at roughly 16× the speed of integer
  matrices, plus avoids ~80% interpreter overhead on the manual loop.
  Net: ~50-100× per call.

* At m=5 with n=32 and ~1025 K-4 classes, `_BuildTraceCtx` is called
  ~1025 times per K-4 m=5 build. If each call currently costs ~50 ms
  (manual loop on n=32), the cumulative cost is ~50 sec. With the
  compiled primitive, that drops to ~1 sec.

* At m=7 with n=128, the scaling is `n^3 / (n^3 in compiled GF(2))`
  ≈ 50-100×. Per-call cost ~5 sec → ~50 ms. Aggregate impact
  significant.

### Test plan

1. Anchor at m=3 (n=8): the existing `tests/test_krr_spectral_characters_sparse.g`
   Test 0 (m=3 cross-check) covers this. Bit-identical results
   expected (the RREF math is the same).
2. Anchor at m=5 (n=32): Test 1 (m=5 cross-check) — same.
3. Profile: wrap `_BuildTraceCtx` calls in `Runtime()` blocks before
   and after the change. Confirm 50-100× speedup at m=5.
4. m=7: not exercised by current tests; verify via Q_8 / D_8 unit
   tests on the lower-level RREF helpers.

### Decision

**DEFER** until the K-4 m=5 production rerun proves `_BuildTraceCtx`
is in the top-5 wall consumers. The audit estimate is based on
order-of-magnitude analysis; actual impact depends on call frequency
(~1025× per build) and whether `_TraceEntry`'s downstream work
dominates the per-call cost.

If proven dominant, the implementation is ~30-line diff to
`krr_spectral_characters_sparse.g:103-170`. Estimated effort: half a
day including the augmented-matrix re-derivation of `P`.

## A-K4-4 — _CTComputeSBlock per-(a, b, k) trace_on_W

### Location

`extraspecial_orbifolds/scripts/ct_modular_data.g:115` —
`_CTComputeSBlock(intertwiner_data, i, j)`.

### Current shape

```gap
for ai in [1..Length(elts_i)] do
    a := elts_i[ai];
    t_a := ts_i[ai];
    for bi in [1..Length(elts_j)] do
        b := elts_j[bi];
        if a * b <> b * a then continue; fi;
        # ... bookkeeping ...
        b_tilde := t_a^-1 * b * t_a;
        a_tilde := s_b^-1 * a * s_b;
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

For each (a, b) pair, `trace_on_W(i, k, b_tilde)` is called Ni times
(once per row k); `trace_on_W(j, l, a_tilde)` is called Nj times
(once per column l). Both depend on (a, b) only through `b_tilde`
and `a_tilde` respectively.

### Proposed batched form

Per (a, b) pair, pre-compute the full per-row vectors:

```gap
# Pre-compute the per-row character values for THIS (a, b) pair:
chi_row := List([1..Ni], k ->
    ComplexConjugate(intertwiner_data.trace_on_W(i, k, b_tilde)));
chi_col := List([1..Nj], l ->
    ComplexConjugate(intertwiner_data.trace_on_W(j, l, a_tilde)));
# Outer product update:
for k in [1..Ni] do
    for l in [1..Nj] do
        M[k][l] := M[k][l] + eps * chi_row[k] * chi_col[l];
    od;
od;
```

This is mathematically identical (the for-loops compute the same sum)
but factors the trace_on_W calls out of the inner (k, l) loop.

A more aggressive variant batches across (a, b) pairs for a fixed
(i, b_tilde) — since b_tilde depends on `t_a * b * t_a^-1` and
multiple (a, b) pairs can yield the same b_tilde (within a centraliser
orbit), we could cache `chi_row` keyed by `(i, b_tilde)`. The audit
didn't quantify how often this would hit.

### Risk and math considerations

1. **Correctness (LOW)**: The factoring is mathematically equivalent.
   Bit-identical results.

2. **Memory (LOW)**: Two new length-N vectors per (a, b) pair (Ni + Nj
   complex numbers). Modest.

3. **trace_on_W per-call setup cost (HIGH-UNCERTAIN)**: The speedup
   depends entirely on whether trace_on_W has significant per-call
   overhead that gets amortised by batching. If trace_on_W is already
   compiled / fast / O(1), the batching saves nothing.

4. **Caching by b_tilde (NEEDS-REVIEW)**: To cache `chi_row` keyed by
   `(i, b_tilde)`, b_tilde must be hashable (e.g., via
   `LookupDictionary`). At m=5, `b_tilde` is a group element in a
   centraliser of size up to 2^11 = 2048; building a dictionary keyed
   on group elements is feasible.

### Expected speedup

* Naive factoring (chi_row + chi_col): saves the Ni × Nj redundant
  evaluations per (a, b) pair. If trace_on_W's per-call cost is
  significant (>100 µs), savings are 10-100× per (a, b). If
  trace_on_W is already <10 µs, savings are <2×.
* Aggressive (b_tilde cache): additional 10-100× if b_tilde repeats
  with high frequency per (i, b_tilde, k) tuple. Audit suggested this
  is the likely case but didn't quantify.

Combined upper bound: ~10-1000× per `_CTComputeSBlock` call. Per-K-4
build, S has ~num_classes^2 = ~1M blocks at m=5, but most are zero
(off-diagonal central-class blocks).

### Test plan

1. Anchor: existing K-4 spectral character tests (Test 4 in
   `test_krr_spectral_characters_sparse.g`) cover S-matrix
   construction. Bit-identical results expected.
2. Profile: time `_CTComputeSBlock` calls before/after the factoring.
3. Decide: if naive factoring gives <2× speedup, batching is not
   worth implementing.

### Decision

**DEFER** until K-4 m=5 production is rerun with the recent perf
PRs (#401 / #405 / #408 / #410 / #412 / #413) and `_CTComputeSBlock`
proves to be in the top-5 hot functions. The naive factoring
(chi_row + chi_col) is a ~10-line diff; the aggressive batching by
b_tilde is ~50 lines with non-trivial cache invalidation logic.

If the K-4 m=7 production timeline requires faster S-matrix
construction, prioritise the naive factoring first (cheap, low-risk)
and reassess the aggressive variant from profile data after.

## Combined recommendation

Defer both A-K4-2 and A-K4-4 indefinitely. Re-evaluate when:

1. K-4 m=5 production is rerun with the audit fixes already merged
   (#401, #405, #408, #410, #412, #413).
2. Profile data shows either `_BuildTraceCtx` or `_CTComputeSBlock`
   in the top 5 wall consumers.
3. K-4 m=7 production timeline requires further speedups beyond what
   the current audit fixes deliver.

If none of (1)-(3) triggers within the next major workstream cycle
(say, by 2026-07-15), mark both items as "won't fix" and close
issue #409.

## Refs

* PR #402 (D-VAN + K-4 audit): main report at
  `extraspecial_orbifolds/docs/superpowers/research/2026-06-02-orthogonal-perf-paths-audit-dvan-k4.md`.
* HIGH-CONFIDENCE companion fixes: #405 (A-K4-3 closure cleanup),
  #413 (A-K4-1 F2_Dot compiled).
* K-4 production state per CLAUDE.md: m=2/m=3 verified-trivial, m=5
  via K-4b sparse trace path, m=7 blocked on #236 Gauss-sum.
