# Audit-tier3 corrected interpretation — 2026-06-02

## Trigger

User challenge during PR #389 review: "Are we sure GAP doesn't have a compiled `PROD_MAT_VEC_INT`?" — re-examination of the audit's P16 probe in `docs/superpowers/research/2026-06-02-perf-audit-full.md` shows the agent's framing was misleading.

## What the audit's probe actually showed

```
1000 iterations of (165×165 int matrix) × (length-165 int vector)
  Plain plist-of-plists:                          29 ms
  After ConvertToMatrixRep(M) [no field arg]:     29 ms  (no-op)
  After ImmutableMatrix(Integers, M):             25 ms  (~16% bump)
```

Per-matvec arithmetic: 29 ms / 1000 / (165 × 165) = **~1 ns per scalar op**.

That **is compiled C-level speed**. There is no slower interpreted layer to escape from. `ProdVectorVector`, the symbol that dominates the live A-5b sample at 28.8% of CPU, is GAP's C-coded dense list-list product. It's the leaf function of the compiled matvec, not an interpreter loop.

## The original audit's framing (wrong)

> "GAP does not ship a dense compiled `PROD_MAT_VEC_INT` for plain integer matrices the way it does `PROD_MAT_VEC_GF2`. Matvec on plain integer plist-of-plist falls through generic `ProdListScl → ProdVectorVector`, which IS the C-level implementation but goes one element at a time with type dispatch each cell."

The sentence after "which IS the C-level implementation" silently contradicts the headline. The "one element at a time with type dispatch each cell" claim is also wrong — `ProdVectorVector` is a tight C loop with no per-cell type dispatch when the inputs are tagged homogeneous integer lists (TNUM 26 = `T_PLIST_HOM`).

## The corrected interpretation

GAP **does** ship compiled integer matvec via `ProdVectorVector`. The 28.8% CPU share of `ProdVectorVector` in the sample is **the compiled matvec firing many times on a very large operand**, not interpreter overhead.

### Why the per-vec wall is 270 s anyway

At m=5 production scale:

- `basis_cache.table` has shape `n² × k` where `n = Order(C)` up to 2048 and `k = 165`. So `n² × k ≈ 4,194,304 × 165 ≈ 692,000,000` scalar entries per matrix.
- `basis_cache.table * vec_target` requires reading every entry: **~692M scalar multiplications per matvec call**.
- At ~1 ns per scalar (compiled), each matvec is ~0.69 s.
- Per Step-4 vec the driver fires Path Z ~256 times (each target whose `vec_target[exp_index] != 0`) × 0.69 s = **~177 s per vec** just in this one matvec.

That matches the observed 270 s plateau. The matvec itself is at compiled speed; the cost is the **product of operands' shape × call frequency**, not interpreter overhead.

### What `ImmutableMatrix(Integers, M)`'s 16% bump actually is

Not a switch to a different primitive. It bypasses some per-call rechecks (e.g., `IsRectangularList` recomputation on every multiplication). At n=165 the overhead is a measurable fraction; at production n²=4M it's noise (the compiled inner loop dominates).

## Implications for what to fix

The audit's rank-1-8 fixes in PR #389 are **still correct**. They target genuine waste — closure dispatches over k-length or n²-length lists where compiled list arithmetic is available. None of them depend on the P16 mischaracterisation.

What changes:

1. **Stop expecting `ConvertToMatrixRep` (no field arg) or `ImmutableMatrix(Integers, M)` to deliver large speedups.** They don't, and the audit's "wait for the structural P16 fix" was right but for the wrong reason.

2. **The real structural fix is to reduce the number of operations**, not to engage a missing primitive. Concrete approaches in the structural-fix issue (#390 follow-up filed alongside this doc):
   - **Column-extract for sparse `vec_target`**: when `vec_target` has only one non-zero (the order-4 axis column 165 case), the full `n² × k` matvec collapses to a single-column read. Per Path Z call: 4M ops → 4M ops still, but only the column-fc data is touched. Cache-friendlier.
   - **GF(2) bit-packing**: at exponent = 4, `basis_cache.table` entries are in {0, 1, 2, 3}. The bottom bit is the GF(2) projection; the top bit is the order-4 lift. Packed-bit matvec via `PROD_GF2MAT_GF2VEC` is ~32-64× faster (vector words of 64 bits at once).
   - **Sparsity exploit on `vec_target_exp`**: as fixed in #389 rank-1, when `vec_target_exp = exp_axis_vec * e_fc`, we don't need the full matvec — just the column-fc read. The audit's framing missed that this fix already partially captures the column-extract strategy.

## What this doc supersedes / clarifies

In the master audit doc (`2026-06-02-perf-audit-full.md`):

- **P2 verification result** section ("HEADLINE FINDING. ConvertToMatrixRep(M) called WITHOUT a field argument..."): correct that the call is a no-op. **Wrong**: the implication that GAP lacks a compiled matvec. Replace with: "the call is a no-op because GAP's compiled matvec doesn't depend on this flag; the operation reaches the compiled C primitive `ProdVectorVector` regardless of the call. The dominant cost is the matvec's operand size, not interpreter overhead."
- **P16 (new): cache_orbit.table * vec matvec...**: replace "the comment-claimed `ConvertToMatrixRep(M)` (no field arg) is a no-op" framing with: "compiled `ProdVectorVector` is already firing; the cost is the n² × k operand shape and the call frequency. Structural workarounds in #390 follow-up: column-extract for sparse vec_target, GF(2) bit-packing, sparsity-aware path Z."

The PR #389 comments at `brw_h3_action.g:159` and `solver/orbit_cache_persist.g:457` should be updated to remove the "interpreted matvec" framing in a follow-up commit (not blocking #389's merge — the underlying fixes are still correct).

## Acknowledgement

The agent's structural recommendations were **directionally correct** (batched GF(2), reduce matvec count) but the *reason* it gave was wrong. The cost is real per-call work, not a primitive misdispatch.
