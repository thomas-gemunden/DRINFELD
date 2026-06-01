# Path Z batch refactor — design + risk analysis (audit finding A-1)

Status: design doc. NEEDS-REVIEW marker in PR #396 audit; this spec resolves the math/risk question and recommends a course of action.

Audit source: `extraspecial_orbifolds/docs/superpowers/research/2026-06-02-orthogonal-perf-paths-audit.md` §A-1 ("Path A is batched; Path Z is per-call", HIGH-CONFIDENCE on the inefficiency, NEEDS-REVIEW on the refactor) and §A-4 ("`IB_StrictF2Witness` and `IB_TableMod2WithLift` could batch the kernel/lift sem back-subs", sub-task of A-1).

This spec is purely about the batching refactor. It is independent of A-2 (bit-form round-trip removal), A-3 (M_y column slicing), and B-7 (B-7 mod closure). It composes with PR #394's sparsity-aware GF(2) combine path — see § "Compatibility with PR #394".

## 1. Math derivation

### 1.1 The current per-call IB_RecCob recursion (m=5, modulus=4)

The Path Z dispatch in `run_e_plus_m_kernel_hap.g:587-695` reaches `IsCoboundary2Z4VecBits(C, c_bot, c_top, n)` per target. Internally (per `solver/iterated_bockstein.g:578-588`) this calls `IsCoboundary2Z2kVec(C, c_g_vec, 2)`, which calls `IB_RecCob(C, c_table, modulus=4, ...)`. The recursion at `modulus=4` does exactly four steps:

```
S1. beta_int := IB_StrictF2Witness(C, c_table, n)
                 == IsCoboundary2Mod2VecWithWitness(C, c_table mod 2)
                 -> {yes, witness sol} | fail
    Failure ⇒ return false.

S2. delta_beta := IB_DeltaBetaMult(beta_int, n, mult, 4)
                  == {(beta[i] + beta[j] - beta[mult[i][j]]) mod 4}
                  in Z (length n² integer vector).

S3. c_table_next := IB_DivBy2(c_table, delta_beta, modulus=2)
                  == ((c_table - delta_beta) mod 4) / 2  mod 2
                  in Z (length n² integer vector with entries in {0,1}).

S4. return IB_TableMod2WithLift(C, c_table_next, n)
           == IsCoboundary2Mod2WithLiftVec(C, c_table_next mod 2)
           -> bool (one back-sub against the cached lift-sem).
```

S1 hits the **cached kernel-sem** (`_GetCachedSemForAT(BoundaryMatrixGF2(C))`) and runs one back-sub of cost `rank × ncols / 64` GF(2) bit-ops PLUS interpreter overhead per `nonzero_heads` index. S4 hits the **cached lift-sem** (`_GetLiftSemForC(C)`) and runs one back-sub with the same shape. The audit (mod2_solver.g:535-538) showed 99.7% of CPU in interpreter overhead (loop, list-elm, eq-test, if-branch) and 0.3% in compiled bit-XOR. Both calls re-pay this overhead per target.

### 1.2 The state coupling between S1 → S2 → S3 → S4

The recursion is NOT a pure pipeline: S2 mutates state (`delta_beta`) derived from S1's `beta_int`, S3 uses S2's output AND S1's input (`c_table`), and S4 only fires if S1 succeeded.

For batching to be sound, we need to preserve this coupling **per target** while sharing the **compiled primitives** across the batch. Specifically:

- S1 returns one witness β per target. We need a way to extract all witnesses in one batched back-sub.
- S2 is pure per-target arithmetic on β. Naturally vectorisable.
- S3 is pure per-target arithmetic on c_table and delta_beta. Naturally vectorisable.
- S4 returns one bool per target. Already batched today via `IsCoboundary2Mod2WithLiftVecBatch` (used by Path A).

The blocker is S1: the existing `IsCoboundary2Mod2VecBatch` returns only booleans (residual = zero check), not the witnesses. We need an `IsCoboundary2Mod2VecWithWitnessBatch` primitive that returns the witness `sol_j` for each RHS.

### 1.3 Batched S1: witness reconstruction from the RREF basis

Recall (mod2_solver.g:142-225) the cached batched artefacts are
```
batched.pivot_cols : ascending index list (length=rank)
batched.Y_full     : rank × ncols GF(2) matrix in RREF
batched.rank, ncols
```
plus `sem.coeffs[vno]` rows that map "pick this pivot row" to "the kernel-side coefficient vector". Per-call, `IsCoboundary2Mod2VecWithWitness` computes

```
sol := 0 in GF(2)^{sol_dim}     -- sol_dim = Length(sem.coeffs[1])
b := ShallowCopy(c_g_vec mod 2)
for i in nonzero_heads do
    vno := sem.heads[i]      -- which row of sem.vectors has pivot at column i
    x := b[i]                -- the bit to cancel
    if x ≠ 0 then
        b   += x · sem.vectors[vno]      -- residual update
        sol += x · sem.coeffs[vno]       -- witness update
    fi
od
return rec(yes = IsZero(b), witness = sol if yes else fail)
```

Observe: `b[pivot_cols[k]] = b_P[k]` (by definition of pivot_cols). The witness can be rewritten as

```
sol = sum_{k : b_P[k] = 1} sem.coeffs[ sem.heads[ pivot_cols[k] ] ]
    = B_P · Coeffs_full          -- GF(2) matrix-vector product
```

where `Coeffs_full` is the rank × sol_dim matrix whose k-th row is `sem.coeffs[ sem.heads[ pivot_cols[k] ] ]`. (Caveat: this identity holds because the cached `Y_full` has been reduced to RREF, so each pivot bit of B contributes exactly its k-th row of Coeffs_full to the witness; no order-of-operations subtlety. See § 3.2 for verification anchors.)

The residual identity from `_RowSpanResidualBatch` already extracts B_P:
```
residual := B_P · Y_full + B       -- one GF(2) PROD_GF2MAT_GF2MAT + add
yes[j]   := IsZero(residual[j])
```

So a batched-with-witness primitive is **one additional matmul**:
```
witnesses := B_P · Coeffs_full     -- (numRHS × rank) × (rank × sol_dim) → numRHS × sol_dim
```

Both matmuls use the same `B_P` slice; the residual matmul against `Y_full` is the existing path. Cost: roughly twice the residual-batch matmul (the Coeffs_full matmul is of the same shape numRHS × rank, with sol_dim = ncols of A = |C| typically much smaller than ncols of `Y_full` = n²). So adding the witness extraction is **cheaper** than the residual matmul that already runs.

### 1.4 Batched S2: vectorised delta_beta

Today `IB_DeltaBetaMult(beta_int, n, mult, modulus)` is

```
for i in [1..n] do
    for j in [1..n] do
        delta_beta[(i-1)*n + j] := (beta_int[i] + beta_int[j] - beta_int[mult[i][j]]) mod modulus
    od
od
```

cost O(n²) per call, all in compiled integer arithmetic (after PR-eliminating the Position lookup). At m=5 (n=1024, modulus=4) this is ~1M ops per call. Across a batch of `B` targets in the same orbit, naive per-target dispatch is `B × 1M` ops.

There's no compiled matrix primitive that subsumes this — it's a structured n² loop indexed by the group multiplication table. We have three options:

**Option α (do not batch S2)**: keep `IB_DeltaBetaMult` per-target. Acceptable because the per-target inner loop is already compiled; the interpreter overhead is `B × (n + small constants)` calls into compiled code, not `B × n²` interpreter steps. The dominant batch saving comes from S1 and S4.

**Option β (stack and vectorise)**: stack `beta_ints` into a `B × n` integer matrix (B rows). For each (i, j), the contribution to all B targets is the column `(B_beta[:, i] + B_beta[:, j] - B_beta[:, mult[i][j]]) mod modulus`. This is one compiled list arithmetic op per (i, j) instead of B separate scalar ops. Cost: O(n² × compiled_vec_op) = O(n² × O(B / 64)) at the bit-vec rate. Net win against α: roughly the ratio `B / (overhead-per-scalar-call ÷ overhead-per-vec-call)` ≈ 5-50× depending on B and GAP's compiled vector op overhead.

**Recommendation**: start with option α (simpler, no new primitives). Re-measure after S1/S4 are batched. Only escalate to option β if S2 is the next dominant bucket. The S2 cost today is dwarfed by S1/S4 (which include n² × rank GF(2) bit-ops PLUS the interpreter overhead); after batching S1/S4, S2 becomes potentially the bottleneck but is itself only ~1M-scalar ops per target.

### 1.5 Batched S3: trivial whole-vector arithmetic

`IB_DivBy2(c_table, delta_beta, modulus=2)` is `((c_table - delta_beta) mod 4) / 2 mod 2`. The whole-vector compiled form across a batch is one matrix subtraction + one matrix mod + one elementwise divide + one matrix mod. Or — since we're working mod 4 and end up mod 2 — we can absorb the divide into a bit-extraction.

Per-target this is already cheap (compiled list-int arithmetic). Stacked across the batch: one compiled matrix subtract + one mod + one shift + one mod, all on `B × n²` integer matrices. Negligible against S1.

### 1.6 Batched S4: lift back-sub with kernel test

S4 is `IsCoboundary2Mod2WithLiftVec(C, c_table_next mod 2)`. The batched primitive `IsCoboundary2Mod2WithLiftVecBatch` (mod2_solver.g:737-806) ALREADY exists and is used by Path A. It does the kernel-then-lift two-stage check in a single chunk: stack inputs to GF(2) once, run kernel residual, then run lift residual on the kernel-failures only. We call it directly.

### 1.7 The recursive case (modulus ≥ 8)

`IB_RecCob` has a general recursion (`for mask in [0 .. 2^num_basis - 1] do recurse(modulus/2) od`) at lines 450-468. This path is NOT taken at m=5 (the m=5 dispatch lands in the `modulus = 4` shortcut at line 444). It is taken for hypothetical m=8/m=9 work (`exp = 8 ⇒ modulus = 8`).

For the m=5-only batch fix, the recursive case is out of scope. The batched API surface we define must remain compatible with the integer recursion — i.e., `IsCoboundary2Z2kVec(C, c_g_vec, k>2)` keeps the per-call path; only the `k=2 / modulus=4` specialisation gets a batched entry point.

This decision (m=5 only, modulus=4 only) is critical for risk management. The recursive case has 2^r mask enumerations × per-recurse work; batching would compound the state coupling complexity. We DEFER recursive-case batching as a separate spec.

## 2. Implementation sketch

### 2.1 New primitive: `IsCoboundary2Mod2VecWithWitnessBatch`

In `solver/mod2_solver.g`, mirror the existing `IsCoboundary2Mod2VecBatch` but return witnesses too:

```
# Cached at sem-build time alongside batched.Y_full / Y_full_T:
batched.Coeffs_full : rank × sol_dim GF(2) matrix.
                      Row k = sem.coeffs[ sem.heads[ pivot_cols[k] ] ].
                      Built ONCE in _BuildBatchedSolverArtefacts at cache time.

# New helper:
_WitnessBatch(batched, B) :=
    if rank = 0 then  -- only the zero RHS has a witness; others fail
        for j: out[j] = (zero witness if IsZero(B[j]) else fail)
    else
        B_P     := B{:, pivot_cols}      -- numRHS × rank GF(2) matrix
        witnesses := B_P · Coeffs_full   -- numRHS × sol_dim
        residual  := B_P · Y_full + B    -- existing batched residual
        for j: out[j] := (witnesses[j] if IsZero(residual[j]) else fail)
    return out

# New entry point:
IsCoboundary2Mod2VecWithWitnessBatch(C, c_g_vec_list) :=
    A := BoundaryMatrixGF2(C)            -- cached
    entry := _GetCachedSemForAT(A)       -- cached, now also has batched.Coeffs_full
    chunked dispatcher (mirror _RunBatchedRowSpanTest) calling _WitnessBatch per chunk
    return [rec(yes, witness) for each input]
```

The matmul cost analysis: B_P · Coeffs_full is shape `numRHS × rank × sol_dim`. At m=5, rank ≈ 2048, sol_dim ≈ 1024 (= |C|), numRHS ≤ chunk_size = 256, so per chunk we do one matmul of (256, 2048, 1024) bits = ~64 KB × 256 = 16 MB of operands. Compiled GF(2) matmul handles this in ~10 ms per chunk. Total added cost on top of the existing residual matmul: roughly half the residual matmul wall (because sol_dim < ncols).

The chunking pattern matches `_RunBatchedRowSpanTest` exactly. Reuse `_StackBVectorsForBatch` for input conversion.

### 2.2 New primitive: `IsCoboundary2Z4VecBitsBatch`

In `solver/iterated_bockstein.g`, add a batched variant alongside the existing per-call entry point:

```
# Inputs:
#   C          : centraliser group
#   c_bots     : list of length-n² packed-GF(2) vectors (one per target)
#   c_tops     : list of length-n² packed-GF(2) vectors (one per target)
#   n          : centraliser size
#   numRHS == Length(c_bots) == Length(c_tops)
#
# Returns: list of booleans of length numRHS.

IsCoboundary2Z4VecBitsBatch(C, c_bots, c_tops, n) :=
    # S0: reconstruct integer c_g_vec per target (length n² each).
    #     Total memory: numRHS × n² × ~5 bytes (small ints). At numRHS=256, n²=4M:
    #     ~5 GB worst case. Chunk to keep peak bounded.
    #
    #     NB: with A-2 (bit-form round-trip removal) landed, S0 disappears
    #     entirely: S1 consumes c_bots directly. This spec assumes A-2 has
    #     NOT landed; if it lands first, simplify S0 → identity pass.
    mult_rec := _GetCachedMultTable(C)   # cached
    n        := mult_rec.n

    # Process in chunks of size CHUNK_Z4 (default 256, matching the
    # _IS_COBOUNDARY2_BATCH_CHUNK used by the existing batched primitive).
    results := []
    chunk_start := 1
    while chunk_start <= numRHS do
        chunk_end := Minimum(numRHS, chunk_start + CHUNK_Z4 - 1)
        chunk    := [chunk_start .. chunk_end]
        chunk_len := Length(chunk)

        # S0 (per-target, integer reconstruction; see A-2 caveat above).
        #     Only needed if A-2 not landed; else feed bits straight through.
        c_g_vecs := EmptyPlist(chunk_len)
        c_tables_mod2 := EmptyPlist(chunk_len)
        for idx in chunk do
            cbi := IntVecFFE(c_bots[idx])
            cti := IntVecFFE(c_tops[idx])
            cg  := 2 * cti + cbi
            Add(c_g_vecs, cg)
            Add(c_tables_mod2, cg mod 2)
        od

        # S1 (BATCHED): IsCoboundary2Mod2VecWithWitnessBatch.
        #     Returns chunk_len results, each rec(yes, witness).
        s1_batch := IsCoboundary2Mod2VecWithWitnessBatch(C, c_tables_mod2)

        # Mark Stage-1-failures.
        chunk_results := EmptyPlist(chunk_len)
        s4_todo       := []           # indices within chunk that need Stage 4
        s4_inputs     := []           # c_table_next (length-n² int) for those
        for j in [1..chunk_len] do
            if not s1_batch[j].yes then
                Add(chunk_results, false)        # provisional false (S1 failed)
            else
                # S2 + S3 (per-target, all compiled list arithmetic).
                beta_int  := List(s1_batch[j].witness,
                                  x -> If_(IsZero(x), 0, 1))     # GF(2) → {0,1}
                delta_beta := IB_DeltaBetaMult(beta_int, n,
                                                mult_rec.mult, 4)
                c_table_next := IB_DivBy2(c_g_vecs[j], delta_beta, 2)
                Add(s4_inputs, c_table_next)
                Add(s4_todo, j)
                Add(chunk_results, false)        # provisional false; flip after S4
            fi
        od

        # S4 (BATCHED): IsCoboundary2Mod2WithLiftVecBatch.
        #     The c_table_next entries are length-n² integer vectors; the
        #     batched primitive does the integer→GF(2) reduction once per chunk.
        if not IsEmpty(s4_inputs) then
            s4_batch := IsCoboundary2Mod2WithLiftVecBatch(C, s4_inputs)
            for jj in [1..Length(s4_todo)] do
                if s4_batch[jj] then
                    chunk_results[s4_todo[jj]] := true
                fi
            od
        fi

        Append(results, chunk_results)
        chunk_start := chunk_end + 1
    od
    return results
```

Three centraliser-level caches are touched: `_GetCachedAF2T`, `_GetCachedMultTable`, `_GetLiftSemForC`. All are keyed by `IsIdenticalObj(C)` and shared with the per-call path. No new cache work.

### 2.3 Driver dispatcher changes in `PerVecTransgressionShared`

Modify `run_e_plus_m_kernel_hap.g:587-695` to accumulate Path Z inputs across the orbit BEFORE dispatching, mirroring Path A's accumulator:

```
for each orbit do
    # Existing Path A accumulators (kept):
    batch_A_inputs  := []
    batch_A_targets := []
    # NEW Path Z accumulators (one pair per "compose_with_bitpack" branch):
    batch_Z_bots    := []         # GF(2) length-n² vectors
    batch_Z_tops    := []         # GF(2) length-n² vectors
    batch_Z_targets := []
    # Path Z fallback (exp != 4 or col_bot_exp = fail) stays per-target:
    # IsCoboundary2SplitVecAware(...) on the rare integer fallback path.

    for target_idx in orbit do
        vec_target := H3VecAtTarget(...)
        if Path Z branch (exp_local > 2 and exp_index ≠ fail and vec_target[exp_index] ≠ 0) then
            if use_pathz_gf2pack and col_bot_exp ≠ fail then
                # Compute slice_bot, slice_top exactly as today (the PR #394
                # sparsity-aware combine — see § 5 for invariance).
                <... compute slice_bot, slice_top per existing code ...>
                Add(batch_Z_bots, slice_bot)
                Add(batch_Z_tops, slice_top)
                Add(batch_Z_targets, target_idx)
            else
                # Integer fallback (rare at m=5): stay per-target.
                results[target_idx] :=
                    IsCoboundary2SplitVecAware(basis_cache.C,
                                                basis_cache, vec_target, setup)
            fi
        else
            # Existing Path A accumulation, unchanged.
            <... compute c_prime_bits ...>
            Add(batch_A_inputs, c_prime_bits)
            Add(batch_A_targets, target_idx)
        fi
    od

    # Existing Path A batched call:
    if not IsEmpty(batch_A_inputs) then
        batch_A_results := IsCoboundary2Mod2WithLiftVecBatch(basis_cache.C, batch_A_inputs)
        for j in [1..Length(batch_A_targets)] do
            results[batch_A_targets[j]] := batch_A_results[j]
        od
    fi

    # NEW Path Z batched call:
    if not IsEmpty(batch_Z_bots) then
        batch_Z_results := IsCoboundary2Z4VecBitsBatch(
            basis_cache.C, batch_Z_bots, batch_Z_tops, basis_cache.n)
        for j in [1..Length(batch_Z_targets)] do
            results[batch_Z_targets[j]] := batch_Z_results[j]
        od
    fi
od
```

Logging: every batched call gets one `_LogPhase("step-4-pathz-batch", "orbit ", oi, ", batch_Z size ", numZ, ", wall ", wall, " s")` line. Per CLAUDE.md, avoid per-call logging inside the batched primitive.

## 3. Risk analysis

### 3.1 Memory

**Per-chunk peak** (chunk_size = 256, m=5, n=1024, n² = 4M):

- `batch_Z_bots`, `batch_Z_tops`: each is `numRHS × n² / 8` bytes of packed GF(2) = `256 × 512 KB` = 128 MB per accumulator at numRHS=256. Total for both accumulators: 256 MB. Held across the orbit (NOT chunked at accumulation time — accumulation is per-orbit, chunking is inside the batched call).
- S0 reconstruction `c_g_vecs[j]` integer length-n² with entries 0-3: ~16 MB per target as a plain GAP plist of small ints. At chunk_size = 256: 4 GB worst case.
- S1's batched witness call: B_P is `numRHS × rank` = `256 × 2048` bits = 64 KB. Y_full and Coeffs_full are the cached rank × ncols / rank × sol_dim matrices (memory-resident, not chunk-peak). `residual` is `numRHS × n²` GF(2) bits = `256 × 4M / 8` = 128 MB per chunk.
- S4's `IsCoboundary2Mod2WithLiftVecBatch`: per Path A's measurements, ~512 MB per chunk worst case at numRHS=256.

**Total peak per orbit** (rough estimate, assuming worst-case orbit with all targets routing through Path Z, numRHS = orbit_size = up to 1024 at m=5):

- Accumulators: 256 MB (bots + tops) + 16 MB × 1024 (`c_g_vecs`) ≈ **16 GB** worst case if c_g_vecs is held across the orbit. **Critical**: must process the integer reconstruction inside the chunk loop and discard each chunk's `c_g_vecs` before the next chunk. With chunking, peak drops to 4 GB.
- Per-chunk transients: ~640 MB (S1 residual + S4 chunk artefacts).

**Compared to existing Path A peak**: Path A at m=5 with chunk_B = 256 already peaks at ~8 GB (per audit + mod2_solver.g:654-660 comments). Adding Path Z batching with chunking inside the batched primitive should keep total peak at the same order of magnitude — IF we chunk inside `IsCoboundary2Z4VecBitsBatch` and don't materialise all integer `c_g_vecs` simultaneously.

**Mitigation**: the spec's `IsCoboundary2Z4VecBitsBatch` body MUST do the integer reconstruction inside the chunk loop, discarding `c_g_vecs` and `c_tables_mod2` at the end of each chunk via GAP's normal GC. The `s4_inputs` list within a chunk is bounded by chunk_size × n² integers = 1 GB per chunk worst case.

**Note**: with A-2 (bit-form round-trip removal) landed, S0 disappears entirely — there's no integer `c_g_vec` per target, so the dominant 4 GB term in the per-orbit peak collapses to ~256 MB (just the bots+tops accumulators). This is a strong reason to land A-2 BEFORE A-1, but A-1 is implementable without A-2.

### 3.2 Correctness boundaries

**State coupling preservation**: The recursion is per-target stateful (β_int from S1 → δβ in S2 → c_table_next in S3 → bool in S4). The batch refactor preserves this by:

1. Running S1 batched and extracting per-target witnesses from the matmul output.
2. Running S2 and S3 per-target on chunk-local lists (no cross-target mixing).
3. Filtering out S1-failures BEFORE building the S4 batch (`s4_todo` indices only contain S1-passes).
4. Running S4 batched on the S1-survivors.

Per-target outputs are reassembled into chunk_results by index. Cross-target contamination is mathematically impossible because S1's witness `sol_j = B_P[j] · Coeffs_full` is a function of `B[j]` alone (the j-th row of the batched input), not of the batch.

**Partial-batch convergence**: there is no "convergence" in this algorithm — each target gets a single yes/no in finite steps. The state coupling above is per-target stateful but per-batch independent. No risk of one target's S1-pass corrupting another's S4 input.

**Witness extraction correctness**: § 1.3 derives `sol = B_P · Coeffs_full`. This holds because the cached `Y_full` is in RREF (mod2_solver.g:126-133), which guarantees pivot columns of B contribute exactly the rank-many k-th coefficient rows. **Verification**: spike test on small group (e.g. D_8) checking
```
for c in some test cocycles:
    sol_per_call := IsCoboundary2Mod2VecWithWitness(C, c).witness
    sol_batch    := IsCoboundary2Mod2VecWithWitnessBatch(C, [c])[1].witness
    assert sol_per_call = sol_batch
```
Must be bit-for-bit equal (both over GF(2)).

**Failure mode #1 — sem.coeffs[0] when rank = 0**: handled by the rank=0 short-circuit (only the zero RHS is a coboundary; witness = zero vector).

**Failure mode #2 — sem.heads with mixed zero/non-zero**: handled by the `pivot_cols = Filtered(...)` step at cache time, identical to the existing batched residual path.

**Failure mode #3 — the integer-arithmetic side**: S2 and S3 are per-target compiled integer arithmetic. The only correctness concern is `IB_DeltaBetaMult`'s `(beta_i + beta[j] - beta[mult[i][j]]) mod modulus` allowing negative intermediates; GAP's `mod` is positive so this is handled. No batch-specific concern.

### 3.3 Test coverage

The existing tests `test_iterated_bockstein.g`, `test_iterated_bockstein_regression.g`, `test_pathz_combine_math.g`, and `test_pathz_gf2pack_math.g` cover the per-call IB and the GF(2) combine math.

Required new tests for the batched primitive:

1. **`test_iscoboundary2_mod2_vec_withwitness_batch.g`** — for each of {D_8, Q_8, C_4 × C_2, E_+(2)}: sample ~50 random length-n² inputs, compare per-call `IsCoboundary2Mod2VecWithWitness` against `IsCoboundary2Mod2VecWithWitnessBatch`. Both yes/no AND witness must match bit-for-bit.

2. **`test_iscoboundary2_z4_vec_bits_batch.g`** — for E_+(2) and E_+(3): sample test (c_bot, c_top) pairs by reducing actual basis-table inputs from the existing orbit caches. Compare per-call `IsCoboundary2Z4VecBits` against `IsCoboundary2Z4VecBitsBatch`. Anchor: at m=2 we know |ker(Tr)| = 2048 and the in-kernel generators are known; the batched dispatcher must produce identical kernel-membership flags across all 2048 candidates.

3. **`test_pathz_batch_dispatcher.g`** — end-to-end at m=3: run `run_e_plus_m_kernel_hap.g` with `MPARAM := 3` once with the per-call dispatcher and once with the batched dispatcher; verify `kernel.g` outputs are identical. Anchor: |ker(Tr)| = 262144 at m=3 with 17 in-kernel generators (per CLAUDE.md A-5b state).

4. **`test_pathz_batch_dispatcher_m5_smoke.g`** — smoke test at m=5 on a single orbit using `computed/transgression/5/orbit_*_cache.g` (already on disk). Compare batch vs per-call on a 100-target subset; the output booleans must agree.

The m=2 and m=3 anchors are decisive: any divergence in the batched output (even a single target) indicates a math bug. Failures at m=5 without m=3 failures point to scale-specific issues (memory pressure, chunking bug, overflow).

### 3.4 Compatibility with A-2 (bit-form round-trip removal)

A-2 refactors `IsCoboundary2Z4VecBits` to consume the bit slices end-to-end, eliminating the `IntVecFFE(c_bot) + 2 * IntVecFFE(c_top) + mod 4` reconstruction. The two specs interact at the S0 step of the batched primitive:

- **A-1 first, A-2 second**: A-1 lands with S0 doing the integer reconstruction per-target (in the chunk loop). After A-2, S0 collapses: S1 consumes `c_bots` directly (it's already mod 2 = the bit_0 slice), and S2-S3 can be re-derived to operate on bit slices.

- **A-2 first, A-1 second**: A-1's `IsCoboundary2Z4VecBitsBatch` skips S0 and feeds `c_bots` directly to a batched `IsCoboundary2Mod2VecWithWitnessBatch` (the bit-form witness extraction has the same shape).

**Sequencing constraint**: A-1 and A-2 can land in either order. A-2 simplifies A-1 (removes the 4 GB per-orbit integer-c_g_vecs term), so landing A-2 first is preferable. But A-1 is correct without A-2 — the spec above is self-contained.

**Joint test**: once both have landed, run the m=3 anchor test once more. The composed path must produce identical `kernel.g`.

### 3.5 Compatibility with PR #394's combine path

PR #394 added the sparsity-aware GF(2) column-XOR branch inside the Path Z dispatch (`run_e_plus_m_kernel_hap.g:620-645`):

```
if k_nz = 0          : slice_top := 0
elif k_nz <= k_thr   : slice_top := XOR-of-columns (table_gf2_top_T[j_supp])
else                 : slice_top := full matvec (table_gf2_top * u_gf2)
```

The branching is **inside the per-target slice computation**, BEFORE the batched dispatcher would collect targets. Each target produces its own `(slice_bot, slice_top)` pair regardless of which sparsity branch was taken. The batched dispatcher collects these pairs and passes them to `IsCoboundary2Z4VecBitsBatch`, which doesn't care how each slice was produced.

**No conflict**: the spec's accumulation loop calls the same slice-computation block per target, then accumulates the result. The sparsity branches remain orthogonal.

**One caveat**: if a future PR pushes the sparsity dispatch INSIDE the batched primitive (e.g. a batched column-XOR primitive that operates on multiple vec_targets at once), that would interact with this spec's batched-IB. For now, keep the sparsity branch per-target before accumulation; revisit in a follow-up if profiling shows the slice computation itself is a bottleneck.

## 4. Expected speedup

### 4.1 Current per-call wall (Path Z)

Path Z at m=5 (from audit) does, per target:
- One `IsCoboundary2Mod2VecWithWitness` call: ~50-200 ms (99.7% interpreter overhead per back-sub).
- One `IB_DeltaBetaMult`: ~10-20 ms (compiled).
- One `IB_DivBy2`: ~5-10 ms (compiled).
- One `IsCoboundary2Mod2WithLiftVec`: ~50-200 ms (same back-sub interpreter overhead).

Per target estimate: ~120-430 ms. Across an orbit of size 1024 with ~50% Path Z routing (audit estimate), ~256-512 Path Z targets per vec × ~270 ms ≈ 70-140 s per vec. The current observed per-vec wall is 50-100 s (CLAUDE.md a5b perf state); the lower observed number suggests the actual Path Z fraction may be lower or the cache state is favourable on the current vec.

### 4.2 Where per-call overhead lives

The 99.7% interpreter overhead in the back-sub loop (`for i in nonzero_heads do if b[i] ≠ 0 then AddRowVector(...) fi od`) is the dominant cost. Per the mod2_solver.g:534-538 audit, this comes from:
- ExecFor3 (loop overhead) ~ 30% per sample
- ExecAssList (list element access) ~ 20%
- EvalFunccall4args (AddRowVector dispatch) ~ 20%
- The compiled `AddRowVector` (GF(2) row XOR) itself ~ 0.3%

The batched form replaces N × `for i in nonzero_heads do ...` with ONE `PROD_GF2MAT_GF2MAT(B_P, Y_full)` call. The interpreter overhead drops from O(N × rank × constants) to O(1) (the matmul dispatch is one compiled C call regardless of N).

### 4.3 How much overhead survives in the batched form

In the batched form, per-call overhead survives only:

- Per-batch, per-orbit: ONE matmul dispatch for S1 witnesses (~10 ms at chunk = 256). ONE matmul for S1 residual (~10 ms). ONE batched lift-test call (~50 ms) that internally chunks.
- Per-target (inside the batched call body): S2 and S3 are compiled but still issue one IB_DeltaBetaMult call per target — that's ~N × 10 ms.
- Per-target accumulator work: building `slice_bot` and `slice_top` happens BEFORE accumulation; same cost as today.

For an orbit with N Path Z targets:
- Current: ~270 ms × N total wall (per-target dominant).
- Batched: ~70 ms fixed (matmul + lift batch) + ~10-20 ms × N (S2/S3 + accumulator) = roughly N × 15 ms + 70 ms.

**Speedup**: at N=256, current = 256 × 270 ms = 69 s. Batched = 70 ms + 256 × 15 ms = 3.9 s. Approximately **15× speedup** on the Path Z portion of the orbit. At N=512: 138 s → 7.8 s, **18×**.

These figures are upper bounds — they assume the interpreter overhead is the only thing being eliminated. Real factors that reduce the speedup:
- Cache thrash if the orbit is large enough to spill across multiple chunks (chunk_size = 256). Each chunk re-dispatches the matmul.
- Memory pressure: integer `c_g_vecs` reconstruction is ~5 ms per target compiled but adds up to ~1 s for N=200.
- GF(2) reduction (`x mod 2 * one`) inside the batched primitive: paid once per chunk, but at numRHS=256 still ~50 ms.

**Conservative estimate**: 5-10× speedup on the per-vec wall's Path Z component. If Path Z is 50% of the per-vec wall (audit's "non-trivial fraction"), the per-vec wall drops by 40-45%.

**Aggressive estimate** (with A-2 + A-3 stack composed): combine factors. Per-vec wall could drop by 60-70%.

### 4.4 Conservative speedup applied to a5b m=5 production

Currently (CLAUDE.md): per-vec wall ~270 s in some configurations; "stuck on per-vec wall" per issue #387. Step 4 cross-check runs over ~100 kernel vecs.

- Current Step 4: ~270 s × 100 = 27000 s ≈ 7.5 h.
- A-1-only: 5-10× on Path Z component (50% of wall) → per-vec wall drops to ~150-200 s → Step 4 ≈ 4-6 h. Saves ~1.5-3 h per A-5b m=5 production run.
- A-1 + A-2 + A-3 + (B-6 if applicable): combined ~3-5× per-vec wall reduction → Step 4 ≈ 1.5-2.5 h. Saves ~5-6 h per run.

Number of remaining A-5b m=5 production runs (per CLAUDE.md): the current run is in flight (PID 79240), Step 1 done, Step 4 in progress. At least one more rerun is anticipated after Step 4 lands. Total ROI of A-1: ~3-6 h saved across the next 1-2 runs.

## 5. Decision: defer (recommend implementing only after A-2 + A-3 land and we re-measure)

### 5.1 Recommendation

**Defer A-1**. Implement A-2 (PR-ready, audit-HIGH-CONFIDENCE), implement A-3 (audit-HIGH-CONFIDENCE), and the merged PR #394 sparsity-aware path FIRST. Re-measure per-vec wall on a fresh A-5b m=5 production rerun. Only then promote A-1 to implement-now status.

### 5.2 Rationale

**Refactor cost**:
- New batched primitive `IsCoboundary2Mod2VecWithWitnessBatch` in `mod2_solver.g`: ~80 LOC + cached `Coeffs_full` artefact build at sem-cache time + 4 new test files.
- New `IsCoboundary2Z4VecBitsBatch` in `iterated_bockstein.g`: ~120 LOC + integration with existing chunk pattern.
- Dispatcher changes in `run_e_plus_m_kernel_hap.g`: ~50 LOC + logging updates.
- Test coverage at m=2 and m=3 anchors: ~150 LOC across 3-4 test files.
- Memory peak verification: requires running m=5 on a checkpoint orbit with /usr/bin/time -l or GAP's `MemoryUsage` to confirm the spec's "chunk inside" mitigation holds.

Total: ~400 LOC + memory smoke test. One focused PR with thorough test coverage. **Effort: medium PR (1-2 days for a focused implementation agent).**

**Risk of breakage**:
- Math risk: LOW. The witness-extraction matmul derivation is straightforward (B_P · Coeffs_full); the m=2/m=3 anchors will catch any error before m=5 production.
- Memory risk: MEDIUM. The integer-c_g_vecs accumulation could OOM at m=5 if not chunked correctly inside the batched primitive. Mitigated by the spec's "chunk inside" pattern. A-2 landing first reduces this to LOW.
- Correctness regression risk on hot path: MEDIUM. The Path Z dispatcher is on the A-5b m=5 production hot path. A subtle bug discovered mid-run wastes hours of compute. Mitigated by m=2/m=3 anchor tests passing before merge.

**Why defer**:

1. **A-2 simplifies A-1 by a lot**. The integer reconstruction term (S0) is the dominant memory pressure in the batched primitive at m=5. A-2 removes it. Implementing A-1 first means we'd write the S0 reconstruction code, then immediately rewrite it for A-2. Wasted effort.

2. **The (A-2 + A-3 + PR #394) stack may already bring Step 4 to acceptable wall**. PR #394 already composes the GF(2) bit-pack with sparsity-aware column-XOR. A-2 removes the bit→int→bit round-trip. A-3 trims the M_y matmul to unconstrained columns. Together, these target the per-call cost, not the per-orbit dispatch overhead. They might reduce per-vec wall by 40-60% without A-1, and at that point A-1's marginal 15-30% improvement may not justify the refactor cost.

3. **The "ground truth on the restart" is missing**. Per the task description, the current per-vec wall is "extrapolated; ground truth on the restart". The current A-5b run (PID 79240) is the data point we need before quoting an A-1 speedup. If post-A-2+A-3+#394 per-vec wall is already < 60 s, A-1's ROI is marginal.

4. **The math is sound; the refactor is non-trivial but not exotic**. Deferral does NOT mean "this is wrong" or "this is too hard". It means: pay the implementation cost only when the measured per-vec wall after A-2/A-3 still demonstrates Path Z per-call overhead as the dominant bucket. This is the same dispatch logic that PR #394's composition followed.

5. **A future iteration can be focused on m=5+m=7 jointly**. If m=7 production (separate workstream) demonstrates a similar per-call IB bottleneck, the A-1 refactor's ROI doubles, and the joint test surface justifies a more aggressive batched IB redesign that also covers the recursive `modulus ≥ 8` case.

### 5.3 Re-evaluation criteria

Promote A-1 to implement-now if **any** of the following becomes true:

- Post-A-2+A-3+#394 per-vec wall remains > 100 s on the A-5b m=5 production rerun.
- Profile shows `IsCoboundary2Mod2VecWithWitness` interpreter overhead remains > 30% of per-vec wall.
- A third A-5b m=5 production rerun becomes necessary (e.g. for cross-validation at exp=4 with a different cocycle basis).
- m=7 production opens and demonstrates the same per-call IB bottleneck.

If none of these triggers within ~2 weeks of A-2/A-3 landing, mark A-1 as **defer indefinitely** — the orthogonal-perf composition is mathematically interesting but no longer rate-limiting.

### 5.4 Open follow-ups (not in this spec)

- **Recursive-case batching (modulus ≥ 8)**: separate spec when m=8/m=9 work begins. The mask-enumeration recursion has 2^r × per-recurse work; batching the recursion (over different masks AND different targets) is a richer design problem.
- **Batched integer-arithmetic path** (`IsCoboundary2SplitVecAware`): a parallel A-1 variant for the integer fallback path. Currently dead code at m=5 (audit § A-5). Defer until exp=8 work makes it hot.
- **Memory ceiling tuning**: if A-1 lands and the chunk_size = 256 turns out to be too large at m=5 with the integer c_g_vecs term, expose it as a configurable. Add to the existing `_IS_COBOUNDARY2_BATCH_CHUNK` knob.

### 5.5 Bottom line

The math is correct, the speedup is real (5-10× on the Path Z portion of the per-vec wall), and the refactor is implementable in a medium PR with thorough test coverage. But the cost-benefit at this moment is dominated by **uncertainty about post-A-2/A-3/#394 per-vec wall**. Defer until we have the ground-truth measurement from the current A-5b m=5 rerun, then re-evaluate against criteria § 5.3.

If a follow-up implementation agent picks this spec up: § 2 contains the full implementation sketch; § 3 contains the risk-mitigation checklist; § 3.3 contains the test anchors. Memory ceiling at m=5 with chunk_size = 256 is the highest-priority verification before merging.
