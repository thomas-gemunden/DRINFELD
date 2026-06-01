# Orthogonal perf-path siloing audit (codebase-wide)

**Date:** 2026-06-02
**Audit branch:** `audit-orthogonal-perf-395`
**Scope:** A-5b m=5 solver hot path + adjacent infrastructure
**Trigger:** PR #394 unmasked the meta-pattern — two PRs (#392 "Approach A: sparsity-aware integer dispatch" and #393 "Approach B: GF(2) bit-pack matvec") each shipped a perf improvement guarded by mutually-exclusive `if`-branches. The two are orthogonal (A shrinks operation count, B shrinks per-op cost); a third PR (#394) had to land the composition. This audit asks: where else in the codebase is the same kind of orthogonal-perf siloing hiding?

## TL;DR

| # | Instance | Tier | Confidence | Composition gap |
|---|---|---|---|---|
| 1 | Path A is batched, Path Z is per-call (driver hot path) | A | HIGH | Batched back-sub + sparsity matvec for Z |
| 2 | `IsCoboundary2Z4VecBits` reconstructs ints from bits then re-extracts bit_0 inside IB | A | HIGH | Pass bit_0 through; skip a 4M int round-trip per call |
| 3 | Column-disposition Batch matmul ignores already-constrained `col_has_constraint` | A | HIGH | Slice M_y to unconstrained columns before the matmul |
| 4 | `IB_StrictF2Witness` reuses cached lift-sem but back-subs one-by-one | A | NEEDS-REVIEW | Same `IsCoboundary2Mod2WithLiftVecBatch` artefacts could batch the lift-test for Path Z |
| 5 | `IsCoboundary2SplitVecAware`'s sparse column accumulator uses `List(table, row -> row[j])` to extract integer columns instead of caching column-major view | A | HIGH | Pre-cache integer `table_T` (rows-as-columns) like the GF(2) variant did in #394 |
| 6 | `BuildReducedTransgressionMatrixFast` Step 1 does per-column back-sub for k=165 columns against the cached lift-sem | B | HIGH | Batch the back-sub over all k columns at once |
| 7 | `_BuildSiblingTableViaTransport` does compiled matmul then closure-mod over rows | B | HIGH | Compiled list-mod-int (#385/#387 pattern) |
| 8 | `BuildPCWithBockstein`'s Bockstein-image row lift uses closure over n² entries | C | HIGH | Compiled `(img_rows[k_b] * exp/2) ` if GF(2) image entries are first lifted to ints with IntVecFFE |

The report below documents each instance with file:line refs, current shape, why the paths are orthogonal, and a composition sketch. **No code changes** were made by this audit; Tier-A fixes are proposed as follow-up issues. See § Methodology for how the audit was performed.

---

## Tier A: in the Step 4 / Path Z / Path A m=5 hot path

### A-1 — Path A is batched; Path Z is per-call. (HIGH-CONFIDENCE)

**Location:** `extraspecial_orbifolds/scripts/run_e_plus_m_kernel_hap.g:587-695` (`PerVecTransgressionShared`)

**Current dispatch shape:**

```gap
for target_idx in orb_info.orbit do
    vec_target := H3VecAtTarget(...);
    if vec_target[exp_index] <> 0 then
        # Path Z: PER-CALL through IsCoboundary2Z4VecBits / IsCoboundary2SplitVecAware
        results[target_idx] := IsCoboundary2Z4VecBits(...);   # or IsCoboundary2SplitVecAware(...)
    else
        # Path A: ACCUMULATE into batch_inputs
        u_gf2 := (vec_target mod 2) * one_gf2;
        c_prime_bits := basis_cache.table_gf2 * u_gf2;
        Add(batch_inputs, c_prime_bits);
        Add(batch_targets, target_idx);
    fi;
od;
if not IsEmpty(batch_inputs) then
    # ONE batched call for all Path A targets in this orbit
    batch_results := IsCoboundary2Mod2WithLiftVecBatch(basis_cache.C, batch_inputs);
    ...
fi;
```

**Why the paths are orthogonal:**

Path A's batching wins come from `_RowSpanResidualBatch` — a single compiled GF(2) `PROD_GF2MAT_GF2MAT` for `B_P * Y_full` against the cached lift-sem (see `solver/mod2_solver.g:596-618`). The win is "amortise interpreter overhead across many RHSes against the same factorisation".

Path Z's per-call wins from #392/#393 come from a different axis: input sparsity + packed-bit matvec. Each Path Z call ultimately reaches the F_2 base case in `IB_RecCob`, which does a single `IsCoboundary2Mod2VecWithWitness` (kernel-sem back-sub) AND a single `IsCoboundary2Mod2WithLiftVec` (lift-sem back-sub) — both unbatched, both against the SAME cached sem records that Path A's batched path uses.

If multiple targets in the same orbit hit Path Z (which they do at m=5 — vec_target[exp_index] depends on vec_target via the BRW endomorphism, and a non-trivial fraction of targets in a typical Step-4 vec have `vec_target[exp_index] != 0`), each pays a separate back-sub.

**Composition sketch:**

WRONG (current):
```gap
for target_idx in orbit do
    if Z-path then results[target_idx] := <per-call>; else <accumulate batch>; fi;
od;
<one batched A call>
```

RIGHT:
```gap
batch_Z_inputs := []; batch_Z_targets := []; batch_Z_lift_inputs := [];
batch_A_inputs := []; batch_A_targets := [];
for target_idx in orbit do
    if Z-path then
        <compute slice_bot, slice_top>
        Add(batch_Z_inputs, slice_bot);             # kernel-sem test
        Add(batch_Z_lift_inputs, residual_for_lift); # lift-sem test
        Add(batch_Z_targets, target_idx);
    else
        <accumulate A as today>
    fi;
od;
batch_Z_strict := IsCoboundary2Mod2VecBatch(C, batch_Z_inputs);   # kernel
# For the targets where strict failed, batched lift test
batch_Z_lift := IsCoboundary2Mod2WithLiftVecBatch(C, batch_Z_lift_inputs);
<combine results>
<one batched A call as today>
```

**Caveat (NEEDS-REVIEW marker):** the m=5 base-case Path Z path is `modulus = 4` and the F_2 base case sits inside `IB_RecCob`, which mutates state between the two back-sub calls (`beta_int` from the strict test feeds `IB_DeltaBetaMult` → `c_table_next` → lift test). Batching across targets would require restructuring `IB_RecCob` so that the strict test, the delta-beta computation, the divide-by-2, and the lift test each operate over a batch of c_tables. It's algorithmically clean (each step is a per-target compiled op) but requires non-trivial refactoring. Flag for human review before quoting a speedup.

**Impact:** A-5b m=5 Step 4 dominant cost is Path Z per-vec wall (#387). If even 50% of the Path Z calls in an orbit could be batched, the back-sub interpreter overhead drops to a single matmul per orbit, mirroring the Path A win. Per-vec wall could drop by O(median Path Z orbit size).

**Proposed follow-up issue:** "Compose Path Z bit-pack with Path A batching: stack Path Z targets per orbit and batch the kernel + lift back-sub against the cached sem."

---

### A-2 — `IsCoboundary2Z4VecBits` round-trips bits → ints → bits. (HIGH-CONFIDENCE)

**Location:** `extraspecial_orbifolds/scripts/solver/iterated_bockstein.g:578-588` + `:521-547` (`IsCoboundary2Z2kVec`) + `:365-373` (`IB_StrictF2Witness`)

**Current shape:**

```gap
IsCoboundary2Z4VecBits := function(C, c_bot, c_top, n)
    local c_bot_int, c_top_int, c_g_vec;
    c_bot_int := IntVecFFE(c_bot);          # GF(2) length-n^2 -> int list (~4M entries at m=5)
    c_top_int := IntVecFFE(c_top);          # GF(2) length-n^2 -> int list (~4M entries at m=5)
    c_g_vec := 2 * c_top_int + c_bot_int;   # int list (~4M entries)
    return IsCoboundary2Z2kVec(C, c_g_vec, 2);   # which calls...
end;

IsCoboundary2Z2kVec := function(C, c_g_vec, k)
    ...
    c_table := c_g_vec mod modulus;   # int list, modulus=4
    ...
    return IB_RecCob(C, c_table, modulus, ...);
end;

IB_RecCob := function(...)
    if modulus = 2 then return IB_StrictF2Witness(...); fi;   # not taken at m=5 first call
    beta_int := IB_StrictF2Witness(C, c_table, n);   # <- internally does `c_table mod 2`
    ...
end;

IB_StrictF2Witness := function(C, c_table, n)
    return IsCoboundary2Mod2VecWithWitness(C, c_table mod 2);   # int -> GF(2) again
end;
```

So the bit-pack route does, per call:
1. Caller built `c_bot` and `c_top` as packed GF(2) — `c_bot` *is* the F_2 reduction of the c_table.
2. `IsCoboundary2Z4VecBits` calls `IntVecFFE` to convert both to integer lists (~4M ints).
3. Reconstructs `c_g_vec = 2 * c_top_int + c_bot_int`.
4. `IsCoboundary2Z2kVec` does `c_table := c_g_vec mod 4` (a 4M list-mod-int).
5. `IB_StrictF2Witness` does `c_table mod 2` (another 4M list-mod-int) and feeds it to `IsCoboundary2Mod2VecWithWitness`, which converts THAT integer list to GF(2) via `(x mod 2) * one_gf2`.

So `c_bot` (the F_2 reduction we ALREADY HAVE) is reconstructed by going GF(2) → int → mod-4 → mod-2 → GF(2). The whole round-trip is unnecessary at m=5.

**Why the paths are orthogonal:**

- `IB_RecCob` was designed for the integer Z/2^k table API (`IsCoboundary2Z2kVec`).
- `IsCoboundary2Z4VecBits` was added in PR #393 as a bit-pack-aware caller entry point, but stops at the dispatch boundary (it just feeds the integer back into the old API).
- The IB internals are already F_2-typed at the strict-test step. A dedicated `IB_RecCob_Z4_Bits` variant could:
  - Take `c_bot`, `c_top` (packed GF(2)) directly.
  - At the strict test: `IsCoboundary2Mod2VecWithWitness(C, c_bot)` (skip the int → GF(2) conversion).
  - Compute `delta_beta` as an integer table from the witness β (still needed because the divide-by-2 step is over Z), then `c_table_next := IB_DivBy2(reconstruct_from_bits, delta_beta, 2)`.
  - At the lift test: `IsCoboundary2Mod2WithLiftVec(C, c_table_next_bot)` — where `c_table_next_bot` is the bottom bit of c_table_next.

The bit-pack route reduces per-op cost; the integer-IB internals retain their integer arithmetic for `IB_DivBy2` and `IB_DeltaBetaMult`. The composition sketch above keeps the F_2 representation at the F_2 boundaries (strict test, lift test) and only materialises ints where Z-arithmetic is genuinely needed.

**Composition sketch:**

WRONG (current — bit-pack route boundary effectively no-op for IB internals):
```gap
IsCoboundary2Z4VecBits := function(C, c_bot, c_top, n)
    c_bot_int := IntVecFFE(c_bot);
    c_top_int := IntVecFFE(c_top);
    c_g_vec := 2 * c_top_int + c_bot_int;
    return IsCoboundary2Z2kVec(C, c_g_vec, 2);
end;
```

RIGHT (refactored IB to consume bits at F_2 boundaries):
```gap
IsCoboundary2Z4VecBits := function(C, c_bot, c_top, n)
    # IB_StrictF2Witness consumes c_bot directly.
    beta_int := IsCoboundary2Mod2VecWithWitness(C, c_bot);
    if not beta_int.yes then return false; fi;
    beta_int := List(beta_int.witness, ...);   # GF(2) -> {0,1} ints, length n only (not n^2)
    # delta_beta still ints (needed for divide-by-2 below)
    delta_beta := IB_DeltaBetaMult(beta_int, n, mult, 4);
    # c_table_next = (2 * c_top + c_bot - delta_beta) / 2 (mod 2)
    #              = (c_top - (delta_beta - c_bot) / 2) mod 2 if c_bot - delta_beta is 0 mod 2 ...
    # ... a careful re-derivation, but the result is still a length-n^2 F_2 vector,
    # which feeds IsCoboundary2Mod2WithLiftVec directly (no int round-trip).
    return IsCoboundary2Mod2WithLiftVec(C, c_table_next_bot);
end;
```

This is exactly the "Design 1" follow-up that PR #393's comment at line 569-574 of `iterated_bockstein.g` already flags:

> Future work (Design 1, post-PR): refactor IB internals to consume the bit slices directly, avoiding even the reconstruction.

The audit confirms: at m=5 hot scale, the unwanted round-trip is 4 × 4M element conversions per call. Even at 30 µs per million-entry op (compiled), that's ~120 µs / call wasted; at thousands of Path Z calls per Step-4 vec, single-digit seconds per vec on a 270-s/vec wall.

**Impact:** Tier-A — directly reduces per-call wall in the m=5 Path Z hot path. Effort: moderate (~1 PR, careful re-derivation of `c_table_next` in bit form).

**Proposed follow-up issue:** "Design 1: refactor IB_RecCob to consume bit slices end-to-end at modulus=4."

---

### A-3 — Column-disposition Batch matmul ignores `col_has_constraint`. (HIGH-CONFIDENCE)

**Location:** `extraspecial_orbifolds/scripts/solver/transgression_matrix_reduced.g:825-857` (`UpdateColumnDispositionFromMBarGF2_Batch`) + the dispatcher at `:1175-1185`.

**Current shape:**

```gap
# Dispatcher (line 1175):
if Length(reduced_matrices[j].M_bar_gf2) > 0
   and Length(Filtered([1..k], i -> not col_has_constraint[i])) > k / 2 then
    UpdateColumnDispositionFromMBarGF2_Batch(M_bar_gf2, M_y_j, col_has_constraint);
else
    UpdateColumnDispositionFromMBarGF2(M_bar_gf2, M_y_j, col_has_constraint);
fi;

# Inside _Batch (line 825):
UpdateColumnDispositionFromMBarGF2_Batch := function(M_bar_gf2, M_y, col_has_constraint)
    ...
    # Build M_y_gf2 over ALL k columns
    M_y_gf2 := [];
    for j in [1..k_dim] do
        row := List([1..k_dim], i -> If_(M_y[j][i] mod 2 = 0, zero_gf2, one_gf2));
        Add(M_y_gf2, row);
    od;
    ...
    prod_full := M_bar_gf2 * M_y_gf2;    # <-- multiplies all k columns
    # Skip already-constrained columns ONLY in inspection, not in matmul:
    for i in [1..k_dim] do
        if col_has_constraint[i] then continue; fi;
        if not ForAll([1..r_local], j -> IsZero(prod_full[j][i])) then
            col_has_constraint[i] := true;
        fi;
    od;
end;
```

**Why the paths are orthogonal:**

- **Batched matmul** (per-orbit, per-target) — `M_bar_gf2 * M_y_gf2` is a single compiled GF(2) `PROD_GF2MAT_GF2MAT`. Wins from greasing / amortised dispatch over numRHS = k.
- **Sparsity** (col_has_constraint) — once a column is marked constrained, it never flips back. As orbits accumulate, more columns become constrained, so per-call useful work shrinks.

The current `_Batch` engages the first axis but not the second. The current `_per_column` engages the second axis (skips the `M_bar_gf2 * v` matvec for already-constrained columns) but not the first (k separate matvecs instead of one matmul).

The dispatch chooses one or the other based on whether > k/2 columns are unconstrained. Either way, useful columns are O(unconstrained) but work done is O(k) (Batch) or O(unconstrained × k_dim^2) (per_column).

**Composition sketch:**

WRONG (current):
```gap
prod_full := M_bar_gf2 * M_y_gf2;   # all k columns of M_y_gf2
for i in [1..k_dim] do
    if col_has_constraint[i] then continue; fi;
    ...
od;
```

RIGHT:
```gap
unconstrained := Filtered([1..k_dim], i -> not col_has_constraint[i]);
# Slice M_y_gf2 to just the unconstrained columns BEFORE the matmul.
M_y_gf2_unconstrained := List(M_y_gf2, row -> row{unconstrained});
ConvertToMatrixRep(M_y_gf2_unconstrained, GF(2));
# Compiled matmul, but now numRHS = unconstrained instead of k.
prod_sliced := M_bar_gf2 * M_y_gf2_unconstrained;
for idx_u in [1..Length(unconstrained)] do
    if not ForAll([1..r_local], j -> IsZero(prod_sliced[j][idx_u])) then
        col_has_constraint[unconstrained[idx_u]] := true;
    fi;
od;
```

This is strictly faster than both current paths once `Length(unconstrained) < k_dim`. The "switch to per-column when few unconstrained" dispatcher becomes unnecessary — the composed batched-sparse path dominates.

**Caveat:** at m=5, k=165 and r=4M. At early orbits all k are unconstrained, so the slice is a no-op and Batch's current cost is paid in full. The saving accrues at later orbits in the per-orbit sweep, where most columns are already constrained. For an orbit at, say, 50% constrained, the matmul size halves. For 90% constrained, it's 10× faster. With the typical A-5b m=5 trajectory (most columns settled by orbit 2 or 3), this composes into a real net speedup on orbits 3-N.

**Why it's still NEEDS-REVIEW worthy:** the per-column variant has memory advantage too (~500 KB peak vs ~80 MB for Batch). The composition above has memory ~ 80 MB × (unconstrained / k) — same factor of slack at later orbits. Should verify peak doesn't matter at any orbit before merging.

**Impact:** Tier-A (in the perf-4' path that A-5b m=5 uses). Effort: small (~30-line PR).

**Proposed follow-up issue:** "Slice M_y to unconstrained columns before the batched GF(2) matmul in UpdateColumnDispositionFromMBarGF2_Batch."

---

### A-4 — `IB_StrictF2Witness` and `IB_TableMod2WithLift` could batch the kernel/lift sem back-subs. (NEEDS-REVIEW)

**Location:** `extraspecial_orbifolds/scripts/solver/iterated_bockstein.g:365-394`.

**Current shape:**

```gap
IB_StrictF2Witness := function(C, c_table, n)
    return IsCoboundary2Mod2VecWithWitness(C, c_table mod 2);   # per-call back-sub
end;

IB_TableMod2WithLift := function(C, c_table, n)
    return IsCoboundary2Mod2WithLiftVec(C, c_table mod 2);   # per-call back-sub
end;
```

**Why the paths are orthogonal — but the composition is contingent:**

- The sem records (`_GetCachedSemForAT`, `_GetLiftSemForC`) already include batched-back-sub artefacts (`batched.Y_full`, `batched.pivot_cols`).
- `IsCoboundary2Mod2WithLiftVecBatch` exists and is used by Path A.
- Path Z calls these per-target. The composition requires batching the c_tables across multiple Path Z calls, which depends on resolving A-1 (refactoring the IB_RecCob recursion to consume a batch of c_tables).

This is a sub-instance of A-1: if A-1 lands, A-4 falls out automatically. Recording it as a separate observation because:
- The cached batched artefacts already exist (no infrastructure work needed inside the sem cache).
- A reader looking at `IB_StrictF2Witness` might miss that `IsCoboundary2Mod2VecBatch` is the right primitive.

**Impact:** Tier-A, but blocked behind A-1's refactor. No separate fix proposed; tracked as a sub-task of A-1.

---

### A-5 — `IsCoboundary2SplitVecAware`'s sparse column accumulator extracts integer columns by closure. (HIGH-CONFIDENCE)

**Location:** `extraspecial_orbifolds/scripts/solver/iscoboundary2_split.g:185-228` (`IsCoboundary2SplitVecAware`).

**Current shape:**

```gap
IsCoboundary2SplitVecAware := function(C, basis_cache, vec_target, setup)
    ...
    if k_nz = 1 then
        j_nz := supp[1];
        col_j := List(basis_cache.table, row -> row[j_nz]);   # <-- closure over n^2 entries
        c_g_vec := col_j * vec_target[j_nz];
        return IsCoboundary2SplitVec(C, c_g_vec, vec_target, setup);
    elif k_nz <= k_threshold then
        n2 := Length(basis_cache.table);
        c_g_vec := ListWithIdenticalEntries(n2, 0);
        for j in supp do
            col_j := List(basis_cache.table, row -> row[j]);   # <-- closure over n^2 entries, per support index
            AddRowVector(c_g_vec, col_j, vec_target[j]);
        od;
        return IsCoboundary2SplitVec(C, c_g_vec, vec_target, setup);
    else
        ...
    fi;
end;
```

The column extraction `List(basis_cache.table, row -> row[j])` is an n²-element closure dispatch per support index — exactly the **P3 anti-pattern** from CLAUDE.md (line 393: "Closure `List(L, x -> f(x))` in arithmetic hot path"). At m=5 with n²=4M and average k_nz ~14, that's ~14 × 4M = 56M closure dispatches per Path Z call (when this entry point is hit, which is when bit-pack is NOT wired — primarily for exp != 4 paths and for the unit-support case at exp=4).

**Why the paths are orthogonal:**

- The GF(2) bit-pack route (PR #393 + #394) stores a column-major view `basis_cache.table_gf2_top_T` so column extraction is just `table_gf2_top_T[j]` — O(1) lookup, packed bits.
- The INTEGER route (`IsCoboundary2SplitVecAware`) has no column-major view of `basis_cache.table` — every column extraction does `List(table, row -> row[j])`.

The two cache fields `table_gf2_top_T` (column-major GF(2)) and `table` (row-major integer) were both updated in PRs #391-#394 but the column-major view was only built for GF(2). The integer dispatcher (called when bit-pack is NOT wired, e.g. exp != 4 or future use cases at exp=8) silently re-pays O(n²) per column extraction.

**Composition sketch:**

WRONG (current):
```gap
col_j := List(basis_cache.table, row -> row[j_nz]);   # n^2 closure dispatches
```

RIGHT:
```gap
# In BuildPerClassCocycleBasis, snf_wrapper.g:735-736:
table_gf2_top_T := TransposedMat(table_gf2);
ConvertToMatrixRep(table_gf2_top_T, GF(2));
# Add INTEGER column-major view too:
table_T := TransposedMatMutable(table);    # n^2 x k -> k x n^2, in compiled C
ConvertToMatrixRep(table_T);
result := rec(..., table := table, table_T := table_T, ...);

# In IsCoboundary2SplitVecAware:
col_j := basis_cache.table_T[j_nz];   # single ELM_LIST, compiled
```

**Caveat:** `TransposedMat` on an n²×k integer matrix at m=5 is ~4M × 165 = 660M entries. Memory-wise this doubles the per-orbit cache from ~1 GB to ~2 GB. Need to verify the m=5 heap budget can absorb this OR confirm the integer path is rare enough at m=5 that the overhead can be paid in non-hot paths only.

At m=5 the integer route is taken only when:
1. exp != 4 (not the case at m=5 — exp = 4 always).
2. The bit-pack `col_bot_exp` is `fail` (rare).
3. As the unit-support fast path inside `IsCoboundary2SplitVecAware` — but at m=5 production we're routed to `IsCoboundary2Z4VecBits` instead (the GF(2) bit-pack path), so `IsCoboundary2SplitVecAware` is currently dead code at m=5.

Verdict: this matters for future m=8/m=9 work (exp=8) and as a defensive optimization. Mark Tier-A for "the broader sweep family" but note this is NOT currently exercised on the A-5b m=5 hot path. Demoted to Tier-B by impact, but the analysis is sharp.

**Re-categorisation:** Tier-B (defensive, not exercised on m=5 hot path).

**Proposed follow-up issue:** "Add integer column-major `basis_cache.table_T` to mirror `table_gf2_top_T`, for IsCoboundary2SplitVecAware's exp != 4 path."

---

## Tier B: driver setup / BRW action

### B-6 — `BuildReducedTransgressionMatrixFast` Step 1 does per-column back-sub against the cached lift-sem. (HIGH-CONFIDENCE)

**Location:** `extraspecial_orbifolds/scripts/solver/transgression_matrix_reduced.g:485-573` (`BuildReducedTransgressionMatrixFast`).

**Current shape:**

```gap
BuildReducedTransgressionMatrixFast := function(setup, g_rep, C)
    ...
    lift_entry := _GetLiftSemForC(C);
    lift_sem := lift_entry.sem;
    lift_batched := lift_entry.batched;
    ...
    cols_gf2 := List([1..k], i -> fail);
    for i in order_2_gens do
        col_i_gf2 := List(table_gf2, row -> row[i]);     # closure n^2 extraction (see A-5 / P3)
        ConvertToVectorRep(col_i_gf2, GF(2));

        # PER-COLUMN back-sub against lift_sem — same loop as IsCoboundary2Mod2WithLiftVec
        if rank = 0 then
            residual := col_i_gf2;
        else
            b := ShallowCopy(col_i_gf2);
            nonzero_heads := lift_entry.nonzero_heads;
            sol_dim := Length(lift_sem.coeffs[1]);
            sol := ListWithIdenticalEntries(sol_dim, zero_gf2);
            ConvertToVectorRep(sol, GF(2));
            for l in nonzero_heads do
                vno := lift_sem.heads[l];
                x := b[l];
                if x <> zero_gf2 then
                    AddRowVector(b, lift_sem.vectors[vno], -x);
                    AddRowVector(sol, lift_sem.coeffs[vno], x);
                fi;
            od;
            residual := b;
        fi;
        col_i_gf2 := residual{non_pivot_cols};
        ...
        cols_gf2[i] := col_i_gf2;
    od;
```

The inner `for l in nonzero_heads do ... AddRowVector ...` is the per-call back-sub identical to `IsCoboundary2Mod2WithLiftVec` (mod2_solver.g:498-526). The wrap `for i in order_2_gens` calls this k times against the SAME `lift_sem`.

**Why the paths are orthogonal:**

- The cached lift-sem record (`_GetLiftSemForC(C)`) already includes batched artefacts (`batched.Y_full`, `batched.pivot_cols`) for exactly this scenario.
- `_RowSpanResidualBatch(lift_batched, B)` computes the residual in one compiled GF(2) matmul for a batch of RHSes.
- `BuildReducedTransgressionMatrixFast` ignores these and uses the per-call interpreter loop.

So the perf-4' Step 1 cost at m=5 is k = 165 separate back-subs against an r=4M sem record. Each back-sub is ~99.7% interpreter overhead per the live A-5b profile (mod2_solver.g:535-538).

**Composition sketch:**

WRONG (current):
```gap
for i in order_2_gens do
    col_i_gf2 := <extract column i>;
    b := ShallowCopy(col_i_gf2);
    for l in nonzero_heads do
        ...
    od;
    residual := b;
    cols_gf2[i] := residual{non_pivot_cols};
od;
```

RIGHT:
```gap
# Build full column matrix B of shape k x n^2 (each row is one column of table_gf2 mod lift_sem).
B := [];
for i in order_2_gens do
    col_i_gf2 := List(table_gf2, row -> row[i]);   # could still benefit from A-5 column-major fix
    ConvertToVectorRep(col_i_gf2, GF(2));
    Add(B, col_i_gf2);
od;
ConvertToMatrixRep(B, GF(2));
# One batched residual computation:
residual_batch := _RowSpanResidualBatch(lift_batched, B);
# Slice each row to non_pivot_cols:
for idx in [1..Length(order_2_gens)] do
    i := order_2_gens[idx];
    cols_gf2[i] := residual_batch[idx]{non_pivot_cols};
    ConvertToVectorRep(cols_gf2[i], GF(2));
od;
```

**Impact:** At m=5 perf-4' Step 1 with k=165 order-2 columns, this saves k × per-call overhead. Tier-B because perf-4' Step 1 is a one-time cost per orbit, not in the Step-4 cross-check loop. Per-orbit, perf-4' Step 1 wall is currently several minutes; batching could drop it to seconds.

**Confidence:** HIGH for the math (identical to Path A's already-deployed batched path). LOW for the wall-time impact since perf-4' Step 1 hasn't been a hot spot in current A-5b production runs.

**Proposed follow-up issue:** "Batch BuildReducedTransgressionMatrixFast's k order-2 column back-subs against the cached lift-sem."

---

### B-7 — `_BuildSiblingTableViaTransport` uses `List(table_sib, row -> List(row, x -> x mod exp))`. (HIGH-CONFIDENCE)

**Location:** `extraspecial_orbifolds/scripts/solver/snf_wrapper.g:981`.

**Current shape:**

```gap
# table_sib is now the row-permuted version of rep_cache.table.
ConvertToMatrixRep(table_sib);
table_sib := table_sib * M_path;
# Reduce mod exp (the matmul produces unbounded integers).
table_sib := List(table_sib, row -> List(row, x -> x mod exp));
ConvertToMatrixRep(table_sib);
```

The double-closure `List(table_sib, row -> List(row, x -> x mod exp))` is exactly the **P6 anti-pattern** from CLAUDE.md (line 414: "Per-row mod via closure inside a for j loop") — at m=5 with n²=4M and k=165, that's 4M × 165 = 660M closure dispatches per sibling.

**Why this is an orthogonal-path observation (not just a P6 hit):**

The OUTER op (the matmul `table_sib * M_path`) was upgraded in PR #371/#372 to compiled `PROD_MAT_MAT_INT`. The INNER mod-pass is still interpreted closure dispatch. The two perf wins are siloed — the compiled matmul is fast, but its O(n²×k) result still pays interpreter overhead per cell on the mod-reduction.

The composition is trivial (CLAUDE.md P6 fix):

WRONG:
```gap
table_sib := List(table_sib, row -> List(row, x -> x mod exp));
```

RIGHT:
```gap
for r in [1..Length(table_sib)] do
    table_sib[r] := table_sib[r] mod exp;   # compiled list-mod-int per row
od;
```

Or with a vectorised whole-matrix mod (if GAP supports it for IsMatrixRep — needs verification):
```gap
table_sib := table_sib mod exp;   # if supported by compiled MOD_INT on matrices
```

**Why not Tier-A:** `_BuildSiblingTableViaTransport` is called only when the per-class sibling-transport path is enabled. The A-5b m=5 production driver uses rep-only caches (per `run_e_plus_m_kernel_hap.g:438-446`), so this code path is not exercised at m=5 today. But if the user enables `BuildPerClassCocycleBasisForOrbit` for downstream consumers, this is the next bottleneck.

**Impact:** Tier-B. Effort: trivial (1-line CLAUDE.md P6 fix). 

**Proposed follow-up issue:** Optional — add to the next "audit-tier3 follow-up" P6 sweep.

---

## Tier C: outside the production hot path

### C-8 — `BuildPCWithBockstein` lifts Bockstein rows via per-cell loop. (HIGH-CONFIDENCE)

**Location:** `extraspecial_orbifolds/scripts/solver/transgression_matrix_reduced.g:242-251`.

**Current shape:**

```gap
for k_b in [1..r_bockstein] do
    row_int := List([1..n*n], i -> 0);    # closure (P5 anti-pattern)
    for x in [1..n*n] do
        if not IsZero(img_rows[k_b][x]) then
            row_int[x] := exp_int / 2;
        fi;
    od;
    Add(M_aug_T_full, row_int);
od;
```

This is in `BuildPCWithBockstein`, which is in the *slow* `BuildReducedTransgressionMatrix_Slow` path (line 639-718), not the fast path actually used by m=5 production.

**Orthogonal-paths take:** `BuildPCWithBockstein` predates the GF(2) cache structure introduced by PRs #391-#394. The `img_rows` is already a list of packed GF(2) vectors from `BocksteinH1ToH2(C)`. The lift `(0/1) * (exp/2)` is just `IntVecFFE(img_rows[k_b]) * (exp/2)` — one compiled IntVecFFE + one compiled list-scalar mul. Bypassed by the per-cell loop.

**Why Tier-C:** The slow path is only used as a fallback / for legacy callers. At m ≤ 3 it's not the hot loop; at m=5 it's not called. Recording for completeness; not urgent.

**Proposed follow-up issue:** Lower priority — optional cleanup at next audit pass.

---

## Negative findings (places examined; siloing not found)

The following sites were examined for the same orthogonal-path pattern and concluded NOT to exhibit it.

### N-1 — `BuildPerClassCocycleBasis`'s perf-5 / perf-5b / perf-5c stack is correctly composed.

`solver/snf_wrapper.g:499-745` (`BuildPerClassCocycleBasis`) implements:
- perf-5 (#281): row-batched compiled matmul `contrib_row * basis_T`.
- perf-5b (#281): HAP-level prefix-Syzygy sharing (`_Syzygy3FromParts`, `S_gRep_a`/`S_a_gRep` hoist).
- perf-5c (#282): O(|w1|+|w2|) `_AddFreeWordsFast` via positional pool.

All three are wired in sequence (`_Syzygy3FromParts` calls `_AddFreeWordsFast`, then the row-batched assembly uses the resulting Syzygies). No `if perf_A then ... else perf_B` siloing — the perf wins compose multiplicatively.

### N-2 — `IsCoboundary2Mod2WithLiftVecBatch` correctly composes kernel and lift tests on one chunk_B.

`solver/mod2_solver.g:737-806`. Both stages of the lift test (kernel-only Stage 1, lift Stage 2) share the same GF(2)-converted `chunk_B`, with explicit comment at line 736 ("the integer→GF(2) reduction ... is the bulk of the per-call cost at small/moderate centraliser sizes. We do it ONCE per chunk"). This is the OPPOSITE pattern from siloing — it's an explicit composition.

### N-3 — `IsCoboundary2Mod2Vec` and `IsCoboundary2Mod2WithLiftVec` correctly share `_BoundaryMatrixGF2_cache`.

`solver/mod2_solver.g:92-100`. Both call `BoundaryMatrixGF2(H)` which is cached by `IsIdenticalObj(H)`. The lift cache (`_GetLiftSemForC`) explicitly uses `B := TransposedMat(BoundaryMatrixGF2(C))` (line 478), sharing the cached `BoundaryMatrixGF2` build cost with the kernel cache.

### N-4 — `ApplyH3Endomorphism` and `ComposeH3Endomorphism` correctly compose compiled matvec with closure-free mod.

`brw_h3_action.g:250-296`. Both ops use compiled `M * v` / `M1 * M2` then `result[j] mod torsion[j]` (compiled list-mod-int per row). The per-row mod loop is intentional (`torsion[j]` differs per row); cannot batch with a single `mod`. No siloing.

### N-5 — The Path Z `IsCoboundary2SplitVecAware` dense-fallback path correctly drops through to `IsCoboundary2SplitVec`.

`iscoboundary2_split.g:223-227`. The branch `k_nz > k_threshold -> IsCoboundary2SplitVec(...)` is a dispatch on input sparsity, not a siloing of two perf optimizations. The dense path is the OLD path; the sparse path is the addition. This is intentional dispatch, not orthogonal-path siloing.

### N-6 — `BoundaryMatrixGF2` sparse-row build is correctly composed with the `_BoundaryMatrixGF2_cache`.

`solver/mod2_solver.g:55-100`. The sparse-row build (per-row `ListWithIdenticalEntries` + `ConvertToVectorRep` + 3 bit flips) is a memory fix for issue #335 (OOM at m=5). The cache keys by `IsIdenticalObj(entry.H, H)`; calls with the same H always hit the cache, so the sparse-row build cost is paid once per centraliser. No siloing.

### N-7 — `_HSyzygy3FromParts` hoist + share are correctly composed.

`solver/snf_wrapper.g:147-497`. The HOIST (out of b-loop) and SHARE (within (a,b)) optimizations from perf-5b nest correctly — the HOIST puts `S_gRep_a` and `S_a_gRep` outside the b-loop, the SHARE computes `S_a_b` once inside the b-loop and passes it to both Triple #1 and Triple #3. Both apply to every (a, b) iteration.

---

## Open questions / NEEDS-REVIEW items

1. **A-1 batch refactor scope.** The composition of Path A batching with Path Z (instance A-1) requires restructuring `IB_RecCob` to operate on a batch of c_tables. This is non-trivial because the recursion has state (beta_int from strict test feeds delta_beta computation feeds next-level c_table). Estimated effort: medium PR with careful invariant preservation.

2. **A-3 memory peak.** Slicing M_y to unconstrained columns before the batched GF(2) matmul (instance A-3) has memory peak ~ 80 MB × (unconstrained / k). At early orbits this saves no time but pays no memory cost; at late orbits this is strictly better than both current paths. Worth verifying peak doesn't matter at any orbit before merging.

3. **A-5 integer column-major view.** Adding an integer `table_T` would double per-orbit cache memory at m=5 (~1 GB → ~2 GB). Whether this is acceptable depends on heap headroom in current A-5b runs. Given that `IsCoboundary2SplitVecAware` is not on the m=5 hot path (the bit-pack route is), this can probably be deferred — but flag if the integer path ever becomes hot (e.g. at m=8/9 with exp=8).

4. **Whether perf-4' Step 1 batched back-sub (B-6) is actually a bottleneck.** Per-orbit perf-4' Step 1 has not been reported as a hot spot in A-5b m=5 production logs (the dominant cost is the Step 4 cross-check loop). Should benchmark before promoting B-6 to Tier-A.

---

## Methodology

**Approach:** Read every file in `extraspecial_orbifolds/scripts/solver/` plus the m=5 production driver and BRW action files, looking specifically for:

1. `if perf_A then ... else perf_B` dispatch shapes.
2. Functions named `*Fast` / `*Batch` / `*Bits` / `*Vec` with corresponding non-fast variants — checking whether the fast variant inherits all the cache/sparsity tricks the non-fast variant uses.
3. Per-call back-substitution loops in code that has access to batched sem artefacts.
4. Per-element closures (`List(L, x -> f(x))`) wrapped around hot-loop arithmetic — confirming whether the surrounding context already uses compiled primitives that would compose.
5. Compiled-arithmetic specialisations (bit-pack, packed-GF(2)) that don't reach the cached structure the integer path uses.

**Files read in full:**
- `extraspecial_orbifolds/scripts/run_e_plus_m_kernel_hap.g` (1117 lines)
- `extraspecial_orbifolds/scripts/solver/iscoboundary2_split.g` (228 lines)
- `extraspecial_orbifolds/scripts/solver/iterated_bockstein.g` (588 lines)
- `extraspecial_orbifolds/scripts/solver/mod2_solver.g` (806 lines)
- `extraspecial_orbifolds/scripts/solver/snf_wrapper.g` (1120 lines)
- `extraspecial_orbifolds/scripts/solver/transgression_matrix_reduced.g` (1508 lines, in 3 passes)
- `extraspecial_orbifolds/scripts/solver/orbit_cache_persist.g` (529 lines)
- `extraspecial_orbifolds/scripts/solver/centraliser_cache.g` (53 lines)
- `extraspecial_orbifolds/scripts/brw_h3_action.g` (453 lines)
- `extraspecial_orbifolds/scripts/transgression_per_generator_brw.g` (361 lines)

**Files partially read (skimmed for perf-relevant sections):**
- `extraspecial_orbifolds/scripts/brw_simples_action.g` (~200 lines around BRW orbit-action and caching)
- `extraspecial_orbifolds/scripts/run_e_plus_2_kernel.g` (slow brute-force harness only)

**Grep queries used:**
- `grep -rn "perf\|fast\|batch\|sparse"` to find perf markers
- `grep -rnE "if .*then"` to enumerate every `if` branch in the solver dir
- `grep -rn "List.*x -> "` to find closures (P3 in CLAUDE.md)
- `grep -rn "TransposedMat\|ConvertToMatrixRep"` to find matrix-rep transitions
- `grep -rn "IsCoboundary2.*Vec\|IsCoboundary2.*Batch"` to enumerate dispatch entry points

**Cross-references checked:**
- For each function found via grep, traced callers to confirm whether the function is on the m=5 hot path (Tier A), driver setup (Tier B), or non-production (Tier C).
- Cross-referenced findings against the CLAUDE.md anti-pattern catalog (P1-P10, P16) and the corrected interpretation in `2026-06-02-perf-audit-full.md` (PR #390) to avoid duplicating already-known P-class findings.

**What this audit did NOT check:**
- HAP-level perf (the perf-5b / perf-5c / perf-5e history is closed — see CLAUDE.md "Historical / archived notes").
- D-VAN m=7 streaming path. The composition pattern in `_DETF_TrimmedFamily_m7_streaming` (incremental detecting-family build) doesn't fit the "two orthogonal perf-paths" mould — it's a single sequential algorithm with checkpointing.
- The K-4a / K-4b code paths in `extraspecial_orbifolds/scripts/keller/`. Per CLAUDE.md, m=5 K-4b uses sparse trace, m=7 K-4a is blocked on #236; neither is on the A-5b hot path being audited.
- Tests under `solver/tests/`. Per task constraint ("non-production code") only the production-callable surface was audited.

---

## Summary by impact tier

**Tier A (m=5 hot path; fix soon):**
- A-1: Compose Path A batching with Path Z bit-pack. Blocked on IB_RecCob refactor. (HIGH)
- A-2: Wire bit slices end-to-end in IB_RecCob_Z4_Bits. (HIGH)
- A-3: Slice M_y to unconstrained columns before batched GF(2) matmul. (HIGH)
- A-4: Sub-task of A-1 — batch IB strict + lift back-subs. (NEEDS-REVIEW)

**Tier B (driver setup / BRW; fix when convenient):**
- A-5 (demoted): Integer column-major `basis_cache.table_T`. Defensive, not on m=5 hot path. (HIGH)
- B-6: Batch perf-4' Step 1's per-column lift back-sub. (HIGH math, LOW measured impact)
- B-7: `_BuildSiblingTableViaTransport` mod-pass closure (P6). (HIGH)

**Tier C (cleanup; track only):**
- C-8: `BuildPCWithBockstein` Bockstein-row lift closure. (HIGH math, NEGLIGIBLE impact)
