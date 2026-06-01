# Path Z sparsity-aware matvec — implementation plan (Approach A, #391)

Design doc: `docs/superpowers/specs/2026-06-02-path-z-sparsity-design.md`.

Probe result: at m=3, Path Z `|support(vec_target)|` has median 14 / k=35
(40% density) with a sharp spike of 329/1497 cases at unit support
(22%). Approach A is worth implementing as a hybrid (unit + sparse +
dense). Expected m=5 wall reduction: ~50-80s/vec off the ~270s/vec
Step-4 baseline. Real but moderate gain; not the 20-30× hoped-for.

## Tasks

### T1: define `IsCoboundary2SplitVecAware` in `solver/iscoboundary2_split.g`

**Signature**:

```gap
IsCoboundary2SplitVecAware := function(C, basis_cache, vec_target, setup)
```

* `C` — centraliser group (same as the existing API).
* `basis_cache` — the full per-orbit cocycle-basis record (NOT just
  the table). Provides `.table` plus the dictionary fields the
  downstream `IsCoboundary2Mod2WithLiftVec` chain consumes (when this
  function falls through to Path A).
* `vec_target` — length-k integer vector (same as existing).
* `setup` — global setup record (same).

**Routing**:

```
supp := PositionsProperty(vec_target, x -> x <> 0);
k_nz := Length(supp);

if k_nz = 0 then
    # Zero vec_target: c_g_vec = zero. Coboundary trivially.
    return true;
elif vec_target[Position(setup.torsion, setup.exponent)] = 0 then
    # Path A: existing fast path. Construct c_g_vec the cheap way.
    # NOTE: the existing call at site 590 has its own Path A inlining
    # via table_gf2; we should NOT route Path A through here. The
    # caller (run_e_plus_m_kernel_hap.g:590) already branches on
    # vec_target[exp_index] != 0 before calling us. The new API is
    # called ONLY on Path Z hits.
    Error("IsCoboundary2SplitVecAware: caller must only invoke when ",
          "vec_target[exp_index] != 0 (Path Z hits only)");
elif k_nz = 1 then
    # Path Z, unit support: column-read fast path.
    return _IsCoboundary2SplitVec_UnitSupport(
        C, basis_cache, supp[1], vec_target[supp[1]], setup);
elif k_nz <= QuoInt(Length(vec_target), 3) then
    # Path Z, sparse: column-accumulation.
    return _IsCoboundary2SplitVec_Sparse(
        C, basis_cache, vec_target, supp, setup);
else
    # Path Z, dense: existing matvec.
    c_g_vec := basis_cache.table * vec_target;
    return IsCoboundary2SplitVec(C, c_g_vec, vec_target, setup);
fi;
```

**Sub-helpers**:

`_IsCoboundary2SplitVec_UnitSupport(C, basis_cache, j_nz, c_nz, setup)`:
```gap
# c_g_vec = basis_cache.table[*][j_nz] * c_nz
col_j := basis_cache.table{[1..Length(basis_cache.table)]}{[j_nz]};
# col_j is a length-n² list-of-lists [[x]]; we want a list of x's.
c_g_vec := List(col_j, row -> row[1] * c_nz);
# But this is an interpreted closure! Use the compiled list-times-int
# form. Slice and scalar-mul both compile.
col_j := basis_cache.table{[1..n²], [j_nz]};
# Actually: basis_cache.table is a list of rows where row[k] is the
# k-th coordinate; basis_cache.table[i][j] is the (i, j) entry. To
# extract column j we use ListExtractColumn or build it as
# List(basis_cache.table, row -> row[j_nz]).
col_j := List(basis_cache.table, row -> row[j_nz]);
c_g_vec := col_j * c_nz;  # compiled list-times-int
return IsCoboundary2SplitVec(C, c_g_vec, vec_target_lifted, setup);
```

`vec_target_lifted` here needs to be the original `vec_target` so the
downstream dispatch in `IsCoboundary2SplitVec` re-routes to Path Z
correctly. The CALLER passes `vec_target` so we reuse it.

`_IsCoboundary2SplitVec_Sparse(C, basis_cache, vec_target, supp, setup)`:
```gap
n2 := Length(basis_cache.table);
c_g_vec := ListWithIdenticalEntries(n2, 0);
for j in supp do
    col_j := List(basis_cache.table, row -> row[j]);
    AddRowVector(c_g_vec, col_j, vec_target[j]);  # compiled
od;
return IsCoboundary2SplitVec(C, c_g_vec, vec_target, setup);
```

**Math derivation**: see Phase 2 of the design doc.

**Implementation gotcha**: `List(basis_cache.table, row -> row[j])` is
itself an n²-element list comprehension with a per-row closure. To beat
the dense matvec's compiled inner loop, this needs to be either (a)
slice-form `basis_cache.table{[1..n2]}{[j]}` (which produces a list of
1-element lists and needs un-wrapping), or (b) the more direct
`TransposedMatMutable(basis_cache.table)[j]` IF the table has been
pre-transposed.

A cleaner option is to extend the cache to pre-store column views, but
that's a separate cache-restructure ticket. For T1, use the slice
approach and verify it's compiled.

### T2: update dispatch at `run_e_plus_m_kernel_hap.g:590`

Current code:
```
if exp_local > 2 and exp_index <> fail and vec_target[exp_index] <> 0 then
    # Path Z: per-call. Needs the full integer c_g_table.
    c_g_table := basis_cache.table * vec_target;
    results[target_idx] :=
        IsCoboundary2SplitVec(basis_cache.C, c_g_table, vec_target,
                               setup);
else
    ...Path A...
fi;
```

Replace with:
```
if exp_local > 2 and exp_index <> fail and vec_target[exp_index] <> 0 then
    # Path Z: route through sparsity-aware entry. Internally:
    #   - |supp(vec_target)|=1   -> column-read fast path
    #   - |supp|<=k/3            -> sparse column accumulation
    #   - |supp|>k/3             -> existing dense matvec
    # See docs/superpowers/specs/2026-06-02-path-z-sparsity-design.md.
    results[target_idx] :=
        IsCoboundary2SplitVecAware(basis_cache.C, basis_cache,
                                    vec_target, setup);
else
    ...Path A (unchanged)...
fi;
```

The `c_g_table` local variable in the function declaration is no longer
needed for this branch (the new entry materialises it internally only
when the dense fallback fires). Leave it declared because Path A's
batched call doesn't reach it, and removing requires a 2-line edit
across the surrounding `local` list. Cosmetic — drop if clean.

### T3: half-vec / fail-column sites — defer

The "2 × e_exp_index" half-vec test (`step-2` of the driver) also uses
`PerVecTransgressionShared` and so will route through the new
dispatcher automatically. No further action needed.

The transgression-matrix-reduced fail-column path
(`solver/transgression_matrix_reduced.g:1335`) is OUT OF SCOPE for this
ticket; PR #389 rank-1 already exploits unit-support there for the
specific axis-sweep pattern. We will not touch it.

### T4: m=2 smoke test

```sh
cd /Users/thomasgemunden/Projects/group_cohomology/DRINFELD/.claude/worktrees/agent-a767f4ec8d513a33e/extraspecial_orbifolds/scripts
timeout 120 /opt/homebrew/bin/gap -q -b -c 'Read("run_e_plus_2_kernel.g");' > /tmp/m2_smoke.log 2>&1
```

Assertion in the driver:
```
Assert(0, exact.kernel_size = 2048, ...)
```

At m=2, exp = 2, so the new dispatcher's Path Z branch is never reached
(the caller's `vec_target[exp_index] != 0` test always fails because
`setup.torsion` has no entry equal to `exp = 2 = exponent` except itself,
and the half-vec test is skipped per `step-2-skip`). So m=2 only
exercises Path A, which is unchanged. Expected: full pass.

### T5: m=3 anchor

For m=3 the H^3(E_+(3); Z/4) kernel anchor is `|ker Tr| = 2^36 =
68719476736` (#42 acceptance). The driver enumerates a kernel of size
2^16 max; if `kernel_size > 2^16` it persists structurally rather than
enumerating. At m=3 the explicit kernel size = 262144 = 2^18 (per the
issue body) which exceeds ENUM_LIMIT, so Step 4 runs on a sampled set.

The full m=3 driver run is ~35 min in the old code; with `perf-4'`
(reduced-tr-matrix) it's ~5 min. We use:

```sh
cd /Users/thomasgemunden/Projects/group_cohomology/DRINFELD/.claude/worktrees/agent-a767f4ec8d513a33e/extraspecial_orbifolds/scripts
timeout 600 /opt/homebrew/bin/gap -q -b -o 16g -c 'MPARAM := 3; USE_REDUCED_TR_MATRIX := false; Read("run_e_plus_m_kernel_hap.g");' > /tmp/m3_anchor.log 2>&1
```

Acceptance:
* `|ker Tr| = 262144` per the m=3 anchor in the driver.
* Step 4 (kernel-sample + non-ker sample) PASS, identical witness
  classes to the existing main code.

If the wall exceeds 600s, the anchor times out — fall back to a single-
generator probe with PROBE_GEN := 1.

### T6: commit + PR

Two commits:
1. **docs**: design doc + plan + probe script.
2. **code**: `IsCoboundary2SplitVecAware` + dispatch site update.

Tests should pass before PR opens. PR title: `[A-5b perf #391] Path Z
sparsity-aware matvec dispatch (Approach A)`.

## Risk mitigation

* The new dispatcher is gated on `vec_target[exp_index] != 0` at the
  call site. Path A (Path A) is untouched, so the bulk of A-5b m=5
  work (Path A) cannot regress.
* The dense fallback (`k_nz > k/3`) calls the existing
  `IsCoboundary2SplitVec` verbatim, so even if the sparse routing
  decisions are wrong (e.g. threshold too low), the worst case is that
  we pay one extra `PositionsProperty` call per Path Z entry but get
  identical results.
* `PositionsProperty(vec_target, x -> x <> 0)` is O(k) = 165 at m=5;
  compared to the n²=4M matvec cost this is rounding error.

## Status (handover)

* Phase 1 (probe): DONE. Result above.
* Phase 2 (design doc): DONE.
* Phase 3 (implementation plan): THIS DOCUMENT.
* Phase 4 (implement): NEXT.
