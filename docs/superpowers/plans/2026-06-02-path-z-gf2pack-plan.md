# Approach B implementation plan — Path Z bit-slice refactor (issue #391)

Companion: `docs/superpowers/specs/2026-06-02-path-z-gf2pack-design.md`.

## T1 — `snf_wrapper.g` / `BuildPerClassCocycleBasis`: add `table_gf2_bot`

File: `extraspecial_orbifolds/scripts/solver/snf_wrapper.g`
Line: ~719–725

Current:
```gap
r_half := exp / 2;
one_gf2 := One(GF(2));
table_gf2 := List(table, row ->
    List(row, x -> (QuoInt(x, r_half) mod 2) * one_gf2));
ConvertToMatrixRep(table_gf2, GF(2));
result := rec(C := C, table := table, table_gf2 := table_gf2,
              elts := elts, n := n, idx_map := idx_map);
```

New:
```gap
r_half := exp / 2;
one_gf2 := One(GF(2));
# table_gf2_top: bit_{log2(r_half)} of table. At exp=4 this is bit_1
# (top bit). At exp=2 this is bit_0. Used by Path A.
table_gf2_top := List(table, row ->
    List(row, x -> (QuoInt(x, r_half) mod 2) * one_gf2));
ConvertToMatrixRep(table_gf2_top, GF(2));
# table_gf2_bot: bit_0 of table. New for Approach B (#391). At exp=2
# this is identical to table_gf2_top (= bit_0). At exp=4 it's the
# bottom bit (zero on order-2 columns, nontrivial on exp_idx column).
# We materialise it uniformly so the Path Z bit-slice route can use a
# single packed GF(2) matvec regardless of m.
table_gf2_bot := List(table, row ->
    List(row, x -> (x mod 2) * one_gf2));
ConvertToMatrixRep(table_gf2_bot, GF(2));
result := rec(C := C, table := table,
              table_gf2 := table_gf2_top,    # back-compat alias
              table_gf2_top := table_gf2_top,
              table_gf2_bot := table_gf2_bot,
              elts := elts, n := n, idx_map := idx_map);
```

Same change in `BuildPerClassCocycleBasisForOrbit`'s sibling builder
(~line 964–971).

## T2 — `orbit_cache_persist.g` / `LoadOrbitCache`: rebuild `table_gf2_bot`

File: `extraspecial_orbifolds/scripts/solver/orbit_cache_persist.g`
Line: ~465–486

Current (snippet):
```gap
table := List(data.table_rows, ShallowCopy);
ConvertToMatrixRep(table);
exp_val := expected_fp.exponent;
r_half := exp_val / 2;
one_gf2 := One(GF(2));
table_gf2 := List(table, row ->
    List(row, x -> (QuoInt(x, r_half) mod 2) * one_gf2));
ConvertToMatrixRep(table_gf2, GF(2));
...
return rec(C := C, table := table, table_gf2 := table_gf2,
           elts := elts, n := n, idx_map := idx_map);
```

New: parallel addition of `table_gf2_bot`, returned in both `table_gf2_top`
and `table_gf2_bot` fields. Same back-compat alias.

## T3 — `iterated_bockstein.g`: add `IsCoboundary2Z4VecBits`

File: `extraspecial_orbifolds/scripts/solver/iterated_bockstein.g`
Position: after `IsCoboundary2Z2kVec` (~line 547).

New function:
```gap
# IsCoboundary2Z4VecBits(C, c_bot, c_top, n) — modulus = 4 specialisation
# of IsCoboundary2Z2kVec consuming bit slices directly (issue #391).
#
# Tests whether [c] = 0 in H²(C; Z/4) where c is given by its two
# bit slices:
#   c_bot[i] = bit_0(c_g[i]), c_top[i] = bit_1(c_g[i])
# both as packed-GF(2) length-n² vectors.
#
# Math: see docs/superpowers/specs/2026-06-02-path-z-gf2pack-design.md
# §"IB refactor". Mirrors IsCoboundary2Z2k for k=2 but stays on bit slices
# throughout, avoiding the integer matvec and integer δβ̃ assembly.
#
# Returns: bool. Same semantics as IsCoboundary2Z2kVec(C, c_g_vec, 2).
IsCoboundary2Z4VecBits := function(C, c_bot, c_top, n)
    local mult_rec, beta_rec, beta_bot, db_bot, db_top, c_next_bot,
          mult, i, j, ij, bi, bj, bij;
    mult_rec := _GetCachedMultTable(C);
    mult := mult_rec.mult;

    # Strict F_2 coboundary test on c_bot (since c_bot is already mod 2).
    # _GetCachedSemForAT factorisation is reused.
    beta_rec := IsCoboundary2Mod2VecWithWitness(C, c_bot);
    if beta_rec.yes = false then return false; fi;
    beta_bot := beta_rec.witness;  # length-n GF(2) vector

    # Compute δβ̃ on bit slices. β values are in {0,1}, so δβ̃[i,j] =
    # β_i + β_j - β_{ij} ∈ {-1, 0, 1, 2}; mod 4 ∈ {0,1,2,3} with:
    #   bit_0 = β_i XOR β_j XOR β_{ij}
    #   bit_1 = (β_i XOR β_{ij}) AND (β_j XOR β_{ij})
    # Materialise both as length-n² GF(2) vectors.
    db_bot := ListWithIdenticalEntries(n * n, Zero(GF(2)));
    db_top := ListWithIdenticalEntries(n * n, Zero(GF(2)));
    for i in [1..n] do
        bi := beta_bot[i];
        for j in [1..n] do
            ij := mult[i][j];
            bj := beta_bot[j];
            bij := beta_bot[ij];
            db_bot[(i-1)*n + j] := bi + bj + bij;
            db_top[(i-1)*n + j] := (bi + bij) * (bj + bij);
        od;
    od;
    ConvertToVectorRep(db_bot, GF(2));
    ConvertToVectorRep(db_top, GF(2));

    # c_next_bot = bit_1((c - db) mod 4)
    #            = c_top XOR db_top XOR (db_bot AND NOT c_bot)
    # In GF(2) ops:
    #   db_bot AND NOT c_bot = db_bot * (One + c_bot) elementwise.
    c_next_bot := c_top + db_top + List([1..n*n], i ->
        db_bot[i] * (One(GF(2)) - c_bot[i]));
    ConvertToVectorRep(c_next_bot, GF(2));

    return IsCoboundary2Mod2WithLiftVec(C, c_next_bot);
end;;
```

Note: the inner loop here is O(n²) interpreted, BUT it operates on
length-n GF(2) values one cell at a time. Three optimisations are
straightforward follow-ups (not in this PR):
- KroneckerProduct-based vectorisation (matches the `IB_AlphaCupAlpha`
  pattern from PR #225).
- Direct packed-word XOR/AND via `SUM_GF2VEC_GF2VEC` + Hadamard.
- Compiled C kernel if profiling shows the loop is the new dominant cost.

The first PR aims for correctness + 30–50× per-call speedup from the
matvec replacement; further IB-side gains can land afterwards.

Concern: `IsCoboundary2Mod2VecWithWitness` and `IsCoboundary2Mod2WithLiftVec`
currently expect INTEGER inputs and apply `(x mod 2) * one` element-wise.
For correctness, we need to make these accept packed-GF(2) inputs OR
convert `c_bot` / `c_next_bot` via `IntVecFFE`. We opt for the latter at
the call sites (simpler PR diff):

```gap
beta_rec := IsCoboundary2Mod2VecWithWitness(C, List(c_bot, IntFFE));
```

This re-pays the n² IntFFE cost but avoids a `mod2_solver.g` API change.
Profiling can drive a later patch to extend the function signature.

(Update: cheaper option — `IsCoboundary2Mod2Vec` style functions already
do `List(c_g_vec, x -> (x mod 2) * one)`. We can pass the packed GF(2)
vector directly because GAP's `mod 2` on an FFE returns the integer
value (0 or 1), and `* one` then casts back. Verify this assumption in
T6 via a small test. If it doesn't work, the IntFFE wrap is the fallback.)

## T4 — `run_e_plus_m_kernel_hap.g`: wire Path Z bit-slice dispatch

File: `extraspecial_orbifolds/scripts/run_e_plus_m_kernel_hap.g`
Line: ~588–593

Current:
```gap
if exp_local > 2 and exp_index <> fail and vec_target[exp_index] <> 0 then
    # Path Z: per-call. Needs the full integer c_g_table.
    c_g_table := basis_cache.table * vec_target;
    results[target_idx] :=
        IsCoboundary2SplitVec(basis_cache.C, c_g_table, vec_target,
                               setup);
```

New:
```gap
if exp_local > 2 and exp_index <> fail and vec_target[exp_index] <> 0 then
    # Path Z (issue #391): bit-slice route.
    # At exp = 4 we route via IsCoboundary2Z4VecBits, which consumes
    # bit_0(table*vec) and bit_1(table*vec) computed as two packed
    # GF(2) matvecs plus a single-column correction. See
    # docs/superpowers/specs/2026-06-02-path-z-gf2pack-design.md.
    #
    # The math (m=5, exp=4):
    #   bit_0(c_g_table)[i] = bit_0(table[i][exp_idx]) AND bit_0(vec[exp_idx])
    #   bit_1(c_g_table)[i] = (table_gf2_top * vec_bot)[i]
    #                          - bit_1(table[i][exp_idx]) * bit_0(vec[exp_idx])
    #                          + bit_0(table[i][exp_idx]) * bit_1(vec[exp_idx])
    #     (all XOR over GF(2))
    if exp_local = 4 then
        # Pack bits of vec_target into single-bit scalars.
        vbot_exp := bit_0(vec_target[exp_index]);   # ∈ GF(2)
        vtop_exp := bit_1(vec_target[exp_index]);   # ∈ GF(2)
        u_bot := (vec_target mod 2) * one_gf2;
        ConvertToVectorRep(u_bot, GF(2));
        # Path A's matvec, on table_gf2_top.
        slice_top_full := basis_cache.table_gf2_top * u_bot;
        # The exp_idx column of table_gf2_top contributes bit_1(table[i][exp_idx]) * bit_0(vec[exp_idx])
        # to slice_top_full; subtract it because we want sum over j != exp_idx.
        col_top_exp := List(basis_cache.table_gf2_top, row -> row[exp_index]);
        ConvertToVectorRep(col_top_exp, GF(2));
        col_bot_exp := List(basis_cache.table_gf2_bot, row -> row[exp_index]);
        ConvertToVectorRep(col_bot_exp, GF(2));
        # bit_1 = slice_top_full XOR (col_top_exp * vbot_exp) XOR (col_bot_exp * vtop_exp)
        slice_top := slice_top_full + col_top_exp * vbot_exp
                                    + col_bot_exp * vtop_exp;
        # bit_0 = col_bot_exp * vbot_exp  (only exp_idx column has bit_0 nonzero)
        slice_bot := col_bot_exp * vbot_exp;
        results[target_idx] :=
            IsCoboundary2Z4VecBits(basis_cache.C, slice_bot, slice_top,
                                    basis_cache.n);
    else
        # exp != 4: fall back to integer path (e.g. exp=8 at m=7 lands here).
        c_g_table := basis_cache.table * vec_target;
        results[target_idx] :=
            IsCoboundary2SplitVec(basis_cache.C, c_g_table, vec_target,
                                   setup);
    fi;
```

Hoist `col_top_exp` and `col_bot_exp` out of the inner loop (one per
basis_cache, not per target_idx).

## T5 — `orbit_cache_persist.g`: bump cache version

File: `extraspecial_orbifolds/scripts/solver/orbit_cache_persist.g`

Line ~187:
```gap
_ORBIT_CACHE_FORMAT_VERSION := 2;;
```

Loader handles both v1 (rebuild `table_gf2_bot` from `table_rows`) and
v2 (same — derived field, not stored). Bump documents the API contract
change in the cache record's exported fields.

Alternative considered: keep version=1 since the on-disk format is
unchanged. **Decision**: bump anyway to make the field-set change
explicit; LoadOrbitCache transparently accepts v1 files (loading them
and computing `table_gf2_bot` the same way as v2).

Wait, that breaks the existing version check. Easier: leave version=1
and just always derive `table_gf2_bot` at load time. The on-disk format
is unchanged. Add a comment explaining.

Final decision: **leave _ORBIT_CACHE_FORMAT_VERSION = 1**. The on-disk
schema is unchanged; we add a derived field at load time. Same approach
as `table_gf2_top` (= old `table_gf2`).

## T6 — m=2 + m=3 regression

T6.1: smoke test `solver/tests/test_iterated_bockstein.g` (and any
related test) to verify that the bit-slice path produces the same
boolean result as the integer path on a synthetic c_g_table.

T6.2: run `solver/tests/test_brw_orbit_cache_quick.g` (m=2, m=3) to
confirm the kernel computation still works.

T6.3: run a small m=3 anchor (a single sweep, ~minutes wall) and confirm
the kernel size matches the pre-PR value.

If any test fails, debug systematically (see superpowers:systematic-debugging):
the most likely failure mode is the boundary between packed-GF(2)
matvec output and integer-arithmetic IB inputs. Use the bit-by-bit
check from T6.1 to localise.

## T7 — commit, push, PR

Commit message:
```
[a5b perf #391 approach B] GF(2) bit-pack Path Z's table*vec matvec

Refactor Path Z in PerVecTransgressionShared (m=5 case, exp=4) to
consume bit slices of basis_cache.table instead of a full integer
matvec. At m=5 the integer matvec is n² × k = 4M × 165 ops per call,
~700 ms at compiled C speed (PR #390 corrected interpretation). Approach
B replaces it with one packed GF(2) matvec on table_gf2_top (already
cached, was used by Path A) plus two single-column corrections and a
new IB_Z4 specialisation that stays on bit slices.

Math: see docs/superpowers/specs/2026-06-02-path-z-gf2pack-design.md.
Expected per-call speedup: ~30-50×; per-vec wall reduction ~177 s → ~5 s
on the matvec; total per-vec wall ~270 s → ~90 s end-to-end at m=5.

Changes:
- solver/snf_wrapper.g: BuildPerClassCocycleBasis (and sibling
  BuildPerClassCocycleBasisForOrbit) now emit both table_gf2_top
  (renamed from table_gf2, with back-compat alias) and table_gf2_bot.
- solver/orbit_cache_persist.g: LoadOrbitCache derives table_gf2_bot
  from table_rows alongside the existing table_gf2_top derivation.
  On-disk schema unchanged.
- solver/iterated_bockstein.g: new IsCoboundary2Z4VecBits that consumes
  bit slices directly, replacing the integer-table IB chain for k=2.
- run_e_plus_m_kernel_hap.g: Path Z dispatch routes through the new
  bit-slice API when exp = 4; falls back to integer path for exp != 4.

Tests:
- m=2 smoke (test_brw_orbit_cache_quick.g, test_iterated_bockstein.g).
- m=3 anchor (kernel size match).

Co-Authored-By: Claude Opus 4.7 <noreply@anthropic.com>
```

PR off `a5b-perf-pathz-gf2pack-391`, base `main`.

## Time estimate

| Task | Estimate |
|---|---|
| T1 | 10 min |
| T2 | 10 min |
| T3 | 20 min |
| T4 | 15 min |
| T5 | 5 min (resolved as no-op) |
| T6 | 30 min |
| T7 | 10 min |
| **Total** | **~100 min** |

Within the 90 min budget if we move fast. If T6 surfaces an
unexpected integration issue, fall back to landing T1+T2+T3+T5
(infrastructure only) on a docs/code branch and finish T4+T6+T7 in a
follow-up.
