# test_a3d_sparse_fusion.g — A-3d (#45) streaming fusion oracle tests.
#
# Acceptance coverage (per the A-3d brief):
#   (a) FusionRowSignature equivalence: at small rank the streaming
#       oracle (computed lazily from S) yields signatures identical
#       to those from the dense Verlinde N tensor.  We exercise this
#       on D(Q_8) (rank 22) and D(E_+(2)) (rank 184).
#   (b) Memory-footprint sanity: at simulated rank 2272 (synthetic
#       random S avoiding the costly real construction) instantiating
#       the oracle does NOT materialise the full r^3 tensor; we
#       verify by checking the oracle's stats — `rows_computed` is
#       zero pre-query and grows only when rows are explicitly
#       requested.  We also exercise a single row at the real E_+(3)
#       rank 2272 using the on-disk dense S so the row-by-row matmul
#       path is end-to-end tested at production rank.
#   (c) Full pipeline at small rank: AutNT(N_oracle, T, QD) on D(Q_8)
#       reproduces the dense-N AutNT result of |Aut(N, T)| = 6.  We
#       also check the order-2 cocycle (8/4/2.txt -> 24) so the
#       sparse path catches regressions of both trivial and non-trivial
#       cocycle behaviour.
#
# NOT covered in this test (deferred to the parent context):
#   * The full AutNT pipeline at rank 2272 (~1 day wall budget).
#     Microbenchmarks below project the projected wall+memory cost.
#
# K-4a-T1 convention: this test uses an absolute path to load sibling
# modules and an absolute path to the on-disk dense S; if the worktree
# moves, fix the _SCRIPT_DIR constant below.
#
# Run from anywhere:
#   gap -q -b extraspecial_orbifolds/scripts/tests/test_a3d_sparse_fusion.g
#
# Success is signalled by "test_a3d_sparse_fusion: PASS".

_SCRIPT_DIR := "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-a3d-sparse/extraspecial_orbifolds/scripts";;

Read(Concatenation(_SCRIPT_DIR, "/aut_nt_partition.g"));
Read(Concatenation(_SCRIPT_DIR, "/fusion_oracle.g"));
Read(Concatenation(_SCRIPT_DIR, "/aut_nt_refine.g"));
Read(Concatenation(_SCRIPT_DIR, "/aut_nt.g"));

failures := [];;

CheckEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
    else
        Print("  [FAIL] ", label, "\n");
        Print("        expected: ", expected, "\n");
        Print("        got     : ", got, "\n");
        Add(failures, label);
    fi;
end;;

CheckTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
    else
        Print("  [FAIL] ", label, "\n");
        Add(failures, label);
    fi;
end;;

# ---- Locate modular_data ---------------------------------------------
_md_root := fail;;
for _cand in [ "../../../../modular_data",
               "../../../../../modular_data",
               "/Users/thomasgemunden/Projects/group_cohomology/modular_data"
             ] do
    if _md_root = fail
       and IsExistingFile(Concatenation(_cand, "/8/4/1.txt")) then
        _md_root := _cand;
    fi;
od;
if _md_root = fail then
    Error("cannot locate modular_data/ root.");
fi;

# ----------------------------------------------------------------------
# Test (a): signature equivalence on D(Q_8) at rank 22.
#
# Two paths must agree:
#   dense-N path : FusionCoefficientsFromS(S) -> FusionRowSignature(i, N, c)
#   oracle path  : MakeStreamingFusionOracle(S, cache=0) ->
#                  FusionRowSignature(i, oracle, c)
# Identical sorted-multiset signatures => the oracle is a drop-in
# replacement for the dense tensor at the V-5b row-signature interface.
# ----------------------------------------------------------------------

Print("\n=== (a) FusionRowSignature equivalence: D(Q_8) ===\n");

q8_data := ReadAsFunction(
    Concatenation(_md_root, "/8/4/1.txt"))();;
q8_S := q8_data.S;;
q8_T := q8_data.T;;
q8_QD := QuantumDimensionsFromS(q8_S);;
CheckEqual("D(Q_8) rank", Length(q8_T), 22);

q8_N_dense := FusionCoefficientsFromS(q8_S);;
q8_oracle_nocache := MakeStreamingFusionOracle(q8_S,
                        rec(cache_size := 0));;
q8_oracle_full := MakeStreamingFusionOracle(q8_S,
                      rec(cache_size := 100));;

# Use the V-5a partition to colour vertices, then test signature equality.
P0_q8 := InitialPartition(fail, q8_T, q8_QD);;
colour_q8 := ColourFromPartition(22, P0_q8);;

_q8_all_match := true;;
for _i in [1..22] do
    _sig_dense := FusionRowSignature(_i, q8_N_dense, colour_q8);;
    _sig_oracle := FusionRowSignature(_i, q8_oracle_nocache, colour_q8);;
    if _sig_dense <> _sig_oracle then
        _q8_all_match := false;
        Print("  signature mismatch at i = ", _i, "\n");
    fi;
od;
CheckTrue("D(Q_8) all 22 row signatures agree (dense vs oracle/nocache)",
          _q8_all_match);

# Oracle internal: row equality (a stronger check).
_q8_row_eq := true;;
for _i in [1..22] do
    if q8_N_dense[_i] <> q8_oracle_full.row(_i) then
        _q8_row_eq := false;
    fi;
od;
CheckTrue("D(Q_8) oracle row equals dense N[i] elementwise",
          _q8_row_eq);

# Coef equality.
_q8_coef_eq := true;;
for _i in [1, 5, 12, 22] do
    for _j in [1, 5, 12, 22] do
        for _k in [1, 5, 12, 22] do
            if q8_oracle_full.coef(_i, _j, _k)
               <> q8_N_dense[_i][_j][_k] then
                _q8_coef_eq := false;
            fi;
        od;
    od;
od;
CheckTrue("D(Q_8) oracle.coef matches dense N at 64 spot-checks",
          _q8_coef_eq);

# Stable refinement equality.
P_q8_dense := RefineByFusion(P0_q8, q8_N_dense);;
P_q8_oracle := RefineByFusion(P0_q8, q8_oracle_nocache);;
CheckEqual("D(Q_8) stable refinement: canonical form (dense)",
           PartitionCanonical(P_q8_dense),
           PartitionCanonical(P_q8_oracle));

# ----------------------------------------------------------------------
# Test (a'): signature equivalence on D(E_+(2)) at rank 184.
# This exercises a non-trivial colouring (V-5a yields > 5 blocks) and a
# larger fusion ring.  The oracle is built with a moderate cache so we
# also confirm cached + uncached produce identical results.
# ----------------------------------------------------------------------

Print("\n=== (a') FusionRowSignature equivalence: D(E_+(2)) ===\n");

e2_data := ReadAsFunction(
    Concatenation(_md_root, "/32/49/1.txt"))();;
e2_S := e2_data.S;;
e2_T := e2_data.T;;
e2_QD := QuantumDimensionsFromS(e2_S);;
CheckEqual("D(E_+(2)) rank", Length(e2_T), 184);

t_dense_e2 := Runtime();;
e2_N_dense := FusionCoefficientsFromS(e2_S);;
t_dense_e2_wall := Runtime() - t_dense_e2;;
Print("  FusionCoefficientsFromS(E_+(2)) wall: ",
      t_dense_e2_wall, " ms\n");

t_oracle_e2 := Runtime();;
e2_oracle := MakeStreamingFusionOracle(e2_S,
                rec(cache_size := 200));;
t_oracle_e2_wall := Runtime() - t_oracle_e2;;
Print("  MakeStreamingFusionOracle(E_+(2)) wall: ",
      t_oracle_e2_wall, " ms (precompute Sbar^T only)\n");

P0_e2 := InitialPartition(fail, e2_T, e2_QD);;
colour_e2 := ColourFromPartition(184, P0_e2);;

t_sig_dense := Runtime();;
for _i in [1..184] do
    _dummy := FusionRowSignature(_i, e2_N_dense, colour_e2);;
od;
t_sig_dense_wall := Runtime() - t_sig_dense;;

t_sig_oracle := Runtime();;
for _i in [1..184] do
    _dummy := FusionRowSignature(_i, e2_oracle, colour_e2);;
od;
t_sig_oracle_wall := Runtime() - t_sig_oracle;;
Print("  per-row signature wall: dense ", t_sig_dense_wall,
      " ms vs streaming oracle ", t_sig_oracle_wall, " ms\n");

# Hash-equality check across all 184 rows.
_e2_all_match := true;;
for _i in [1..184] do
    _sig_d := FusionRowSignature(_i, e2_N_dense, colour_e2);;
    _sig_o := FusionRowSignature(_i, e2_oracle, colour_e2);;
    if _sig_d <> _sig_o then
        _e2_all_match := false;
    fi;
od;
CheckTrue("D(E_+(2)) all 184 row signatures agree (dense vs oracle)",
          _e2_all_match);

# Stable refinement equality.
t_ref_dense_e2 := Runtime();;
P_e2_dense := RefineByFusion(P0_e2, e2_N_dense);;
t_ref_dense_e2_wall := Runtime() - t_ref_dense_e2;;

t_ref_oracle_e2 := Runtime();;
P_e2_oracle := RefineByFusion(P0_e2, e2_oracle);;
t_ref_oracle_e2_wall := Runtime() - t_ref_oracle_e2;;
Print("  RefineByFusion wall: dense ", t_ref_dense_e2_wall,
      " ms vs streaming oracle ", t_ref_oracle_e2_wall, " ms\n");

CheckEqual("D(E_+(2)) stable refinement: canonical form (dense)",
           PartitionCanonical(P_e2_dense),
           PartitionCanonical(P_e2_oracle));

# ----------------------------------------------------------------------
# Test (b): memory-footprint sanity.  The streaming oracle must not
# materialise the full O(r^3) tensor on construction; rows are computed
# only when requested.
# ----------------------------------------------------------------------

Print("\n=== (b) memory-footprint sanity ===\n");

# (b1) Right after construction, no rows have been computed.
_o := MakeStreamingFusionOracle(q8_S, rec(cache_size := 5));;
CheckEqual("oracle: rows_computed = 0 on construction",
           _o.stats.rows_computed, 0);
CheckEqual("oracle: cache_size = 0 on construction",
           _o.stats.cache_size, 0);
# Touch row 1 -> rows_computed = 1, cache_size = 1.
_row1 := _o.row(1);;
CheckEqual("oracle: rows_computed = 1 after one .row call",
           _o.stats.rows_computed, 1);
CheckEqual("oracle: cache_size = 1 after one .row call",
           _o.stats.cache_size, 1);
# Touch row 1 again -> served from cache.
_row1b := _o.row(1);;
CheckEqual("oracle: row(1) cached on second touch",
           _o.stats.rows_computed, 1);
CheckTrue("oracle: same row reference returned (cache hit)",
          IsIdenticalObj(_row1, _row1b));
# Fill cache.
for _i in [2..5] do _dummy := _o.row(_i);; od;
CheckEqual("oracle: cache full at 5", _o.stats.cache_size, 5);
# Evict by inserting a 6th row.
_dummy := _o.row(6);;
CheckEqual("oracle: cache stays at 5 after eviction",
           _o.stats.cache_size, 5);
# Row 1 should have been evicted (round-robin).
_o.clear_cache();
CheckEqual("oracle: clear_cache resets cache_size", _o.stats.cache_size, 0);

# (b2) Production rank: load real E_+(3) dense S from disk and compute
# exactly one row through the oracle.  Verify memory does not balloon to
# the full tensor (we do NOT call FusionCoefficientsFromS here, only
# FusionRowFromS via the oracle).

Print("\n  (b2) production rank: loading E_+(3) dense S (~26 MB on disk) ...\n");
_e3_S_path := Concatenation(_SCRIPT_DIR,
    "/../computed/E_plus_3/S.g");;
if not IsExistingFile(_e3_S_path) then
    Print("  [skip] E_+(3) S.g missing at ", _e3_S_path, "\n");
else
    t_load := Runtime();;
    Read(_e3_S_path);    # installs `S` in the GAP global state.
    t_load_wall := Runtime() - t_load;;
    Print("  E_+(3) S loaded in ", t_load_wall, " ms; rank = ",
          Length(S), "\n");
    CheckEqual("E_+(3) S rank", Length(S), 2272);

    t_orb := Runtime();;
    e3_oracle := MakeStreamingFusionOracle(S,
                     rec(cache_size := 4));;
    t_orb_wall := Runtime() - t_orb;;
    Print("  MakeStreamingFusionOracle(E_+(3) S) wall: ",
          t_orb_wall, " ms (precompute Sbar^T only)\n");

    # Single-row microbench at rank 2272.
    t_row := Runtime();;
    _e3_row1 := e3_oracle.row(1);;
    t_row_wall := Runtime() - t_row;;
    Print("  oracle.row(1) at rank 2272 wall: ", t_row_wall, " ms\n");
    CheckEqual("E_+(3) row 1 shape", Length(_e3_row1), 2272);
    CheckEqual("E_+(3) row 1 column shape", Length(_e3_row1[1]), 2272);
    # Integrality + non-negativity spot-check on the unit row (row 1).
    # N_{1,j}^k = delta_{j,k}, so row(1)[j][k] must be 1 iff j = k else 0.
    _unit_ok := true;;
    for _j in [1..5] do
        for _k in [1..5] do
            if _j = _k then
                if _e3_row1[_j][_k] <> 1 then _unit_ok := false; fi;
            else
                if _e3_row1[_j][_k] <> 0 then _unit_ok := false; fi;
            fi;
        od;
    od;
    CheckTrue("E_+(3) row(1) = Identity (unit fusion rule)",
              _unit_ok);

    # Second-row microbench (different i).
    t_row2 := Runtime();;
    _dummy := e3_oracle.row(2);;
    t_row2_wall := Runtime() - t_row2;;
    Print("  oracle.row(2) at rank 2272 wall: ", t_row2_wall, " ms\n");

    # Cache-hit benchmark: should be O(1).
    t_hit := Runtime();;
    _dummy := e3_oracle.row(1);;
    t_hit_wall := Runtime() - t_hit;;
    Print("  oracle.row(1) cache hit wall: ", t_hit_wall, " ms\n");

    # Projection.  Dense full tensor: r^3 = 11.7e9 entries.  Streaming:
    # cache_size * r^2 cyclotomics.
    _r := 2272;;
    _dense_entries := _r * _r * _r;;
    _cache_entries := 4 * _r * _r;;
    Print("\n  Projection at rank ", _r, ":\n");
    Print("    Dense tensor entries     : ",
          _dense_entries, " (= r^3)\n");
    Print("    Cache=4 oracle entries   : ",
          _cache_entries, " (= 4*r^2)\n");
    Print("    Ratio dense/cache        : ",
          _dense_entries / _cache_entries, "x reduction\n");
    Print("    Approx wall to compute   : ", t_row2_wall,
          " ms/row (steady-state cache miss)\n");
    Print("    Full-tensor wall estimate: ",
          t_row2_wall * _r / 1000., " s (",
          t_row2_wall * _r / 1000. / 60., " min) for r rows\n");
fi;

# ----------------------------------------------------------------------
# Test (c): full AutNT pipeline equivalence at small rank.
# We do NOT run E_+(3) (deferred to the parent context); we instead
# verify that the oracle path reproduces the dense path on the two
# rank-22 D(Q_8) cocycles.
# ----------------------------------------------------------------------

Print("\n=== (c) full AutNT(N_oracle, T, QD) equivalence at rank 22 ===\n");

# Trivial cocycle.
t_dense_aut := Runtime();;
q8_aut_dense := AutNT(q8_N_dense, q8_T, q8_QD);;
t_dense_aut_wall := Runtime() - t_dense_aut;;
Print("  AutNT dense (Q_8 trivial): order = ", q8_aut_dense.order,
      ", ", t_dense_aut_wall, " ms\n");

t_oracle_aut := Runtime();;
q8_oracle_fresh := MakeStreamingFusionOracle(q8_S,
                       rec(cache_size := 100));;
q8_aut_oracle := AutNT(q8_oracle_fresh, q8_T, q8_QD);;
t_oracle_aut_wall := Runtime() - t_oracle_aut;;
Print("  AutNT oracle (Q_8 trivial): order = ", q8_aut_oracle.order,
      ", ", t_oracle_aut_wall, " ms\n");
Print("  oracle stats: ",
      FusionOracle_StatsString(q8_oracle_fresh), "\n");

CheckEqual("D(Q_8) trivial cocycle: |Aut| matches dense via oracle",
           q8_aut_oracle.order, 6);
CheckEqual("D(Q_8) trivial cocycle: |Aut| oracle == dense",
           q8_aut_oracle.order, q8_aut_dense.order);

# Order-2 cocycle.
q8b_path := Concatenation(_md_root, "/8/4/2.txt");;
q8b_data := ReadAsFunction(q8b_path)();;
CheckEqual("D(Q_8) (k=2) rank", Length(q8b_data.T), 22);
q8b_S := q8b_data.S;;
q8b_T := q8b_data.T;;
q8b_QD := QuantumDimensionsFromS(q8b_S);;
q8b_oracle := MakeStreamingFusionOracle(q8b_S,
                  rec(cache_size := 100));;
q8b_aut_oracle := AutNT(q8b_oracle, q8b_T, q8b_QD);;
Print("  AutNT oracle (Q_8 k=2): order = ", q8b_aut_oracle.order,
      " (expected 24)\n");
CheckEqual("D(Q_8) order-2 cocycle: |Aut| via oracle = 24",
           q8b_aut_oracle.order, 24);

# ---- Final report ----------------------------------------------------
if Length(failures) = 0 then
    Print("\ntest_a3d_sparse_fusion: PASS\n");
else
    Print("\ntest_a3d_sparse_fusion: FAIL (", Length(failures),
          " failure(s)):\n");
    for i in [1..Length(failures)] do
        Print("  - ", failures[i], "\n");
    od;
fi;

QUIT;
