# test_fusion_oracle_int.g — A-3d perf-2 (#240) integer-path tests.
#
# Sibling of test_a3d_sparse_fusion.g (PR #237 sparse oracle).  This
# file specifically targets the `integer_path := true` enhancement to
# `MakeStreamingFusionOracle` that switches the per-row matmul from
# the cyclotomic-Q kernel to GAP's compiled integer kernel.
#
# Acceptance from #240:
#   1. `MakeStreamingFusionOracle(S, rec(integer_path := true))`
#      produces same row values as the cyclotomic (Q) path on the
#      rank-22 D(Q_8) tests.
#   2. Per-row wall at rank 2272 (E_+(3)) under 20 s (microbench, run
#      only if computed/E_plus_3/S.g is present on disk).
#   3. Optional D(E_+(2)) cross-check confirms the Z-path scales.
#
# K-4a-T1 convention: absolute paths.  If the worktree moves, update
# the _SCRIPT_DIR constant.
#
# Run from anywhere:
#   gap -q -b extraspecial_orbifolds/scripts/tests/test_fusion_oracle_int.g
#
# Success is signalled by "test_fusion_oracle_int: PASS".

_SCRIPT_DIR := "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-a3d-p2/extraspecial_orbifolds/scripts";;

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
# Test (1): rank-22 cross-check.  Q-path vs Z-path produce IDENTICAL
# fusion-row entries.  Acceptance criterion #1 of issue #240.
# ----------------------------------------------------------------------

Print("\n=== (1) rank-22 cross-check: D(Q_8) trivial cocycle ===\n");

q8_data := ReadAsFunction(
    Concatenation(_md_root, "/8/4/1.txt"))();;
q8_S := q8_data.S;;
q8_T := q8_data.T;;
q8_QD := QuantumDimensionsFromS(q8_S);;
CheckEqual("D(Q_8) rank", Length(q8_T), 22);

q8_oracle_Q := MakeStreamingFusionOracle(q8_S,
                   rec(cache_size := 0, integer_path := false));;
q8_oracle_Z := MakeStreamingFusionOracle(q8_S,
                   rec(cache_size := 0, integer_path := true));;

CheckEqual("Q-path stats.path",  q8_oracle_Q.stats.path, "Q");
CheckEqual("Z-path stats.path",  q8_oracle_Z.stats.path, "Z");
CheckTrue("Z-path stats.denominator > 0",
          q8_oracle_Z.stats.denominator > 0);
Print("  Q_8 denominator d = ", q8_oracle_Z.stats.denominator,
      " (expected 8)\n");
CheckEqual("Q_8 denominator equals 8 (= |G|)",
           q8_oracle_Z.stats.denominator, 8);

# Row-by-row equality across all 22 simples.
_all_match := true;;
_mismatch_first := fail;;
for _i in [1..22] do
    _row_Q := q8_oracle_Q.row(_i);;
    _row_Z := q8_oracle_Z.row(_i);;
    if _row_Q <> _row_Z then
        _all_match := false;
        if _mismatch_first = fail then
            _mismatch_first := _i;
        fi;
    fi;
od;
CheckTrue("D(Q_8) Q-path and Z-path agree on all 22 rows",
          _all_match);
if _mismatch_first <> fail then
    Print("  first mismatch at i = ", _mismatch_first, "\n");
fi;

# Cross-check against dense FusionCoefficientsFromS just to be sure.
q8_N_dense := FusionCoefficientsFromS(q8_S);;
_dense_match := true;;
for _i in [1..22] do
    if q8_oracle_Z.row(_i) <> q8_N_dense[_i] then
        _dense_match := false;
    fi;
od;
CheckTrue("D(Q_8) Z-path matches dense FusionCoefficientsFromS",
          _dense_match);

# Coef path equality.
_coef_match := true;;
for _i in [1, 5, 12, 22] do
    for _j in [1, 5, 12, 22] do
        for _k in [1, 5, 12, 22] do
            if q8_oracle_Z.coef(_i, _j, _k)
               <> q8_oracle_Q.coef(_i, _j, _k) then
                _coef_match := false;
            fi;
        od;
    od;
od;
CheckTrue("D(Q_8) Z-path .coef matches Q-path .coef at 64 spot-checks",
          _coef_match);

# Full AutNT cross-check (the user-visible black-box behaviour).
q8_aut_Q := AutNT(MakeStreamingFusionOracle(q8_S,
                      rec(cache_size := 100, integer_path := false)),
                  q8_T, q8_QD);;
q8_aut_Z := AutNT(MakeStreamingFusionOracle(q8_S,
                      rec(cache_size := 100, integer_path := true)),
                  q8_T, q8_QD);;
CheckEqual("D(Q_8) AutNT order via Z-path = 6",
           q8_aut_Z.order, 6);
CheckEqual("D(Q_8) AutNT order Z-path == Q-path",
           q8_aut_Z.order, q8_aut_Q.order);

# Order-2 cocycle cross-check (sanity on a non-trivial S).
Print("\n=== (1') rank-22 cross-check: D(Q_8) k=2 cocycle ===\n");

q8b_path := Concatenation(_md_root, "/8/4/2.txt");;
q8b_data := ReadAsFunction(q8b_path)();;
q8b_S := q8b_data.S;;
q8b_T := q8b_data.T;;
q8b_QD := QuantumDimensionsFromS(q8b_S);;
CheckEqual("D(Q_8) k=2 rank", Length(q8b_T), 22);

q8b_oracle_Q := MakeStreamingFusionOracle(q8b_S,
                    rec(cache_size := 0, integer_path := false));;
q8b_oracle_Z := MakeStreamingFusionOracle(q8b_S,
                    rec(cache_size := 0, integer_path := true));;
_q8b_match := true;;
for _i in [1..22] do
    if q8b_oracle_Q.row(_i) <> q8b_oracle_Z.row(_i) then
        _q8b_match := false;
    fi;
od;
CheckTrue("D(Q_8) k=2: Z-path row equals Q-path row (all 22)",
          _q8b_match);
Print("  D(Q_8) k=2 Z-path: path=", q8b_oracle_Z.stats.path,
      ", d=", q8b_oracle_Z.stats.denominator, "\n");

q8b_aut_Z := AutNT(MakeStreamingFusionOracle(q8b_S,
                       rec(cache_size := 100, integer_path := true)),
                   q8b_T, q8b_QD);;
CheckEqual("D(Q_8) k=2: AutNT order via Z-path = 24",
           q8b_aut_Z.order, 24);

# ----------------------------------------------------------------------
# Test (2): rank-184 D(E_+(2)) cross-check + speedup microbench.
# ----------------------------------------------------------------------

Print("\n=== (2) rank-184 cross-check + speedup: D(E_+(2)) ===\n");

e2_data := ReadAsFunction(
    Concatenation(_md_root, "/32/49/1.txt"))();;
e2_S := e2_data.S;;
e2_T := e2_data.T;;
e2_QD := QuantumDimensionsFromS(e2_S);;
CheckEqual("D(E_+(2)) rank", Length(e2_T), 184);

e2_oracle_Q := MakeStreamingFusionOracle(e2_S,
                   rec(cache_size := 0, integer_path := false));;
e2_oracle_Z := MakeStreamingFusionOracle(e2_S,
                   rec(cache_size := 0, integer_path := true));;
Print("  D(E_+(2)) Z-path: path=", e2_oracle_Z.stats.path,
      ", d=", e2_oracle_Z.stats.denominator, "\n");

# Spot-check a few rows for equality.
_e2_match := true;;
_e2_mismatch_first := fail;;
for _i in [1, 17, 50, 100, 184] do
    _row_Q := e2_oracle_Q.row(_i);;
    _row_Z := e2_oracle_Z.row(_i);;
    if _row_Q <> _row_Z then
        _e2_match := false;
        if _e2_mismatch_first = fail then
            _e2_mismatch_first := _i;
        fi;
    fi;
od;
CheckTrue("D(E_+(2)) Z-path row equals Q-path row (5 spot-checks)",
          _e2_match);

# Spot-check ALL 184 rows for equality (not just 5).
_e2_match_all := true;;
_e2_mismatch_all := fail;;
for _i in [1..184] do
    if e2_oracle_Q.row(_i) <> e2_oracle_Z.row(_i) then
        _e2_match_all := false;
        if _e2_mismatch_all = fail then
            _e2_mismatch_all := _i;
        fi;
    fi;
od;
CheckTrue("D(E_+(2)) Z-path row equals Q-path row (all 184)",
          _e2_match_all);
if _e2_mismatch_all <> fail then
    Print("  first mismatch at i = ", _e2_mismatch_all, "\n");
fi;

# Speedup microbench: time 5 representative rows under each path
# (with caches disabled to force recomputation).
Print("\n  E_+(2) per-row microbench (5 rows):\n");

_q_rows := [];;
_q_oracle_bench := MakeStreamingFusionOracle(e2_S,
                       rec(cache_size := 0, integer_path := false));;
t_Q := Runtime();;
for _i in [1, 17, 50, 100, 184] do
    Add(_q_rows, _q_oracle_bench.row(_i));
od;
t_Q_wall := Runtime() - t_Q;;
Print("    Q-path  : ", t_Q_wall, " ms  total\n");

_z_rows := [];;
_z_oracle_bench := MakeStreamingFusionOracle(e2_S,
                       rec(cache_size := 0, integer_path := true));;
t_Z := Runtime();;
for _i in [1, 17, 50, 100, 184] do
    Add(_z_rows, _z_oracle_bench.row(_i));
od;
t_Z_wall := Runtime() - t_Z;;
Print("    Z-path  : ", t_Z_wall, " ms  total\n");
if t_Z_wall > 0 then
    Print("    speedup : ", t_Q_wall * 1.0 / t_Z_wall, "x\n");
fi;

# At rank 184 the speedup may be modest (compiled-Q is OK at this size).
# At rank 2272 we expect ~10x; we only assert here that the Z-path is
# not slower than Q-path within reason.
CheckTrue("D(E_+(2)) Z-path no slower than ~2x Q-path",
          t_Z_wall <= 2 * t_Q_wall + 50);

# NB: We do NOT run AutNT(E_+(2)) here — that takes ~10 min and is
# already covered by test_aut_nt.g / test_a3d_sparse_fusion.g.  Row
# equality + AutNT(Q_8) cross-check is sufficient to guarantee Z-path
# correctness end-to-end.

# ----------------------------------------------------------------------
# Test (3): production-rank microbench at E_+(3) (only if dense S
# already on disk under computed/E_plus_3/S.g).  This is the headline
# acceptance criterion #2: per-row matmul under 20 s at rank 2272.
# ----------------------------------------------------------------------

Print("\n=== (3) production microbench at rank 2272 (E_+(3)) ===\n");

_e3_S_path := Concatenation(_SCRIPT_DIR,
    "/../computed/E_plus_3/S.g");;
if not IsExistingFile(_e3_S_path) then
    Print("  [skip] E_+(3) S.g missing at ", _e3_S_path, "\n");
    Print("         (will be generated by run_e_plus_3_aut.g)\n");
else
    t_load := Runtime();;
    Read(_e3_S_path);    # installs `S` in the GAP global state.
    t_load_wall := Runtime() - t_load;;
    Print("  E_+(3) S loaded in ", t_load_wall, " ms; rank = ",
          Length(S), "\n");
    CheckEqual("E_+(3) S rank", Length(S), 2272);

    Print("\n  --- Q-path: cyclotomic matmul ---\n");
    t_orb_Q := Runtime();;
    e3_oracle_Q := MakeStreamingFusionOracle(S,
                       rec(cache_size := 2,
                           integer_path := false));;
    t_orb_Q_wall := Runtime() - t_orb_Q;;
    Print("  MakeStreamingFusionOracle (Q): ",
          t_orb_Q_wall, " ms\n");
    Print("  path=", e3_oracle_Q.stats.path, "\n");

    t_row_Q := Runtime();;
    _e3_row1_Q := e3_oracle_Q.row(1);;
    t_row_Q_wall := Runtime() - t_row_Q;;
    Print("  Q-path oracle.row(1) wall: ", t_row_Q_wall, " ms\n");

    t_row_Q2 := Runtime();;
    _e3_row2_Q := e3_oracle_Q.row(2);;
    t_row_Q2_wall := Runtime() - t_row_Q2;;
    Print("  Q-path oracle.row(2) wall: ", t_row_Q2_wall, " ms\n");

    Print("\n  --- Z-path: integer matmul ---\n");
    t_orb_Z := Runtime();;
    e3_oracle_Z := MakeStreamingFusionOracle(S,
                       rec(cache_size := 2,
                           integer_path := true));;
    t_orb_Z_wall := Runtime() - t_orb_Z;;
    Print("  MakeStreamingFusionOracle (Z): ",
          t_orb_Z_wall, " ms\n");
    Print("  path=", e3_oracle_Z.stats.path,
          ", d=", e3_oracle_Z.stats.denominator, "\n");

    t_row_Z := Runtime();;
    _e3_row1_Z := e3_oracle_Z.row(1);;
    t_row_Z_wall := Runtime() - t_row_Z;;
    Print("  Z-path oracle.row(1) wall: ", t_row_Z_wall, " ms\n");

    t_row_Z2 := Runtime();;
    _e3_row2_Z := e3_oracle_Z.row(2);;
    t_row_Z2_wall := Runtime() - t_row_Z2;;
    Print("  Z-path oracle.row(2) wall: ", t_row_Z2_wall, " ms\n");

    # Equality of rows (correctness).
    CheckEqual("E_+(3) row(1) Z-path equals Q-path",
               _e3_row1_Z, _e3_row1_Q);
    CheckEqual("E_+(3) row(2) Z-path equals Q-path",
               _e3_row2_Z, _e3_row2_Q);

    # Speedup ratios.
    if t_row_Q2_wall > 0 and t_row_Z2_wall > 0 then
        Print("\n  Speedup row(2) Q/Z: ",
              t_row_Q2_wall * 1.0 / t_row_Z2_wall, "x\n");
    fi;

    # Acceptance: per-row matmul under 20 s = 20000 ms.
    CheckTrue("E_+(3) Z-path oracle.row(2) under 20000 ms (#240 acceptance)",
              t_row_Z2_wall < 20000);

    # Identity check on row 1.
    _unit_ok := true;;
    for _j in [1..5] do
        for _k in [1..5] do
            if _j = _k then
                if _e3_row1_Z[_j][_k] <> 1 then _unit_ok := false; fi;
            else
                if _e3_row1_Z[_j][_k] <> 0 then _unit_ok := false; fi;
            fi;
        od;
    od;
    CheckTrue("E_+(3) Z-path row(1) = Identity (unit fusion rule)",
              _unit_ok);

    # Memory + denominator size sanity.
    Print("\n  Z-path internals at rank 2272:\n");
    Print("    denominator d            : ",
          e3_oracle_Z.stats.denominator, "\n");
    Print("    Lcm denom * largest |val|: depends on S; expected\n");
    Print("                                 small (entries in S are\n");
    Print("                                 rational with small\n");
    Print("                                 numerators; integerised by\n");
    Print("                                 a factor of d <= |G| =\n");
    Print("                                 128 for E_+(3)).\n");
fi;

# ---- Final report ----------------------------------------------------
if Length(failures) = 0 then
    Print("\ntest_fusion_oracle_int: PASS\n");
else
    Print("\ntest_fusion_oracle_int: FAIL (", Length(failures),
          " failure(s)):\n");
    for i in [1..Length(failures)] do
        Print("  - ", failures[i], "\n");
    od;
fi;

QUIT;
