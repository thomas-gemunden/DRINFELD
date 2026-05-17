# test_aut_nt_brw_symmetry_m1.g — minimal sanity for #241.
#
# Tests ONLY m=1 (E_+(1) = D_8) — rank 8, fast. Used to validate
# the BRWSimplesAction + AutNTBRWSymmetry plumbing before exercising
# m=2 (rank 184) or m=3 (rank 2272) in the full test.

_SCRIPT_DIR := "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-a3d-p3/extraspecial_orbifolds/scripts";;
ChangeDirectoryCurrent(_SCRIPT_DIR);

Read("aut_nt_partition.g");
Read("fusion_oracle.g");
Read("aut_nt_refine.g");
Read("aut_nt.g");
Read("untwisted_modular_data.g");
Read("em_construction.g");
Read("brw_construction.g");
Read("brw_conjugacy_action.g");
Read("brw_simples_action.g");
Read("aut_nt_brw_symmetry.g");

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

# ----------------------------------------------------------------------
# BRWSimplesAction(1) at m=1: D_8.
# ----------------------------------------------------------------------
Print("\n=== Section: BRWSimplesAction(1) (D_8) ===\n");
t0 := Runtime();;
sa1 := BRWSimplesAction(1);;
t1 := Runtime() - t0;;
Print("  BRWSimplesAction(1) wall: ", t1, " ms\n");

stats1 := BRWSimplesActionStats(sa1);;
Print("  rank             = ", stats1.rank, "\n");
Print("  n_orbits         = ", stats1.n_orbits, "\n");
Print("  orbit sizes      = ", stats1.orbit_sizes, "\n");
Print("  |image_subgroup| = ", stats1.image_order, "\n");

CheckEqual("D_8 rank = 22", sa1.rank, 22);
CheckTrue("D_8 orbits sum to rank", Sum(sa1.orbits, Length) = sa1.rank);
CheckTrue("D_8 orbit_of covers [1..n_orbits]",
          Set(sa1.orbit_of) = [1..sa1.n_orbits]);

# Each gen induces a permutation.
_all_perms := true;;
for _ in sa1.image_lists do
    if Set(_) <> [1..sa1.rank] then _all_perms := false; fi;
od;
CheckTrue("D_8 every BRW gen induces a permutation", _all_perms);

# ----------------------------------------------------------------------
# Equivalence of AutNTBRWSymmetry vs AutNT on D_8.
# ----------------------------------------------------------------------
Print("\n=== Section: equivalence on D_8 ===\n");
t0 := Runtime();;
md1 := ComputeUntwistedModularData(sa1.em);;
t_md1 := Runtime() - t0;;
Print("  md(D_8) wall: ", t_md1, " ms\n");

T_1 := md1.T;;
QD_1 := QuantumDimensionsFromS(md1.S);;
N_1 := FusionCoefficientsFromS(md1.S);;

t0 := Runtime();;
plain1 := AutNT(N_1, T_1, QD_1);;
t_plain1 := Runtime() - t0;;
Print("  plain AutNT order = ", plain1.order, "  (", t_plain1, " ms)\n");

t0 := Runtime();;
brw1 := AutNTBRWSymmetry(1, N_1, T_1, QD_1);;
t_brw1 := Runtime() - t0;;
Print("  brw   AutNT order = ", brw1.order, "  (", t_brw1, " ms)\n");
Print("  brw used_brw_symmetry = ", brw1.used_brw_symmetry, "\n");
Print("  brw refined partition: ", AutNTBRWSymmetryStats(brw1), "\n");

CheckEqual("D_8: AutNT vs AutNTBRWSymmetry order",
           brw1.order, plain1.order);

# ----------------------------------------------------------------------
# Streaming oracle equivalence on D_8: feed both an N tensor and a
# streaming oracle to AutNTBRWSymmetry; results must agree.
# ----------------------------------------------------------------------
Print("\n=== Section: oracle equivalence on D_8 ===\n");
N_1_oracle := MakeStreamingFusionOracle(md1.S, rec(cache_size := 8));;
t0 := Runtime();;
brw1_oracle := AutNTBRWSymmetry(1, N_1_oracle, T_1, QD_1);;
t_brw1_oracle := Runtime() - t0;;
Print("  brw AutNT (oracle) order = ", brw1_oracle.order,
      "  (", t_brw1_oracle, " ms)\n");
CheckEqual("D_8: oracle vs dense AutNTBRWSymmetry order",
           brw1_oracle.order, brw1.order);

# ---- Final report ----------------------------------------------------
if Length(failures) = 0 then
    Print("\ntest_aut_nt_brw_symmetry_m1: PASS\n");
else
    Print("\ntest_aut_nt_brw_symmetry_m1: FAIL (", Length(failures),
          " failure(s)):\n");
    for i in [1..Length(failures)] do
        Print("  - ", failures[i], "\n");
    od;
fi;

QUIT;
