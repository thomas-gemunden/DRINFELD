# test_aut_nt_brw_symmetry_m3_orbits.g — orbit-count smoke for m=3.
#
# Computes only BRWSimplesAction(3) and reports the orbit structure.
# Does NOT run AutNT (deferred to run_e_plus_3_aut.g). Useful for
# checking the expected ~22 orbits at E_+(3) (per issue #241) without
# the full multi-hour pipeline.

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

Print("\n=== BRWSimplesAction(3) (E_+(3), rank 2272) ===\n");
t0 := Runtime();;
sa3 := BRWSimplesAction(3);;
t3 := Runtime() - t0;;
Print("  BRWSimplesAction(3) wall: ", t3, " ms\n");

stats3 := BRWSimplesActionStats(sa3);;
Print("  rank             = ", stats3.rank, "\n");
Print("  n_orbits         = ", stats3.n_orbits, "\n");
Print("  orbit sizes      = ", stats3.orbit_sizes, "\n");
Print("  max orbit        = ", stats3.max_orbit, "\n");
Print("  min orbit        = ", stats3.min_orbit, "\n");
Print("  |image_subgroup| = ", stats3.image_order, "\n");
Print("  expected |image| = 1451520 = |O+(6, F_2)|\n");

CheckEqual("E_+(3) rank = 2272", sa3.rank, 2272);
CheckEqual("E_+(3) orbits sum to rank",
           Sum(sa3.orbits, Length), sa3.rank);
CheckTrue("E_+(3) orbit_of covers [1..n_orbits]",
          Set(sa3.orbit_of) = [1..sa3.n_orbits]);
CheckTrue("E_+(3) every BRW gen induces a permutation",
          ForAll(sa3.image_lists,
                 lst -> Set(lst) = [1..sa3.rank]));
CheckTrue("E_+(3) orbits more than just trivial",
          sa3.n_orbits < sa3.rank);
CheckTrue("E_+(3) orbits ~22 expected per issue #241",
          sa3.n_orbits <= 50);

# ---- Final report ----------------------------------------------------
if Length(failures) = 0 then
    Print("\ntest_aut_nt_brw_symmetry_m3_orbits: PASS\n");
else
    Print("\ntest_aut_nt_brw_symmetry_m3_orbits: FAIL (", Length(failures),
          " failure(s)):\n");
    for i in [1..Length(failures)] do
        Print("  - ", failures[i], "\n");
    od;
fi;

QUIT;
