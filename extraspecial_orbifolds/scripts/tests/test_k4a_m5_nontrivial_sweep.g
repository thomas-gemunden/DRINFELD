# test_k4a_m5_nontrivial_sweep.g — K-4a m=5 non-trivial sweep.
#
# Verifies that `K4aClassify(5, rec(lattice_source := true,
# omega_vec := unit_vec_i))` returns verdict "non-trivial" for the
# first N unit vectors e_i ∈ H^3(E_+(5); U(1)).
#
# Mathematical basis: by AM04 IV.4-IV.5 + Quillen, the restriction
# H^3(E_+(5); U(1)) -> ⊕_H H^3(H; U(1)) over the detecting family
# H ∈ {EA, D_8, Q_8} is injective. So any non-zero class e_i must
# be detected as non-trivial on at least one branch.
#
# Configurable via global K4A_M5_OMEGA_TEST_COUNT (default 5):
#
#   gap -q -b -c 'K4A_M5_OMEGA_TEST_COUNT := 5;  Read("tests/test_k4a_m5_nontrivial_sweep.g"); QUIT;'  # smoke
#   gap -q -b -c 'K4A_M5_OMEGA_TEST_COUNT := 20; Read("tests/test_k4a_m5_nontrivial_sweep.g"); QUIT;'  # medium
#   gap -q -b -c 'K4A_M5_OMEGA_TEST_COUNT := 165; Read("tests/test_k4a_m5_nontrivial_sweep.g"); QUIT;' # full sweep

if not IsBoundGlobal("K4A_M5_OMEGA_TEST_COUNT") then
    K4A_M5_OMEGA_TEST_COUNT := 5;
fi;
N_OMEGAS := Minimum(K4A_M5_OMEGA_TEST_COUNT, 165);;

Read("/Users/thomasgemunden/Projects/group_cohomology/DRINFELD/src/modular_data.g");
Read("k4a_classify.g");

Print("=== K-4a m=5 non-trivial sweep: ", N_OMEGAS, " unit vectors ===\n");
Print("Each unit vector e_i is a non-zero generator of H^3(E_+(5); U(1)),\n");
Print("so K4aClassify should return verdict 'non-trivial' by\n");
Print("AM04 + Quillen detection.\n\n");

total_pass := 0;;
total_fail := 0;;
total_incomplete := 0;;
failures := [];;
t_total_start := Runtime();;

for i in [1..N_OMEGAS] do
    omega_vec := ListWithIdenticalEntries(165, 0);;
    omega_vec[i] := 1;
    t_i := Runtime();
    r := K4aClassify(5, rec(omega_vec := omega_vec, lattice_source := true));
    wall_i := (Runtime() - t_i) / 1000.;
    if r.verdict = "non-trivial" then
        total_pass := total_pass + 1;
        Print("  PASS: e_", i, "/", N_OMEGAS, " -> 'non-trivial' (wall ",
              wall_i, " s)\n");
    elif r.verdict = "trivial" then
        total_fail := total_fail + 1;
        Add(failures, rec(i := i, verdict := "trivial",
                          E := r.E_class, D8 := r.D8_class,
                          Q8 := r.Q8_class));
        Print("  FAIL: e_", i, "/", N_OMEGAS,
              " classified TRIVIAL — should be non-trivial!\n");
    else
        total_incomplete := total_incomplete + 1;
        Add(failures, rec(i := i, verdict := r.verdict,
                          E := r.E_class, D8 := r.D8_class,
                          Q8 := r.Q8_class));
        Print("  INCOMPLETE: e_", i, "/", N_OMEGAS, " -> '",
              r.verdict, "' (one or more branches deferred)\n");
    fi;
od;

wall_total := (Runtime() - t_total_start) / 1000.;;
Print("\n=== Result: ", total_pass, "/", N_OMEGAS, " non-trivial (PASS), ",
      total_fail, " trivial (FAIL), ", total_incomplete,
      " incomplete (wall ", wall_total, " s) ===\n");

if total_fail = 0 and total_incomplete = 0 then
    Print("K-4a m=5 non-trivial sweep (N=", N_OMEGAS, "): GREEN.\n");
    QuitGap(0);
else
    Print("K-4a m=5 non-trivial sweep (N=", N_OMEGAS, "): RED.\n");
    Print("Failures detail:\n");
    for f in failures do
        Print("  e_", f.i, ": verdict=", f.verdict,
              ", E.is_coboundary=", f.E.is_coboundary,
              ", D8.class_idx=", f.D8.class_idx,
              ", Q8.class_idx=", f.Q8.class_idx, "\n");
    od;
    QuitGap(1);
fi;
