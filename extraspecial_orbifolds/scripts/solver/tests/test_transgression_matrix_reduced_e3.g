# test_transgression_matrix_reduced_e3.g — anchor test for perf-4' at m=3.
#
# LOG_FILE: /tmp/a7p4_m3_test.log (mirror of stdout, line-buffered).
#
# Verifies that KernelOfTransgressionViaMBar at G = E_+(3) (BRW-driven)
# produces:
#   kernel_size = 262144 = 2^18
#   in_kernel_gens = [1,2,3,4,5,6,8,10,11,12,13,14,15,17,18,19,30] (17)
#   exp_index = 35
#   half_vec_in_kernel = true
#
# Reference: computed/transgression/3/kernel.g.
#
# Target wall: < 5 minutes (issue #271 acceptance).

_SCRIPT_DIR := "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-a7p4/extraspecial_orbifolds/scripts";;
ChangeDirectoryCurrent(_SCRIPT_DIR);;

# Dependency: BRW conjugacy + H^3 action + matrices, like run_e_plus_m_kernel_hap.g.
Read("transgression_per_generator_brw.g");
Read("solver/transgression_matrix_reduced.g");

Print("\n========= test_transgression_matrix_reduced_e3 =========\n");
t_total := Runtime();;

# Mirror the unified driver's setup at m=3 (per #266 bug-fix: build setup
# on conj_action.em directly).
m := 3;;
Print("Building BRW conjugacy action for m = ", m, " ...\n");
t_brw := Runtime();;
conj_action := BRWConjugacyAction(m);;
Print("BRWConjugacyAction wall: ", (Runtime() - t_brw) / 1000., " s\n");

G := conj_action.em;;
Print("|G| = ", Order(G), "\n");

Print("Building setup := SetupCohomology3(G) ...\n");
t_setup := Runtime();;
setup := SetupCohomology3(G);;
Print("SetupCohomology3 wall: ", (Runtime() - t_setup) / 1000., " s\n");

# Build BRW H^3 action matrices using consistent setup (m=2/3/5 path).
Print("Building BRW H^3 action matrices ...\n");
t_h3 := Runtime();;
brw_m := BRW(m);;
brw_gens_m := GeneratorsOfGroup(brw_m);;
h3_matrices := [];;
for i in [1..Length(brw_gens_m)] do
    y_i := brw_gens_m[i];
    phi_i := ConjugationAutomorphismThroughIso(G, conj_action.iso_em, y_i);
    M_y := H3MatrixOfAutomorphism(setup, phi_i);
    Add(h3_matrices, M_y);
od;
Print("BRW H^3 matrices wall: ", (Runtime() - t_h3) / 1000., " s\n");

# Build BRW orbits (Schreier-vector BFS, same as run_e_plus_m_kernel_hap.g).
perm_gens := conj_action.perms;;
classes := conj_action.classes;;
n_classes := Length(classes);;
Print("n_classes = ", n_classes, "\n");

visited_all := BlistList([1..n_classes], []);;
orbits_data := [];;
for start_idx in [1..n_classes] do
    if visited_all[start_idx] then continue; fi;
    sv := OrbitWithSchreierVec(perm_gens, n_classes, start_idx);
    for target_idx in sv.orbit do
        visited_all[target_idx] := true;
    od;
    Add(orbits_data, rec(start_idx := start_idx,
                          orbit := sv.orbit,
                          parent := sv.parent,
                          gen_used := sv.gen_used));
od;
Print("Found ", Length(orbits_data), " BRW orbits.\n");

t0 := Runtime();;
result := KernelOfTransgressionViaMBar(setup, orbits_data, classes, G, h3_matrices);;
t_wall := (Runtime() - t0) / 1000.;;

Print("\n--- m=3 anchor check ---\n");
Print("kernel_size: ", result.kernel_size, "\n");
Print("expected:    262144 = 2^18\n");
Print("MATCH: ", result.kernel_size = 262144, "\n");

EXPECTED_IN_KERNEL := [ 1, 2, 3, 4, 5, 6, 8, 10, 11, 12, 13, 14, 15, 17, 18, 19, 30 ];;
Print("in_kernel_gens: ", result.in_kernel_gens, "\n");
Print("expected:       ", EXPECTED_IN_KERNEL, "\n");
Print("MATCH: ", result.in_kernel_gens = EXPECTED_IN_KERNEL, "\n");

Print("exp_index: ", result.exp_index, "  (expected 35)\n");
Print("half_in_kernel (2*e_35 in ker?): ", result.half_in_kernel,
      "  (expected true)\n");

Print("\nWall (KernelOfTransgressionViaMBar): ", t_wall, " s\n");
Print("Total wall: ", (Runtime() - t_total) / 1000., " s\n");

Print("\nAcceptance:\n");
Print("  kernel_size == 262144: ", result.kernel_size = 262144, "\n");
Print("  in_kernel_gens matches: ",
      result.in_kernel_gens = EXPECTED_IN_KERNEL, "\n");
Print("  exp_index == 35: ", result.exp_index = 35, "\n");
Print("  half_in_kernel == true: ", result.half_in_kernel = true, "\n");
Print("  wall < 300s (5 min): ", t_wall < 300., "\n");

QUIT;
