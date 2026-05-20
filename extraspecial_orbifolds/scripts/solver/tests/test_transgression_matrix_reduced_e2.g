# test_transgression_matrix_reduced_e2.g — anchor test for perf-4' at m=2.
#
# Verifies that KernelOfTransgressionSimple at G = E_+(2) = SmallGroup(32, 49)
# produces:
#   kernel_size = 2048 (matches computed/transgression/2/kernel.g)
#   in_kernel_gens = [1..9] (the 9 order-2 generators in ker)
#   exp_index = 10 (the order-8 generator)
#   half_in_kernel = ?  (need 4*e_10 in ker; ker has order 4 in the
#                        Z/8 axis per the m=2 baseline)
#
# Note: m=2 has torsion [2..2, 8], so half_vec_in_kernel as 2*e_10 = order
# 4 (since gcd(8, 2) = 2, so 2*e_10 has order 8/2 = 4 in Z/8). The
# "half_vec_in_kernel" test here just checks 2*e_10 in ker.
#
# For m=2 the baseline kernel.g says basis has |ker| = 2048 = 2^11 =
# 2^9 (the 9 order-2 generators) × 4 (the <e_10> ∩ ker = <2*e_10> of
# order 4). So 2 * e_10 IS in ker — the "half" entry should be true.
#
# Usage: run from extraspecial_orbifolds/scripts/.
#   gap -q -b -o 8g -c '_SCRIPT_DIR := "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-a7p4/extraspecial_orbifolds/scripts";; ChangeDirectoryCurrent(_SCRIPT_DIR);; Read("solver/tests/test_transgression_matrix_reduced_e2.g");'

_SCRIPT_DIR := "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-a7p4/extraspecial_orbifolds/scripts";;
ChangeDirectoryCurrent(_SCRIPT_DIR);;

Read("solver/transgression_matrix_reduced.g");

Print("\n========= test_transgression_matrix_reduced_e2 =========\n");
t_total := Runtime();;

G := SmallGroup(32, 49);;
Print("G = SmallGroup(32, 49) = E_+(2); |G| = ", Order(G), "\n");

t0 := Runtime();;
result := KernelOfTransgressionSimple(G);;
t_wall := (Runtime() - t0) / 1000.;;

Print("\n--- m=2 anchor check ---\n");
Print("kernel_size: ", result.kernel_size, "\n");
Print("expected:    2048\n");
Print("MATCH: ", result.kernel_size = 2048, "\n");
Print("in_kernel_gens: ", result.in_kernel_gens, "\n");
Print("expected:       [ 1, 2, 3, 4, 5, 6, 7, 8, 9 ]\n");
Print("MATCH: ", result.in_kernel_gens = [1..9], "\n");
Print("exp_index: ", result.exp_index, "  (expected 10)\n");
Print("half_in_kernel (2*e_10 in ker?): ", result.half_in_kernel,
      "  (expected true)\n");

Print("\nTotal wall: ", t_wall, " s\n");
Print("\nkernel_torsion: ", result.kernel_torsion, "\n");
Print("kernel size from kernel_torsion: ", Product(result.kernel_torsion), "\n");

Print("\nAcceptance:\n");
Print("  kernel_size == 2048: ", result.kernel_size = 2048, "\n");
Print("  in_kernel_gens == [1..9]: ", result.in_kernel_gens = [1..9], "\n");
Print("  exp_index == 10: ", result.exp_index = 10, "\n");
Print("  half_in_kernel == true: ", result.half_in_kernel = true, "\n");

Print("\nTotal test wall: ", (Runtime() - t_total) / 1000., " s\n");
QUIT;
