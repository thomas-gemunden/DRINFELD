# Tier 4 kernel for E_+(2) via per-generator + targeted brute-force.
#
# Per-generator (test_transgression_per_gen_e2 with the corrected
# StandardCocycleOf) shows:
#   generators e_1..e_9 (all order 2) are IN ker Tr,
#   generator  e_10     (order 8)      is NOT.
#
# Since all order-2 generators are in the kernel, the only non-trivial
# Tr restricted to a single cyclic factor is on the e_10 axis.  The
# kernel ker Tr ∩ <e_10> = <k * e_10> for the smallest k > 0 such that
# k * e_10 is in the kernel (i.e., all c_g for that vec are
# coboundaries).
#
# So to find ker Tr exactly we brute-force all 8 vec = [0,...,0,k] for
# k = 0..7 and check IsCoboundary2 over all 17 classes.

LogPath := "/tmp/eplus2_full_kernel.log";;
PrintTo(LogPath, "");

Read("transgression_kernel.g");

G := SmallGroup(32, 49);;
setup_G := SetupCohomology3(G);;
classes := ConjugacyClasses(G);;
n_classes := Length(classes);;
k := setup_G.num_generators;;

AppendTo(LogPath, "E_+(2): H^3 torsion = ", setup_G.torsion,
         ", #generators = ", k, ", #classes = ", n_classes, "\n");
AppendTo(LogPath, "Generator e_", k, " has order ", setup_G.torsion[k], "\n\n");

# Per-vec Tr-coboundary test
TestVec := function(vec)
    local omega, i, gRep, c_g, isCob, in_ker;
    omega := StandardCocycleOf(setup_G, vec);
    in_ker := true;
    for i in [1..n_classes] do
        gRep := Representative(classes[i]);
        c_g := CGCocycleFunc(omega, gRep);
        isCob := IsCoboundary2(Centralizer(G, gRep), c_g, setup_G.exponent);
        if not isCob then in_ker := false; break; fi;
    od;
    return in_ker;
end;;

# Brute-force the e_10 axis
AppendTo(LogPath, "--- Brute-force on <e_10> = Z/8 ---\n");
e10_kernel := [];;
for k_e10 in [0..7] do
    vec := List([1..k], j -> 0);
    vec[k] := k_e10;
    in_ker := TestVec(vec);
    AppendTo(LogPath, "  k=", k_e10, "*e_", k, ": ", If_(in_ker, "IN", "NOT"), " kernel\n");
    if in_ker then Add(e10_kernel, k_e10); fi;
od;
AppendTo(LogPath, "\nKernel of Tr on <e_10>: {", e10_kernel, "}\n");

# Determine the order-killer
order_killer := Minimum(Filtered(e10_kernel, k -> k > 0));;
e10_subgroup_in_kernel := 8 / order_killer;;
AppendTo(LogPath, "Smallest k > 0 with k*e_10 in ker = ", order_killer, "\n");
AppendTo(LogPath, "|<e_10> ∩ ker Tr| = ", e10_subgroup_in_kernel, "\n");

# Total kernel size
total_kernel_size := 2^9 * e10_subgroup_in_kernel;;
AppendTo(LogPath, "\n--- Total ker Tr ---\n");
AppendTo(LogPath, "ker Tr order = 2^9 * ", e10_subgroup_in_kernel, " = ", total_kernel_size, "\n");
AppendTo(LogPath, "|H^3(E_+(2); U(1))| = ", Product(setup_G.torsion), "\n");
AppendTo(LogPath, "|coker Tr| = ", Product(setup_G.torsion) / total_kernel_size, "\n");

QUIT;
