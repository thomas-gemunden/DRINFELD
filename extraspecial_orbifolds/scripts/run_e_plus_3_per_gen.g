# Tier 4 per-generator transgression test on E_+(3).
#
# Sweeps all 35 H^3(E_+(3); U(1)) generators and tests, for each class g,
# whether c_g_i is a mod-exp coboundary on C_G(g).
#
# Output: incremental log to /tmp/e_plus_3_per_gen.log, plus a saved
# results table to ../computed/E_plus_3/transgression_per_gen.g for
# resumption / downstream analysis.
#
# Estimated wall: ~22 hours.

Read("transgression_per_generator.g");

OutDir := "../computed/E_plus_3";;
Exec(Concatenation("mkdir -p ", OutDir));
LogPath := "/tmp/e_plus_3_per_gen.log";;
ResultsPath := Concatenation(OutDir, "/transgression_per_gen.g");;

PrintTo(LogPath, "=== E_+(3) per-generator transgression sweep ===\n");
t_start := Runtime();;
AppendTo(LogPath, "Started: Runtime ms = ", t_start, "\n");

G := SmallGroup(128, 2326);;       # E_+(3)
AppendTo(LogPath, "G = E_+(3) = SmallGroup(128, 2326), |G| = ", Order(G), "\n");

t_setup := Runtime();;
setup := SetupCohomology3(G);;
classes := ConjugacyClasses(G);;
n_classes := Length(classes);;
k := setup.num_generators;;
exp := setup.exponent;;
AppendTo(LogPath, "Setup wall: ", (Runtime() - t_setup)/1000., " s\n");
AppendTo(LogPath, "k = ", k, " generators, exp = ", exp, "\n");
AppendTo(LogPath, "torsion = ", setup.torsion, "\n");
AppendTo(LogPath, "# classes = ", n_classes, "\n");

centraliser_orders := List(classes, cl -> Order(Centralizer(G, Representative(cl))));;
AppendTo(LogPath, "centraliser orders: ", Collected(centraliser_orders), "\n\n");

results := [];;
in_kernel := [];;
AppendTo(LogPath, "--- Per-generator sweep ---\n");
for i in [1..k] do
    t_gen := Runtime();
    vec := List([1..k], j -> If_(j = i, 1, 0));
    omega := StandardCocycleOf(setup, vec);
    per_gen := [];
    all_in_kernel_i := true;
    for j in [1..n_classes] do
        t_call := Runtime();
        gRep := Representative(classes[j]);
        C := Centralizer(G, gRep);
        c_g := CGCocycleFunc(omega, gRep);
        isCob := IsCoboundary2(C, c_g, exp);
        Add(per_gen, [j, If_(isCob, 1, 0), (Runtime() - t_call)/1000.]);
        if not isCob then all_in_kernel_i := false; fi;
    od;
    Add(results, per_gen);
    if all_in_kernel_i then Add(in_kernel, i); fi;
    AppendTo(LogPath, "  e_", i, " (order ", setup.torsion[i], "): ",
             If_(all_in_kernel_i, "IN", "NOT"), " kernel  (wall ",
             (Runtime() - t_gen)/1000., " s)\n");

    PrintTo(ResultsPath,
        "# E_+(3) per-generator transgression results (partial; updated incrementally).\n",
        "results := ", results, ";;\n",
        "in_kernel := ", in_kernel, ";;\n",
        "torsion := ", setup.torsion, ";;\n",
        "exp := ", exp, ";;\n",
        "n_classes := ", n_classes, ";;\n",
        "centraliser_orders := ", centraliser_orders, ";;\n");
od;

AppendTo(LogPath, "\n=== Summary ===\n");
AppendTo(LogPath, "Generators IN ker Tr (mod exp): ", Length(in_kernel), " / ", k, "\n");
AppendTo(LogPath, "In-kernel indices: ", in_kernel, "\n");
AppendTo(LogPath, "NOT-in-kernel indices: ", Difference([1..k], in_kernel), "\n");
AppendTo(LogPath, "Total wall (ms): ", Runtime() - t_start, "\n");

QUIT;
