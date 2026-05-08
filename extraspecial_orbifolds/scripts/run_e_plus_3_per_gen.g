# Tier 4 per-generator transgression test on E_+(3).
#
# Sweeps all 35 H^3(E_+(3); U(1)) generators and tests, for each class g,
# whether c_g_i is a mod-exp coboundary on C_G(g).
#
# Output: incremental log to /tmp/e_plus_3_per_gen.log, plus a saved
# results table to ../computed/E_plus_3/transgression_per_gen.g for
# resumption / downstream analysis.
#
# Estimated wall time: 35 generators × (2 central classes + 63 non-central)
# × per-call cost. Per-call IsCoboundary2 at:
#   n = 128 (central centralisers): ~2-3 min
#   n = 64  (non-central centralisers): ~30 s
# Total ~ 35 × (2*120 + 63*30) seconds = ~ 22 hours.
#
# The per-gen result alone determines which e_i are in mod-exp ker Tr.
# Generators NOT in mod-exp ker may still be in U(1) ker (Bockstein
# triviality test) -- run that as a follow-up only on the failures.

Read("transgression_per_generator.g");

OutDir := "../computed/E_plus_3";;
Exec(Concatenation("mkdir -p ", OutDir));
LogPath := "/tmp/e_plus_3_per_gen.log";;
ResultsPath := Concatenation(OutDir, "/transgression_per_gen.g");;

PrintTo(LogPath, "");
LogLn := function(s) AppendTo(LogPath, s, "\n"); end;;

LogLn(Concatenation("=== E_+(3) per-generator transgression sweep ==="));
t_start_runtime := Runtime();;
LogLn(Concatenation("Started (Runtime ms): ", String(t_start_runtime)));

G := SmallGroup(128, 2326);;       # E_+(3)
LogLn(Concatenation("G = E_+(3) = SmallGroup(128, 2326), |G| = ", String(Order(G))));

t_setup := Runtime();;
setup := SetupCohomology3(G);;
classes := ConjugacyClasses(G);;
n_classes := Length(classes);;
k := setup.num_generators;;
exp := setup.exponent;;
LogLn(Concatenation("Setup wall: ", String((Runtime() - t_setup)/1000.), " s"));
LogLn(Concatenation("k = ", String(k), " generators, exp = ", String(exp),
                    ", torsion = ", String(setup.torsion)));
LogLn(Concatenation("# classes = ", String(n_classes)));

# Pre-compute centraliser orders
centraliser_orders := List(classes, cl -> Order(Centralizer(G, Representative(cl))));;
LogLn(Concatenation("centraliser orders: ", String(Collected(centraliser_orders))));

# Per-generator sweep
results := [];;     # results[i] = list of [j, isCob (0/1), wall_seconds]
in_kernel := [];;
LogLn("");
LogLn("--- Per-generator sweep ---");
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
    LogLn(Concatenation("  e_", String(i), " (order ", String(setup.torsion[i]), "): ",
                        If_(all_in_kernel_i, "IN", "NOT"), " kernel  (wall ",
                        String((Runtime() - t_gen)/1000.), " s)"));

    # Save partial results after each generator
    PrintTo(ResultsPath,
        "# E_+(3) per-generator transgression results (partial; updated incrementally).\n",
        "results := ", results, ";;\n",
        "in_kernel := ", in_kernel, ";;\n",
        "torsion := ", setup.torsion, ";;\n",
        "exp := ", exp, ";;\n",
        "n_classes := ", n_classes, ";;\n",
        "centraliser_orders := ", centraliser_orders, ";;\n");
od;

LogLn("");
LogLn("=== Summary ===");
LogLn(Concatenation("Generators IN ker Tr (mod exp): ", String(Length(in_kernel)),
                    " / ", String(k)));
LogLn(Concatenation("In-kernel indices: ", String(in_kernel)));
LogLn(Concatenation("NOT-in-kernel indices: ",
                    String(Difference([1..k], in_kernel))));
LogLn(Concatenation("Total wall time (ms): ", String(Runtime() - t_start_runtime)));

QUIT;
