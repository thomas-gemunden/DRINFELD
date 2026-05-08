# Linearity-based variant of the transgression-kernel test.
# Instead of brute-force enumerating every H^3 class, evaluate the
# transgression on each *generator* of H^3, and check coboundary-ness
# of c_g for each conjugacy class g.
#
# If Tr(e_i) ≠ 0 for many generators e_i, the kernel of Tr is "small".
# A more thorough kernel computation would form the full matrix of Tr
# (between abelian groups) and compute its kernel via SNF, but the
# per-generator pattern is already informative.

Read("transgression_kernel.g");

# For a generator e_i (the i-th basis element of H^3), this returns
# its transgression status: a record with
#   .generator: i
#   .vec: the e_i vector in (Z/m)^k
#   .per_class: list of [class_index, |C_g|, IsCoboundary2 result]
#   .all_in_kernel: true iff every c_g is a coboundary
TestGenerator := function(setup, i, classes)
    local k, vec, omega, j, gRep, c_g, isCob, results, allIn;
    k := setup.num_generators;
    vec := List([1..k], j -> 0);
    vec[i] := 1;
    omega := StandardCocycleOf(setup, vec);
    results := [];
    allIn := true;
    for j in [1..Length(classes)] do
        gRep := Representative(classes[j]);
        c_g := CGCocycleFunc(omega, gRep);
        isCob := IsCoboundary2(Centralizer(setup.group, gRep), c_g,
                               setup.exponent);
        Add(results, [j, Order(Centralizer(setup.group, gRep)), isCob]);
        if not isCob then allIn := false; fi;
    od;
    return rec(generator := i, vec := vec, per_class := results,
               all_in_kernel := allIn);
end;;

TestAllGenerators := function(G)
    local setup, classes, k, summary, i, r, count_in_kernel,
          witness_classes, witness_set;
    setup := SetupCohomology3(G);
    classes := ConjugacyClasses(G);
    k := setup.num_generators;
    Print("\n=== Per-generator transgression test for ",
          StructureDescription(G), " ===\n");
    Print("|G| = ", Order(G), "\n");
    Print("|H^3(G; U(1))| = ", setup.num_h3_classes, "\n");
    Print("UCT.torsion = ", setup.torsion, "\n");
    Print("Number of generators of H^3: ", k, "\n");
    Print("Number of conjugacy classes: ", Length(classes), "\n");
    summary := [];
    count_in_kernel := 0;
    witness_set := [];
    for i in [1..k] do
        r := TestGenerator(setup, i, classes);
        Add(summary, r);
        if r.all_in_kernel then
            count_in_kernel := count_in_kernel + 1;
            Print("  generator ", i, ": IN kernel\n");
        else
            witness_classes := Filtered(r.per_class, p -> not p[3]);
            Print("  generator ", i, ": NOT in kernel; witness classes ",
                  List(witness_classes, p -> p[1]), "\n");
            for p in witness_classes do
                AddSet(witness_set, p[1]);
            od;
        fi;
    od;
    Print("\nGenerators with Tr(e_i) = 0: ", count_in_kernel, " / ", k, "\n");
    Print("Witness conjugacy classes (those that detect non-kernel): ",
          witness_set, "\n");
    return rec(setup := setup, classes := classes, summary := summary,
               count_in_kernel := count_in_kernel,
               witness_classes := witness_set);
end;;
