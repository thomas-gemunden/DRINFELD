# test_rung2_e_plus_2.g — per-generator booleans on E_+(2) must match baseline.

Read("../iscoboundary2_split.g");

G := SmallGroup(32, 49);;            # E_+(2)
setup := SetupCohomology3(G);;
classes := ConjugacyClasses(G);;

Print("E_+(2) torsion = ", setup.torsion, ", exp = ", setup.exponent, "\n");
Print("# generators k = ", Length(setup.torsion), "\n");
Print("# classes = ", Length(classes), "\n\n");

mismatches := 0;;
for i in [1..Length(setup.torsion)] do
    vec := List([1..Length(setup.torsion)], j -> 0);
    vec[i] := 1;
    omega := StandardCocycleOf(setup, vec);
    all_old := true;
    all_new := true;
    for j in [1..Length(classes)] do
        gRep := Representative(classes[j]);
        C := Centralizer(G, gRep);
        c_g := CGCocycleFunc(omega, gRep);
        if not IsCoboundary2(C, c_g, setup.exponent) then all_old := false; fi;
        if not IsCoboundary2Split(C, c_g, vec, setup) then all_new := false; fi;
    od;
    if all_old <> all_new then
        mismatches := mismatches + 1;
        Print("e_", i, ": old in_kernel = ", all_old, ", new = ", all_new, " — MISMATCH\n");
    else
        Print("e_", i, ": in_kernel = ", all_old, " ✓\n");
    fi;
od;
Assert(0, mismatches = 0, Concatenation(String(mismatches), " per-gen mismatches"));
Print("\ntest_rung2_e_plus_2: PASS\n");
QUIT;
