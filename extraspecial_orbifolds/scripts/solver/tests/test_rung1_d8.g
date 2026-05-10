# test_rung1_d8.g — full enumeration on D_8 using the new solver.
# Pass criteria: kernel is trivial AND every per-class boolean matches the
# existing IsCoboundary2 baseline.

Read("../iscoboundary2_split.g");

G := SmallGroup(8, 3);;
setup := SetupCohomology3(G);;
classes := ConjugacyClasses(G);;

mismatches := 0;;
for vec in Cartesian(List(setup.torsion, t -> [0..t-1])) do
    omega := StandardCocycleOf(setup, vec);
    for j in [1..Length(classes)] do
        gRep := Representative(classes[j]);
        C := Centralizer(G, gRep);
        c_g := CGCocycleFunc(omega, gRep);
        b_old := IsCoboundary2(C, c_g, setup.exponent);
        b_new := IsCoboundary2Split(C, c_g, vec, setup);
        if b_old <> b_new then
            mismatches := mismatches + 1;
            Print("MISMATCH: vec=", vec, ", class=", j, ": old=", b_old,
                  " new=", b_new, "\n");
        fi;
    od;
od;
Assert(0, mismatches = 0,
       Concatenation(String(mismatches), " mismatches between old and new on D_8"));
Print("test_rung1_d8: PASS (full D_8 enumeration matches baseline)\n");
QUIT;
