# spike_2divisibility.g — for each order-2 generator e_i of H^3(E_+(2); Z/8),
# compute c_g for one non-central class g and check that all values lie in
# {0, 4} mod 8 (i.e., are 4-divisible).
#
# Background. The plan T-1a Q1 asks whether the standard cocycle representative
# produced by StandardCocycleOf is "r-divisible" for the order-2 generators of
# H^3(G; Z/exp), where r := exp/2.  If yes, the simple formula
#    c'_g = c_g / r mod 2
# works directly.  If no, we need a preprocessing step that finds a divisor-aware
# representative.
#
# E_+(2) = SmallGroup(32, 49) has H^3 torsion [2, 2, 2, 2, 2, 2, 2, 2, 2, 8],
# i.e., 9 order-2 generators (e_1 .. e_9) and one order-8 generator (e_10).
# We check e_1 .. e_9 only; e_10 is path B (order-exp gen, handled separately).
#
# We pick conjugacy class 5 — a non-central class of representative order 2,
# centraliser size 16 (so the inner h × k loop is 256 evaluations per gen).
#
# Note on Read paths. transgression_kernel.g internally does
#     Read("../../src/modular_data.g")
# which is resolved relative to GAP's CWD, not to the calling file. So we
# must cd into the scripts/ dir before reading transgression_kernel.g.
spike_orig_dir := DirectoryCurrent();;
ChangeDirectoryCurrent("../..");;     # extraspecial_orbifolds/scripts/
Read("transgression_kernel.g");
ChangeDirectoryCurrent(Filename(spike_orig_dir, ""));;

G := SmallGroup(32, 49);;            # E_+(2)
setup := SetupCohomology3(G);;
Print("E_+(2) torsion = ", setup.torsion, "\n");
Print("exp = ", setup.exponent, "\n");
expected_divisor := setup.exponent / 2;;     # = 4 for E_+(2)
Print("expected_divisor = exp/2 = ", expected_divisor, "\n");

classes := ConjugacyClasses(G);;
gRep := Representative(classes[5]);;          # non-central class, order 2
Print("Using class 5: rep order = ", Order(gRep), ", class size = ",
      Size(classes[5]), "\n");
C := Centralizer(G, gRep);;
Print("|C_G(gRep)| = ", Order(C), "\n");
elts := AsList(C);;
n := Length(elts);;

ok_all := true;;
for i in [1..Length(setup.torsion)] do
    if setup.torsion[i] <> 2 then continue; fi;
    vec := List([1..Length(setup.torsion)], j -> 0);
    vec[i] := 1;
    omega := StandardCocycleOf(setup, vec);
    c_g := CGCocycleFunc(omega, gRep);
    bad := 0;
    seen_values := [];
    for h in elts do for k in elts do
        v := c_g(h, k) mod setup.exponent;
        if not v in seen_values then Add(seen_values, v); fi;
        if v mod expected_divisor <> 0 then bad := bad + 1; fi;
    od; od;
    Sort(seen_values);
    Print("  e_", i, ": bad = ", bad, " (out of ", n*n,
          "); values seen = ", seen_values, "\n");
    if bad > 0 then ok_all := false; fi;
od;
Print("\nAll order-2 c_g values are ", expected_divisor, "-divisible: ",
      ok_all, "\n");
QUIT;
