# test_split_dispatch.g — smoke test for the public dispatcher.
#
# On D_8, torsion = [2, 2, 4], exponent = 4. The dispatcher routes:
#   * the two order-2 unit vectors through Path A (mod-2 + Bockstein lift),
#   * the order-4 unit vector through Path Z (Z/exp fallback),
#   * the zero vector through Path A trivially.
#
# Each call's result is compared against the slow baseline IsCoboundary2.
Read("../iscoboundary2_split.g");

G := SmallGroup(8, 3);;     # D_8
setup := SetupCohomology3(G);;
classes := ConjugacyClasses(G);;
gRep := Representative(classes[2]);;
C := Centralizer(G, gRep);;

# Test 1: zero vec -> trivial cocycle -> coboundary on every class.
zero_vec := List([1..Length(setup.torsion)], i -> 0);;
omega := StandardCocycleOf(setup, zero_vec);;
c_g := CGCocycleFunc(omega, gRep);;
Assert(0, IsCoboundary2Split(C, c_g, zero_vec, setup) = true,
       "zero class is always a coboundary");

# Test 2: each unit vector e_i should match the existing IsCoboundary2 result.
for i in [1..Length(setup.torsion)] do
    vec := List([1..Length(setup.torsion)], j -> 0);
    vec[i] := 1;
    omega := StandardCocycleOf(setup, vec);
    c_g := CGCocycleFunc(omega, gRep);
    expected := IsCoboundary2(C, c_g, setup.exponent);
    actual   := IsCoboundary2Split(C, c_g, vec, setup);
    Assert(0, expected = actual,
           Concatenation("e_", String(i), ": split disagrees with baseline"));
od;
Print("test_split_dispatch: PASS\n");
QUIT;
