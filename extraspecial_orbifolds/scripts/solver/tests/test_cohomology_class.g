# test_cohomology_class.g — unit test for CohomologyClass2.
#
# CohomologyClass2(C, c, vec, setup) returns the coordinate vector of [c] in
# a fixed basis of H^2(C; Z/exp). For this smoke test we feed the zero
# 2-cochain (built from the zero 3-cocycle on D_8) and demand that the
# resulting coordinate vector is identically zero.
Read("../cohomology_class.g");

# Test: zero cochain projects to the zero coordinate vector.
G := SmallGroup(8, 3);;
setup := SetupCohomology3(G);;
zero_vec := List([1..Length(setup.torsion)], i -> 0);;
omega := StandardCocycleOf(setup, zero_vec);;
classes := ConjugacyClasses(G);;
gRep := Representative(classes[2]);;
C := Centralizer(G, gRep);;
c_g := CGCocycleFunc(omega, gRep);;

coords := CohomologyClass2(C, c_g, zero_vec, setup);;
Assert(0, ForAll(coords, c -> c = 0),
       "zero cochain must project to zero coordinates");
Print("test_cohomology_class: PASS\n");
QUIT;
