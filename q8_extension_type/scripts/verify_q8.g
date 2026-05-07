# Verify SmallGroup(8,4) is Q_8 and identify the cocycles unambiguously.

LoadPackage("hap");
LoadPackage("IO");

G := SmallGroup(8, 4);
Print("StructureDescription: ", StructureDescription(G), "\n");
Print("|G|: ", Order(G), "\n");
Print("Center order: ", Order(Center(G)), "\n");
Print("Exponent: ", Exponent(G), "\n");
Print("Element orders: ", Set(List(G, Order)), "\n");
# Q_8 has 1 element of order 1 (identity), 1 element of order 2 (-1), and 6 elements of order 4 (±i, ±j, ±k)
Print("Element-order distribution: ", Collected(List(G, Order)), "\n");
Print("IsAbelian: ", IsAbelian(G), "\n");
# Q_8 is the unique non-abelian group of order 8 in which every subgroup is normal
Print("All subgroups normal? ", ForAll(AllSubgroups(G), N -> IsNormal(G, N)), "\n");

Print("\n--- Cohomology via Gruen's setup ---\n");
R := ResolutionFiniteGroup(G, 4);;
K := TensorWithIntegers(R);;

# Re-implement UCT inline to avoid relying on the Gruen file (we want the genuine values)
cycles := NullspaceIntMat(TransposedMat(BoundaryMatrix(K, 3)));;
boundries := BaseIntMat(TransposedMat(BoundaryMatrix(K, 4)));;
Print("dim K_3: ", K!.dimension(3), "\n");
Print("dim Z_3 (cycles): ", Length(cycles), "\n");
Print("dim B_3 (boundaries): ", Length(boundries), "\n");

# The exponent and torsion structure of H_3(G, Z) using SNF on the cycle/boundary inclusion
# We use Gruen's helper to get the UCT record cleanly.
Read("../../src/modular_data.g");
UCT := UniversalCoefficientsTheorem(K, 3);;
Print("UCT.exponent: ", UCT.exponent, "\n");
Print("UCT.torsion : ", UCT.torsion, "\n");
Print("Length of cocycle vector (= K!.dimension(3)): ", K!.dimension(3), "\n");

Print("\n--- Cocycle orbits as stored ---\n");
orbits := AutomorphismOrbits(G, R, K, UCT);;
Print("Number of orbits: ", Length(orbits), "\n");
Print("Orbit sizes: ", List(orbits, Length), "\n");

# For each orbit, take its first element (this is the homology class as a list mod UCT.exponent)
# and lift it to a cocycle vector.
liftedOrbits := List(orbits, orbit -> UCT.lift * orbit[1]);;

Print("\n--- Comparing first-orbit-rep to what is stored as cocycle 1 ---\n");
storedCocycles := ReadAsFunction("Modular_Data/8/4/3-cocycles.txt")();;
for i in [1..Length(storedCocycles)] do
    Print("Stored ", i, ": ", storedCocycles[i], "\n");
od;

Print("\n--- Cocycle ORDER for each stored vector ---\n");
for i in [1..Length(storedCocycles)] do
    v := storedCocycles[i];
    g := Gcd(Concatenation([UCT.exponent], Filtered(v, x -> x <> 0)));
    if Filtered(v, x -> x <> 0) = [] then g := UCT.exponent; fi;
    Print("  cocycle ", i, " vector ", v,
        "  --> homology element order = ", UCT.exponent/g, "\n");
od;

# Also map: which homology class in Z/8 is each?
# Project a cocycle vector down to H^3 (Z/exponent) by hombasis
Print("\n--- Projection to H^3 ≅ Z/", UCT.exponent, " ---\n");
for i in [1..Length(storedCocycles)] do
    v := storedCocycles[i];
    # The homology class is the orbit element, before lifting.
    # We can recover it as: orbit class = ZZ * v (after taking mod exponent)...
    # but easier: we just have the orbits[i][1] directly.
    # Print orbits[i][1] which is the H^3 vector
    Print("  cocycle ", i, " H^3 class vector: ", orbits[i][1],
          "  (first nonzero entry: ", First(orbits[i][1], x -> x <> 0), ")\n");
od;

# Direct: find which stored cocycle is trivial
Print("\n--- Identify the trivial and order-2 cocycles ---\n");
for i in [1..Length(storedCocycles)] do
    v := storedCocycles[i];
    isZero := ForAll(v, x -> x = 0);
    g := Gcd(Concatenation([UCT.exponent], Filtered(v, x -> x <> 0)));
    if Filtered(v, x -> x <> 0) = [] then g := UCT.exponent; fi;
    ord := UCT.exponent/g;
    if isZero then
        Print("  TRIVIAL  cocycle is at file index ", i, "\n");
    elif ord = 2 then
        Print("  ORDER-2  cocycle is at file index ", i, "\n");
    fi;
od;

QUIT;
