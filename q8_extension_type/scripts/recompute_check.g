# Recompute modular data for Q_8 cocycles 1 (trivial) and 2 (order-2) from
# scratch and compare to the stored Modular_Data/8/4/{1,2}.txt.

Read("../../src/modular_data.g");

G := SmallGroup(8, 4);;
R := ResolutionFiniteGroup(G, 4);;
K := TensorWithIntegers(R);;
UCT := UniversalCoefficientsTheorem(K, 3);;
m := UCT.exponent;;

storedCocycles := ReadAsFunction("Modular_Data/8/4/3-cocycles.txt")();;

for i in [1, 2] do
    Print("\n=== Recomputing cocycle ", i, " (", storedCocycles[i], ") ===\n");
    vec := storedCocycles[i];
    val := Gcd(Concatenation([m], Filtered(vec, x -> x <> 0)));
    if Filtered(vec, x -> x <> 0) = [] then val := m; fi;
    exp := m / val;
    Print("  cocycle order: ", exp, "\n");
    omega := StandardCocycle(R, vec, 3, m);
    fresh := ComputeModularData(G, omega, val, exp);
    stored := LoadModularData(8, 4, i);
    Print("  fresh.S = stored.S? ", fresh.S = stored.S, "\n");
    Print("  fresh.T = stored.T? ", DiagonalMat(DiagonalOfMat(fresh.T)) = stored.T, "\n");
od;

QUIT;
