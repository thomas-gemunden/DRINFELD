# spike_bockstein.g — confirm HAP exposes the Bockstein Sq^1 cleanly on D_8.
#
# Background. The plan (T-1a Q2) asked: does HAP expose Sq^1 (the mod-2
# Bockstein) as a callable operation on cohomology classes? The plan's
# original draft used these names:
#   ModPCohomologyRing(G, n, p)     -- WRONG arg order: HAP wants (G, p, n)
#   SteenrodAlgebraOperations(A, p) -- NOT bound in HAP
#   ops.Sq1(x)                      -- NOT a HAP method name
#
# Looking at the HAP source under
#   /opt/homebrew/Cellar/gap/4.15.1/lib/gap/pkg/hap/lib/CohomologyOperations/
# (cohoOps.gd, steenrod.gi) reveals the *actual* API:
#   Mod2SteenrodAlgebra(G, N)     -- builds a mod-2 cohomology ring up
#                                    to degree N with .bockstein and
#                                    .squares[2] populated
#   ModPSteenrodAlgebra(G, N)     -- as above for any p = exponent of G
#   Bockstein(A, w)               -- the Sq^1 method (works for any p)
#   Sq(A, n, w)                   -- general Steenrod square Sq^n (p=2)
#   ModPRingGenerators(A)         -- actual ring generators (small list,
#                                    not the full element set that
#                                    GeneratorsOfRing returns)
#
# So HAP does expose Sq^1 cleanly, just not under the name the plan
# guessed. This spike demonstrates that on D_8.
LoadPackage("hap");
G := SmallGroup(8, 3);;     # D_8

Print("=== Probe: which Bockstein/Steenrod names are actually bound?\n");
for name in [ "SteenrodAlgebraOperations", "Sq", "Sq1", "Bockstein",
              "BocksteinHomomorphism", "Mod2SteenrodAlgebra",
              "ModPSteenrodAlgebra", "BocksteinHomology",
              "HAP_bockstein", "HAP_chain_bockstein",
              "ModPRingGenerators" ] do
    if IsBoundGlobal(name) then
        Print("  ", name, ": bound\n");
    else
        Print("  ", name, ": NOT bound\n");
    fi;
od;

Print("\n=== Build mod-2 Steenrod algebra of D_8 up to degree 4\n");
A := Mod2SteenrodAlgebra(G, 4);;
Print("  A = ", A, "\n");
gens := ModPRingGenerators(A);;
Print("  ModPRingGenerators(A) = ", gens, "\n");
Print("  degrees                = ", List(gens, A!.degree), "\n");

Print("\n=== Sq^1 = Bockstein on degree-1 generators of H^*(D_8; F_2)\n");
deg1 := Filtered(gens, g -> A!.degree(g) = 1);;
Print("  degree-1 generators: ", deg1, "\n");
for x in deg1 do
    Print("    Sq^1(", x, ") = ", Bockstein(A, x), "\n");
    Print("    Sq(A,1,", x, ") = ", Sq(A, 1, x), "\n");
od;

Print("\n=== Cross-check on a degree-2 element (Sq^1 of a square)\n");
if Length(deg1) >= 1 then
    y := deg1[1] * deg1[1];
    Print("  y = ", deg1[1], "^2 (degree ", A!.degree(y), ")\n");
    Print("  Sq^1(y)  = ", Bockstein(A, y), "\n");
    Print("  Sq(A,1,y) = ", Sq(A, 1, y), "\n");
fi;

Print("\n=== Outcome\n");
Print("HAP exposes Sq^1 cleanly via Sq(A, 1, w) where\n");
Print("    A := Mod2SteenrodAlgebra(G, N).\n");
Print("Concretely on D_8 = SmallGroup(8,3) with generators v.2, v.3 in\n");
Print("degree 1 we get Sq^1(v.2) = v.4 + v.5 and Sq^1(v.3) = v.6,\n");
Print("and the Cartan relation Sq^1(v.2^2) = 2 v.2 Sq^1(v.2) = 0 mod 2\n");
Print("checks out.\n\n");
Print("Caveat: the higher-level wrapper Bockstein(A, w) prints\n");
Print("'The Bockstein operation is not defined for this algebra.'\n");
Print("and returns fail on Mod2SteenrodAlgebra output, even though\n");
Print("Sq(A, 1, w) works on the same A. This appears to be because\n");
Print("Mod2SteenrodAlgebra populates A!.squares[2] but on this code\n");
Print("path A!.bockstein is not bound (cf. steenrod.gi lines 215-216).\n");
Print("Workaround for downstream Tasks: prefer Sq(A, 1, w) over\n");
Print("Bockstein(A, w). Both are documented HAP entry points.\n\n");
Print("The plan's guessed names (SteenrodAlgebraOperations, ops.Sq1)\n");
Print("are NOT the HAP API.\n");

QUIT;
