# test_mod2_solver.g — unit tests for IsCoboundary2Mod2.
Read("../mod2_solver.g");

# Test 1: a genuine coboundary roundtrip on D_8.
G := SmallGroup(8, 3);;     # D_8
elts := AsList(G);;
# Define a non-zero 1-cochain beta : G -> Z/2 (here: indicator of one element).
beta := function(g) if g = elts[3] then return 1; else return 0; fi; end;;
# Its coboundary: dβ(h, k) = β(h) - β(hk) + β(k) mod 2 = β(h) + β(hk) + β(k) mod 2.
delta_beta := function(h, k)
    return (beta(h) + beta(h*k) + beta(k)) mod 2;
end;;
Assert(0, IsCoboundary2Mod2(G, delta_beta) = true,
       "δβ for a non-zero β must be a coboundary");

# Test 2: known non-coboundary on Z/2 x Z/2 — an asymmetric cochain.
H := SmallGroup(4, 2);;          # C_2 x C_2
elts := AsList(H);;
gens := GeneratorsOfGroup(H);;
# An asymmetric cochain that cannot be a coboundary because the coboundary δβ
# on a commutative group satisfies δβ(h, k) = δβ(k, h), but our cochain has
# c(a, b) = 1 ≠ 0 = c(b, a).
cup_c := function(h, k)
    if h = gens[1] and k = gens[2] then return 1; else return 0; fi;
end;;
Assert(0, IsCoboundary2Mod2(H, cup_c) = false,
       "asymmetric cochain on C_2 x C_2 must NOT be a coboundary");

Print("test_mod2_solver: PASS\n");
QUIT;
