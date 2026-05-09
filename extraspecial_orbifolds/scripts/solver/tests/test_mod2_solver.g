# test_mod2_solver.g — unit tests for IsCoboundary2Mod2.
Read("../mod2_solver.g");

# Test 1: the zero cochain on D_8 is trivially a coboundary.
G := SmallGroup(8, 3);;
zero_c := function(h, k) return 0; end;;
Assert(0, IsCoboundary2Mod2(G, zero_c) = true,
       "zero cochain must be a coboundary");

# Test 2: known non-coboundary on Z/2 x Z/2 — the cup product class.
H := SmallGroup(4, 2);;          # C_2 x C_2
elts := AsList(H);;
gens := GeneratorsOfGroup(H);;
# Cup product cocycle: c(h, k) = (h_1)(k_2) where h_1, k_2 are coordinate projections.
# In coordinates with H = <a, b>, c(a, b) = 1, all others 0.
cup_c := function(h, k)
    if h = gens[1] and k = gens[2] then return 1; else return 0; fi;
end;;
Assert(0, IsCoboundary2Mod2(H, cup_c) = false,
       "cup product class on C_2 x C_2 must NOT be a coboundary");

Print("test_mod2_solver: PASS\n");
QUIT;
