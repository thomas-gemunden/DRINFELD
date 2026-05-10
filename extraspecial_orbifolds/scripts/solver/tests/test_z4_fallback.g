# test_z4_fallback.g
Read("../z4_fallback.g");

# Test: zero cochain on D_8 at exp = 8 — trivially a coboundary.
G := SmallGroup(8, 3);;
zero_c := function(h, k) return 0; end;;
Assert(0, IsCoboundary2Zexp(G, zero_c, 8) = true,
       "zero Z/8 cochain must be a coboundary");

Print("test_z4_fallback: PASS\n");
QUIT;
