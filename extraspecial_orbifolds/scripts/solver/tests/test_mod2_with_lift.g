# test_mod2_with_lift.g — unit tests for IsCoboundary2Mod2WithLift.
#
# Two assertions:
#   (1) Trivial: zero cochain on D_8 lifts trivially.
#   (2) Corrected-algorithm regression: on Z/2 x Z/2, the cochain
#       β(α₁+α₂)(h, k) = α(h)·α(k) with α := α₁+α₂ (sum of the two
#       projections) is a Bockstein image as a *cohomology* class, so
#       IsCoboundary2Mod2WithLift must return true. At the cochain level
#       β(α₁+α₂) ≠ β(α₁) + β(α₂); they differ by α₁∪α₂ + α₂∪α₁ which is
#       a coboundary. A naive "in row span of BocksteinH1ToH2 output"
#       check would return false here.
Read("../mod2_solver.g");

# (1) Sanity: trivial cochain returns true.
G := SmallGroup(8, 3);;
zero_c := function(h, k) return 0; end;;
Assert(0, IsCoboundary2Mod2WithLift(G, zero_c) = true,
       "zero cochain must lift trivially");

# (2) On K = Z/2 x Z/2, build α := α₁ + α₂ and feed β(α) as a cochain.
K := SmallGroup(4, 2);;            # C_2 x C_2
elts := AsList(K);;
phi := MaximalAbelianQuotient(K);;
GA := Image(phi);;
abgens := IndependentGeneratorsOfAbelianGroup(GA);;
# α : K -> F_2 (as Int) defined as the sum mod 2 of the two IGE coordinates.
alpha_int := function(g)
    local exps;
    exps := IndependentGeneratorExponents(GA, Image(phi, g));
    return (exps[1] + exps[2]) mod 2;
end;;
beta_alpha := function(h, k)
    return (alpha_int(h) * alpha_int(k)) mod 2;
end;;

# Sanity: α is non-zero on at least one element (so β(α) is non-zero too).
Assert(0, ForAny(elts, g -> alpha_int(g) = 1),
       "α₁+α₂ must be non-zero on K");

# β(α) is NOT a Z/2 coboundary: α∪α with α a non-trivial F_2 hom on
# an elementary-abelian 2-group represents a non-zero class in H^2(K; F_2).
Assert(0, IsCoboundary2Mod2(K, beta_alpha) = false,
       "β(α₁+α₂) is not a Z/2 coboundary on Z/2 x Z/2");

# But it IS in the Bockstein image (as a cohomology class), so
# IsCoboundary2Mod2WithLift must return true.
Assert(0, IsCoboundary2Mod2WithLift(K, beta_alpha) = true,
       "β(α₁+α₂) on Z/2 x Z/2 must lift to a Z/4 coboundary (Bockstein image)");

Print("test_mod2_with_lift: PASS\n");
QUIT;
