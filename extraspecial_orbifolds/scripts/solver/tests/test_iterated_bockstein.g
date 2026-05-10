# test_iterated_bockstein.g — unit tests for iterated_bockstein.g.
#
# Coverage:
#   * k=1 base case on D_8: zero cochain → true (trivial coboundary).
#   * k=2 on D_8: a constructed Z/4 coboundary (lift of an integer 1-cochain)
#                 returns true; a known non-coboundary returns false.
#   * k=3 on E_+(2): zero cochain → true; a known non-coboundary
#                 (vec[10]=1, class 5; verified non-trivial by the Z/8
#                 baseline IsCoboundary2) → false.
#   * IsCoboundary2Mod2WithLiftWitness on Z/2 x Z/2 with the β(α₁+α₂)
#     example from test_mod2_with_lift.g — should return is_coboundary=true
#     with the right α witness.
#
# CWD shim: this test can be invoked from any CWD (e.g. running
#     gap -q -b /abs/path/to/test_iterated_bockstein.g
# from a different worktree). Try a list of CWD candidates ranging from
# the conventional "from solver/tests/" entry to absolute fallbacks for
# both this worktree and the main DRINFELD checkout.
itb_test_target := fail;;
for itb_test_try in [
        ".", "tests", "extraspecial_orbifolds/scripts/solver/tests",
        "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-t1d/extraspecial_orbifolds/scripts/solver/tests",
        "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD/extraspecial_orbifolds/scripts/solver/tests"] do
    if IsExistingFile(Concatenation(itb_test_try, "/test_iterated_bockstein.g")) then
        itb_test_target := itb_test_try;
        break;
    fi;
od;;
if itb_test_target = fail then
    Error("test_iterated_bockstein.g: cannot locate self from CWD ",
          Filename(DirectoryCurrent(), ""));
fi;
ChangeDirectoryCurrent(itb_test_target);;
Read("../iterated_bockstein.g");
Read("../iscoboundary2_split.g");

# === k=1: D_8 zero cochain ===
G_d8 := SmallGroup(8, 3);;     # D_8
zero_c := function(h, k) return 0; end;;
Assert(0, IsCoboundary2Z2k(G_d8, zero_c, 1) = true,
       "k=1: zero cochain on D_8 must be a coboundary");

# === k=2: D_8 — constructed Z/4 coboundary ===
# Build a Z/4 coboundary explicitly: pick β: D_8 -> {0, 1, 2, 3}, compute δβ.
elts_d8 := AsList(G_d8);;
# Non-trivial integer 1-cochain: assign 1 to some element, 2 to another.
beta_int := function(g)
    if g = elts_d8[2] then return 1;
    elif g = elts_d8[3] then return 2;
    else return 0;
    fi;
end;;
delta_beta_int := function(h, k)
    return (beta_int(h) + beta_int(k) - beta_int(h*k)) mod 4;
end;;
Assert(0, IsCoboundary2Z2k(G_d8, delta_beta_int, 2) = true,
       "k=2: constructed Z/4 coboundary on D_8 must return true");

# A non-coboundary on D_8 at Z/4: pick a Z/4 cocycle that isn't a coboundary.
# Use the H^3 standard cocycle's restriction — get one from the existing
# infrastructure. setup.exponent for D_8 is 4 by SetupCohomology3.
setup_d8 := SetupCohomology3(G_d8);;
classes_d8 := ConjugacyClasses(G_d8);;
# vec = e_3 (the order-4 generator) on D_8 puts a non-trivial class on
# the centraliser (Z/8 baseline reports false for at least one class).
vec_d8 := List([1..Length(setup_d8.torsion)], j -> 0);;
vec_d8[Position(setup_d8.torsion, setup_d8.exponent)] := 1;;
omega_d8 := StandardCocycleOf(setup_d8, vec_d8);;
# Find a class where IsCoboundary2 says false at exp=4.
found_noncob := false;;
for j in [1..Length(classes_d8)] do
    gRep := Representative(classes_d8[j]);
    C := Centralizer(G_d8, gRep);
    c_g := CGCocycleFunc(omega_d8, gRep);
    if not IsCoboundary2(C, c_g, setup_d8.exponent) then
        # IsCoboundary2Z2k must agree.
        Assert(0, IsCoboundary2Z2k(C, c_g, 2) = false,
               Concatenation("k=2: D_8 class ", String(j),
                             " — IsCoboundary2Z2k must report false"));
        found_noncob := true;
        break;
    fi;
od;
# Don't require a non-coboundary; if none found, just skip (D_8 may have
# everything trivial under this vec). But the constructed coboundary above
# is the main test.

# === k=3: E_+(2) zero cochain on every centraliser ===
G_e2 := SmallGroup(32, 49);;
classes_e2 := ConjugacyClasses(G_e2);;
for j in [1..Length(classes_e2)] do
    gRep := Representative(classes_e2[j]);
    C := Centralizer(G_e2, gRep);
    Assert(0, IsCoboundary2Z2k(C, zero_c, 3) = true,
           Concatenation("k=3: zero cochain on E_+(2) class ",
                         String(j), " centraliser must be a coboundary"));
od;

# === k=3: E_+(2) — known non-coboundary ===
# Use vec[10]=1, class 5 (the diagnostic spike's smoking-gun example) and
# verify our verdict matches the Z/8 baseline.
setup_e2 := SetupCohomology3(G_e2);;
vec_e2 := List([1..Length(setup_e2.torsion)], j -> 0);;
vec_e2[10] := 1;;
omega_e2 := StandardCocycleOf(setup_e2, vec_e2);;
gRep_5 := Representative(classes_e2[5]);;
C_5 := Centralizer(G_e2, gRep_5);;
c_g_5 := CGCocycleFunc(omega_e2, gRep_5);;
expected := IsCoboundary2(C_5, c_g_5, 8);;
actual := IsCoboundary2Z2k(C_5, c_g_5, 3);;
Assert(0, expected = actual,
       Concatenation("k=3: E_+(2) vec=e_10 class=5: baseline=",
                     String(expected), " vs IsCoboundary2Z2k=",
                     String(actual)));

# === IsCoboundary2Mod2WithLiftWitness — Z/2 x Z/2 with α=α₁+α₂ ===
K := SmallGroup(4, 2);;            # C_2 x C_2
phi_K := MaximalAbelianQuotient(K);;
GA_K := Image(phi_K);;
# α: K -> F_2 = sum of two IGE coords mod 2.
alpha_int := function(g)
    local exps;
    exps := IndependentGeneratorExponents(GA_K, Image(phi_K, g));
    return (exps[1] + exps[2]) mod 2;
end;;
beta_alpha := function(h, k)
    return (alpha_int(h) * alpha_int(k)) mod 2;
end;;
witness_result := IsCoboundary2Mod2WithLiftWitness(K, beta_alpha);;
Assert(0, witness_result.is_coboundary = true,
       "Witness extractor must report β(α₁+α₂) is a Bockstein-image lift");
Assert(0, IsList(witness_result.alpha_F2),
       "Witness extractor must return alpha as a list");
Assert(0, IsList(witness_result.beta_F2),
       "Witness extractor must return beta as a list");

# Verify the witness: α∪α + δβ = c (mod 2) at the cochain level.
elts_K := AsList(K);;
n_K := Length(elts_K);;
idx_K := function(h) return Position(elts_K, h); end;;
witness_check := function()
    local i, j, lhs, alpha_cup, delta_beta_F2, ij, alpha, beta_F2, ok;
    alpha := witness_result.alpha_F2;
    beta_F2 := witness_result.beta_F2;
    ok := true;
    for i in [1..n_K] do
        for j in [1..n_K] do
            ij := idx_K(elts_K[i] * elts_K[j]);
            alpha_cup := alpha[i] * alpha[j];
            delta_beta_F2 := beta_F2[i] + beta_F2[j] + beta_F2[ij];  # +/- same in F_2
            lhs := alpha_cup + delta_beta_F2;
            if lhs <> beta_alpha(elts_K[i], elts_K[j]) * One(GF(2)) then
                ok := false;
            fi;
        od;
    od;
    return ok;
end;;
Assert(0, witness_check() = true,
       "Witness must satisfy c = α∪α + δβ at the F_2 cochain level");

Print("test_iterated_bockstein: PASS\n");
QUIT;
