# test_bar_cocycle.g — Stage B1 acceptance for closed-form bar 3-cocycles.
#
# Verifies that the bar_cocycle.g primitives (F2HomFromImages,
# Cup1x1x1) produce STRICT bar 3-cocycles -- satisfying the
# inhomogeneous bar 3-cocycle equation on every quadruple, not just
# up to homotopy.
#
# This is the V-4a-style acceptance: HAP's StandardCocycle gives
# 448/4096 violations at q=2 on D_8 for the bad basis vec; our
# cup-product cocycles give 0/4096 by construction.
#
# Run from extraspecial_orbifolds/scripts/:
#   gap -q -b -c 'Read("tests/test_bar_cocycle.g");'

BreakOnError := false;;
Read("bar_cocycle.g");

Print("\n=== test_bar_cocycle.g (Quillen integration Stage B1) ===\n");

testFailures := [];;

AssertOrLog := function(label, cond)
    Print("  ", label, ": ", If_(cond, "PASS", "FAIL"), "\n");
    if not cond then Add(testFailures, label); fi;
end;;

# --------------------------------------------------------------------
# D_8 = SmallGroup(8, 3). 3 generators per GAP; G^ab = (Z/2)^2.
# --------------------------------------------------------------------

Print("\n--- D_8: build two non-trivial F_2 homs ---\n");
G := SmallGroup(8, 3);;
gens := GeneratorsOfGroup(G);;
Print("  gens: ", Length(gens), ";  G^ab = ", AbelianInvariants(G), "\n");

# Enumerate F_2-image vectors and keep the valid ones.
valid_assignments := [];;
for v in Cartesian(List(gens, g -> [0, 1])) do
    catch := CALL_WITH_CATCH(F2HomFromImages, [G, v]);
    if catch[1] then Add(valid_assignments, v); fi;
od;
AssertOrLog(Concatenation("|H^1(D_8; F_2)| = 4 (got ",
                           String(Length(valid_assignments)), ")"),
            Length(valid_assignments) = 4);

# Pick the two non-zero "elementary" classes (rank-1 supports).
non_zero := Filtered(valid_assignments, v -> Sum(v) > 0);;
Sort(non_zero, function(a, b) return Sum(a) < Sum(b); end);
# First two non-zero homs.
x_assignment := non_zero[1];;
y_assignment := non_zero[2];;
x := F2HomFromImages(G, x_assignment);;
y := F2HomFromImages(G, y_assignment);;
Print("  x_1 gen-images: ", x_assignment, "\n");
Print("  x_2 gen-images: ", y_assignment, "\n");

# --------------------------------------------------------------------
# Triple cup products: 8 combinations of (x, y) in each slot.
# All should give 0 violations of the bar 3-cocycle equation (mod 2).
# --------------------------------------------------------------------

Print("\n--- Triple cup products: bar 3-cocycle equation (mod 2) ---\n");
homs := [x, y];;
labels := ["x_1", "x_2"];;
for i in [1..2] do for j in [1..2] do for k in [1..2] do
    f := Cup1x1x1(homs[i], homs[j], homs[k]);
    n_viol := VerifyBar3CocycleEquation(G, f, 2);
    AssertOrLog(
        Concatenation(labels[i], " * ", labels[j], " * ", labels[k],
                      " mod 2"),
        n_viol = 0);
od; od; od;

# --------------------------------------------------------------------
# Sanity: at least one triple cup must be non-trivially-zero (not
# just the zero function). Otherwise we're testing nothing.
# --------------------------------------------------------------------

Print("\n--- Triple cups are non-trivial (not all-zero functions) ---\n");
elts := Elements(G);;
some_nontrivial := false;;
for i in [1..2] do for j in [1..2] do for k in [1..2] do
    f := Cup1x1x1(homs[i], homs[j], homs[k]);
    nz := false;
    for g1 in elts do for g2 in elts do for g3 in elts do
        if f(g1, g2, g3) <> 0 then nz := true; break; fi;
    od; if nz then break; fi; od; if nz then break; fi; od;
    if nz then some_nontrivial := true; fi;
od; od; od;
AssertOrLog("at least one triple cup non-trivial", some_nontrivial);

# --------------------------------------------------------------------
# Compare against the V-4a HAP-StandardCocycle baseline: HAP's
# Cocycle gave 448 violations at q=2 for D_8's bad basis vec.
# Our cup products give 0 by construction.
# --------------------------------------------------------------------

Print("\n--- Cross-baseline: vs. HAP StandardCocycle violation counts ---\n");
# Pick x*x*x specifically.
f_xxx := Cup1x1x1(x, x, x);;
v_xxx := VerifyBar3CocycleEquation(G, f_xxx, 2);
Print("  x_1*x_1*x_1: bar-equation violations = ", v_xxx, "/4096\n");
# Compare to the Q_8 V-4a baseline (different group, same phenomenon):
Print("  (HAP StandardCocycle on Q_8 had 448/4096 violations at q=2 ",
      "for bad basis vec; our cup-product approach has 0 by ",
      "construction.)\n");
AssertOrLog("x_1*x_1*x_1 strict bar 3-cocycle", v_xxx = 0);

# --------------------------------------------------------------------
# Stage B2: cup-of-two product Cup1x1 is a bar 2-cocycle.
# --------------------------------------------------------------------

Print("\n--- Cup1x1(x_1, x_2): bar 2-cocycle equation (mod 2) ---\n");
f2 := Cup1x1(x, y);;
n_viol_2 := VerifyBar2CocycleEquation(G, f2, 2);
AssertOrLog("Cup1x1(x_1, x_2) bar 2-cocycle equation",
            n_viol_2 = 0);

# --------------------------------------------------------------------
# Stage B2: Cochain-level Bockstein at degree 1.
# β(x) = x ∪ x. Verify the closed-form formula and that it gives a
# bar 2-cocycle.
# --------------------------------------------------------------------

Print("\n--- BocksteinAt1(x_1): bar 2-cocycle equation ---\n");
beta_x := BocksteinAt1(G, x);;
AssertOrLog("BocksteinAt1(x_1) is a bar 2-cocycle",
            VerifyBar2CocycleEquation(G, beta_x, 2) = 0);

# Verify the formula β(x) = x ∪ x as functions on G × G.
Print("\n--- β(x_1) = x_1 ∪ x_1 (pointwise equality) ---\n");
xux := Cup1x1(x, x);;
match := true;;
for g1 in elts do for g2 in elts do
    if beta_x(g1, g2) <> xux(g1, g2) then match := false; break; fi;
od; if not match then break; fi; od;
AssertOrLog("β(x_1) and x_1 ∪ x_1 agree on all of G × G", match);

# --------------------------------------------------------------------
# Stage B2: Cochain-level Bockstein at degree 2.
# Verify β(x ∪ y) = x²·y + x·y² (the derivation formula).
# --------------------------------------------------------------------

Print("\n--- BocksteinAt2(x_1 ∪ x_2) is a bar 3-cocycle ---\n");
xuy := Cup1x1(x, y);;
beta_xuy := BocksteinAt2(G, xuy);;
AssertOrLog("BocksteinAt2(x_1 ∪ x_2) is a bar 3-cocycle (mod 2)",
            VerifyBar3CocycleEquation(G, beta_xuy, 2) = 0);

# β(x ∪ y) = x²·y + x·y² = (x∪x∪y) + (x∪y∪y) pointwise.
Print("\n--- β(x ∪ y) = x∪x∪y + x∪y∪y pointwise ---\n");
xxy := Cup1x1x1(x, x, y);;
xyy := Cup1x1x1(x, y, y);;
match := true;;
for g1 in elts do for g2 in elts do for g3 in elts do
    if beta_xuy(g1, g2, g3) <> (xxy(g1, g2, g3) + xyy(g1, g2, g3)) mod 2 then
        match := false; break;
    fi;
od; if not match then break; fi; od; if not match then break; fi; od;
AssertOrLog("β(x_1 ∪ x_2) = (x_1∪x_1∪x_2) + (x_1∪x_2∪x_2) on G^3",
            match);

# --------------------------------------------------------------------
# Summary
# --------------------------------------------------------------------

Print("\n=== Summary ===\n");
if IsEmpty(testFailures) then
    Print("test_bar_cocycle: ALL PASS\n");
    Print("Stage B1 acceptance met: cup-product bar 3-cocycles satisfy ",
          "the bar 3-cocycle equation strictly.\n");
else
    Print("test_bar_cocycle: FAIL (", Length(testFailures), " failures)\n");
    for f in testFailures do Print("  - ", f, "\n"); od;
fi;
