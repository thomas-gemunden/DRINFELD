# test_steenrod_cup1.g — regression test for the Steenrod cup-1 product
# on bar cochains. Issue #160 (Q-int B2-1).
#
# Run from extraspecial_orbifolds/scripts/:
#   gap -q -b -c 'Read("tests/test_steenrod_cup1.g"); QUIT;'
#
# Anchor group: D_8 = SmallGroup(8, 3). Smallest non-trivial 2-group;
# all cochain identities can be exhaustively verified on (g_1, ..., g_n)
# tuples (|G| = 8, so |G^4| = 4096 — fully tractable).

BreakOnError := false;;

Read("steenrod_cup1.g");
Read("bar_cocycle.g");

Print("\n=== test_steenrod_cup1.g (issue #160) ===\n");

testFailures := [];;
If_loc := function(c, a, b) if c then return a; else return b; fi; end;;
AssertOrLog := function(label, cond)
    Print("  ", label, ": ", If_loc(cond, "PASS", "FAIL"), "\n");
    if not cond then Add(testFailures, label); fi;
end;;

# --------------------------------------------------------------------
# Task 1: F_2 1-classes on D_8 → 1-cochains.
# --------------------------------------------------------------------

Print("\n--- Task 1: F_2 1-cochains via F2HomFromImages ---\n");

G := SmallGroup(8, 3);;
_gens_G := GeneratorsOfGroup(G);;
Print("  |G| = ", Order(G), ", #gens = ", Length(_gens_G), "\n");

# Build two non-trivial F_2 hom classes.
_Z2 := CyclicGroup(IsPermGroup, 2);;
_z2_one := GeneratorsOfGroup(_Z2)[1];;
_z2_id  := Identity(_Z2);;
valid_assignments := [];;
for v in Cartesian(List(_gens_G, g -> [0, 1])) do
    if GroupHomomorphismByImages(G, _Z2, _gens_G,
            List(v, x -> If_loc(x = 0, _z2_id, _z2_one))) <> fail then
        Add(valid_assignments, v);
    fi;
od;
Print("  |valid F_2 hom assignments| = ", Length(valid_assignments),
      " (expected 4 for D_8)\n");

non_zero := Filtered(valid_assignments, v -> Sum(v) > 0);;
x_hom := F2HomFromImages(G, non_zero[1]);;
y_hom := F2HomFromImages(G, non_zero[2]);;

AssertOrLog("F_2 hom x_hom is a bar 1-cocycle (cocycle condition on G^2)",
    ForAll(Tuples(AsList(G), 2),
           t -> (x_hom(t[2]) - x_hom(t[1] * t[2]) + x_hom(t[1])) mod 2 = 0));

# --------------------------------------------------------------------
# Task 2: SteenrodCup1 at (p, q) = (1, 1) → 1-cochain.
# --------------------------------------------------------------------

Print("\n--- Task 2: SteenrodCup1 at (p, q) = (1, 1) ---\n");

cup1_xy := SteenrodCup1(x_hom, 1, y_hom, 1);;
val_sample := cup1_xy(Identity(G));;
AssertOrLog("Cup1 at (1,1) returns an integer",
            IsInt(val_sample));

n_distinct := Length(Set(List(AsList(G), g -> cup1_xy(g))));;
AssertOrLog("Cup1 at (1,1) takes both 0 and 1 on D_8",
            n_distinct = 2);

# --------------------------------------------------------------------
# Task 3: Cup-1 coboundary identity at (p, q) = (1, 1).
# --------------------------------------------------------------------

Print("\n--- Task 3: cup-1 coboundary identity (mod 2) at (1, 1) ---\n");

r_xy := TestBarCup1CoboundaryIdentity(G, x_hom, 1, y_hom, 1);;
Print("  identity on ", r_xy.total,
      " tuples; violations = ", r_xy.violations, "\n");
AssertOrLog("Cup-1 coboundary identity at (1,1) on D_8: 0 violations",
            r_xy.violations = 0);

r_xx := TestBarCup1CoboundaryIdentity(G, x_hom, 1, x_hom, 1);;
Print("  [α=β=x] identity on ", r_xx.total,
      " tuples; violations = ", r_xx.violations, "\n");
AssertOrLog("Cup-1 coboundary identity at (1,1) [α=β] on D_8: 0 violations",
            r_xx.violations = 0);

# --------------------------------------------------------------------
# Task 4: Cup-1 coboundary identity at (p, q) = (2, 1).
# --------------------------------------------------------------------

Print("\n--- Task 4: cup-1 coboundary identity at (2, 1) ---\n");

xx_cup := BarCup(x_hom, 1, x_hom, 1);;
r_xxy := TestBarCup1CoboundaryIdentity(G, xx_cup, 2, y_hom, 1);;
Print("  d((x∪x) ∪₁ y) identity on ", r_xxy.total,
      " tuples; violations = ", r_xxy.violations, "\n");
AssertOrLog("Cup-1 coboundary identity at (2,1) on D_8: 0 violations",
            r_xxy.violations = 0);

# --------------------------------------------------------------------
# Task 5: Cup-1 at (p, q) = (3, 2) — the Pontryagin square shape.
# --------------------------------------------------------------------

Print("\n--- Task 5: cup-1 coboundary identity at (3, 2) [Pontryagin shape] ---\n");

alpha_tilde := function(g, h) return x_hom(g) * y_hom(h); end;;
d_alpha_tilde := BarCoboundary(alpha_tilde, 2);;

r_32 := TestBarCup1CoboundaryIdentity(G, d_alpha_tilde, 3, alpha_tilde, 2);;
Print("  d(dα̃ ∪₁ α̃) identity on ", r_32.total,
      " tuples; violations = ", r_32.violations, "\n");
AssertOrLog("Cup-1 coboundary identity at (3,2) on D_8: 0 violations",
            r_32.violations = 0);

# --------------------------------------------------------------------
# Summary.
# --------------------------------------------------------------------

Print("\n=== Summary ===\n");
if IsEmpty(testFailures) then
    Print("test_steenrod_cup1: ALL PASS\n");
else
    Print("test_steenrod_cup1: FAIL (", Length(testFailures), " failures)\n");
    for f in testFailures do Print("  - ", f, "\n"); od;
fi;
