# Tests for Q-6 UnitCircleCohomology wrapper.
#
# Acceptance targets from issue #26:
#   * E_+(2) at n=3: torsion = [2^9, 8] (10 divisors).
#   * API parity with transgression_kernel.g::SetupCohomology3.
#   * HAP cross-check: StandardCocycle agrees with HAP's direct path
#     on a fixed evaluation tuple.
#
# Run from this directory:
#   gap -q -b ./test_quillen_h3_u1.g

Read("../quillen_h3_u1.g");

SortedCopy := function(v) local w; w := ShallowCopy(v); Sort(w); return w; end;;

# ---------------------------------------------------------------------
# Test 1: E_+(2) torsion match
# ---------------------------------------------------------------------
Print("--- Test 1: E_+(2) H^3(G; U(1)) torsion via wrapper ---\n");
setup := UnitCircleCohomology(SmallGroup(32, 49), 3);
Print("torsion = ", setup.torsion, "\n");
Print("|torsion| = ", Product(setup.torsion), "\n");
Print("# elementary divisors = ", Length(setup.torsion), "\n");
Print("exponent = ", setup.exponent, "\n");
Assert(0, Length(setup.torsion) = 10,
       Concatenation("E_+(2) H^3(G;U(1)) should have 10 divisors, got ",
                     String(Length(setup.torsion))));
Assert(0, SortedCopy(setup.torsion) = [2,2,2,2,2,2,2,2,2,8],
       Concatenation("E_+(2) torsion expected [2^9, 8], got ",
                     String(setup.torsion)));
Assert(0, setup.exponent = 8,
       Concatenation("E_+(2) exponent should be 8, got ",
                     String(setup.exponent)));

# ---------------------------------------------------------------------
# Test 2: API shape parity with SetupCohomology3
# ---------------------------------------------------------------------
Print("\n--- Test 2: API shape parity ---\n");
required_fields := ["G", "n", "R", "K", "UCT", "torsion", "exponent",
                    "StandardCocycle"];
for f in required_fields do
    Assert(0, IsBound(setup.(f)),
           Concatenation("UnitCircleCohomology missing field: ", f));
od;
Print("setup has fields: ", required_fields, "\n");

required_uct_fields := ["lift", "hombasis", "cyclebasis", "torsion",
                        "exponent"];
for f in required_uct_fields do
    Assert(0, IsBound(setup.UCT.(f)),
           Concatenation("setup.UCT missing field: ", f));
od;
Print("setup.UCT has fields: ", required_uct_fields, "\n");

# ---------------------------------------------------------------------
# Test 3: HAP cross-check on a fixed evaluation tuple
# ---------------------------------------------------------------------
Print("\n--- Test 3: HAP cross-check on a fixed evaluation tuple ---\n");
# Use D_8 = SmallGroup(8, 3) for a quick cross-check — smaller than
# E_+(2) but exercises the same code path.
d8_setup := UnitCircleCohomology(SmallGroup(8, 3), 3);
Print("D_8 torsion = ", d8_setup.torsion, "\n");
Print("D_8 |hombasis| = ", Length(d8_setup.UCT.hombasis), "\n");

# Three group elements for the cocycle evaluation.
G := SmallGroup(8, 3);
elts := Elements(G);
g1 := elts[2];
g2 := elts[3];
g3 := elts[5];
Print("Evaluating cocycle on (g1, g2, g3) = (", g1, ", ", g2, ", ", g3, ")\n");

for i in [1 .. Length(d8_setup.UCT.hombasis)] do
    omega_wrap := d8_setup.StandardCocycle(d8_setup.UCT.hombasis[i]);
    omega_hap := StandardCocycle(d8_setup.R,
                                 d8_setup.UCT.lift * d8_setup.UCT.hombasis[i],
                                 d8_setup.n,
                                 d8_setup.exponent);
    val_wrap := omega_wrap(g1, g2, g3);
    val_hap := omega_hap(g1, g2, g3);
    Print("  generator ", i, ": wrapper=", val_wrap,
          ", HAP=", val_hap, "\n");
    Assert(0, val_wrap = val_hap,
           Concatenation("Generator ", String(i),
                         ": wrapper output ", String(val_wrap),
                         " disagrees with HAP ", String(val_hap)));
od;
Print("All ", Length(d8_setup.UCT.hombasis), " generators match HAP.\n");

# Note: the wrapper errors out cleanly on n != 3 (see the gate inside
# UnitCircleCohomology).  GAP's Error() is not catchable in a stable
# cross-version way, so we verify the gate by inspection rather than
# in an asserted test.

Print("\ntest_quillen_h3_u1: PASS\n");
QUIT;
