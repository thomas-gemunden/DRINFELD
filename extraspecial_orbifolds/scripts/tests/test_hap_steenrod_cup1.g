# test_hap_steenrod_cup1.g — initial regression for B3-1.
#
# Issue #170. Tests the symmetric F_2 cup-1 product on HAP's resolution.
#
# Anchor at D_8. The symmetric cup-1 of a 1-cocycle x with itself gives
# the chain-level representative of Sq^0(x ∪ x) = x ∪ x at cohomology
# level, modulo coboundaries.

BreakOnError := false;;

LoadPackage("hap");

Read("hap_steenrod_cup1.g");

Print("\n=== test_hap_steenrod_cup1.g (issue #170 first impl) ===\n");

testFailures := [];;
If_loc := function(c, a, b) if c then return a; else return b; fi; end;;
AssertOrLog := function(label, cond)
    Print("  ", label, ": ", If_loc(cond, "PASS", "FAIL"), "\n");
    if not cond then Add(testFailures, label); fi;
end;;

# --------------------------------------------------------------------
# Build R = ResolutionFiniteGroup(D_8, 4) and a 1-cocycle.
# --------------------------------------------------------------------

Print("\n--- Setup: D_8 resolution ---\n");
G := SmallGroup(8, 3);;
R := ResolutionFiniteGroup(G, 4);;
Print("  |G| = ", Order(G), "\n");
Print("  R!.dimension(d) for d=0..4: ",
      List([0..4], d -> R!.dimension(d)), "\n");

# --------------------------------------------------------------------
# Build a 1-cocycle by enumerating non-zero F_2-vectors of length
# R!.dimension(1) and picking one that's a cocycle (its image under
# the coboundary δ_1 is zero).
# --------------------------------------------------------------------

Print("\n--- Task 1: pick a non-trivial F_2 1-cocycle on R ---\n");

dim1 := R!.dimension(1);;
dim2 := R!.dimension(2);;
Print("  dim_1 = ", dim1, ", dim_2 = ", dim2, "\n");

# Coboundary δ_1 sends a 1-cochain to a 2-cochain. We compute the
# kernel and pick a non-zero element.
delta_1 := function(alpha_vec)
    return HAP_BarCoboundary(R, alpha_vec, 1);
end;;

# Search small F_2 1-cochains.
alpha_vec := fail;;
for v in Cartesian(List([1..dim1], _ -> [0, 1])) do
    if Sum(v) = 0 then continue; fi;
    if ForAll(delta_1(v), x -> x mod 2 = 0) then
        alpha_vec := v;
        break;
    fi;
od;

if alpha_vec = fail then
    Print("  No non-trivial F_2 1-cocycle found in small search.\n");
    AssertOrLog("setup: found a non-trivial 1-cocycle", false);
else
    Print("  alpha_vec = ", alpha_vec, "\n");
    AssertOrLog("setup: 1-cocycle found",
                ForAll(delta_1(alpha_vec), x -> x mod 2 = 0));
fi;

# --------------------------------------------------------------------
# Compute HAP_SteenrodCup1Symmetric(R, α, α, 1).
# Expected output: a length-`R!.dimension(1)` F_2 vector representing
# α ∪₁ α. Cohomologically this is Sq^0(α ∪ α) up to choice — i.e., it
# should be a 1-cocycle (its coboundary mod 2 is zero).
# --------------------------------------------------------------------

if alpha_vec <> fail then
    Print("\n--- Task 2: compute α ∪₁ α via HAP_SteenrodCup1Symmetric ---\n");

    t0 := Runtime();;
    cup1_result := HAP_SteenrodCup1Symmetric(R, alpha_vec, alpha_vec, 1);;
    Print("  Wall: ", (Runtime() - t0) / 1000., " s\n");
    Print("  cup1 result has length ", Length(cup1_result),
          " (expected R!.dimension(1) = ", dim1, ")\n");
    AssertOrLog("HAP_SteenrodCup1Symmetric returned a vector",
                IsList(cup1_result));
    AssertOrLog(Concatenation(
                  "output length matches R!.dimension(2*n - 1) = R!.dimension(1) = ",
                  String(dim1)),
                Length(cup1_result) = dim1);

    # Verify result is a 1-cocycle: δ_1(result) = 0 mod 2.
    if Length(cup1_result) > 0 then
        AssertOrLog("output is an F_2 1-cocycle (δ ≡ 0 mod 2)",
                    ForAll(delta_1(List(cup1_result, x -> Int(x))),
                           x -> x mod 2 = 0));
    fi;
fi;

# --------------------------------------------------------------------
# Summary.
# --------------------------------------------------------------------

Print("\n=== Summary ===\n");
if IsEmpty(testFailures) then
    Print("test_hap_steenrod_cup1: ALL PASS\n");
else
    Print("test_hap_steenrod_cup1: FAIL (",
          Length(testFailures), " failures)\n");
    for f in testFailures do Print("  - ", f, "\n"); od;
fi;
