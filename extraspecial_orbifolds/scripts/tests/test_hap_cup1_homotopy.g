# test_hap_cup1_homotopy.g — unit test for hap_cup1_homotopy.g.
#
# Issue #171 follow-up.
# Anchor at D_8 = SmallGroup(8, 3) on ResolutionFiniteGroup(D_8, 5).

BreakOnError := false;;
LoadPackage("hap");
Read("hap_cup1_homotopy.g");

Print("\n=== test_hap_cup1_homotopy.g (issue #171 follow-up) ===\n");

testFailures := [];;
If_loc := function(c, a, b) if c then return a; else return b; fi; end;;
AssertOrLog := function(label, cond)
    Print("  ", label, ": ", If_loc(cond, "PASS", "FAIL"), "\n");
    if not cond then Add(testFailures, label); fi;
end;;

# ------------------------------------------------------------------
# Setup: D_8 on ResolutionFiniteGroup, Δ and h_1 built to degree 4.
# ------------------------------------------------------------------

Print("\n--- Setup: ResolutionFiniteGroup(D_8, 5) + Δ, h_1 ---\n");
G := SmallGroup(8, 3);;
R := ResolutionFiniteGroup(G, 5);;
Print("  R characteristic: ", EvaluateProperty(R, "characteristic"), "\n");
Print("  R!.dimension(d) for d=0..5: ",
      List([0..5], d -> R!.dimension(d)), "\n");

t0 := Runtime();;
DiagMap := HAP_BuildDiagonal(R, 4);;
Print("  Δ built in ", (Runtime() - t0) / 1000., " s\n");

t0 := Runtime();;
Cup1Hty := HAP_BuildCup1Homotopy(R, DiagMap, 4);;
Print("  h_1 built in ", (Runtime() - t0) / 1000., " s\n");

AssertOrLog("Cup1Hty has 5 entries (degrees 0..4)",
            Length(Cup1Hty) = 5);
AssertOrLog("h_1(e_0^1) = 0",
            Cup1Hty[1][1] = []);

# ------------------------------------------------------------------
# Task 1: h_1 chain-homotopy property.
# ∂_RR(h_1[n][i]) = (τΔ - Δ)(e_n^i) - h_1(∂_R e_n^i).
# ------------------------------------------------------------------

Print("\n--- Task 1: h_1 chain-homotopy property at n ∈ [1..4] ---\n");

r := HAP_VerifyCup1Homotopy(R, DiagMap, Cup1Hty, 4);;
Print("  violations: ", r.violations, " / ", r.total, "\n");
AssertOrLog("h_1 chain-homotopy property: 0 violations",
            r.violations = 0);
if r.violations > 0 then
    Print("  Details (first 3):\n");
    for d in r.details{[1..Minimum(3, Length(r.details))]} do
        Print("    n=", d.n, ", i=", d.i, ", diff_len=", d.diff_len, "\n");
    od;
fi;

# ------------------------------------------------------------------
# Task 2: τ swap consistency.
# Applying τ twice on a chain should give the original (since τ² = id).
# ------------------------------------------------------------------

Print("\n--- Task 2: τ² = id on Δ values ---\n");

violations_tau := 0;;
total_tau := 0;;
for n in [1..4] do
    for i in [1..R!.dimension(n)] do
        total_tau := total_tau + 1;
        c := DiagMap[n+1][i];
        tt := _HAP_RR_Swap(_HAP_RR_Swap(c));
        diff := _HAP_RR_Reduce(Concatenation(tt, _HAP_RR_Scale(c, -1)));
        if Length(diff) <> 0 then
            violations_tau := violations_tau + 1;
        fi;
    od;
od;
AssertOrLog(Concatenation("τ² = id: 0 violations across ",
                          String(total_tau), " (n, i)"),
            violations_tau = 0);

# ------------------------------------------------------------------
# Summary.
# ------------------------------------------------------------------

Print("\n=== Summary ===\n");
if IsEmpty(testFailures) then
    Print("test_hap_cup1_homotopy: ALL PASS\n");
else
    Print("test_hap_cup1_homotopy: FAIL (",
          Length(testFailures), " failures)\n");
    for f in testFailures do Print("  - ", f, "\n"); od;
fi;
