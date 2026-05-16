# test_hap_diagonal.g — unit test for hap_diagonal.g.
#
# Issue #171 follow-up.
# Anchor at D_8 = SmallGroup(8, 3) on ResolutionFiniteGroup(D_8, 5).

BreakOnError := false;;
LoadPackage("hap");
Read("hap_diagonal.g");

Print("\n=== test_hap_diagonal.g (issue #171 follow-up) ===\n");

testFailures := [];;
If_loc := function(c, a, b) if c then return a; else return b; fi; end;;
AssertOrLog := function(label, cond)
    Print("  ", label, ": ", If_loc(cond, "PASS", "FAIL"), "\n");
    if not cond then Add(testFailures, label); fi;
end;;

# ------------------------------------------------------------------
# Setup: D_8 on ResolutionFiniteGroup.
# ------------------------------------------------------------------

Print("\n--- Setup: ResolutionFiniteGroup(D_8, 5) ---\n");
G := SmallGroup(8, 3);;
R := ResolutionFiniteGroup(G, 5);;
Print("  R characteristic: ", EvaluateProperty(R, "characteristic"), "\n");
Print("  R!.dimension(d) for d=0..5: ",
      List([0..5], d -> R!.dimension(d)), "\n");

AssertOrLog("R has Z (characteristic 0)",
            EvaluateProperty(R, "characteristic") = 0);

# ------------------------------------------------------------------
# Task 1: Build Δ to degree 4.
# ------------------------------------------------------------------

Print("\n--- Task 1: Build Δ via HAP_BuildDiagonal(R, 4) ---\n");

t0 := Runtime();;
DiagMap := HAP_BuildDiagonal(R, 4);;
Print("  Wall: ", (Runtime() - t0) / 1000., " s\n");

AssertOrLog("DiagMap is a list with 5 entries (degrees 0..4)",
            Length(DiagMap) = 5);

for n in [0..4] do
    Print("  degree ", n, " has ", Length(DiagMap[n+1]), " entries\n");
od;

AssertOrLog("DiagMap[1][1] is a single-record list",
            IsList(DiagMap[1]) and Length(DiagMap[1]) = 1
            and Length(DiagMap[1][1]) = 1);
AssertOrLog("DiagMap[1][1] = [rec(p=0, q=0, jp=1, jq=1, sgn=1)]",
            DiagMap[1][1][1].p = 0 and DiagMap[1][1][1].q = 0
            and DiagMap[1][1][1].jp = 1 and DiagMap[1][1][1].jq = 1
            and DiagMap[1][1][1].sgn = 1);

# ------------------------------------------------------------------
# Task 2: Δ chain-map property.
# ------------------------------------------------------------------

Print("\n--- Task 2: Δ chain-map property at all (n, i) for n ∈ [1..4] ---\n");

r := HAP_VerifyDiagonalChainMap(R, DiagMap, 4);;
Print("  violations: ", r.violations, " / ", r.total, "\n");
AssertOrLog("Δ chain-map property: 0 violations",
            r.violations = 0);
if r.violations > 0 then
    Print("  Details (first 3):\n");
    for d in r.details{[1..Minimum(3, Length(r.details))]} do
        Print("    n=", d.n, ", i=", d.i, ", diff_len=", d.diff_len, "\n");
    od;
fi;

# ------------------------------------------------------------------
# Task 3: ZG-equivariance of boundary and action.
#
# We verify: ∂_RR((g, g) · c) = (g, g) · ∂_RR(c) for the diagonal
# G-action. This is the defining property of R⊗R as a ZG-module
# (boundary commutes with the G-action).
# ------------------------------------------------------------------

Print("\n--- Task 3: ∂_RR commutes with diagonal G-action ---\n");

violations_eqv := 0;;
total_eqv := 0;;
for n in [2..3] do
    for i in [1..R!.dimension(n)] do
        for g_pos in [1..Minimum(Length(R!.elts), 4)] do
            total_eqv := total_eqv + 1;
            c := DiagMap[n+1][i];
            gc := _HAP_RR_DiagAction(R, g_pos, c);
            bdr_gc := _HAP_RR_Boundary(R, gc);
            g_bdr_c := _HAP_RR_DiagAction(R, g_pos, _HAP_RR_Boundary(R, c));
            diff := _HAP_RR_Reduce(Concatenation(bdr_gc, _HAP_RR_Scale(g_bdr_c, -1)));
            if Length(diff) <> 0 then
                violations_eqv := violations_eqv + 1;
            fi;
        od;
    od;
od;
AssertOrLog(Concatenation("∂_RR commutes with G-action: 0 violations across ",
                          String(total_eqv), " (n, i, g)"),
            violations_eqv = 0);

# ------------------------------------------------------------------
# Task 4: Augmentation property.
# At degree 0, Δ(e_0^1) = e_0^1 ⊗ e_0^1 = [rec(p=0, q=0, jp=1, jq=1,
# sgn=1, gl=iden, gr=iden)].
# ------------------------------------------------------------------

Print("\n--- Task 4: Augmentation property ---\n");

iden := Position(R!.elts, Identity(R!.group));
AssertOrLog("Δ(e_0^1) has gl = gr = identity",
            DiagMap[1][1][1].gl = iden and DiagMap[1][1][1].gr = iden);

# ------------------------------------------------------------------
# Summary.
# ------------------------------------------------------------------

Print("\n=== Summary ===\n");
if IsEmpty(testFailures) then
    Print("test_hap_diagonal: ALL PASS\n");
else
    Print("test_hap_diagonal: FAIL (",
          Length(testFailures), " failures)\n");
    for f in testFailures do Print("  - ", f, "\n"); od;
fi;
