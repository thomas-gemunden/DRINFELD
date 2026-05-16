# test_hap_pontryagin_square.g — regression for B3-2 / #171.
#
# Anchor at D_8 = SmallGroup(8, 3). Verifies Pontryagin square on the
# HAP_PHI-internal resolution (= ResolutionPrimePowerGroup-based RG).

BreakOnError := false;;
LoadPackage("hap");

Read("hap_pontryagin_square.g");

Print("\n=== test_hap_pontryagin_square.g (issue #171) ===\n");

testFailures := [];;
If_loc := function(c, a, b) if c then return a; else return b; fi; end;;
AssertOrLog := function(label, cond)
    Print("  ", label, ": ", If_loc(cond, "PASS", "FAIL"), "\n");
    if not cond then Add(testFailures, label); fi;
end;;

# ------------------------------------------------------------------
# Setup: extract RG, find an F_2 2-cocycle on it.
# ------------------------------------------------------------------

Print("\n--- Setup: D_8 internal HAP_PHI resolution + F_2 2-cocycle ---\n");
G := SmallGroup(8, 3);;
R := HAP_PontryaginGetResolution(G, 5);;
Print("  |G| = ", Order(G), "\n");
Print("  R!.dimension(d) for d=0..5: ",
      List([0..5], d -> R!.dimension(d)), "\n");

dim2 := R!.dimension(2);;
dim3 := R!.dimension(3);;
dim4 := R!.dimension(4);;

# Find a non-trivial F_2 2-cocycle by enumerating small support.
alpha_F2 := fail;;
alpha_int := fail;;
for v in Cartesian(List([1..dim2], _ -> [0, 1])) do
    if Sum(v) = 0 then continue; fi;
    if ForAll(HAP_BarCoboundary(R, v, 2), x -> x mod 2 = 0) then
        alpha_F2 := List(v, x -> If_loc(x = 0, 0 * Z(2), Z(2)^0));
        alpha_int := v;
        break;
    fi;
od;

if alpha_F2 = fail then
    AssertOrLog("setup: F_2 2-cocycle found", false);
fi;

if alpha_F2 <> fail then
    Print("  α_F2 = ", alpha_F2, "\n");
    Print("  α_int = ", alpha_int, "\n");
    AssertOrLog("setup: F_2 2-cocycle found",
                ForAll(HAP_BarCoboundary(R, alpha_int, 2), x -> x mod 2 = 0));
fi;

# ------------------------------------------------------------------
# Tasks 1-4: compute P(α), shape + cocycle equation + mod-2 reduction + non-triviality.
# ------------------------------------------------------------------

if alpha_F2 = fail then
    Print("\n--- Skipping Tasks 1-4: no F_2 2-cocycle. ---\n");
else
Print("\n--- Task 1: HAP_PontryaginSquare(G, α_F2, 2) ---\n");

t0 := Runtime();;
PQ := HAP_PontryaginSquare(G, alpha_F2, 2);;
Print("  Wall: ", (Runtime() - t0) / 1000., " s\n");
Print("  P(α) = ", PQ, "\n");

AssertOrLog("P(α) is a list",
            IsList(PQ));
AssertOrLog(Concatenation(
              "P(α) has length R!.dimension(4) = ", String(dim4)),
            Length(PQ) = dim4);

AssertOrLog("P(α) entries are in {0, 1, 2, 3}",
            ForAll(PQ, x -> x in [0, 1, 2, 3]));

# Task 2: P(α) is a Z/4 4-cocycle mod 4.
#
# KNOWN GAP (recorded on the PR): the chain-level cup product used here
# is HAP's CR_ChainMapFromCocycle, which only satisfies Leibniz on Z
# cocycles. For α a non-Z-cocycle (the integer lift of an F_2 cocycle),
# the result of α̃ ∪ α̃ is bilinear but Leibniz fails — verified directly:
# d(α̃∪α̃) ≠ cup(δα̃, α̃) + cup(α̃, δα̃). The fix is to build a true
# chain-level diagonal Δ : R → R⊗R via R!.boundary + R!.homotopy. See
# 2026-05-16-pontryagin-diagonal-chain-map-spec.md (follow-up).
Print("\n--- Task 2: P(α) is a Z/4 4-cocycle mod 4 ---\n");

r := HAP_VerifyZ4CocycleMod4(R, PQ, 2);;
Print("  d(P(α)) mod 4 violations: ", r.violations, " / ", r.total, "\n");
Print("  (KNOWN GAP — pending true chain-level Δ construction)\n");
# Soft-record violations as a known-issue counter; don't fail the suite.
Add(testFailures, Concatenation(
    "KNOWN: P(α) cocycle violations: ", String(r.violations), " / ",
    String(r.total)));

# Task 3: F_2 reduction. P(α) mod 2 = α̃ ∪ α̃ mod 2.
Print("\n--- Task 3: F_2 reduction P(α) mod 2 = α ∪ α ---\n");

alpha_cup_alpha_int := HAP_ChainCupProduct_Int(R, alpha_int, 2, alpha_int, 2);;
mismatches := 0;;
for i in [1..dim4] do
    if (PQ[i] mod 2) <> (alpha_cup_alpha_int[i] mod 2) then
        mismatches := mismatches + 1;
    fi;
od;
AssertOrLog("P(α) mod 2 == (α̃ ∪ α̃) mod 2 on R^4 cells",
            mismatches = 0);

# Task 4: non-triviality.
Print("\n--- Task 4: P(α) is not identically zero mod 4 ---\n");

AssertOrLog("P(α) takes some non-zero value mod 4",
            not ForAll(PQ, x -> x = 0));
fi;

# ------------------------------------------------------------------
# Summary.
# ------------------------------------------------------------------

Print("\n=== Summary ===\n");
if IsEmpty(testFailures) then
    Print("test_hap_pontryagin_square: ALL PASS\n");
else
    Print("test_hap_pontryagin_square: FAIL (",
          Length(testFailures), " failures)\n");
    for f in testFailures do Print("  - ", f, "\n"); od;
fi;
