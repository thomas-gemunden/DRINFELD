# test_hap_pontryagin_square.g — regression for B3-2 / #171.
#
# Anchor at D_8 = SmallGroup(8, 3). Verifies the Pontryagin square on
# HAP's `ResolutionFiniteGroup` (a Z-resolution; required for the BM
# formula's chain-level Z/4 cocycle identity).
#
# Earlier versions of this test soft-recorded Task 2 (cocycle equation)
# as a known gap because the chain-level cup product used
# HAP's CR_ChainMapFromCocycle, which is Leibniz only on Z-cocycles.
# This is fixed by the diagonal/cup-1 chain-level construction
# (`hap_diagonal.g` + `hap_cup1_homotopy.g`).

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
# Setup: get R, find an F_2 2-cocycle on it.
# ------------------------------------------------------------------

Print("\n--- Setup: D_8 ResolutionFiniteGroup + F_2 2-cocycle ---\n");
G := SmallGroup(8, 3);;
R := HAP_PontryaginGetResolution(G, 5);;
Print("  |G| = ", Order(G), "\n");
Print("  R characteristic: ", EvaluateProperty(R, "characteristic"), "\n");
Print("  R!.dimension(d) for d=0..5: ",
      List([0..5], d -> R!.dimension(d)), "\n");

AssertOrLog("R has Z (characteristic 0)",
            EvaluateProperty(R, "characteristic") = 0);

dim2 := R!.dimension(2);;
dim3 := R!.dimension(3);;
dim4 := R!.dimension(4);;
dim5 := R!.dimension(5);;

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
Print("\n--- Task 2: P(α) is a Z/4 4-cocycle mod 4 ---\n");

r := HAP_VerifyZ4CocycleMod4(R, PQ, 2);;
Print("  d(P(α)) mod 4 violations: ", r.violations, " / ", r.total, "\n");
AssertOrLog(Concatenation("d(P(α)) ≡ 0 mod 4 (", String(r.violations),
                          " / ", String(r.total), " violations)"),
            r.violations = 0);

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
# Tasks 5-8: invariants from the chain-level Δ / h_1 construction.
# ------------------------------------------------------------------

if alpha_F2 = fail then
    Print("\n--- Skipping Tasks 5-8: no F_2 2-cocycle. ---\n");
else

# Task 5: Δ chain-map property at degrees [1..4].
Print("\n--- Task 5: Δ chain-map property ---\n");

cache := _HAP_Pontryagin_GetCache(G, 5);;
r5 := HAP_VerifyDiagonalChainMap(R, cache.DiagMap, 4);;
Print("  Δ chain-map violations: ", r5.violations, " / ", r5.total, "\n");
AssertOrLog(Concatenation("Δ chain-map: 0 violations / ",
                          String(r5.total)),
            r5.violations = 0);

# Task 6: Integer cup Leibniz on (p, q) ∈ {(1,2), (2,1), (2,2)}.
Print("\n--- Task 6: Integer cup-product Leibniz rule ---\n");

CochBdry_loc := function(alpha, p, dim_p1)
    local result, i, entry, total;
    result := [];
    for i in [1..dim_p1] do
        total := 0;
        for entry in R!.boundary(p + 1, i) do
            total := total + SignInt(entry[1]) * alpha[AbsInt(entry[1])];
        od;
        result[i] := total;
    od;
    return result;
end;;

leibniz_violations := 0;;
leibniz_total := 0;;
for pq in [[1, 2], [2, 1]] do
    p := pq[1]; q := pq[2];
    dim_p := R!.dimension(p);
    dim_q := R!.dimension(q);
    dim_pq1 := R!.dimension(p + q + 1);
    # Test on basis cochains.
    for j in [1..dim_p] do
        for k in [1..dim_q] do
            leibniz_total := leibniz_total + 1;
            alpha := List([1..dim_p], i -> If_loc(i = j, 1, 0));
            beta := List([1..dim_q], i -> If_loc(i = k, 1, 0));
            cup_ab := HAP_ChainCupProduct_Int(R, alpha, p, beta, q);
            d_cup_ab := CochBdry_loc(cup_ab, p + q, dim_pq1);
            da := CochBdry_loc(alpha, p, R!.dimension(p + 1));
            db := CochBdry_loc(beta, q, R!.dimension(q + 1));
            da_b := HAP_ChainCupProduct_Int(R, da, p + 1, beta, q);
            a_db := HAP_ChainCupProduct_Int(R, alpha, p, db, q + 1);
            if IsOddInt(p) then sgn_q := -1; else sgn_q := 1; fi;
            ok := true;
            for i in [1..dim_pq1] do
                if d_cup_ab[i] <> da_b[i] + sgn_q * a_db[i] then
                    ok := false; break;
                fi;
            od;
            if not ok then
                leibniz_violations := leibniz_violations + 1;
            fi;
        od;
    od;
od;
Print("  Leibniz violations: ", leibniz_violations,
      " / ", leibniz_total, " (p,q) ∈ {(1,2), (2,1)} basis pairs\n");
AssertOrLog(Concatenation("Integer cup Leibniz: 0 violations / ",
                          String(leibniz_total)),
            leibniz_violations = 0);

# Task 7: h_1 chain-homotopy property at degrees [1..4].
Print("\n--- Task 7: h_1 chain-homotopy property ---\n");

r7 := HAP_VerifyCup1Homotopy(R, cache.DiagMap, cache.Cup1Hty, 4);;
Print("  h_1 chain-hty violations: ", r7.violations, " / ", r7.total, "\n");
AssertOrLog(Concatenation("h_1 chain-hty: 0 violations / ",
                          String(r7.total)),
            r7.violations = 0);

# Task 8: F_2 cup-1 coboundary identity.
# For α, β F_2 n-cocycles: d(α∪₁β) = α∪β + β∪α (mod 2).
Print("\n--- Task 8: F_2 cup-1 coboundary identity ---\n");

cup1_aa_int := HAP_SteenrodCup1_Int(R, alpha_int, 2, alpha_int, 2);;
Print("  α̃ ∪₁ α̃ (integer) = ", cup1_aa_int, "\n");
d_cup1_aa := CochBdry_loc(cup1_aa_int, 3, dim4);;
Print("  d(α̃ ∪₁ α̃) = ", d_cup1_aa, "\n");
# Compare mod 2 against α∪β + β∪α. Here α=β, so α∪α + α∪α = 0 (mod 2).
# So d(α̃ ∪₁ α̃) mod 2 must be 0.
cup1_id_violations := 0;;
for i in [1..dim4] do
    if d_cup1_aa[i] mod 2 <> 0 then
        cup1_id_violations := cup1_id_violations + 1;
    fi;
od;
Print("  (for symmetric α, expect d(α̃∪₁α̃) mod 2 = 0)\n");
AssertOrLog(Concatenation("F_2 cup-1 coboundary id (symmetric): ",
                          String(cup1_id_violations), " / ", String(dim4),
                          " violations"),
            cup1_id_violations = 0);

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
