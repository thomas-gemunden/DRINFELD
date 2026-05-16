# test_hap_integrate_to_z4_cocycle.g — anchor regression for #172
# (Q-int B3-3) at D_8 = SmallGroup(8, 3).
#
# Steps:
#   1. Build R = HAP_PontryaginGetResolution(D_8, 5) (Z-resolution).
#   2. Enumerate F_2 2-cocycles α on R until we find one whose
#      Pontryagin square P(α) has β_4([P(α)]) = 0 in H^5(D_8; Z) —
#      i.e. for which the Stage A linear-solve in
#      HAP_IntegrateToZ4Cocycle has an integer solution. The Bockstein
#      β_4 is the precondition for Stage A; it's zero exactly when
#      [P(α)] lies in the image of the reduction
#      H^4(G; Z) → H^4(G; Z/4). Not all F_2 2-cocycles α give classes
#      [P(α)] with vanishing β_4 — see notes below.
#   3. Compute P = HAP_PontryaginSquare(D_8, α, 2) — a Z/4 4-cocycle on R.
#   4. result := HAP_IntegrateToZ4Cocycle(R, P, 2) — descend to a Z/4
#      3-cocycle f on R.
#   5. Verify:
#      - result.f has the right shape and entries in {0, 1, 2, 3}.
#      - δ(f) ≡ 0 mod 4 (f is a Z/4 3-cocycle on R).
#      - result.f_int has δ(f_int) = 4·result.G_int over Z (Stage B identity).
#      - result.G_int is a Z 4-cocycle (Stage A identity).
#      - result.G_int mod 4 = P (Stage A reduction).
#      - result.f is not identically zero (non-triviality).
#
# # On the Bockstein-zero precondition.
#
# The two-stage construction in HAP_IntegrateToZ4Cocycle assumes the
# input Z/4 cocycle F has class [F] ∈ H^{2n}(G; Z/4) in the image of
# the reduction `H^{2n}(G; Z) → H^{2n}(G; Z/4)`. Equivalently, the
# integer Bockstein β_4([F]) ∈ H^{2n+1}(G; Z) (= [δ(F_int)/4]) is zero.
# For F = P(α) the Pontryagin square, this holds iff α belongs to a
# specific subset of F_2 2-cocycles — at D_8 on R, 4 out of 7 non-zero
# F_2 2-cocycles satisfy this. The bar-resolution test at #162 uses the
# Quillen quadratic form Q = x(g)·y(h), which lifts to Z (since the
# Pontryagin square of any decomposable F_2 quadratic form has a known
# Z lift). Here we enumerate and pick.
#
# # Wall-time expectation.
#
# At D_8, R!.dimension(d) for d = 3, 4, 5 is 5, 8, 12. Stage A is
# 12 × 8 over Z; Stage B is 8 × 5 over Z. Both linear systems are tiny.
# Wall time is sub-second.

BreakOnError := false;;
LoadPackage("hap");

Read("hap_integrate_to_z4_cocycle.g");

Print("\n=== test_hap_integrate_to_z4_cocycle.g (issue #172) ===\n");

testFailures := [];;
If_loc := function(c, a, b) if c then return a; else return b; fi; end;;
AssertOrLog := function(label, cond)
    Print("  ", label, ": ", If_loc(cond, "PASS", "FAIL"), "\n");
    if not cond then Add(testFailures, label); fi;
end;;

# ------------------------------------------------------------------
# Setup: D_8 on R = ResolutionFiniteGroup(D_8, 5).
# ------------------------------------------------------------------

Print("\n--- Setup: D_8 + ResolutionFiniteGroup(D_8, 5) ---\n");
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

# ------------------------------------------------------------------
# Enumerate F_2 2-cocycles α on R; for each, compute P(α) and check
# whether Stage A is solvable (i.e. β_4([P(α)]) = 0 in H^5(D_8; Z)).
# Pick the first α with a solvable Stage A.
# ------------------------------------------------------------------

Print("\n--- Enumerate F_2 2-cocycles, pick one with β_4([P(α)]) = 0 ---\n");

# Precompute the Stage A boundary matrix once (cached internally too).
M_4_check := HAP_BoundaryMatrixZ(R, 4);;

alpha_F2 := fail;;
alpha_int := fail;;
PQ := fail;;
n_F2_cocycles := 0;;
n_bockstein_zero := 0;;
for v in Cartesian(List([1..dim2], _ -> [0, 1])) do
    if Sum(v) = 0 then continue; fi;
    if not ForAll(HAP_BarCoboundary(R, v, 2), x -> x mod 2 = 0) then continue; fi;
    n_F2_cocycles := n_F2_cocycles + 1;
    aF2_cand := List(v, x -> If_loc(x = 0, 0 * Z(2), Z(2)^0));
    P_cand := HAP_PontryaginSquare(G, aF2_cand, 2);
    dP_cand := M_4_check * P_cand;
    dP_div4 := List(dP_cand, x -> x / 4);
    sol_cand := SolutionIntMat(TransposedMat(M_4_check), dP_div4);
    if sol_cand <> fail then
        n_bockstein_zero := n_bockstein_zero + 1;
        if alpha_F2 = fail then
            alpha_F2 := aF2_cand;
            alpha_int := v;
            PQ := P_cand;
        fi;
    fi;
od;

Print("  F_2 2-cocycles found: ", n_F2_cocycles, "\n");
Print("  with β_4([P(α)]) = 0: ", n_bockstein_zero, "\n");

if alpha_F2 = fail then
    AssertOrLog("setup: F_2 2-cocycle with vanishing Bockstein found",
                false);
else
    Print("  selected α_F2  = ", alpha_F2, "\n");
    Print("  selected α_int = ", alpha_int, "\n");
    Print("  selected P(α)  = ", PQ, "\n");
    AssertOrLog("setup: F_2 2-cocycle with β_4([P(α)]) = 0 found", true);
fi;

# Sanity precondition: P(α) is a Z/4 4-cocycle on R.
if alpha_F2 <> fail then
    dPQ_check := HAP_BarCoboundary(R, PQ, 4);;
    AssertOrLog("precondition: δ(P_lift) ≡ 0 mod 4 (P is a Z/4 4-cocycle on R)",
                ForAll(dPQ_check, x -> x mod 4 = 0));
fi;

# ------------------------------------------------------------------
# Run the integration.
# ------------------------------------------------------------------

if alpha_F2 <> fail then

Print("\n--- Run HAP_IntegrateToZ4Cocycle(R, P, 2) ---\n");
t0 := Runtime();;
result := HAP_IntegrateToZ4Cocycle(R, PQ, 2);;
wall_integrate := (Runtime() - t0) / 1000.;;
Print("  Wall: ", wall_integrate, " s\n");
Print("  result.f      = ", result.f, "\n");
Print("  result.f_int  = ", result.f_int, "\n");
Print("  result.G_int  = ", result.G_int, "\n");
Print("  result.h      = ", result.h, "\n");

AssertOrLog("integration returned a record", IsRecord(result));

# ------------------------------------------------------------------
# Task 1: shape and value constraints on f.
# ------------------------------------------------------------------

Print("\n--- Task 1: f shape and value constraints ---\n");

AssertOrLog(Concatenation("f has length R!.dimension(3) = ", String(dim3)),
            Length(result.f) = dim3);
AssertOrLog("f entries in {0, 1, 2, 3}",
            ForAll(result.f, x -> x in [0, 1, 2, 3]));

# ------------------------------------------------------------------
# Task 2: f is a Z/4 3-cocycle — δ(f) ≡ 0 mod 4 on R.
# ------------------------------------------------------------------

Print("\n--- Task 2: f is a Z/4 3-cocycle on R (δf ≡ 0 mod 4) ---\n");

df_int := HAP_BarCoboundary(R, result.f, 3);;
Print("  δ(f) (integer lift of mod-4 result) = ", df_int, "\n");
violations_mod4 := Length(Filtered(df_int, x -> x mod 4 <> 0));;
Print("  δ(f) mod 4 violations: ", violations_mod4, " / ", dim4, "\n");
AssertOrLog(Concatenation("δ(f) ≡ 0 mod 4 on R (",
                          String(violations_mod4), " / ", String(dim4),
                          " violations)"),
            violations_mod4 = 0);

# ------------------------------------------------------------------
# Task 3: G_int is a Z 4-cocycle AND G_int mod 4 = P at the chain level.
# ------------------------------------------------------------------

Print("\n--- Task 3: G_int validation ---\n");

dG_int := HAP_BarCoboundary(R, result.G_int, 4);;
AssertOrLog("G_int is a Z 4-cocycle on R (δG_int = 0)",
            ForAll(dG_int, x -> x = 0));

mismatches_GP := 0;;
for i in [1..dim4] do
    if (result.G_int[i] mod 4) <> PQ[i] then
        mismatches_GP := mismatches_GP + 1;
    fi;
od;
AssertOrLog(Concatenation("G_int mod 4 = P(α) on all ",
                          String(dim4), " R^4 cells"),
            mismatches_GP = 0);

# ------------------------------------------------------------------
# Task 4: δ(f_int) = 4·G_int over Z (Stage B identity).
# ------------------------------------------------------------------

Print("\n--- Task 4: δ(f_int) = 4·G_int over Z (Stage B identity) ---\n");

df_int_full := HAP_BarCoboundary(R, result.f_int, 3);;
target_4G := List(result.G_int, x -> 4 * x);;
AssertOrLog("δ(f_int) = 4·G_int as integer 4-cochains",
            df_int_full = target_4G);

# ------------------------------------------------------------------
# Task 5: f non-triviality (acceptance criterion).
# ------------------------------------------------------------------

Print("\n--- Task 5: f is non-trivial ---\n");

f_values := Set(result.f);;
Print("  distinct values of f mod 4 on R: ", f_values, "\n");
AssertOrLog("f is not identically zero",
            not ForAll(result.f, x -> x = 0));

# ------------------------------------------------------------------
# Task 6: f = f_int mod 4 elementwise.
# ------------------------------------------------------------------

Print("\n--- Task 6: f = f_int mod 4 elementwise ---\n");

mismatches_f := 0;;
for i in [1..dim3] do
    if (result.f_int[i] mod 4) <> result.f[i] then
        mismatches_f := mismatches_f + 1;
    fi;
od;
AssertOrLog("f = f_int mod 4 on R^3",
            mismatches_f = 0);

# ------------------------------------------------------------------
# Task 7: wall time is well under 1 minute (acceptance criterion).
# ------------------------------------------------------------------

Print("\n--- Task 7: wall-time budget ---\n");
Print("  Integration wall time: ", wall_integrate, " s\n");
AssertOrLog("integration completes in < 60 s on D_8",
            wall_integrate < 60.0);

fi;  # alpha_F2 <> fail

# ------------------------------------------------------------------
# Summary.
# ------------------------------------------------------------------

Print("\n=== Summary ===\n");
if IsEmpty(testFailures) then
    Print("test_hap_integrate_to_z4_cocycle: ALL PASS\n");
else
    Print("test_hap_integrate_to_z4_cocycle: FAIL (",
          Length(testFailures), " failures)\n");
    for f in testFailures do Print("  - ", f, "\n"); od;
fi;
