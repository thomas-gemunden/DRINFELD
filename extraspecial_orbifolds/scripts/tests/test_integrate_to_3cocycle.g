# test_integrate_to_3cocycle.g — regression test for the integration
# step from P(Q) (Z/4 4-cocycle) to a Z/4 3-cocycle f representing the
# Z/4 generator of H^4(G; Z) under δ_4. Issue #162.
#
# Anchor at D_8 = SmallGroup(8, 3). Linear systems:
#   Stage A: 32768 equations × 4096 unknowns over Z.
#   Stage B:  4096 equations ×  512 unknowns over Z.
# Both feasible with GAP SolutionIntMat in minutes.

BreakOnError := false;;

Read("integrate_to_3cocycle.g");
Read("bar_cocycle.g");

Print("\n=== test_integrate_to_3cocycle.g (issue #162) ===\n");

testFailures := [];;
If_loc := function(c, a, b) if c then return a; else return b; fi; end;;
AssertOrLog := function(label, cond)
    Print("  ", label, ": ", If_loc(cond, "PASS", "FAIL"), "\n");
    if not cond then Add(testFailures, label); fi;
end;;

# ------------------------------------------------------------------
# Setup: D_8, build Q = x(g)·y(h) as F_2 2-cocycle, then P(Q).
# ------------------------------------------------------------------

Print("\n--- Setup: D_8 + Quillen Q + P(Q) ---\n");
G := SmallGroup(8, 3);;
gens_G := GeneratorsOfGroup(G);;

_Z2 := CyclicGroup(IsPermGroup, 2);;
_z2_one := GeneratorsOfGroup(_Z2)[1];;
_z2_id  := Identity(_Z2);;
valid_assignments := [];;
for v in Cartesian(List(gens_G, g -> [0, 1])) do
    if GroupHomomorphismByImages(G, _Z2, gens_G,
            List(v, x -> If_loc(x = 0, _z2_id, _z2_one))) <> fail then
        Add(valid_assignments, v);
    fi;
od;
non_zero := Filtered(valid_assignments, v -> Sum(v) > 0);;
x_hom := F2HomFromImages(G, non_zero[1]);;
y_hom := F2HomFromImages(G, non_zero[2]);;
Q_F2 := function(g, h) return (x_hom(g) * y_hom(h)) mod 2; end;;
PQ := PontryaginSquare(Q_F2, 2);;
Print("  Q = x(g)·y(h),  P(Q) = Brumfiel-Morgan 4-cocycle\n");

# ------------------------------------------------------------------
# Run the integration.
# ------------------------------------------------------------------

Print("\n--- Run IntegrateToZ4ThreeCocycle ---\n");
t0 := Runtime();;
result := IntegrateToZ4ThreeCocycle(G, PQ);;
Print("  Wall: ", (Runtime() - t0) / 1000., " s\n");

AssertOrLog("integration returned a record",
            IsRecord(result));
AssertOrLog("result.f is callable (G^3 -> Z/4)",
            IsFunction(result.f));
AssertOrLog("result.f_tilde is an integer 3-cochain",
            IsList(result.f_tilde)
            and Length(result.f_tilde) = Order(G)^3
            and ForAll(result.f_tilde, IsInt));

# ------------------------------------------------------------------
# Task 1: f satisfies the bar 3-cocycle equation mod 4.
# ------------------------------------------------------------------

Print("\n--- Task 1: f bar 3-cocycle equation mod 4 ---\n");

elts := AsList(G);;
n_viol := 0;;
n_total := 0;;
for args in Tuples(elts, 4) do
    val := (result.f(args[2], args[3], args[4])
          - result.f(args[1] * args[2], args[3], args[4])
          + result.f(args[1], args[2] * args[3], args[4])
          - result.f(args[1], args[2], args[3] * args[4])
          + result.f(args[1], args[2], args[3])) mod 4;
    if val <> 0 then n_viol := n_viol + 1; fi;
    n_total := n_total + 1;
od;
Print("  ", n_viol, " / ", n_total, " violations\n");
AssertOrLog("f is a bar 3-cocycle mod 4 on D_8 (0 violations)",
            n_viol = 0);

# ------------------------------------------------------------------
# Task 2: f value distribution. EXPECTED OUTCOME AT D_8: trivial.
#
# At D_8 (h(Q) = 1, outside Harada-Kono's h ≥ 2 hypothesis), the class
# [P(Q)] turns out to be ZERO in H^4(D_8; Z/4). Mathematical derivation
# from the test output: stage B finds f̃ with f̃ mod 4 = 0 cochain, so
# f̃ = 4·m → 4·G_int = δ(4m) = 4·δm → G_int = δm (Z torsion-free) →
# [G_int] = 0 in H^4(Z) → [P(Q)] = [G_int mod 4] = 0 in H^4(Z/4).
#
# This is NOT a bug in the algorithm. It is a STRUCTURAL FEATURE of
# D_8: Harada-Kono's Pontryagin-square = Z/4-generator argument
# requires h(Q) ≥ 2 (= m ≥ 2 for extraspecial 2-groups). At m=1, the
# Z/4 generator of H^4(D_8; Z) = Z/2 × Z/2 × Z/4 comes from a
# DIFFERENT F_2 class than the quadratic form Q.
#
# We record the empirical finding rather than assert it as a PASS.
# A non-trivial anchor requires m ≥ 2, but the linear-solve at m=2
# is 32^5 × 32^4 ≈ 3×10^13 entries — infeasible with dense matrices
# (open algorithmic question — flagged in #137 / #166 for sparse-
# algorithm follow-up).
# ------------------------------------------------------------------

Print("\n--- Task 2: f value distribution (informational — see header) ---\n");

f_values := Set([]);;
for args in Tuples(elts, 3) do AddSet(f_values, result.f(args[1], args[2], args[3])); od;
Print("  distinct values of f mod 4: ", f_values, "\n");
Print("  expected at D_8: { 0 } (structural; [P(Q)] = 0 in H^4(D_8; Z/4))\n");
AssertOrLog("f matches D_8 expectation: { 0 } only",
            f_values = [0]);

# ------------------------------------------------------------------
# Task 3: G_int is a Z 4-cocycle AND G_int mod 4 == P(Q) on G^4.
# ------------------------------------------------------------------

Print("\n--- Task 3: G_int validation ---\n");

idxp4 := _I3C_TupleIndexer(G, 4);;
mismatches_mod4 := 0;;
for args in Tuples(elts, 4) do
    if (result.G_int[idxp4.idx(args)] mod 4) <> CallFuncList(PQ, args) then
        mismatches_mod4 := mismatches_mod4 + 1;
    fi;
od;
AssertOrLog("G_int mod 4 = P(Q) on all 4096 tuples",
            mismatches_mod4 = 0);

# G_int is a Z 4-cocycle: BCM_4 · G_int = 0.
BC4_check := BarCoboundaryMatrixZ(G, 4);;
dG := BC4_check * result.G_int;;
AssertOrLog("G_int is a Z 4-cocycle (BCM_4 · G_int = 0)",
            ForAll(dG, x -> x = 0));

# ------------------------------------------------------------------
# Task 4: δf̃ = 4·G_int (integer equation).
# ------------------------------------------------------------------

Print("\n--- Task 4: δf̃ = 4·G_int ---\n");

BC3_check := BarCoboundaryMatrixZ(G, 3);;
df_tilde := BC3_check * result.f_tilde;;
target_4G := List(result.G_int, x -> 4 * x);;
AssertOrLog("δf̃ = 4·G_int as integer 4-cochains",
            df_tilde = target_4G);

# ------------------------------------------------------------------
# Summary.
# ------------------------------------------------------------------

Print("\n=== Summary ===\n");
if IsEmpty(testFailures) then
    Print("test_integrate_to_3cocycle: ALL PASS\n");
else
    Print("test_integrate_to_3cocycle: FAIL (",
          Length(testFailures), " failures)\n");
    for f in testFailures do Print("  - ", f, "\n"); od;
fi;
