# test_iterated_bockstein_kronecker_equiv.g — A-5b R2-3 sibling verification.
#
# Verifies the KroneckerProduct vectorisation of the inner cup-square loop
# in IsCoboundary2Mod2WithLiftWitness (iterated_bockstein.g) is
# mathematically equivalent to the original nested for-loop, mirroring
# the parent fix in BocksteinH1ToH2 (mod2_solver.g) shipped by #221.
#
# The change replaced:
#     alpha_cup_alpha := List([1..n*n], i -> zero);
#     for i in [1..n] do
#         for j in [1..n] do
#             alpha_cup_alpha[(i-1)*n + j] := alpha[i] * alpha[j];
#         od;
#     od;
# with:
#     alpha_cup_alpha := KroneckerProduct([alpha], [alpha])[1];
#
# This file:
#   (1) Reconstructs the OLD per-α inner-body computation inline and
#       compares to the NEW KroneckerProduct form across a handful of
#       small-group hom_basis elements, plus the F_2-sum mask (α₁+α₂)
#       to exercise non-pure-basis α's.
#   (2) Calls the actual patched IsCoboundary2Mod2WithLiftWitness on the
#       β(α₁+α₂) example from test_iterated_bockstein.g and re-checks
#       the chain-level identity α∪α + δβ = c (mod 2) holds with the
#       returned witness — load-bearing for callers that consume the
#       record (the dispatcher's Path Z).
#   (3) Microbenchmarks the per-α inner body at n = 2048 (matches the
#       largest centraliser size encountered at m = 5).
#
# Run with absolute path invocation:
#   /opt/homebrew/bin/gap -q -b \
#     /Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-a5b-r2-3-sibling/extraspecial_orbifolds/scripts/solver/tests/test_iterated_bockstein_kronecker_equiv.g

# Load the patched iterated_bockstein.g (provides IsCoboundary2Mod2WithLiftWitness)
# using the same CWD shim pattern as test_iterated_bockstein.g.
ibke_test_target := fail;;
for ibke_test_try in [
        ".", "tests", "extraspecial_orbifolds/scripts/solver/tests",
        "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-a5b-r2-3-sibling/extraspecial_orbifolds/scripts/solver/tests",
        "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD/extraspecial_orbifolds/scripts/solver/tests"] do
    if IsExistingFile(Concatenation(ibke_test_try,
                                    "/test_iterated_bockstein_kronecker_equiv.g")) then
        ibke_test_target := ibke_test_try;
        break;
    fi;
od;;
if ibke_test_target = fail then
    Error("test_iterated_bockstein_kronecker_equiv.g: cannot locate self from CWD ",
          Filename(DirectoryCurrent(), ""));
fi;
ChangeDirectoryCurrent(ibke_test_target);;
Read("../iterated_bockstein.g");;

# ----------------------------------------------------------------------
# Test bookkeeping.
# ----------------------------------------------------------------------
IBKE_PASSES   := 0;;
IBKE_FAILURES := [];;

IBKEAssertTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
        IBKE_PASSES := IBKE_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Add(IBKE_FAILURES, label);
    fi;
end;;

# ----------------------------------------------------------------------
# Inline reproduction of the OLD α∪α construction (the exact body that
# was replaced). Returns the length-n² GF(2) row vector.
#
# We take alpha as a GF(2) length-n list (same as the patched function's
# internal alpha), so the comparison is on the raw cup-square output
# BEFORE ConvertToVectorRep — that's the load-bearing equality.
# ----------------------------------------------------------------------
IBKE_AlphaCupAlphaOLD := function(alpha)
    local n, v, i, j, zero;
    n := Length(alpha);
    zero := Zero(GF(2));
    v := List([1..n*n], i -> zero);
    for i in [1..n] do
        for j in [1..n] do
            v[(i-1)*n + j] := alpha[i] * alpha[j];
        od;
    od;
    return v;
end;;

IBKE_AlphaCupAlphaNEW := function(alpha)
    return KroneckerProduct([alpha], [alpha])[1];
end;;

# Build the F_2 hom_basis for a centraliser, exactly as the patched
# function does internally. Used to feed both forms identical α's.
IBKE_HomBasisGF2 := function(C)
    local elts, n, phi, GA, abgens, ab_orders, hom_basis, alpha_vals,
          k, ord, one;
    one := One(GF(2));
    elts := AsList(C);
    n := Length(elts);
    phi := MaximalAbelianQuotient(C);
    GA := Image(phi);
    abgens := IndependentGeneratorsOfAbelianGroup(GA);
    ab_orders := List(abgens, Order);
    hom_basis := [];
    for k in [1..Length(abgens)] do
        ord := ab_orders[k];
        if ord mod 2 = 0 then
            alpha_vals := List(elts, g ->
                (IndependentGeneratorExponents(GA, Image(phi, g))[k] mod 2) * one);
            Add(hom_basis, alpha_vals);
        fi;
    od;
    return hom_basis;
end;;

# Assemble α as the GF(2) bitwise sum of basis elements selected by mask.
# Mirrors the patched function's mask enumeration (line 138-143).
IBKE_AlphaFromMaskGF2 := function(hom_basis, mask)
    local n, num_basis, alpha, k, zero;
    num_basis := Length(hom_basis);
    zero := Zero(GF(2));
    if num_basis = 0 then return []; fi;
    n := Length(hom_basis[1]);
    alpha := List([1..n], i -> zero);
    for k in [1..num_basis] do
        if (mask mod (2^k)) >= 2^(k-1) then
            alpha := alpha + hom_basis[k];
        fi;
    od;
    return alpha;
end;;

# ----------------------------------------------------------------------
# (1) Per-α equivalence across a handful of centralisers.
#
# For each test group we enumerate ALL 2^|hom_basis| masks (matching the
# enumeration inside IsCoboundary2Mod2WithLiftWitness) and check OLD/NEW
# agree pointwise on the resulting α's. Mask = 0 (α = 0) and full-mask
# (α = sum of all basis) are both exercised.
# ----------------------------------------------------------------------
Print("\n=== (1) Per-α equivalence (OLD nested loop vs NEW KroneckerProduct) ===\n");

IBKE_TestGroup := function(label, C)
    local hom_basis, num_basis, mask, alpha, v_old, v_new, mismatches, m;
    Print("\n  Testing on ", label, " (|C| = ", Order(C), ")\n");
    hom_basis := IBKE_HomBasisGF2(C);
    num_basis := Length(hom_basis);
    Print("    |hom_basis| = ", num_basis, " (enumerating ", 2^num_basis,
          " masks)\n");
    mismatches := [];
    for mask in [0..(2^num_basis - 1)] do
        alpha := IBKE_AlphaFromMaskGF2(hom_basis, mask);
        if Length(alpha) = 0 then
            # num_basis = 0 (odd-order group): nothing to compare; old loop
            # would build a length-0 vector. Skip — the patched function's
            # outer loop range [0..0] yields a single mask=0 with empty α,
            # and KroneckerProduct on empty rows returns an empty length-0
            # row too. Both branches degenerate consistently.
        else
            v_old := IBKE_AlphaCupAlphaOLD(alpha);
            v_new := IBKE_AlphaCupAlphaNEW(alpha);
            if v_old <> v_new then
                Add(mismatches, mask);
            fi;
        fi;
    od;
    IBKEAssertTrue(
        Concatenation(label, ": all ", String(2^num_basis),
                      " masks element-equal"),
        mismatches = []);
    if mismatches <> [] then
        Print("    mismatching masks: ", mismatches, "\n");
    fi;
end;;

IBKE_TestGroup("Z/2", SmallGroup(2, 1));
IBKE_TestGroup("C_2 x C_2", SmallGroup(4, 2));
IBKE_TestGroup("Z/4", SmallGroup(4, 1));
IBKE_TestGroup("D_8", SmallGroup(8, 3));
IBKE_TestGroup("E_+(2)", SmallGroup(32, 49));

# E_+(3) centraliser: pick a non-central conjugacy class so |C_G(g)| < |G|.
Print("\n  Selecting an E_+(3) centraliser...\n");
IBKE_G3 := SmallGroup(128, 2326);;
IBKE_CC3 := ConjugacyClasses(IBKE_G3);;
IBKE_C3 := fail;;
for IBKE_cl in IBKE_CC3 do
    if Order(Representative(IBKE_cl)) > 1 then
        IBKE_C3 := Centralizer(IBKE_G3, Representative(IBKE_cl));
        if Order(IBKE_C3) < Order(IBKE_G3) then
            Print("    chose class with rep order ",
                  Order(Representative(IBKE_cl)),
                  ", |C_G(g)| = ", Order(IBKE_C3), "\n");
            break;
        fi;
    fi;
od;
if IBKE_C3 <> fail then
    IBKE_TestGroup("E_+(3) centraliser", IBKE_C3);
else
    Print("  [FAIL] could not select an E_+(3) centraliser\n");
    Add(IBKE_FAILURES, "E_+(3) centraliser selection");
fi;

# ----------------------------------------------------------------------
# (2) End-to-end witness round-trip on the β(α₁+α₂) example.
#
# Mirrors the Z/2 x Z/2 chain-level check at the bottom of
# test_iterated_bockstein.g but exercises the PATCHED
# IsCoboundary2Mod2WithLiftWitness directly: the returned witness must
# still satisfy α∪α + δβ = c (mod 2). If the KroneckerProduct rewrite
# silently produced a different α∪α, the witness would no longer
# satisfy the identity — this catches such a regression.
# ----------------------------------------------------------------------
Print("\n=== (2) Witness round-trip on Z/2 x Z/2 β(α₁+α₂) ===\n");

IBKE_K := SmallGroup(4, 2);;
IBKE_phi_K := MaximalAbelianQuotient(IBKE_K);;
IBKE_GA_K := Image(IBKE_phi_K);;
IBKE_alpha_int := function(g)
    local exps;
    exps := IndependentGeneratorExponents(IBKE_GA_K, Image(IBKE_phi_K, g));
    return (exps[1] + exps[2]) mod 2;
end;;
IBKE_beta_alpha := function(h, k)
    return (IBKE_alpha_int(h) * IBKE_alpha_int(k)) mod 2;
end;;
IBKE_witness := IsCoboundary2Mod2WithLiftWitness(IBKE_K, IBKE_beta_alpha);;
IBKEAssertTrue("witness: is_coboundary = true on β(α₁+α₂)",
               IBKE_witness.is_coboundary = true);
IBKEAssertTrue("witness: alpha_F2 is a list",
               IsList(IBKE_witness.alpha_F2));
IBKEAssertTrue("witness: beta_F2 is a list",
               IsList(IBKE_witness.beta_F2));

IBKE_elts_K := AsList(IBKE_K);;
IBKE_n_K := Length(IBKE_elts_K);;
IBKE_idx_K := function(h) return Position(IBKE_elts_K, h); end;;
IBKE_chain_ok := function()
    local i, j, lhs, alpha_cup, delta_beta_F2, ij, alpha, beta_F2, ok;
    alpha := IBKE_witness.alpha_F2;
    beta_F2 := IBKE_witness.beta_F2;
    ok := true;
    for i in [1..IBKE_n_K] do
        for j in [1..IBKE_n_K] do
            ij := IBKE_idx_K(IBKE_elts_K[i] * IBKE_elts_K[j]);
            alpha_cup := alpha[i] * alpha[j];
            delta_beta_F2 := beta_F2[i] + beta_F2[j] + beta_F2[ij];
            lhs := alpha_cup + delta_beta_F2;
            if lhs <> IBKE_beta_alpha(IBKE_elts_K[i], IBKE_elts_K[j])
                      * One(GF(2)) then
                ok := false;
            fi;
        od;
    od;
    return ok;
end;;
IBKEAssertTrue("witness: α∪α + δβ = c (mod 2) at cochain level",
               IBKE_chain_ok() = true);

# ----------------------------------------------------------------------
# (3) Microbenchmark at n = 2048.
#
# Mirrors the parent #221 test (test_bockstein_h1h2_kronecker_equiv.g):
# we want a representative measurement at the n = 2048 hot-path scale
# encountered at m = 5. We isolate the per-α inner body so the timing
# is not dominated by AbelianQuotient scaffolding.
# ----------------------------------------------------------------------
Print("\n=== (3) Microbenchmark ===\n");

IBKE_C2048 := AbelianGroup([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]);;
IBKE_n2048 := Order(IBKE_C2048);;
Print("  benchmark group: AbelianGroup([2,...,2]) of order ",
      IBKE_n2048, " (n^2 = ", IBKE_n2048 * IBKE_n2048, ")\n");

IBKE_hom_basis := IBKE_HomBasisGF2(IBKE_C2048);;
Print("  |hom_basis| = ", Length(IBKE_hom_basis),
      " (= F_2-rank of C^ab)\n");

# Use the full-mask α (sum of all basis elements) so every coordinate
# carries a non-trivial value — exercises the GF(2) multiply branch.
IBKE_alpha := IBKE_AlphaFromMaskGF2(IBKE_hom_basis,
                                    2^Length(IBKE_hom_basis) - 1);;

IBKE_TRIALS_NEW := 20;;
IBKE_TRIALS_OLD := 5;;

# Time the OLD inner body.
IBKE_zero := Zero(GF(2));;
IBKE_t0 := Runtime();;
for IBKE_trial in [1..IBKE_TRIALS_OLD] do
    IBKE_v_old := List([1..IBKE_n2048 * IBKE_n2048], i -> IBKE_zero);
    for IBKE_i in [1..IBKE_n2048] do
        for IBKE_j in [1..IBKE_n2048] do
            IBKE_v_old[(IBKE_i - 1) * IBKE_n2048 + IBKE_j]
                := IBKE_alpha[IBKE_i] * IBKE_alpha[IBKE_j];
        od;
    od;
od;
IBKE_dt_old_ms := Runtime() - IBKE_t0;;
IBKE_dt_old_per := IBKE_dt_old_ms / IBKE_TRIALS_OLD;;

# Time the NEW KroneckerProduct body.
IBKE_t0 := Runtime();;
for IBKE_trial in [1..IBKE_TRIALS_NEW] do
    IBKE_v_new := KroneckerProduct([IBKE_alpha], [IBKE_alpha])[1];
od;
IBKE_dt_new_ms := Runtime() - IBKE_t0;;
IBKE_dt_new_per := IBKE_dt_new_ms / IBKE_TRIALS_NEW;;

IBKEAssertTrue("microbenchmark: OLD result element-equal to NEW result",
               IBKE_v_old = IBKE_v_new);

Print("\n  OLD (nested for-loop): ", IBKE_dt_old_per, " ms / call (mean over ",
      IBKE_TRIALS_OLD, " trials)\n");
Print("  NEW (KroneckerProduct): ", IBKE_dt_new_per, " ms / call (mean over ",
      IBKE_TRIALS_NEW, " trials)\n");
if IBKE_dt_new_per > 0 then
    Print("  speedup (OLD / NEW): ",
          Int(100 * IBKE_dt_old_per / IBKE_dt_new_per) / 100, "x\n");
fi;

IBKEAssertTrue("microbenchmark: NEW body under 1000 ms / call",
               IBKE_dt_new_per < 1000);
IBKEAssertTrue("microbenchmark: NEW body is faster than OLD body",
               IBKE_dt_new_per < IBKE_dt_old_per);

# ----------------------------------------------------------------------
# Final report.
# ----------------------------------------------------------------------
Print("\n=== Final summary ===\n");
Print("  passes:   ", IBKE_PASSES, "\n");
Print("  failures: ", Length(IBKE_FAILURES), "\n");
if Length(IBKE_FAILURES) = 0 then
    Print("\ntest_iterated_bockstein_kronecker_equiv: PASS\n");
else
    Print("\ntest_iterated_bockstein_kronecker_equiv: FAIL (",
          Length(IBKE_FAILURES), "):\n");
    for IBKE_F in IBKE_FAILURES do
        Print("  - ", IBKE_F, "\n");
    od;
fi;

QUIT;
