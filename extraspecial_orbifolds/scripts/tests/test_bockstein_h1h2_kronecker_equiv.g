# test_bockstein_h1h2_kronecker_equiv.g — A-5b R2-3 (#186) verification.
#
# Verifies the KroneckerProduct vectorisation of the inner loop in
# BocksteinH1ToH2 (mod2_solver.g) is mathematically equivalent to the
# original nested for-loop, and measures the speedup.
#
# The change replaced:
#     v := List([1..n*n], i -> zero);
#     for i in [1..n] do
#         for j in [1..n] do
#             v[(i - 1) * n + j] := alpha_vals[i] * alpha_vals[j];
#         od;
#     od;
# with:
#     v := KroneckerProduct([alpha_vals], [alpha_vals])[1];
#
# This file:
#   (1) Reconstructs the OLD computation inline (not by reading the patched
#       file twice) and compares its output to the NEW KroneckerProduct form
#       on a handful of small group centralisers.
#   (2) Runs a microbenchmark at n = 2048 (n^2 = 4194304), matching the
#       largest centraliser size encountered at m = 5, and prints wall
#       times for both forms.
#
# Run with absolute path invocation:
#   /opt/homebrew/bin/gap -q -b \
#     /Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-a5b-r2-3/extraspecial_orbifolds/scripts/tests/test_bockstein_h1h2_kronecker_equiv.g

# Load the patched mod2_solver.g (provides the new BocksteinH1ToH2).
Read("/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-a5b-r2-3/extraspecial_orbifolds/scripts/solver/mod2_solver.g");;

# ----------------------------------------------------------------------
# Test bookkeeping.
# ----------------------------------------------------------------------
BKE_PASSES   := 0;;
BKE_FAILURES := [];;

BKEAssertTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
        BKE_PASSES := BKE_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Add(BKE_FAILURES, label);
    fi;
end;;

# ----------------------------------------------------------------------
# Inline reproduction of the OLD vec construction. This is the exact body
# of the original inner loop (the bit that was replaced). We keep the
# surrounding scaffolding identical to BocksteinH1ToH2 so we can feed the
# same hom_basis to both forms and check the vecs lists agree.
#
# Returns the LIST of length-n^2 GF(2) row vectors BEFORE BaseMat / matrix
# conversion — that's the load-bearing comparison: the new code must
# produce the same raw vecs that go into BaseMat.
# ----------------------------------------------------------------------
BocksteinH1ToH2_vecs_OLD := function(C)
    local elts, n, phi, GA, abgens, ab_orders, hom_basis, alpha_vals,
          k, ord, vecs, i, j, v, zero, one;
    elts := AsList(C);
    n := Length(elts);
    zero := Zero(GF(2));
    one  := One(GF(2));

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

    vecs := [];
    for alpha_vals in hom_basis do
        v := List([1..n*n], i -> zero);
        for i in [1..n] do
            for j in [1..n] do
                v[(i - 1) * n + j] := alpha_vals[i] * alpha_vals[j];
            od;
        od;
        Add(vecs, v);
    od;

    return vecs;
end;;

# ----------------------------------------------------------------------
# Inline reproduction of the NEW vec construction (the same body the
# patched BocksteinH1ToH2 now uses), again without BaseMat / matrix
# conversion so we compare the raw vecs.
# ----------------------------------------------------------------------
BocksteinH1ToH2_vecs_NEW := function(C)
    local elts, phi, GA, abgens, ab_orders, hom_basis, alpha_vals,
          k, ord, vecs, v, one;
    elts := AsList(C);
    one  := One(GF(2));

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

    vecs := [];
    for alpha_vals in hom_basis do
        v := KroneckerProduct([alpha_vals], [alpha_vals])[1];
        Add(vecs, v);
    od;

    return vecs;
end;;

# ----------------------------------------------------------------------
# (1) Equivalence: OLD vecs == NEW vecs for a handful of centralisers.
#
# We pick groups across a range:
#   * Z/2 — smallest non-trivial case.
#   * C_2 x C_2 — multi-generator hom_basis.
#   * Z/4 — even-order generator, hom_basis of rank 1.
#   * D_8 (= SmallGroup(8, 3)) — non-abelian, abelianisation Z/2 x Z/2.
#   * E_+(2) = SmallGroup(32, 49) — actual transgression-sweep target.
#   * A centraliser of E_+(3) — issue's reference target.
# ----------------------------------------------------------------------
Print("\n=== (1) Equivalence of OLD nested loop vs NEW KroneckerProduct ===\n");

BKETestGroup := function(label, C)
    local old_vecs, new_vecs, ok;
    Print("\n  Testing on ", label, " (|C| = ", Order(C), ")\n");
    old_vecs := BocksteinH1ToH2_vecs_OLD(C);
    new_vecs := BocksteinH1ToH2_vecs_NEW(C);
    BKEAssertTrue(
        Concatenation(label, ": Length(vecs) matches"),
        Length(old_vecs) = Length(new_vecs));
    if Length(old_vecs) = Length(new_vecs) then
        ok := ForAll([1..Length(old_vecs)],
                     i -> old_vecs[i] = new_vecs[i]);
        BKEAssertTrue(
            Concatenation(label, ": all vecs element-equal"), ok);
        if not ok then
            Print("    first mismatch: i=",
                  First([1..Length(old_vecs)],
                        i -> old_vecs[i] <> new_vecs[i]), "\n");
        fi;
    fi;
end;;

BKETestGroup("Z/2", SmallGroup(2, 1));
BKETestGroup("C_2 x C_2", SmallGroup(4, 2));
BKETestGroup("Z/4", SmallGroup(4, 1));
BKETestGroup("D_8", SmallGroup(8, 3));
BKETestGroup("E_+(2)", SmallGroup(32, 49));

# E_+(3) centraliser: pick a non-central conjugacy class so |C_G(g)| < |G|.
# The order-2 centre of E_+(3) gives |C_G(g)| = 128 for central g; for an
# off-centre class we expect |C_G(g)| = 64 (the centraliser of a Q_8/D_8-type
# generator). Either way it gives a multi-α hom_basis to exercise.
Print("\n  Selecting an E_+(3) centraliser...\n");
BKE_G3 := SmallGroup(128, 2326);;
BKE_CC3 := ConjugacyClasses(BKE_G3);;
BKE_C3 := fail;;
for BKE_cl in BKE_CC3 do
    if Order(Representative(BKE_cl)) > 1 then
        BKE_C3 := Centralizer(BKE_G3, Representative(BKE_cl));
        if Order(BKE_C3) < Order(BKE_G3) then
            Print("    chose class with rep order ", Order(Representative(BKE_cl)),
                  ", |C_G(g)| = ", Order(BKE_C3), "\n");
            break;
        fi;
    fi;
od;
if BKE_C3 <> fail then
    BKETestGroup("E_+(3) centraliser", BKE_C3);
else
    Print("  [FAIL] could not select an E_+(3) centraliser\n");
    Add(BKE_FAILURES, "E_+(3) centraliser selection");
fi;

# ----------------------------------------------------------------------
# (2) Microbenchmark.
#
# Pick the actual hot-path centraliser size at m = 5: n = 2048
# (n^2 = 4194304). At n = 256 (n^2 = 65536) the old nested loop is already
# within interpreter-noise of KroneckerProduct — both finish in a few ms,
# so the signal is dominated by Runtime() quantisation. The live m = 5
# regression hits this n directly. We exercise the same scale here so the
# microbenchmark is genuinely representative.
#
# We choose (Z/2)^11 = AbelianGroup([2,...,2]) of order 2048 to maximise
# hom_basis (11 generators all of order 2). Both forms share the
# AbelianQuotient / hom_basis phase; only the per-α inner work differs.
# ----------------------------------------------------------------------
Print("\n=== (2) Microbenchmark ===\n");

BKE_C256 := AbelianGroup([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]);;
BKE_n256 := Order(BKE_C256);;
Print("  benchmark group: AbelianGroup([2,...,2]) of order ",
      BKE_n256, " (n^2 = ", BKE_n256 * BKE_n256, ")\n");

# We will benchmark only the inner-loop body, not the AbelianQuotient
# scaffolding (which is shared and bounded). Build hom_basis once and
# then time exactly the inner vec construction over a number of trials.
BKE_elts := AsList(BKE_C256);;
BKE_one := One(GF(2));;
BKE_zero := Zero(GF(2));;
BKE_phi := MaximalAbelianQuotient(BKE_C256);;
BKE_GA := Image(BKE_phi);;
BKE_abgens := IndependentGeneratorsOfAbelianGroup(BKE_GA);;
BKE_ab_orders := List(BKE_abgens, Order);;
BKE_hom_basis := [];;
for BKE_k in [1..Length(BKE_abgens)] do
    if BKE_ab_orders[BKE_k] mod 2 = 0 then
        BKE_alpha_vals := List(BKE_elts, g ->
            (IndependentGeneratorExponents(BKE_GA, Image(BKE_phi, g))[BKE_k] mod 2) * BKE_one);
        Add(BKE_hom_basis, BKE_alpha_vals);
    fi;
od;
Print("  |hom_basis| = ", Length(BKE_hom_basis),
      " (= F_2-rank of C^ab)\n");

# Trial counts. The new form is expected to be sub-second per call; the
# old form is expected to dominate. Pick TRIALS so total wall stays modest
# but the timing signal is clear (avoid Runtime() quantisation).
BKE_TRIALS_NEW := 20;;
BKE_TRIALS_OLD := 5;;

# Time the OLD inner body.
BKE_alpha := BKE_hom_basis[1];;
BKE_t0 := Runtime();;
for BKE_trial in [1..BKE_TRIALS_OLD] do
    BKE_v_old := List([1..BKE_n256 * BKE_n256], i -> BKE_zero);
    for BKE_i in [1..BKE_n256] do
        for BKE_j in [1..BKE_n256] do
            BKE_v_old[(BKE_i - 1) * BKE_n256 + BKE_j]
                := BKE_alpha[BKE_i] * BKE_alpha[BKE_j];
        od;
    od;
od;
BKE_dt_old_ms := Runtime() - BKE_t0;;
BKE_dt_old_per := BKE_dt_old_ms / BKE_TRIALS_OLD;;

# Time the NEW KroneckerProduct body.
BKE_t0 := Runtime();;
for BKE_trial in [1..BKE_TRIALS_NEW] do
    BKE_v_new := KroneckerProduct([BKE_alpha], [BKE_alpha])[1];
od;
BKE_dt_new_ms := Runtime() - BKE_t0;;
BKE_dt_new_per := BKE_dt_new_ms / BKE_TRIALS_NEW;;

# Element-equal at n = 256 too (final sanity).
BKEAssertTrue("microbenchmark: OLD result element-equal to NEW result",
              BKE_v_old = BKE_v_new);

Print("\n  OLD (nested for-loop): ", BKE_dt_old_per, " ms / call (mean over ",
      BKE_TRIALS_OLD, " trials)\n");
Print("  NEW (KroneckerProduct): ", BKE_dt_new_per, " ms / call (mean over ",
      BKE_TRIALS_NEW, " trials)\n");
if BKE_dt_new_per > 0 then
    # BKE_dt_*_per may be rational (Runtime() returns ms; / TRIALS yields
    # a rational mean). Cast through Int for the speedup ratio display.
    Print("  speedup (OLD / NEW): ",
          Int(100 * BKE_dt_old_per / BKE_dt_new_per) / 100, "x\n");
fi;

# Acceptance check: NEW should be sub-second and much faster than OLD.
BKEAssertTrue("microbenchmark: NEW body under 1000 ms / call",
              BKE_dt_new_per < 1000);
BKEAssertTrue("microbenchmark: NEW body is faster than OLD body",
              BKE_dt_new_per < BKE_dt_old_per);

# ----------------------------------------------------------------------
# Final report.
# ----------------------------------------------------------------------
Print("\n=== Final summary ===\n");
Print("  passes:   ", BKE_PASSES, "\n");
Print("  failures: ", Length(BKE_FAILURES), "\n");
if Length(BKE_FAILURES) = 0 then
    Print("\ntest_bockstein_h1h2_kronecker_equiv: PASS\n");
else
    Print("\ntest_bockstein_h1h2_kronecker_equiv: FAIL (",
          Length(BKE_FAILURES), "):\n");
    for BKE_F in BKE_FAILURES do
        Print("  - ", BKE_F, "\n");
    od;
fi;

QUIT;
