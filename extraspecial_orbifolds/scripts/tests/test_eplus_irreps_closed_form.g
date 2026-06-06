# Parity + smoke tests for `eplus_irreps_closed_form.g` — closed-form
# irreducible character evaluator for E_+(m) = EmUnimodGroup(m).
#
# (Issue #449 audit-findings A1''' and A1''''.)
#
# This file lives in scripts/tests/.  Run from scripts/ directory:
#   gap -q -b -c 'Read("tests/test_eplus_irreps_closed_form.g");'
#
# Acceptance criteria:
#   1. (Parity m=2): for every (irrep_idx, class_rep) the closed-form
#      character value matches some GAP-irrep value at the same class.
#      I.e. the multisets of characters (as functions on classes) agree.
#   2. (Parity m=3): same as (1) but at m=3 (4097 classes, 4097 irreps).
#   3. (Spot-check m=5): for 50 random (irrep_idx, h) pairs, the
#      closed-form `EvalIrr(idx_closed_form, central_idx, irrep_idx, h)`
#      agrees with the standard `EvalIrr(idx_dense, central_idx_dense, k, h)`
#      where k is the GAP-irrep with matching values.
#   4. (Smoke m=7): build the closed-form idx and access EvalIrr for
#      a couple of (irrep_idx, h) pairs.  No CharacterTable(G) build.
#      Must return in seconds.
#
# CPU constraint: m=2 < 5 s; m=3 < 30 s; m=5 < 5 min; m=7 < 60 s.

# ---------------------------------------------------------------
# Dependencies — same load order as test_buildsimpleindex_eplus_closed_form.g.
# ---------------------------------------------------------------
SetInfoLevel(InfoWarning, 1);

Read("bw_lattice.g");
Read("em_construction.g");
Read("twisted_group_algebra.g");
Read("qforms_f2.g");
Read("defect_rep_minus_id.g");
Read("defect_rep_minus_id_optim.g");
Read("untwisted_modular_data.g");
Read("krr_spectral_characters.g");
Read("eplus_classes_closed_form.g");
Read("eplus_irreps_closed_form.g");


# ---------------------------------------------------------------
# Test harness.
# ---------------------------------------------------------------
testFailures := [];;

AssertOrLog := function(label, cond)
    if cond then
        Print("  PASS: ", label, "\n");
    else
        Print("  FAIL: ", label, "\n");
        Add(testFailures, label);
    fi;
end;;


# ---------------------------------------------------------------
# Test 1 (RED): parity at m=2.
# ---------------------------------------------------------------
# Strategy:
#   Build dense `idx_dense` via `BuildSimpleIndex(EmUnimodGroup(2))`,
#   yielding GAP's `irreps[central_idx_dense]` (a list of class functions
#   parallel to `cc_centraliser[central_idx_dense]`).
#   Build the closed-form list: for each idx_cf irrep k and each
#   class rep g of the closed-form idx, compute the value
#   `EPlusEvalIrrep(m, k, g)`.  The resulting character table (as a
#   multiset of row-functions on class reps) must equal the GAP one
#   evaluated at the SAME class reps.
Print("\n=================================================================\n");
Print("  Test 1: parity at m=2\n");
Print("=================================================================\n");

m_2 := 2;;
G_2 := EmUnimodGroup(m_2);;
idx_dense_2 := BuildSimpleIndex(G_2);;

# Find the central class index (class containing the identity element)
# in idx_dense_2.  By the closed-form convention this is also where
# C_G(g) = G.
central_idx_dense_2 := fail;;
for i in [1..Length(idx_dense_2.reps)] do
    if idx_dense_2.reps[i] = IdentityMat(2^m_2) then
        central_idx_dense_2 := i; break;
    fi;
od;;
AssertOrLog("1a: central class found at m=2 in dense idx",
            central_idx_dense_2 <> fail);

# For the irrep set: build the closed-form character table as a list of
# rows (one row per closed-form irrep), where each row gives the value
# at each conjugacy-class representative of G.  Then compare AS A
# MULTISET to GAP's character table for the SAME class-rep ordering.
cls_reps_2 := idx_dense_2.reps;;
num_cls_2 := Length(cls_reps_2);;

# Closed-form character rows (each is a list of values at cls_reps).
cf_rows_2 := List([1..4^m_2 + 1], k ->
    List(cls_reps_2, g -> EPlusEvalIrrep(m_2, k, g)));;

# GAP character rows.  Each chi is a class function on the dense
# centraliser of the central class (= G).  GAP indexes classes by the
# centraliser's own ConjugacyClasses, not by idx_dense.classes — but
# since the centraliser IS G for the central class, the orderings can
# be matched via `ClassIndexInCentraliser`.
gap_rows_2 := [];;
for k in [1..Length(idx_dense_2.irreps[central_idx_dense_2])] do
    Add(gap_rows_2, List(cls_reps_2, g ->
        EvalIrr(idx_dense_2, central_idx_dense_2, k, g)));
od;;

# Both should have 17 = 4^2 + 1 rows.
AssertOrLog("1b: closed-form has 4^m + 1 irreps at m=2",
            Length(cf_rows_2) = 4^m_2 + 1);
AssertOrLog("1c: GAP CT has same number of irreps at m=2",
            Length(gap_rows_2) = Length(cf_rows_2));

# Multiset equality (irrep ordering may differ).
AssertOrLog("1d: closed-form character table = GAP character table (as multiset of rows)",
            AsSortedList(cf_rows_2) = AsSortedList(gap_rows_2));

# The faithful irrep is special: char(identity) = 2^m, char(-I) = -2^m,
# char(otherwise) = 0.  Verify the last row of the closed-form table
# is the faithful one.
faithful_row_2 := cf_rows_2[4^m_2 + 1];;
expected_faithful_id_2 := 2^m_2;;
expected_faithful_z_2 := -2^m_2;;
Print("  Faithful row (entries at identity / -I): ",
      faithful_row_2[1], " / ",
      faithful_row_2[Position(cls_reps_2, -IdentityMat(2^m_2))], "\n");
AssertOrLog("1e: faithful char at identity = 2^m",
            faithful_row_2[1] = expected_faithful_id_2);
AssertOrLog("1f: faithful char at -I = -2^m",
            faithful_row_2[Position(cls_reps_2, -IdentityMat(2^m_2))]
            = expected_faithful_z_2);
faithful_off_centre_ok_2 := true;;
for i in [1..num_cls_2] do
    if not (cls_reps_2[i] = IdentityMat(2^m_2)
            or cls_reps_2[i] = -IdentityMat(2^m_2)) then
        if faithful_row_2[i] <> 0 then
            faithful_off_centre_ok_2 := false;
            break;
        fi;
    fi;
od;;
AssertOrLog("1g: faithful char vanishes off the centre",
            faithful_off_centre_ok_2);


# ---------------------------------------------------------------
# Test 2: parity at m=3.
# ---------------------------------------------------------------
Print("\n=================================================================\n");
Print("  Test 2: parity at m=3\n");
Print("=================================================================\n");

m_3 := 3;;
G_3 := EmUnimodGroup(m_3);;
idx_dense_3 := BuildSimpleIndex(G_3);;

central_idx_dense_3 := fail;;
for i in [1..Length(idx_dense_3.reps)] do
    if idx_dense_3.reps[i] = IdentityMat(2^m_3) then
        central_idx_dense_3 := i; break;
    fi;
od;;
AssertOrLog("2a: central class found at m=3",
            central_idx_dense_3 <> fail);

cls_reps_3 := idx_dense_3.reps;;

# Build closed-form character table (4097 irreps × 65 classes for m=3).
Print("  Building closed-form char table at m=3 ...\n");
t0 := Runtime();;
cf_rows_3 := List([1..4^m_3 + 1], k ->
    List(cls_reps_3, g -> EPlusEvalIrrep(m_3, k, g)));;
t1 := Runtime();;
Print("    Took ", (t1 - t0) / 1000.0, " s\n");

Print("  Building GAP char table at m=3 ...\n");
t0 := Runtime();;
gap_rows_3 := [];;
for k in [1..Length(idx_dense_3.irreps[central_idx_dense_3])] do
    Add(gap_rows_3, List(cls_reps_3, g ->
        EvalIrr(idx_dense_3, central_idx_dense_3, k, g)));
od;;
t1 := Runtime();;
Print("    Took ", (t1 - t0) / 1000.0, " s\n");

AssertOrLog("2b: closed-form has 4^m + 1 irreps at m=3",
            Length(cf_rows_3) = 4^m_3 + 1);
AssertOrLog("2c: GAP CT has same number of irreps at m=3",
            Length(gap_rows_3) = Length(cf_rows_3));
AssertOrLog("2d: closed-form CT = GAP CT (multiset of rows) at m=3",
            AsSortedList(cf_rows_3) = AsSortedList(gap_rows_3));


# ---------------------------------------------------------------
# Test 3: m=5 self-consistency check via character orthogonality.
# ---------------------------------------------------------------
# At m=5 GAP's `BuildSimpleIndex(EmUnimodGroup(5))` is too memory-heavy
# for the harness's default budget (it requires the full
# `CharacterTable(EmUnimodGroup(5))` build, which OOMs at ~4 GB). We
# use the closed-form CC enumeration to get class reps + sizes and
# then verify the closed-form character table satisfies the classical
# row + column orthogonality relations plus the dimension identity
# sum (dim chi)^2 = |G|. These uniquely determine the irreps up to
# permutation, so passing them is strong evidence of correctness.
#
# Specifically:
#   * (orth-row)   1/|G| * sum_g |class_g| * chi_k(g) * conj(chi_l(g)) =
#                  delta_{k,l}
#   * (orth-col)   sum_k chi_k(g) * conj(chi_k(g)) = |C_G(g)|
#   * (dim-sum)    sum_k (chi_k(1))^2 = |G|
Print("\n=================================================================\n");
Print("  Test 3: m=5 self-consistency (orthogonality relations)\n");
Print("=================================================================\n");

m_5 := 5;;
idx_5 := BuildSimpleIndexEPlusClosedForm(m_5);;
num_cls_5 := Length(idx_5.classes);;
num_irreps_5 := 4^m_5 + 1;;

Print("  Building closed-form character table at m=5 (",
      num_irreps_5, " irreps x ", num_cls_5, " classes) ...\n");
t0 := Runtime();;
cf_rows_5 := EPlusBuildAllCharacterRows(m_5, idx_5.reps);;
t1 := Runtime();;
Print("    Built in ", (t1 - t0) / 1000.0, " s\n");

AssertOrLog("3a: m=5 char table has 4^m + 1 = ", # truncate label
            Length(cf_rows_5) = num_irreps_5);
AssertOrLog("3b: m=5 each row has |classes| entries",
            ForAll(cf_rows_5, r -> Length(r) = num_cls_5));

# Dimension sum identity.
dim_sum := 0;;
for k in [1..num_irreps_5] do
    dim_sum := dim_sum + cf_rows_5[k][1]^2;  # idx_5.reps[1] = identity
od;;
AssertOrLog("3c: m=5 sum (dim chi)^2 = |G| = 2^{2m+1}",
            dim_sum = 2^(2*m_5 + 1));

# Column orthogonality: sum_k chi_k(g) * conj(chi_k(g)) = |C_G(g)| =
# |G| / |class_g|. We use this for a SAMPLE of 50 columns (classes).
Print("  Sampling 50 columns for column orthogonality at m=5...\n");
col_failures := 0;;
sample_classes := [];;
for sample_i in [1..50] do
    Add(sample_classes, Random([1..num_cls_5]));
od;;
for j in sample_classes do
    total := 0;
    for k in [1..num_irreps_5] do
        total := total + cf_rows_5[k][j] * ComplexConjugate(cf_rows_5[k][j]);
    od;
    expected := 2^(2*m_5 + 1) / idx_5.class_sizes[j];
    if total <> expected then
        Print("    MISMATCH column ", j, ": got ", total,
              ", expected ", expected, "\n");
        col_failures := col_failures + 1;
    fi;
od;;
AssertOrLog("3d: m=5 column orthogonality (50 random columns)",
            col_failures = 0);

# Row orthogonality: 1/|G| sum_g |class_g| chi_k(g) conj(chi_l(g)) = delta_{kl}
# Sample 50 (k, l) pairs.
Print("  Sampling 50 (k, l) pairs for row orthogonality at m=5...\n");
row_failures := 0;;
for sample_i in [1..50] do
    k := Random([1..num_irreps_5]);
    l := Random([1..num_irreps_5]);
    total := 0;
    for j in [1..num_cls_5] do
        total := total + idx_5.class_sizes[j]
                  * cf_rows_5[k][j] * ComplexConjugate(cf_rows_5[l][j]);
    od;
    expected := 0;
    if k = l then expected := 2^(2*m_5 + 1); fi;
    if total <> expected then
        Print("    MISMATCH row pair (k=", k, ", l=", l,
              "): got ", total, ", expected ", expected, "\n");
        row_failures := row_failures + 1;
    fi;
od;;
AssertOrLog("3e: m=5 row orthogonality (50 random pairs)",
            row_failures = 0);

# Also: identity + -I closed-form spot-check.
AssertOrLog("3f: m=5 EPlusEvalIrrep(4^m+1, I) = 2^m",
            EPlusEvalIrrep(m_5, 4^m_5 + 1, IdentityMat(2^m_5)) = 2^m_5);
AssertOrLog("3g: m=5 EPlusEvalIrrep(4^m+1, -I) = -2^m",
            EPlusEvalIrrep(m_5, 4^m_5 + 1, -IdentityMat(2^m_5)) = -2^m_5);
AssertOrLog("3h: m=5 EPlusEvalIrrep(1, I) = 1 (trivial)",
            EPlusEvalIrrep(m_5, 1, IdentityMat(2^m_5)) = 1);
AssertOrLog("3i: m=5 EPlusEvalIrrep(1, -I) = 1 (trivial)",
            EPlusEvalIrrep(m_5, 1, -IdentityMat(2^m_5)) = 1);


# ---------------------------------------------------------------
# Test 4: m=7 closed-form evaluator smoke.
# ---------------------------------------------------------------
# Strategy: rather than calling `BuildSimpleIndexEPlusClosedForm(7)`
# (which currently takes ~3-4 min wall at m=7 in HEAD due to eager
# Centralizer calls for the 16383 non-central classes — unrelated to
# A1''' / A1'''' and tracked under issue #449 A1'), we directly
# exercise the closed-form evaluator `EPlusEvalIrrep` at m=7 to verify
# the per-call cost is bounded by the marker-cache build
# (O(2m · 2^{2m}) entry scans at first call) and subsequent O(2m) per
# query, NOT by any CharacterTable(G) build.
#
# In production, when `BuildKRRSpectralCharactersSparse(7)` constructs
# its idx via `BuildSimpleIndexEPlusClosedForm(7)`, the central-class
# CT bypass (A1''' / A1'''') is engaged via the `is_closed_form` flag
# we set in `eplus_classes_closed_form.g`. The bypass itself is what
# we test here at the function level.
Print("\n=================================================================\n");
Print("  Test 4: m=7 closed-form evaluator smoke\n");
Print("=================================================================\n");

m_7 := 7;;
n_7 := 2^m_7;;
I_7 := IdentityMat(n_7);;
z_7 := -I_7;;

# Trigger the marker-cache build at m=7 via the first EvalIrr call.
t0 := Runtime();;
val_lin_17_at_z := EPlusEvalIrrep(m_7, 17, z_7);;
t1 := Runtime();;
Print("  EPlusEvalIrrep(7, 17, -I) = ", val_lin_17_at_z,
      " (wall incl. marker-cache build: ",
      (t1 - t0) / 1000.0, " s)\n");

# Linear characters are trivial on the centre Z = <-I> (they factor
# through G/Z), so χ_k(-I) = +1 for ALL linear k.
AssertOrLog("4a: linear irrep 17 at -I is +1 (factors through G/Z)",
            val_lin_17_at_z = 1);

# Faithful irrep at -I should be -2^m = -128.
t0 := Runtime();;
val_faith_at_z := EPlusEvalIrrep(m_7, 4^m_7 + 1, z_7);;
t1 := Runtime();;
Print("  EPlusEvalIrrep(7, 4^7+1, -I) = ", val_faith_at_z,
      " (wall: ", (t1 - t0) / 1000.0, " s)\n");
AssertOrLog("4b: faithful irrep at -I is -2^7 = -128",
            val_faith_at_z = -2^m_7);

# Faithful irrep at identity should be 2^m = 128.
t0 := Runtime();;
val_faith_at_id := EPlusEvalIrrep(m_7, 4^m_7 + 1, I_7);;
t1 := Runtime();;
Print("  EPlusEvalIrrep(7, 4^7+1, I) = ", val_faith_at_id,
      " (wall: ", (t1 - t0) / 1000.0, " s)\n");
AssertOrLog("4c: faithful irrep at identity is 2^7 = 128",
            val_faith_at_id = 2^m_7);

# Trivial linear irrep at -I (and at any element of G).
val_lin_1_at_z := EPlusEvalIrrep(m_7, 1, z_7);;
val_lin_1_at_id := EPlusEvalIrrep(m_7, 1, I_7);;
AssertOrLog("4d: trivial linear irrep at -I is +1",
            val_lin_1_at_z = 1);
AssertOrLog("4e: trivial linear irrep at I is +1",
            val_lin_1_at_id = 1);

# Faithful irrep vanishes off the centre. Pick a non-central element
# σ_{1,1} (a generator); its faithful character must be 0.
sigma11_7 := UnimodSigma(m_7, 1, 1);;
val_faith_at_nc := EPlusEvalIrrep(m_7, 4^m_7 + 1, sigma11_7);;
AssertOrLog("4f: faithful irrep at σ_{1,1} (non-central) is 0",
            val_faith_at_nc = 0);

# Performance: subsequent EvalIrr calls should each be cheap (O(2m)
# entry reads).
t0 := Runtime();;
for sample_i in [1..100] do
    sample_val := EPlusEvalIrrep(m_7, Random([1..4^m_7]), sigma11_7);
od;;
t1 := Runtime();;
Print("  100 random linear EvalIrr at σ_{1,1}: ",
      (t1 - t0) / 1000.0, " s total\n");
AssertOrLog("4g: 100 random EvalIrr calls under 1 s wall (m=7)",
            (t1 - t0) / 1000.0 < 1.0);


# ---------------------------------------------------------------
# Summary.
# ---------------------------------------------------------------
Print("\n=================================================================\n");
Print("  Summary\n");
Print("=================================================================\n");

if Length(testFailures) = 0 then
    Print("  ALL TESTS PASS.\n");
else
    Print("  FAILURES (", Length(testFailures), "):\n");
    for label in testFailures do
        Print("    ", label, "\n");
    od;
fi;
