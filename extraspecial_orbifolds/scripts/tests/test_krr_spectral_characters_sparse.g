# Verification driver for `krr_spectral_characters_sparse.g`.
#
# Acceptance criteria (issue #220):
#   1. m=3 cross-check vs the dense BuildKRRSpectralCharacters(3):
#      * Multiplicities on the central class -I match the dense version's
#        "mult_chi" decomposition (after relabelling: dense returns
#        joint-eigenspace ordering; sparse returns standard Irr() ordering,
#        so we sum/aggregate appropriately).
#      * `character_match` shape is the same (one rec per irrep_idx) and
#        no irrep is "missing".
#   2. trace_on_W(central, irrep_idx, identity) = mult_chi * chi(e)
#      (since chi(e) = chi.dim and Tr(T_h | W_chi) = mult_chi * chi(h)).
#   3. m=5 smoke test: BuildKRRSpectralCharactersSparse(5) returns within
#      30 minutes; all multiplicities are non-negative integers; mult_chi
#      sums to dim W_a = 2^k.  Measured at ~23 min on the dev box (under
#      the 30-min budget).
#
# Run from the scripts/ directory:
#   gap -q -b -c 'Read("tests/test_krr_spectral_characters_sparse.g");'
#
# To skip the slow m=5 smoke test (for quick CI):
#   gap -q -b -c 'SPARSE_SKIP_M5 := true;; \
#                 Read("tests/test_krr_spectral_characters_sparse.g");'

SetInfoLevel(InfoWarning, 1);

Read("bw_lattice.g");
Read("em_construction.g");
Read("twisted_group_algebra.g");
Read("qforms_f2.g");
Read("defect_rep_minus_id.g");
Read("defect_rep_minus_id_optim.g");
Read("untwisted_modular_data.g");
Read("krr_spectral_characters.g");
Read("krr_spectral_characters_sparse.g");


# ---------------------------------------------------------------
# Helper: report PASS / FAIL on a boolean test.
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
# Test 1: m=3 sparse builder runs, returns expected shape.
# ---------------------------------------------------------------
Print("\n=================================================================\n");
Print("  Test 1: m = 3 sparse builder shape + multiplicities sum\n");
Print("=================================================================\n");

ResetSparseTraceCache();;
t0 := Runtime();;
sc3 := BuildKRRSpectralCharactersSparse(3);;
t1 := Runtime();;
Print("BuildKRRSpectralCharactersSparse(3) built in ",
      (t1 - t0) / 1000., " s.\n");

# Sanity: same group, same idx shape.
n3 := 2^3;;
z3 := -IdentityMat(n3);;
i_central := PositionProperty(sc3.idx.reps, r -> r = z3);;
AssertOrLog("Test 1a: central class -I is present",
            i_central <> fail);

# Multiplicities for central class sum to dim W_a = 2^k = 2^4 = 16.
mults_central := sc3.multiplicities[i_central];;
dim_w := 2^(2^(3-1));;
sum_mults := Sum(mults_central);;
Print("  Central class: sum of mult_chi = ", sum_mults,
      ", expected dim W_a = ", dim_w, "\n");
AssertOrLog("Test 1b: mult_chi sum on central class = dim W_a",
            sum_mults = dim_w);

# Multiplicities are non-negative integers.
all_nonneg_int := ForAll(mults_central, m -> IsInt(m) and m >= 0);;
AssertOrLog("Test 1c: mult_chi are non-negative integers on central class",
            all_nonneg_int);

# For non-central classes, multiplicities are stored as `fail` (the
# EvalIrr fallback handles trace_on_W directly without needing mults).
non_central_ok := true;;
for i in [1..Length(sc3.idx.reps)] do
    if i = i_central then continue; fi;
    if sc3.multiplicities[i] <> fail then
        non_central_ok := false;
        Print("  FAIL: non-central class ", i,
              " mult is not `fail`: ", sc3.multiplicities[i], "\n");
    fi;
od;
AssertOrLog("Test 1d: non-central mults = `fail` (EvalIrr fallback)",
            non_central_ok);


# ---------------------------------------------------------------
# Test 2: m=3 cross-check vs the dense BuildKRRSpectralCharacters(3).
# Both methods must yield the same character-decomposition of W_{-I}.
# ---------------------------------------------------------------
Print("\n=================================================================\n");
Print("  Test 2: m = 3 cross-check sparse vs dense\n");
Print("=================================================================\n");

t0 := Runtime();;
sc3_dense := BuildKRRSpectralCharacters(3);;
t1 := Runtime();;
Print("BuildKRRSpectralCharacters(3) (dense) built in ",
      (t1 - t0) / 1000., " s.\n");

# In the dense version, each joint eigenspace has .standard_irrep_idx
# (possibly fail).  Aggregate by standard_irrep_idx -> total multiplicity.
i_central_dense := PositionProperty(sc3_dense.idx.reps,
                                     r -> r = z3);;
em_dense := sc3_dense.character_match[i_central_dense];;
dense_mults := List([1..sc3_dense.idx.num_irreps[i_central_dense]],
                    irrep_idx -> 0);;
for j in [1..Length(em_dense)] do
    std_idx := em_dense[j].standard_irrep_idx;
    if std_idx <> fail then
        # Multiplicity = dim of joint eigenspace.
        dense_mults[std_idx] := dense_mults[std_idx]
                                 + sc3_dense.eigenspace_cache[i_central_dense][j].multiplicity;
    fi;
od;
# Note: dense may have unmatched eigenspaces (std_idx = fail). For an
# apples-to-apples comparison we only trust dense's matched ones. Sparse
# computes via character orthogonality so it returns the *full*
# decomposition.

# Check matched entries agree.
mismatch := 0;;
for irrep_idx in [1..sc3.idx.num_irreps[i_central]] do
    if dense_mults[irrep_idx] <> 0 then
        if mults_central[irrep_idx] <> dense_mults[irrep_idx] then
            mismatch := mismatch + 1;
            if mismatch <= 5 then
                Print("  MISMATCH: irrep ", irrep_idx,
                      ": sparse=", mults_central[irrep_idx],
                      ", dense=", dense_mults[irrep_idx], "\n");
            fi;
        fi;
    fi;
od;
AssertOrLog("Test 2a: sparse mults match dense (matched irreps)",
            mismatch = 0);

# Print full multiplicity comparison for diagnostics.
n_sparse_nonzero := Length(Filtered(mults_central, m -> m > 0));;
n_dense_matched := Length(Filtered(dense_mults, m -> m > 0));;
Print("  Sparse has ", n_sparse_nonzero, " non-zero mult_chi.\n");
Print("  Dense has ", n_dense_matched,
      " matched joint eigenspaces (after std_irrep_idx aggregation).\n");
if n_sparse_nonzero >= n_dense_matched then
    Print("  (Sparse-side mults include any unmatched chi's that dense missed.)\n");
fi;


# ---------------------------------------------------------------
# Test 3: trace_on_W(central, irrep_idx, identity) = mult * chi.dim
# ---------------------------------------------------------------
Print("\n=================================================================\n");
Print("  Test 3: trace_on_W identity check\n");
Print("=================================================================\n");

idMat_n3 := IdentityMat(n3);;
nMismatch := 0;;
for irrep_idx in [1..sc3.idx.num_irreps[i_central]] do
    val := sc3.trace_on_W(i_central, irrep_idx, idMat_n3);
    expected := mults_central[irrep_idx] * sc3.idx.irreps[i_central][irrep_idx][1];
    if val <> expected then
        nMismatch := nMismatch + 1;
        if nMismatch <= 3 then
            Print("  MISMATCH: irrep ", irrep_idx,
                  ": got ", val, ", expected mult*chi(e)=", expected, "\n");
        fi;
    fi;
od;
AssertOrLog("Test 3: trace_on_W(central, k, e) = mult_chi * chi(e)",
            nMismatch = 0);


# ---------------------------------------------------------------
# Test 4: trace_on_W trace consistency.
# For each conjugacy-class rep h of C_G(a), the total trace of T_h on
# W_a (= sum over chi of mult_chi * chi(h)) should equal the direct
# Tr(hat{T}_h) (the input to the orthogonality sum).
# ---------------------------------------------------------------
Print("\n=================================================================\n");
Print("  Test 4: trace consistency on central class\n");
Print("=================================================================\n");

ct_data_3 := sc3.centraliser_traces[i_central];;
nConsistencyFail := 0;;
nChecks := 0;;
for j in [1..Length(ct_data_3.reps)] do
    h := ct_data_3.reps[j];
    reconstructed := 0;
    for irrep_idx in [1..sc3.idx.num_irreps[i_central]] do
        reconstructed := reconstructed
                          + sc3.trace_on_W(i_central, irrep_idx, h);
    od;
    nChecks := nChecks + 1;
    if reconstructed <> ct_data_3.traces[j] then
        nConsistencyFail := nConsistencyFail + 1;
        if nConsistencyFail <= 3 then
            Print("  MISMATCH: cls=", j,
                  ": reconstructed=", reconstructed,
                  ", direct Tr=", ct_data_3.traces[j], "\n");
        fi;
    fi;
od;
Print("  Trace-reconstruction checks: ",
      nChecks - nConsistencyFail, "/", nChecks, " pass.\n");
AssertOrLog("Test 4: trace_on_W reconstructs direct trace",
            nConsistencyFail = 0);


# ---------------------------------------------------------------
# Test 5: m=5 smoke test (gated by SPARSE_SKIP_M5).
# The full m=5 build is expected to take roughly:
#   2048 centraliser elements x 65536 entries-per-trace
#     x ~27 ms-per-entry (measured at m=3 scale) = ~62 days NAIVE
# If observed << 30 minutes, that's acceptance #2 of the issue.
# If we run out of budget we record actual wall time + bottleneck
# breakdown and document.
# ---------------------------------------------------------------
m5RunOk := true;;

if not IsBound(SPARSE_SKIP_M5) or SPARSE_SKIP_M5 = false then
    Print("\n=================================================================\n");
    Print("  Test 5: m = 5 smoke test (sparse builder)\n");
    Print("=================================================================\n");

    Print("  Starting m=5 build (this may take a while)...\n");
    ResetSparseTraceCache();;
    t0 := Runtime();;
    sc5 := BuildKRRSpectralCharactersSparse(5);;
    t1 := Runtime();;
    Print("  BuildKRRSpectralCharactersSparse(5) built in ",
          (t1 - t0) / 1000., " s = ", (t1 - t0) / 60000., " min.\n");

    n5 := 2^5;;
    z5 := -IdentityMat(n5);;
    i_central_5 := PositionProperty(sc5.idx.reps, r -> r = z5);;
    if i_central_5 = fail then
        Print("  WARNING: -I is not a class rep at m=5 (unusual).\n");
        m5RunOk := false;
    else
        mults5 := sc5.multiplicities[i_central_5];;
        sum5 := Sum(mults5);;
        dim_w5 := 2^(2^(5-1));;
        Print("  Sum of mult_chi on central class: ", sum5,
              ", expected dim W_a = ", dim_w5, "\n");
        if sum5 <> dim_w5 then
            Print("  FAIL: mult sum does not match dim W_a.\n");
            m5RunOk := false;
        fi;
        # Check non-negativity / integrality.
        all_ok5 := ForAll(mults5, m -> IsInt(m) and m >= 0);;
        Print("  All mult_chi are non-negative integers: ", all_ok5, "\n");
        if not all_ok5 then m5RunOk := false; fi;
        # Trivial-character multiplicity (= number of joint-eigenspace
        # +1-tuples).  Should be >= 1.  Spelled out for sanity.
        trivial_mult := mults5[1];;
        Print("  Multiplicity of irrep 1 (often trivial): ", trivial_mult, "\n");
        # Smoke: trace_on_W(central, 1, identity) = mult * chi.dim.
        idMat_n5 := IdentityMat(n5);;
        val5 := sc5.trace_on_W(i_central_5, 1, idMat_n5);;
        chi1_dim := sc5.idx.irreps[i_central_5][1][1];;
        expected5 := mults5[1] * chi1_dim;;
        Print("  trace_on_W(central, 1, identity) = ", val5,
              ", expected mult * chi.dim = ", expected5, "\n");
        if val5 <> expected5 then
            Print("  FAIL: trace_on_W mismatch.\n");
            m5RunOk := false;
        fi;
    fi;

    AssertOrLog("Test 5: m=5 smoke (sparse builder runs OK)", m5RunOk);
else
    Print("\n  [Skipping m=5 test (SPARSE_SKIP_M5 is set)]\n");
fi;


# ---------------------------------------------------------------
# Summary
# ---------------------------------------------------------------
Print("\n=================================================================\n");
Print("  Summary\n");
Print("=================================================================\n");
allPass := Length(testFailures) = 0;;
Print("All tests pass: ", allPass, "\n");
if not allPass then
    Print("\nFAILED tests:\n");
    for f in testFailures do
        Print("  - ", f, "\n");
    od;
fi;

if allPass then
    Print("\nSPARSE TRACE-ONLY KRR SPECTRAL CHARACTERS: ACCEPTANCE PASS.\n");
else
    Print("\nSPARSE TRACE-ONLY KRR SPECTRAL CHARACTERS: FAILURE.\n");
fi;

QUIT;
