# Verification driver for `TraceOnOmega0Gauss` (issue #236).
#
# Acceptance criteria (issue #236):
#   1. `TraceOnOmega0Gauss(h, m)` implemented and consumed by
#      `BuildKRRSpectralCharactersSparse(m)` at m=7.
#   2. m=5 cross-validation: for every conjugacy class h in C_G(-I) at
#      m=5 (1025 classes), TraceOnOmega0Gauss(h, 5) equals
#      TraceOnOmega0Batch(h, 5).  1025/1025 PASS.
#   3. m=7 build: BuildKRRSpectralCharactersSparse(7) returns within
#      < 5 minutes.
#   4. m=7 sanity: sum of mults on central class equals dim Omega_0
#      = 2^k = 2^64; all mults are non-negative integers.
#   5. m=7 a few trivial-irrep multiplicities reported for inspection.
#
# Run from the scripts/ directory:
#   gap -q -b -c 'Read("tests/test_krr_gauss_sum.g");'
#
# Optional environment switches:
#   GAUSS_SKIP_M7 := true   skip the m=7 build (acceptance #3/#4/#5).
#   GAUSS_SKIP_M3 := true   skip the m=3 micro cross-check.

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
# Test harness: PASS / FAIL on bool.
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


# ===============================================================
# Test 0: m = 3 micro cross-check.
# Compare TraceOnOmega0Gauss against the entry-summing
# TraceOnOmega0Batch on every conjugacy-class rep of C_G(-I) at m=3.
# At m=3 the centraliser is E(3) with 33 classes; both methods are
# trivially fast.
# ===============================================================

if not IsBound(GAUSS_SKIP_M3) or GAUSS_SKIP_M3 = false then
    Print("\n=================================================================\n");
    Print("  Test 0: m = 3 cross-check  Gauss vs entry-sum\n");
    Print("=================================================================\n");

    ResetSparseTraceCache();;
    ResetTraceHCache();;
    ResetGaussCtxCache();;

    G3 := EmUnimodGroup(3);;
    cls3 := ConjugacyClasses(G3);;
    reps3 := List(cls3, Representative);;
    Print("  C_G(-I) at m=3 has ", Length(reps3), " conjugacy classes.\n");

    n_fail_m3 := 0;;
    t0 := Runtime();;
    for j in [1..Length(reps3)] do
        h := reps3[j];
        vGauss := TraceOnOmega0Gauss(h, 3);
        vBatch := TraceOnOmega0Batch(h, 3);
        if vGauss <> vBatch then
            n_fail_m3 := n_fail_m3 + 1;
            if n_fail_m3 <= 5 then
                Print("    MISMATCH at class ", j,
                      ": Gauss=", vGauss, "  Batch=", vBatch, "\n");
            fi;
        fi;
    od;
    t1 := Runtime();;
    Print("  m=3 cross-check: ", Length(reps3) - n_fail_m3, "/",
          Length(reps3), " match (", (t1 - t0) / 1000., " s).\n");
    AssertOrLog("Test 0: m=3 Gauss == Batch on all centraliser classes",
                n_fail_m3 = 0);
else
    Print("\n  [Skipping m=3 cross-check (GAUSS_SKIP_M3 set)]\n");
fi;


# ===============================================================
# Test 1: m = 5 cross-validation.
# For every conjugacy-class rep h of C_G(-I) at m=5 (1025 classes),
# TraceOnOmega0Gauss(h, 5) must equal TraceOnOmega0Batch(h, 5).
# 1025 classes x instant per Gauss-sum is sub-second.
# ===============================================================

Print("\n=================================================================\n");
Print("  Test 1: m = 5 cross-validation  Gauss vs Batch\n");
Print("=================================================================\n");

ResetSparseTraceCache();;
ResetTraceHCache();;
ResetGaussCtxCache();;

G5 := EmUnimodGroup(5);;
cls5 := ConjugacyClasses(G5);;
reps5 := List(cls5, Representative);;
Print("  C_G(-I) at m=5 has ", Length(reps5), " conjugacy classes.\n");

n_fail_m5 := 0;;
t0 := Runtime();;
n_done := 0;;
for j in [1..Length(reps5)] do
    h := reps5[j];
    vGauss := TraceOnOmega0Gauss(h, 5);
    vBatch := TraceOnOmega0Batch(h, 5);
    if vGauss <> vBatch then
        n_fail_m5 := n_fail_m5 + 1;
        if n_fail_m5 <= 5 then
            Print("    MISMATCH at class ", j,
                  ": Gauss=", vGauss, "  Batch=", vBatch, "\n");
        fi;
    fi;
    n_done := n_done + 1;
    # Light progress every 200 classes (m=5 batch is ~1.3 s/trace; ~22 min total).
    if n_done mod 200 = 0 then
        Print("    ... progress: ", n_done, "/", Length(reps5),
              " classes verified (", (Runtime() - t0) / 1000., " s).\n");
    fi;
od;
t1 := Runtime();;
Print("  m=5 cross-validation: ", Length(reps5) - n_fail_m5, "/",
      Length(reps5), " match (", (t1 - t0) / 60000., " min).\n");
AssertOrLog("Test 1: m=5 Gauss == Batch on all 1025 centraliser classes",
            n_fail_m5 = 0);


# ===============================================================
# Test 2: m = 7 build + sanity.
# Gated by GAUSS_SKIP_M7.  Acceptance: build returns in < 5 min,
# multiplicities are non-negative integers, sum = 2^k = 2^64.
# ===============================================================

m7Ok := true;;

if not IsBound(GAUSS_SKIP_M7) or GAUSS_SKIP_M7 = false then
    Print("\n=================================================================\n");
    Print("  Test 2: m = 7 build  BuildKRRSpectralCharactersSparse(7)\n");
    Print("=================================================================\n");

    Print("  Starting m=7 build...\n");
    ResetSparseTraceCache();;
    ResetTraceHCache();;
    ResetGaussCtxCache();;
    t0 := Runtime();;
    sc7 := BuildKRRSpectralCharactersSparse(7);;
    t1 := Runtime();;
    Print("  BuildKRRSpectralCharactersSparse(7) built in ",
          (t1 - t0) / 1000., " s = ", (t1 - t0) / 60000., " min.\n");

    n7 := 2^7;;
    z7 := -IdentityMat(n7);;
    i_central_7 := PositionProperty(sc7.idx.reps, r -> r = z7);;
    if i_central_7 = fail then
        Print("  WARNING: -I is not a class rep at m=7 (unusual).\n");
        m7Ok := false;
    else
        mults7 := sc7.multiplicities[i_central_7];;
        sum7 := Sum(mults7);;
        dim_w7 := 2^(2^(7-1));;       # = 2^64
        Print("  Sum of mult_chi on central class: ", sum7, "\n");
        Print("  Expected dim W_a = 2^k = 2^64 = ", dim_w7, "\n");
        if sum7 <> dim_w7 then
            Print("  FAIL: mult sum does not match dim W_a.\n");
            m7Ok := false;
        fi;
        # Non-negativity / integrality.
        all_ok7 := ForAll(mults7, m -> IsInt(m) and m >= 0);;
        Print("  All mult_chi non-negative integers: ", all_ok7, "\n");
        if not all_ok7 then
            # First 5 offending values.
            bad7 := Filtered([1..Length(mults7)],
                              i -> not (IsInt(mults7[i]) and mults7[i] >= 0));
            Print("  Offending indices (first 5): ",
                  bad7{[1..Minimum(5, Length(bad7))]}, "\n");
            for j in bad7{[1..Minimum(5, Length(bad7))]} do
                Print("    mults7[", j, "] = ", mults7[j], "\n");
            od;
            m7Ok := false;
        fi;
        # Multiplicity of the trivial irrep (irrep index 1 usually).
        Print("  Multiplicity of irrep 1 (often trivial): ", mults7[1], "\n");
        # Report the first 16 multiplicities for sanity.
        Print("  First 16 mult_chi: ", mults7{[1..Minimum(16, Length(mults7))]}, "\n");
        # Smoke: trace_on_W(central, 1, identity) = mult * chi.dim.
        idMat_n7 := IdentityMat(n7);;
        val7 := sc7.trace_on_W(i_central_7, 1, idMat_n7);;
        chi1_dim := sc7.idx.irreps[i_central_7][1][1];;
        expected7 := mults7[1] * chi1_dim;;
        Print("  trace_on_W(central, 1, identity) = ", val7,
              ", expected mult * chi.dim = ", expected7, "\n");
        if val7 <> expected7 then
            Print("  FAIL: trace_on_W mismatch.\n");
            m7Ok := false;
        fi;
    fi;

    AssertOrLog("Test 2: m=7 build sum(mults) = 2^64 and non-neg ints", m7Ok);

    # Soft check: was it under 5 minutes?
    if (t1 - t0) / 60000. < 5. then
        AssertOrLog("Test 2b: m=7 build under 5 minutes", true);
    else
        Print("  NOTE: m=7 build took ", (t1 - t0) / 60000.,
              " min (over the 5-min soft target).  Still functional.\n");
        AssertOrLog("Test 2b: m=7 build under 5 minutes",
                    (t1 - t0) / 60000. < 5.);
    fi;
else
    Print("\n  [Skipping m=7 build test (GAUSS_SKIP_M7 set)]\n");
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
    Print("\nKRR GAUSS-SUM TRACE: ACCEPTANCE PASS.\n");
else
    Print("\nKRR GAUSS-SUM TRACE: FAILURE.\n");
fi;

QUIT;
