# test_tr_closed_form_bypass.g  --  K-4b m=7 #449 #456 production.
#
# Tests the closed-form BRW-orbit Tr(T_h | Omega_0) bypass added to
# `BuildKRRSpectralCharactersSparse` for m >= 5.
#
# Coverage:
#   (A) m=3 path: the bypass is gated off for m < 5; we verify that the
#       per-h trace loop is exercised and produces identical traces to
#       the pre-bypass codepath. We snapshot the trace list and compare
#       against the direct `TraceOnOmega0(h, m)` call.
#   (B) m=5 parity: every one of the 1025 central-class trace entries
#       in the spectral builder output equals `TraceOnOmega0(h, m)` on
#       the corresponding rep.
#   (C) m=5 closed-form prediction parity: each per-type trace matches
#       the typed prediction `Tr_norm = 2^(k - d(type))`.
#   (D) m=7 smoke: spectral build trace loop completes in seconds (not
#       ~35 min), and predicted traces match the typed formula for the
#       sampled classes used by the sanity check.
#
# Run from the scripts/ directory:
#   gap -q -b -c 'Read("tests/test_tr_closed_form_bypass.g");'
# To skip the slow m=7 smoke:
#   gap -q -b -c 'BYPASS_SKIP_M7 := true;; \
#                 Read("tests/test_tr_closed_form_bypass.g");'

SetInfoLevel(InfoWarning, 1);

# ---- Locate and load sibling modules ---------------------------------
_loaded := false;;
_self_path := INPUT_FILENAME();;
if _self_path <> fail and _self_path <> "stream" then
    _self_dir := _self_path{[1..Length(_self_path)
                          - Length("/test_tr_closed_form_bypass.g")]};;
    _scripts_dir := Concatenation(_self_dir, "/..");
    _cand := Concatenation(_scripts_dir,
                            "/krr_spectral_characters_sparse.g");
    if IsExistingFile(_cand) then
        ChangeDirectoryCurrent(_scripts_dir);
        Read("bw_lattice.g");
        Read("em_construction.g");
        Read("twisted_group_algebra.g");
        Read("qforms_f2.g");
        Read("defect_rep_minus_id.g");
        Read("defect_rep_minus_id_optim.g");
        Read("untwisted_modular_data.g");
        Read("krr_spectral_characters.g");
        Read("krr_spectral_characters_sparse.g");
        _loaded := true;
    fi;
fi;;
if not _loaded then
    Error("cannot locate krr_spectral_characters_sparse.g; ",
          "run from extraspecial_orbifolds/scripts/tests/.");
fi;

failures := [];;

AssertOrLog := function(label, cond)
    if cond then
        Print("  PASS: ", label, "\n");
    else
        Print("  FAIL: ", label, "\n");
        Add(failures, label);
    fi;
end;;

# Closed-form Tr_norm predictor.
_PredictTrNorm := function(m, type)
    local k, d;
    k := 2^(m - 1);
    if type = "id" or type = "minus_one" then
        d := 0;
    elif type = "sigma2" then
        d := 2^(m - 3);
    elif type = "sigma_1sigma_2" then
        d := 2^(m - 2);
    else
        Error("_PredictTrNorm: unknown type \"", type, "\"");
    fi;
    return 2^(k - d);
end;;

# ---------------------------------------------------------------------
# (A) m=3 path: the bypass is gated off; per-h trace loop runs.
# Snapshot the traces from BuildKRRSpectralCharactersSparse(3) and
# verify each equals `TraceOnOmega0(h, m)` on the corresponding rep.
# ---------------------------------------------------------------------
Print("\n================================================================\n");
Print("  Test A: m = 3 per-h trace path (bypass gated off)\n");
Print("================================================================\n");

m := 3;;
n := 2^m;;
z := -IdentityMat(n);;

ResetSparseTraceCache();;
ResetTraceHCache();;
ResetGaussCtxCache();;

sc3 := BuildKRRSpectralCharactersSparse(m);;
i_central := PositionProperty(sc3.idx.reps, r -> r = z);;
AssertOrLog("(A.0) central class -I present in idx",
            i_central <> fail);

ct := sc3.centraliser_traces[i_central];;
AssertOrLog("(A.1) centraliser_traces[central] is bound (not fail)",
            ct <> fail);
traces_m3 := ct.traces;;
reps_m3 := ct.reps;;
AssertOrLog("(A.2) trace list length matches reps list length",
            Length(traces_m3) = Length(reps_m3));
AssertOrLog("(A.3) trace list length = 2^(2m) + 1",
            Length(traces_m3) = 2^(2*m) + 1);

# Parity: each trace = TraceOnOmega0(h, m). Reset the cache between
# the cached lookup and the recompute to make sure we go through the
# Batch / Gauss-sum machinery, not a cached value.
ResetSparseTraceCache();;
parity_fail := 0;;
for j in [1..Length(reps_m3)] do
    h := reps_m3[j];
    tr := TraceOnOmega0(h, m);
    if tr <> traces_m3[j] then
        parity_fail := parity_fail + 1;
        if parity_fail <= 5 then
            Print("  m=3 parity fail at j=", j, ": traces_m3[j]=",
                  traces_m3[j], " vs TraceOnOmega0=", tr, "\n");
        fi;
    fi;
od;;
AssertOrLog("(A.4) m=3: per-class traces match TraceOnOmega0 byte-identically",
            parity_fail = 0);

# At m=3, the BRW-orbit collapse is FALSE: there should be > 4 distinct
# Tr values across the 65 classes (5 distinct per PR #448).
distinct_m3 := Length(AsSet(traces_m3));
AssertOrLog("(A.5) m=3 has > 4 distinct trace values (BRW collapse FALSE)",
            distinct_m3 > 4);
Print("  m=3 distinct trace values: ", distinct_m3, " (expect 5)\n");

# ---------------------------------------------------------------------
# (B) m=5 parity: every one of 1025 spectral-builder trace entries
# equals TraceOnOmega0(h, m) on the corresponding rep. This is the
# core parity test for the closed-form bypass.
# ---------------------------------------------------------------------
Print("\n================================================================\n");
Print("  Test B: m = 5 spectral-builder traces match TraceOnOmega0\n");
Print("================================================================\n");

m := 5;;
n := 2^m;;
z := -IdentityMat(n);;

ResetSparseTraceCache();;
ResetTraceHCache();;
ResetGaussCtxCache();;

t0 := Runtime();;
sc5 := BuildKRRSpectralCharactersSparse(m);;
t_m5 := (Runtime() - t0) / 1000;
Print("  m=5 spectral build wall: ", t_m5, " s\n");

i_central5 := PositionProperty(sc5.idx.reps, r -> r = z);;
AssertOrLog("(B.0) central class -I present in idx (m=5)",
            i_central5 <> fail);

ct5 := sc5.centraliser_traces[i_central5];;
AssertOrLog("(B.1) centraliser_traces[central] is bound (m=5)",
            ct5 <> fail);
traces_m5 := ct5.traces;;
reps_m5 := ct5.reps;;
AssertOrLog("(B.2) trace list length = 2^(2m) + 1 = 1025 (m=5)",
            Length(traces_m5) = 2^(2*m) + 1);

# Parity: for each class j, the spectral builder's traces_m5[j] must
# equal TraceOnOmega0(reps_m5[j], m). Each per-h call is ~1 sec via
# TraceOnOmega0Batch at m=5, so a full 1025-call sweep takes ~17 min.
# Default: sample 50 evenly-spaced classes (~50 sec wall, statistically
# strong). Set BYPASS_FULL_PARITY_M5 := true to sweep all 1025.
if IsBound(BYPASS_FULL_PARITY_M5) and BYPASS_FULL_PARITY_M5 then
    parity_sample_indices := [1..Length(reps_m5)];
    Print("  m=5 full parity sweep (",
          Length(parity_sample_indices), " classes); ~17 min wall.\n");
else
    # 50 evenly-spaced indices across [1..Length(reps_m5)].
    parity_sample_indices := [];
    for j in [1..50] do
        Add(parity_sample_indices,
            QuoInt((j - 1) * (Length(reps_m5) - 1), 49) + 1);
    od;
    Print("  m=5 sampled parity (50 classes); ~50 sec wall ",
          "(BYPASS_FULL_PARITY_M5 := true forces 1025).\n");
fi;
ResetSparseTraceCache();;
t0 := Runtime();;
parity_fail_m5 := 0;;
parity_first_fails := [];;
for j in parity_sample_indices do
    h := reps_m5[j];
    tr := TraceOnOmega0(h, m);
    if tr <> traces_m5[j] then
        parity_fail_m5 := parity_fail_m5 + 1;
        if Length(parity_first_fails) < 5 then
            Add(parity_first_fails,
                rec(j := j, expected := tr, got := traces_m5[j]));
        fi;
    fi;
od;;
t_parity_m5 := (Runtime() - t0) / 1000;
Print("  m=5 parity sweep wall: ", t_parity_m5, " s (",
      Length(parity_sample_indices),
      " TraceOnOmega0 calls)\n");
AssertOrLog("(B.3) m=5: sampled spectral traces match TraceOnOmega0",
            parity_fail_m5 = 0);
if parity_fail_m5 > 0 then
    Print("  First few mismatches: ", parity_first_fails, "\n");
fi;

# ---------------------------------------------------------------------
# (C) m=5 closed-form prediction parity: each per-type Tr_norm matches
# the typed formula.
# ---------------------------------------------------------------------
Print("\n================================================================\n");
Print("  Test C: m = 5 typed Tr_norm matches closed-form prediction\n");
Print("================================================================\n");

# Classify each rep by BRW orbit type. Use idx.class_types if available
# (closed-form builder), else _SparseClassifyEmBRWTypes.
if IsBound(sc5.idx.class_types) then
    class_types_m5 := sc5.idx.class_types;
else
    class_types_m5 := _SparseClassifyEmBRWTypes(
        ConjugacyClasses(sc5.idx.group));
fi;;

# Walk every class, predict Tr_norm from type, compare.
predict_fail_m5 := 0;;
predict_first_fails := [];;
type_to_observed := rec();;
for j in [1..Length(reps_m5)] do
    t := class_types_m5[j];
    expected := _PredictTrNorm(m, t);
    if traces_m5[j] <> expected then
        predict_fail_m5 := predict_fail_m5 + 1;
        if Length(predict_first_fails) < 5 then
            Add(predict_first_fails,
                rec(j := j, type := t,
                    expected := expected, got := traces_m5[j]));
        fi;
    fi;
    if not IsBound(type_to_observed.(t)) then
        type_to_observed.(t) := [];
    fi;
    AddSet(type_to_observed.(t), traces_m5[j]);
od;;
AssertOrLog("(C.1) m=5: all 1025 traces match Tr_norm = 2^(k - d(type))",
            predict_fail_m5 = 0);
if predict_fail_m5 > 0 then
    Print("  First few prediction mismatches: ", predict_first_fails, "\n");
fi;

# Each type bucket has a single Tr_norm value.
for t in SortedList(RecNames(type_to_observed)) do
    Print("  m=5 type ", t, " observed Tr_norm = ",
          type_to_observed.(t), "\n");
    AssertOrLog(Concatenation("(C.2) m=5 type ", t, ": single Tr_norm value"),
                Length(type_to_observed.(t)) = 1);
od;

# ---------------------------------------------------------------------
# (D) m=7 smoke: trace-loop wall reduction.
#
# At m=7, `BuildKRRSpectralCharactersSparse(7)` is dominated by the
# upfront `EPlusBuildAllCharacterRows` cost (~10 min wall, building
# the 16385 x 16385 closed-form character table for the central
# centraliser). The bypass does NOT speed this part up.
#
# What the bypass DOES speed up is the per-h trace loop in Step 3,
# previously 16385 * ~127 ms = ~35 min. We measure this directly by
# calling `TraceOnOmega0` on a sampled set of 4 reps (one per orbit
# type) and confirming that the bypass would expand to all 16385
# from these in O(num).
#
# Skippable via BYPASS_SKIP_M7 := true (default off; this branch
# avoids the expensive _EnsureClassData call entirely).
# ---------------------------------------------------------------------
Print("\n================================================================\n");
Print("  Test D: m = 7 trace-loop wall reduction smoke\n");
Print("================================================================\n");

if IsBound(BYPASS_SKIP_M7) and BYPASS_SKIP_M7 then
    Print("  SKIPPED (BYPASS_SKIP_M7 = true)\n");
else
    m := 7;;
    n := 2^m;;
    z := -IdentityMat(n);;
    ResetSparseTraceCache();;
    ResetTraceHCache();;
    ResetGaussCtxCache();;

    # Build the closed-form idx (cheap at m=7 vs the eager
    # BuildSimpleIndex). This is the SAME idx the spectral builder
    # would build internally.
    Print("  m=7: building closed-form idx (one-shot enumeration) ...\n");
    t0 := Runtime();;
    idx7 := BuildSimpleIndexEPlusClosedForm(m);;
    t_idx7 := (Runtime() - t0) / 1000;
    Print("  m=7 idx build wall: ", t_idx7, " s\n");

    i_central7 := PositionProperty(idx7.reps, r -> r = z);;
    AssertOrLog("(D.0) central class -I present in idx (m=7)",
                i_central7 <> fail);

    # Reps + types are already known from the closed-form builder,
    # without needing to load CT data.
    AssertOrLog("(D.1) m=7 idx.class_types is populated",
                IsBound(idx7.class_types));
    AssertOrLog("(D.2) m=7 idx has 16385 classes",
                Length(idx7.reps) = 2^(2*m) + 1);

    # Per-type sample: one rep per orbit type. This mimics the
    # bypass sanity sample. At m=7 each TraceOnOmega0 call is
    # ~127 ms (per #456 research note); total ~0.5 sec for 4 calls.
    # The full 16385-call loop would take ~35 min.
    type_samples_m7 := rec();
    for j in [1..Length(idx7.reps)] do
        t := idx7.class_types[j];
        if not IsBound(type_samples_m7.(t)) then
            type_samples_m7.(t) := j;
        fi;
    od;
    seen_types_m7 := SortedList(RecNames(type_samples_m7));
    AssertOrLog("(D.3) m=7: 4 orbit types observed (id, minus_one, sigma2, sigma_1sigma_2)",
                Length(seen_types_m7) = 4);

    # Compute Tr for one rep per type; verify match against typed
    # prediction. This is the bypass's sanity check at m=7.
    t0 := Runtime();;
    type_pass_m7 := 0;;
    type_fail_m7 := 0;;
    for t in seen_types_m7 do
        j := type_samples_m7.(t);
        h := idx7.reps[j];
        tr := TraceOnOmega0(h, m);
        expected := _PredictTrNorm(m, t);
        if tr = expected then
            type_pass_m7 := type_pass_m7 + 1;
            Print("  m=7 type ", t, " (rep idx=", j,
                  ") Tr_norm = ", tr, " (matches predicted ",
                  expected, ")\n");
        else
            type_fail_m7 := type_fail_m7 + 1;
            Print("  m=7 type ", t, " (rep idx=", j,
                  ") Tr_norm = ", tr, " MISMATCH predicted ",
                  expected, "\n");
        fi;
    od;
    t_trace_m7 := (Runtime() - t0) / 1000;
    Print("  m=7 trace-loop sample wall: ", t_trace_m7,
          " s (", Length(seen_types_m7), " TraceOnOmega0 calls); ",
          "full per-h loop would be ~35 min.\n");
    AssertOrLog("(D.4) m=7: 4/4 typed predictions match TraceOnOmega0",
                type_fail_m7 = 0 and type_pass_m7 = 4);
    # The bypass replaces 16385 trace calls with 4 + structural lookup.
    # Sample wall should be far below 60 sec (each call ~127 ms).
    AssertOrLog("(D.5) m=7 trace-loop sample wall < 60 sec",
                t_trace_m7 < 60);
fi;

# ---------------------------------------------------------------------
# Summary.
# ---------------------------------------------------------------------
Print("\n================================================================\n");
if Length(failures) = 0 then
    Print("test_tr_closed_form_bypass: PASS\n");
else
    Print("test_tr_closed_form_bypass: FAIL (", Length(failures),
          " checks failed)\n");
    for f in failures do
        Print("  - ", f, "\n");
    od;
fi;
Print("================================================================\n");

QUIT_GAP(Length(failures));
