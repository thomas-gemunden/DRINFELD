# test_k4a_classify_m5_smoke.g
#
# K-4b m = 5 post-run smoke test. Loads the persisted K4aClassify(5)
# result record (written by `run_k4b_m5.sh`) and asserts well-formedness.
#
# Why a smoke test rather than an end-to-end re-run: K4aClassify(5)
# takes ~30-40 minutes wall (dominated by
# BuildKRRSpectralCharactersSparse(5)'s 1025-class central-twist
# trace table). That cost is paid once by the production driver; this
# regression test cheaply checks the persisted artefact each commit.
#
# What we check:
#
#   T1. The result file exists and binds RESULT.
#   T2. The RESULT record has the expected shape (m=5, group, verdict,
#       trivial, E_class, D8_class, Q8_class, spectral_data, timing).
#   T3. The verdict is one of "trivial" | "non-trivial" | "incomplete".
#   T4. The per-branch fields have the expected sub-shapes (is_abelian
#       flag, class_idx for D_8/Q_8, etc.).
#   T5. The spectral_data.source is "krr-sparse" (the m=5 spec ask:
#       BuildKRRSpectralCharactersSparse(5) was actually called, not
#       the untwisted_baseline fallback).
#   T6. The timing record exposes wall_seconds + per-branch + spectral.
#
# Run from absolute path:
#   gap -q -b /Users/.../tests/test_k4a_classify_m5_smoke.g
#
# Exit 0 on success, non-zero on any failure.

# ---- Test bookkeeping --------------------------------------------------

K4A_M5_PASSES   := 0;;
K4A_M5_FAILURES := [];;

K4AM5AssertEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
        K4A_M5_PASSES := K4A_M5_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Print("         expected: ", expected, "\n");
        Print("         got:      ", got, "\n");
        Add(K4A_M5_FAILURES, label);
    fi;
end;;

K4AM5AssertTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
        K4A_M5_PASSES := K4A_M5_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Add(K4A_M5_FAILURES, label);
    fi;
end;;

K4AM5AssertIn := function(label, got, allowed_set)
    if got in allowed_set then
        Print("  [ok] ", label, "\n");
        K4A_M5_PASSES := K4A_M5_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Print("         expected one of: ", allowed_set, "\n");
        Print("         got:             ", got, "\n");
        Add(K4A_M5_FAILURES, label);
    fi;
end;;

# ---- Locate worktree, scripts, result file -----------------------------

K4A_M5_SELF := INPUT_FILENAME();;
if K4A_M5_SELF = fail or K4A_M5_SELF = "stream" then
    Error("test_k4a_classify_m5_smoke.g: INPUT_FILENAME() unavailable; ",
          "Read the file by its absolute path.");
fi;
K4A_M5_SELFDIR := K4A_M5_SELF{
    [1..Length(K4A_M5_SELF) - Length("/test_k4a_classify_m5_smoke.g")]};;
K4A_M5_SCRIPTSDIR := K4A_M5_SELFDIR{
    [1..Length(K4A_M5_SELFDIR) - Length("/tests")]};;
K4A_M5_WT_ROOT := K4A_M5_SCRIPTSDIR{
    [1..Length(K4A_M5_SCRIPTSDIR) - Length("/extraspecial_orbifolds/scripts")]};;

Print("=================================================================\n");
Print("test_k4a_classify_m5_smoke.g (K-4b m = 5 post-run smoke)\n");
Print("=================================================================\n");
Print("self          : ", K4A_M5_SELF, "\n");
Print("scripts dir   : ", K4A_M5_SCRIPTSDIR, "\n");
Print("worktree root : ", K4A_M5_WT_ROOT, "\n");

# Candidate result-file locations, in order of preference:
#   1. extraspecial_orbifolds/computed/k4b/m5_verdict.g  (canonical
#      persisted location per the K-4b spec).
#   2. extraspecial_orbifolds/scripts/k4b_m5_result.g     (driver's
#      raw output before any post-processing).
K4A_M5_CANDIDATES :=
    [ Concatenation(K4A_M5_WT_ROOT,
                     "/extraspecial_orbifolds/computed/k4b/m5_verdict.g"),
      Concatenation(K4A_M5_SCRIPTSDIR, "/k4b_m5_result.g") ];;

K4A_M5_RESULT_PATH := fail;;
for K4A_M5_C in K4A_M5_CANDIDATES do
    if K4A_M5_RESULT_PATH = fail and IsExistingFile(K4A_M5_C) then
        K4A_M5_RESULT_PATH := K4A_M5_C;
    fi;
od;

if K4A_M5_RESULT_PATH = fail then
    Print("\n[SKIPPED] No K-4b m=5 result file found. Looked at:\n");
    for K4A_M5_C in K4A_M5_CANDIDATES do
        Print("  - ", K4A_M5_C, "\n");
    od;
    Print("\n  Run ./extraspecial_orbifolds/scripts/run_k4b_m5.sh first.\n");
    Print("  This test is a POST-RUN smoke check — it relies on the\n");
    Print("  driver having produced a result file.\n");
    Print("\nSKIP test_k4a_classify_m5_smoke\n");
    QUIT_GAP(0);
fi;

Print("\nresult file   : ", K4A_M5_RESULT_PATH, "\n");

# ---- T1: result file binds RESULT --------------------------------------
Print("\n-----------------------------------------------------------------\n");
Print("T1: result file binds RESULT\n");
Print("-----------------------------------------------------------------\n");

Read(K4A_M5_RESULT_PATH);
K4AM5AssertTrue("RESULT is bound after Read", IsBound(RESULT));
K4AM5AssertTrue("RESULT is a record", IsRecord(RESULT));

# ---- T2: RESULT has expected fields ------------------------------------
Print("\n-----------------------------------------------------------------\n");
Print("T2: RESULT has the expected fields\n");
Print("-----------------------------------------------------------------\n");

K4AM5AssertEqual("RESULT.m = 5", RESULT.m, 5);
K4AM5AssertTrue("RESULT.group is a group (informational EmGroup(5))",
                IsGroup(RESULT.group));
K4AM5AssertTrue("RESULT.verdict is bound", IsBound(RESULT.verdict));
K4AM5AssertTrue("RESULT.trivial is bound", IsBound(RESULT.trivial));
K4AM5AssertTrue("RESULT.E_class is a record",
                IsRecord(RESULT.E_class));
K4AM5AssertTrue("RESULT.D8_class is a record",
                IsRecord(RESULT.D8_class));
K4AM5AssertTrue("RESULT.Q8_class is a record",
                IsRecord(RESULT.Q8_class));
K4AM5AssertTrue("RESULT.spectral_data is a record",
                IsRecord(RESULT.spectral_data));
K4AM5AssertTrue("RESULT.timing is a record",
                IsRecord(RESULT.timing));

# ---- T3: verdict is one of the three allowed values --------------------
Print("\n-----------------------------------------------------------------\n");
Print("T3: verdict is in {trivial, non-trivial, incomplete}\n");
Print("-----------------------------------------------------------------\n");

K4AM5AssertIn("RESULT.verdict allowed",
              RESULT.verdict,
              ["trivial", "non-trivial", "incomplete"]);
# trivial is one of the GAP booleans true / false / fail.
K4AM5AssertTrue("RESULT.trivial in {true, false, fail}",
                RESULT.trivial = true or RESULT.trivial = false
                or RESULT.trivial = fail);
# Verdict and trivial agree.
if RESULT.verdict = "trivial" then
    K4AM5AssertEqual("verdict 'trivial' <=> trivial = true",
                     RESULT.trivial, true);
elif RESULT.verdict = "non-trivial" then
    K4AM5AssertEqual("verdict 'non-trivial' <=> trivial = false",
                     RESULT.trivial, false);
else
    K4AM5AssertEqual("verdict 'incomplete' <=> trivial = fail",
                     RESULT.trivial, fail);
fi;

# ---- T4: per-branch sub-shapes -----------------------------------------
Print("\n-----------------------------------------------------------------\n");
Print("T4: per-branch records have the expected sub-shapes\n");
Print("-----------------------------------------------------------------\n");

# E branch. The persisted form is a lite record (the 4096x4096 modular
# data matrices are stripped by run_k4b_m5.sh's persist filter — they
# would exceed 100MB on disk for the E branch alone). We assert on the
# preserved meta-fields.
K4AM5AssertTrue("E_class.is_abelian = true",
                RESULT.E_class.is_abelian = true);
K4AM5AssertTrue("E_class.is_coboundary in {true, false, fail}",
                RESULT.E_class.is_coboundary = true
                or RESULT.E_class.is_coboundary = false
                or RESULT.E_class.is_coboundary = fail);
# E = (Z/2)^6 at m=5: |E| = 64, rank of Drinfeld center = |E|^2 = 4096.
K4AM5AssertEqual("E CT modular data rank = 4096 (m = 5)",
                 RESULT.E_class.modular_ct_rank, 4096);
K4AM5AssertEqual("E untwisted modular data rank = 4096 (m = 5)",
                 RESULT.E_class.modular_untwisted_rank, 4096);
K4AM5AssertTrue("E_class.match_ok bound",
                IsBound(RESULT.E_class.match_ok));

# D_8 branch.
K4AM5AssertTrue("D8_class.is_abelian = false",
                RESULT.D8_class.is_abelian = false);
K4AM5AssertTrue("D8_class.class_idx in [1..22] or fail",
                RESULT.D8_class.class_idx = fail
                or (IsInt(RESULT.D8_class.class_idx)
                    and RESULT.D8_class.class_idx >= 1
                    and RESULT.D8_class.class_idx <= 22));
K4AM5AssertEqual("D_8 CT modular data is rank 22",
                 RESULT.D8_class.modular_ct_rank, 22);

# Q_8 branch.
K4AM5AssertTrue("Q8_class.is_abelian = false",
                RESULT.Q8_class.is_abelian = false);
K4AM5AssertTrue("Q8_class.class_idx in [1..8] or fail",
                RESULT.Q8_class.class_idx = fail
                or (IsInt(RESULT.Q8_class.class_idx)
                    and RESULT.Q8_class.class_idx >= 1
                    and RESULT.Q8_class.class_idx <= 8));
K4AM5AssertEqual("Q_8 CT modular data is rank 22",
                 RESULT.Q8_class.modular_ct_rank, 22);

# Additional sub-shape checks (added inline for the verdict).
if RESULT.verdict = "trivial" then
    K4AM5AssertEqual("E_class.match_ok = true (trivial verdict)",
                     RESULT.E_class.match_ok, true);
    # Unambiguous classification: exactly one stored class matches.
    if IsList(RESULT.D8_class.all_matches) then
        K4AM5AssertTrue("D8_class.all_matches has length 1 (unambiguous)",
                        Length(RESULT.D8_class.all_matches) = 1);
    fi;
    if IsList(RESULT.Q8_class.all_matches) then
        K4AM5AssertTrue("Q8_class.all_matches has length 1 (unambiguous)",
                        Length(RESULT.Q8_class.all_matches) = 1);
    fi;
fi;

# Issue #449: multi-EA spectral E-branch sub-shape (when present).
# At m=5 with default opts and the D-VAN min-family loaded, the E branch
# is dispatched through _K4A_ClassifySpectralEBranchMulti, which adds
# a `spectral_multi_ea := true` flag, a `family_source` label, and a
# `per_ea_results` list with one entry per EA in the D-VAN family.
if IsBound(RESULT.E_class.spectral_multi_ea)
   and RESULT.E_class.spectral_multi_ea = true then
    K4AM5AssertEqual("E_class.family_source = 'dvan-min-family'",
                     RESULT.E_class.family_source, "dvan-min-family");
    K4AM5AssertTrue("E_class.per_ea_results is a list",
                    IsList(RESULT.E_class.per_ea_results));
    # D-VAN m=5 family has 9 EAs.
    K4AM5AssertEqual("E_class.per_ea_results length = 9 (D-VAN m=5 family)",
                     Length(RESULT.E_class.per_ea_results), 9);
    # Each per-EA entry has the expected shape.
    K4AM5AssertTrue("E_class.per_ea_results[1] has ea_order = 64",
                    RESULT.E_class.per_ea_results[1].ea_order = 64);
    # Aggregate AND of per-EA is_coboundary equals top-level
    # is_coboundary.
    K4AM5AssertEqual(
        "E_class.is_coboundary = AND over per_ea_results",
        RESULT.E_class.is_coboundary,
        ForAll(RESULT.E_class.per_ea_results,
               r -> r.is_coboundary = true));
fi;

# ---- T5: spectral_data.source = "krr-sparse" ---------------------------
Print("\n-----------------------------------------------------------------\n");
Print("T5: spectral_data.source = 'krr-sparse' (m = 5 spec ask)\n");
Print("-----------------------------------------------------------------\n");

K4AM5AssertEqual(
    "spectral_data.source = 'krr-sparse' (BuildKRRSpectralCharactersSparse called)",
    RESULT.spectral_data.source, "krr-sparse");
K4AM5AssertEqual("spectral_data.spectral_call_skipped = false",
                 RESULT.spectral_data.spectral_call_skipped, false);
K4AM5AssertTrue("spectral_data.sparse is a record",
                IsRecord(RESULT.spectral_data.sparse));
K4AM5AssertEqual("spectral_data.sparse.source = 'krr-sparse'",
                 RESULT.spectral_data.sparse.source, "krr-sparse");
K4AM5AssertEqual("spectral_data.sparse.m = 5",
                 RESULT.spectral_data.sparse.m, 5);
K4AM5AssertTrue("spectral_data.sparse.group is a group",
                IsGroup(RESULT.spectral_data.sparse.group));
K4AM5AssertEqual("spectral_data.sparse.group has order 2048",
                 Order(RESULT.spectral_data.sparse.group), 2048);

# ---- T6: timing record exposes per-branch wall_seconds -----------------
Print("\n-----------------------------------------------------------------\n");
Print("T6: timing record exposes per-branch + spectral wall_seconds\n");
Print("-----------------------------------------------------------------\n");

K4AM5AssertTrue("timing.wall_seconds bound",
                IsBound(RESULT.timing.wall_seconds));
K4AM5AssertTrue("timing.wall_seconds > 0",
                RESULT.timing.wall_seconds > 0.0);
K4AM5AssertTrue("timing.E_branch bound",
                IsBound(RESULT.timing.E_branch));
K4AM5AssertTrue("timing.D8_branch bound",
                IsBound(RESULT.timing.D8_branch));
K4AM5AssertTrue("timing.Q8_branch bound",
                IsBound(RESULT.timing.Q8_branch));
K4AM5AssertTrue("timing.spectral_data bound",
                IsBound(RESULT.timing.spectral_data));
K4AM5AssertTrue("timing.spectral_data > 0 (sparse build ran)",
                RESULT.timing.spectral_data > 0.0);

# ---- Final report ------------------------------------------------------

Print("\n=================================================================\n");
Print("Verdict-at-a-glance from RESULT record:\n");
Print("  m              : ", RESULT.m, "\n");
Print("  verdict        : ", RESULT.verdict, "\n");
Print("  trivial        : ", RESULT.trivial, "\n");
Print("  E_class.is_cob : ", RESULT.E_class.is_coboundary, "\n");
Print("  D8_class.idx   : ", RESULT.D8_class.class_idx, "\n");
Print("  Q8_class.idx   : ", RESULT.Q8_class.class_idx, "\n");
Print("  spectral src   : ", RESULT.spectral_data.source, "\n");
Print("  wall (s)       : ", RESULT.timing.wall_seconds, "\n");
Print("=================================================================\n");

Print("\n=================================================================\n");
Print("Summary: ", K4A_M5_PASSES, " passes, ",
      Length(K4A_M5_FAILURES), " failures.\n");
Print("=================================================================\n");

if Length(K4A_M5_FAILURES) = 0 then
    Print("\nPASS test_k4a_classify_m5_smoke\n");
    QUIT_GAP(0);
else
    Print("\nFAIL test_k4a_classify_m5_smoke:\n");
    for K4A_M5_F in K4A_M5_FAILURES do
        Print("  - ", K4A_M5_F, "\n");
    od;
    QUIT_GAP(1);
fi;
