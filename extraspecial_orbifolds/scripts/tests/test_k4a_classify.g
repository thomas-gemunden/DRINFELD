# test_k4a_classify.g
#
# K-4a-T6 (issue #200) regression test + K-4a-T7 (issue #201) anchor.
#
# Test cases:
#
#   T1. Smoke: K4aClassify is bound after loading k4a_classify.g.
#
#   T2. m = 3 trivial anchor (the K-4a-T7 acceptance gate, #201):
#       K4aClassify(3) returns verdict = "trivial", all three branch
#       classifications return their trivial indices
#         * E_class.is_coboundary = true
#         * D8_class.class_idx = 1
#         * Q8_class.class_idx = 1
#       and the whole run completes in < 5 minutes wall.
#
#   T3. Error at m >= 4: K4aClassify(4) errors with a clear message
#       pointing at issue #220 (the sparse-trace_on_W follow-up).
#
#   T4. Optional m = 2 smoke: K4aClassify(2) completes and returns
#       verdict = "trivial" (Keller alpha = 0 holds at m = 2 as well).
#
# IF T2 PASSES, the K-4a-T7 acceptance criterion (#201) is satisfied
# by definition: T2 is exactly the m = 3 "Keller alpha = 0, verdict
# = trivial" end-to-end pipeline at the orchestrator level.
#
# Run from absolute path:
#   gap -q -b /Users/thomasgemunden/.../tests/test_k4a_classify.g

# ---- Test bookkeeping --------------------------------------------------

K4A_PASSES   := 0;;
K4A_FAILURES := [];;

K4AAssertEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
        K4A_PASSES := K4A_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Print("         expected: ", expected, "\n");
        Print("         got:      ", got, "\n");
        Add(K4A_FAILURES, label);
    fi;
end;;

K4AAssertTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
        K4A_PASSES := K4A_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Add(K4A_FAILURES, label);
    fi;
end;;

# ---- Locate worktree, scripts, sibling files ---------------------------

K4A_SELF := INPUT_FILENAME();;
if K4A_SELF = fail or K4A_SELF = "stream" then
    Error("test_k4a_classify.g: INPUT_FILENAME() unavailable; ",
          "Read the file by its absolute path.");
fi;
K4A_SELFDIR := K4A_SELF{
    [1..Length(K4A_SELF) - Length("/test_k4a_classify.g")]};;
K4A_SCRIPTSDIR := K4A_SELFDIR{
    [1..Length(K4A_SELFDIR) - Length("/tests")]};;
K4A_WT_ROOT := K4A_SCRIPTSDIR{
    [1..Length(K4A_SCRIPTSDIR) - Length("/extraspecial_orbifolds/scripts")]};;

# Order of loads matters:
# 1. src/modular_data.g for LoadModularData (the classifiers Error
#    if it is unbound at their own load time; k4a_classify.g lazy-loads
#    them inside K4aClassify if needed but the pattern is more robust
#    if LoadModularData is bound up front).
# 2. k4a_classify.g — the orchestrator under test. It transitively loads
#    every required sibling.

Read(Concatenation(K4A_WT_ROOT, "/src/modular_data.g"));
K4AAssertTrue("LoadModularData bound (from src/modular_data.g)",
              IsBound(LoadModularData));

Read(Concatenation(K4A_SCRIPTSDIR, "/k4a_classify.g"));

# ---- T1: Smoke - K4aClassify is bound ----------------------------------

Print("\n=================================================================\n");
Print("T1: smoke - K4aClassify is bound\n");
Print("=================================================================\n");

K4AAssertTrue("K4aClassify bound", IsBound(K4aClassify));
K4AAssertTrue("ClassifyOnD8 bound (transitively)",
              IsBound(ClassifyOnD8));
K4AAssertTrue("ClassifyOnQ8 bound (transitively)",
              IsBound(ClassifyOnQ8));
K4AAssertTrue("RestrictTraceOnWToSubgroup bound (transitively)",
              IsBound(RestrictTraceOnWToSubgroup));
K4AAssertTrue("ComputeCTModularData bound (transitively)",
              IsBound(ComputeCTModularData));
K4AAssertTrue("MaximalElementaryAbelian_E_plus bound (transitively)",
              IsBound(MaximalElementaryAbelian_E_plus));
K4AAssertTrue("D8Section_E_plus bound (transitively)",
              IsBound(D8Section_E_plus));
K4AAssertTrue("Q8Section_E_plus bound (transitively)",
              IsBound(Q8Section_E_plus));
K4AAssertTrue("EmGroup bound (transitively)", IsBound(EmGroup));

# ---- Prepare Modular_Data symlink and chdir ----------------------------
# Same pattern as test_ct_modular_data / test_q8_classifier:
# create tests/k4a/orchestrator/Modular_Data -> ../../../../modular_data
# and chdir there so LoadModularData(...) resolves.

K4A_MD_ROOT := fail;;
for K4A_CAND in
    [ Concatenation(K4A_WT_ROOT, "/../modular_data"),
      "/Users/thomasgemunden/Projects/group_cohomology/modular_data" ] do
    if K4A_MD_ROOT = fail
       and IsExistingFile(Concatenation(K4A_CAND, "/8/4/1.txt")) then
        K4A_MD_ROOT := K4A_CAND;
    fi;
od;
if K4A_MD_ROOT = fail then
    Error("test_k4a_classify.g: cannot locate modular_data tree.");
fi;
Print("modular_data root: ", K4A_MD_ROOT, "\n");

K4A_LINKDIR := Concatenation(K4A_SELFDIR, "/k4a/orchestrator");;
if not IsExistingFile(K4A_LINKDIR) then
    Exec(Concatenation("mkdir -p '", K4A_LINKDIR, "'"));
fi;
K4A_LINKPATH := Concatenation(K4A_LINKDIR, "/Modular_Data");;
if not IsExistingFile(K4A_LINKPATH) then
    Exec(Concatenation("ln -s '", K4A_MD_ROOT, "' '",
                       K4A_LINKPATH, "'"));
fi;
if not IsExistingFile(Concatenation(K4A_LINKPATH, "/8/4/1.txt")) then
    Error("test_k4a_classify.g: Modular_Data symlink at ",
          K4A_LINKPATH, " does not resolve to a tree containing ",
          "8/4/1.txt.");
fi;
ChangeDirectoryCurrent(K4A_LINKDIR);

# ---- T2: m = 3 trivial anchor (K-4a-T7 acceptance gate) ----------------

Print("\n=================================================================\n");
Print("T2: m = 3 trivial anchor (K-4a-T7 acceptance gate, issue #201)\n");
Print("=================================================================\n");

K4A_T2_BUDGET_SEC := 300.0;;        # 5 min, per the K-4a-T6 spec.

K4A_T2_T0 := Runtime();;
K4A_T2_RES := K4aClassify(3);;
K4A_T2_WALL := (Runtime() - K4A_T2_T0) / 1000.0;;

Print("\n  T2 wall time: ", K4A_T2_WALL, " s ",
      "(budget ", K4A_T2_BUDGET_SEC, " s)\n");

K4AAssertTrue("T2: K4aClassify(3) returned a record",
              IsRecord(K4A_T2_RES));
K4AAssertEqual("T2: result.m = 3", K4A_T2_RES.m, 3);
K4AAssertTrue("T2: result.group is a group",
              IsGroup(K4A_T2_RES.group));

# Verdict and triviality.
K4AAssertEqual("T2: verdict = 'trivial' (K-4a-T7 gate)",
               K4A_T2_RES.verdict, "trivial");
K4AAssertEqual("T2: trivial = true", K4A_T2_RES.trivial, true);

# Per-branch checks.
K4AAssertEqual("T2: E_class.is_coboundary = true",
               K4A_T2_RES.E_class.is_coboundary, true);
K4AAssertEqual("T2: D8_class.class_idx = 1 (trivial cocycle)",
               K4A_T2_RES.D8_class.class_idx, 1);
K4AAssertEqual("T2: Q8_class.class_idx = 1 (trivial cocycle)",
               K4A_T2_RES.Q8_class.class_idx, 1);

# Performance.
K4AAssertTrue(Concatenation(
                  "T2: wall < ", String(Int(K4A_T2_BUDGET_SEC)),
                  " s (got ", String(K4A_T2_WALL), ")"),
              K4A_T2_WALL < K4A_T2_BUDGET_SEC);

# Shape diagnostics: the per-branch records have the expected fields.
K4AAssertTrue("T2: E_class.is_abelian = true",
              K4A_T2_RES.E_class.is_abelian = true);
K4AAssertTrue("T2: D8_class.is_abelian = false",
              K4A_T2_RES.D8_class.is_abelian = false);
K4AAssertTrue("T2: Q8_class.is_abelian = false",
              K4A_T2_RES.Q8_class.is_abelian = false);

# Branch CT modular data has expected rank for D_8 / Q_8 (= 22).
K4AAssertEqual("T2: D8 CT modular data is rank 22",
               Length(K4A_T2_RES.D8_class.modular_ct.S), 22);
K4AAssertEqual("T2: Q8 CT modular data is rank 22",
               Length(K4A_T2_RES.Q8_class.modular_ct.S), 22);

# E-branch rank is |E|^2 = (2^4)^2 = 256 at m = 3.
K4AAssertEqual("T2: E CT modular data is rank 256 (m = 3)",
               Length(K4A_T2_RES.E_class.modular_ct.S), 256);

# spectral_data record present and well-formed.
K4AAssertTrue("T2: spectral_data is a record",
              IsRecord(K4A_T2_RES.spectral_data));
K4AAssertEqual(
    "T2: spectral_data.source = 'untwisted_baseline' (per K-4a-T6 spec)",
    K4A_T2_RES.spectral_data.source, "untwisted_baseline");

# Timing record sanity.
K4AAssertTrue("T2: timing.wall_seconds > 0",
              K4A_T2_RES.timing.wall_seconds > 0.0);
K4AAssertTrue("T2: per-branch timings present",
              IsBound(K4A_T2_RES.timing.E_branch)
              and IsBound(K4A_T2_RES.timing.D8_branch)
              and IsBound(K4A_T2_RES.timing.Q8_branch));

# ---- T3: error at m >= 4 -----------------------------------------------

Print("\n=================================================================\n");
Print("T3: error at m >= 4 (pointing at issue #220)\n");
Print("=================================================================\n");

# CALL_WITH_CATCH is the GAP idiom for catching an Error inside a
# function call without dropping into the break loop. Returns
# [success_bool, result-or-error-message]. Pair with
# BreakOnError := false so that the catch fires without interactive
# break-mode prompts. See test_s_twisted_central.g for the canonical
# pattern.
K4A_T3_OK_SAVE := BreakOnError;;
BreakOnError := false;;
K4A_T3_OUT := CALL_WITH_CATCH(K4aClassify, [4]);;
BreakOnError := K4A_T3_OK_SAVE;;
K4AAssertEqual("T3: K4aClassify(4) errored (caught, first slot = false)",
               K4A_T3_OUT[1], false);

# Also call at m = 5 for the same expectation.
BreakOnError := false;;
K4A_T3_OUT5 := CALL_WITH_CATCH(K4aClassify, [5]);;
BreakOnError := K4A_T3_OK_SAVE;;
K4AAssertEqual("T3: K4aClassify(5) errored (caught)",
               K4A_T3_OUT5[1], false);

# ---- T4: optional m = 2 smoke test -------------------------------------

Print("\n=================================================================\n");
Print("T4: optional m = 2 smoke test (Keller alpha = 0 at m = 2)\n");
Print("=================================================================\n");

K4A_T4_T0 := Runtime();;
K4A_T4_RES := K4aClassify(2);;
K4A_T4_WALL := (Runtime() - K4A_T4_T0) / 1000.0;;

Print("\n  T4 wall time: ", K4A_T4_WALL, " s\n");

K4AAssertTrue("T4: K4aClassify(2) returned a record",
              IsRecord(K4A_T4_RES));
K4AAssertEqual("T4: result.m = 2", K4A_T4_RES.m, 2);
K4AAssertEqual("T4: verdict = 'trivial' at m = 2",
               K4A_T4_RES.verdict, "trivial");
K4AAssertEqual("T4: trivial = true at m = 2",
               K4A_T4_RES.trivial, true);
K4AAssertEqual("T4: E_class.is_coboundary = true at m = 2",
               K4A_T4_RES.E_class.is_coboundary, true);
K4AAssertEqual("T4: D8_class.class_idx = 1 at m = 2",
               K4A_T4_RES.D8_class.class_idx, 1);
K4AAssertEqual("T4: Q8_class.class_idx = 1 at m = 2",
               K4A_T4_RES.Q8_class.class_idx, 1);
# E-branch rank at m=2: |E|^2 = (2^3)^2 = 64.
K4AAssertEqual("T4: E CT modular data is rank 64 (m = 2)",
               Length(K4A_T4_RES.E_class.modular_ct.S), 64);

# ---- Final report ------------------------------------------------------

Print("\n=================================================================\n");
Print("Summary: ", K4A_PASSES, " passes, ",
      Length(K4A_FAILURES), " failures.\n");
Print("=================================================================\n");

if Length(K4A_FAILURES) = 0 then
    Print("\nPASS test_k4a_classify\n");
else
    Print("\nFAIL test_k4a_classify:\n");
    for K4A_F in K4A_FAILURES do
        Print("  - ", K4A_F, "\n");
    od;
fi;

QUIT;
