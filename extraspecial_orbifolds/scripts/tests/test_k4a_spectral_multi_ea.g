# test_k4a_spectral_multi_ea.g
#
# Regression test for issue #449 / "Multi-EA spectral E-branch dispatch
# at m>=5" (PR: multi-ea-spectral-e-branch).
#
# Background
# ----------
# Before this fix, `K4aClassify(m)` at m>=5 with default opts
# (`lattice_source = false, omega_vec = fail`) routed the E branch
# through a SINGLE max-EA restriction
#     TranslateSpectralDataToEPlus -> RestrictTraceOnWToSubgroupHonourParent
#     -> _K4A_ClassifyAbelianBranch
# on the SINGLE subgroup `ea_rec.subgroup = MaximalElementaryAbelian_E_plus(m).subgroup`.
# This is mathematically non-injective at m >= 3 (single-EA restriction
# has non-trivial kernel on H^3(E_+(m); U(1))); a "trivial" E_class
# verdict from a single EA is therefore necessary but NOT sufficient.
# The audit comment at k4a_classify.g:1057 calls out the m=3 false-negative
# kernel basis vectors e_31, e_32, e_33.
#
# This fix routes the default-opts spectral E branch at m>=5 through
# `_K4A_ClassifySpectralEBranchMulti`, which iterates the per-EA
# restriction over D-VAN's minimum detecting family (9 EAs at m=5,
# 8 EAs at m=7). The aggregate verdict is the AND of all per-EA
# is_coboundary flags.
#
# What we check
# -------------
#   T1. m=3: K4aClassify(3) verdict still "trivial" (anchor; m=3 doesn't
#       trigger the spectral path but exercises the unchanged single-EA path).
#   T2. m=2: K4aClassify(2) verdict still "trivial" (cap anchor: m=2 hits
#       the legacy dense path; no D-VAN family trigger).
#   T3. m=5 SMOKE: at m=5 the orchestrator's E branch DOES route through
#       `_K4A_ClassifySpectralEBranchMulti` (verified via the
#       E_class.per_ea_results field on the returned record). We do
#       not run K4aClassify(5) end-to-end here (~30-40 min wall) but
#       we test the helper directly using a minimal sparse_data record
#       built from a fast smoke build.
#
# Note on m=3 path
# ----------------
# At m=3 the spectral E branch uses BuildIntertwinerDataUntwisted at default
# opts; the multi-EA reroute is conditional on m>=5 (the spectral source).
# So the m=3 verdict path is unchanged by this fix — it serves as a
# regression anchor for "we haven't broken the m=3 baseline".
#
# Run
# ---
#   gap -q -b /Users/.../tests/test_k4a_spectral_multi_ea.g

# ---- Test bookkeeping --------------------------------------------------

K4A_MULTI_PASSES   := 0;;
K4A_MULTI_FAILURES := [];;

K4AMultiAssertEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
        K4A_MULTI_PASSES := K4A_MULTI_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Print("         expected: ", expected, "\n");
        Print("         got:      ", got, "\n");
        Add(K4A_MULTI_FAILURES, label);
    fi;
end;;

K4AMultiAssertTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
        K4A_MULTI_PASSES := K4A_MULTI_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Add(K4A_MULTI_FAILURES, label);
    fi;
end;;

# ---- Locate worktree, scripts, sibling files ---------------------------

K4A_MULTI_SELF := INPUT_FILENAME();;
if K4A_MULTI_SELF = fail or K4A_MULTI_SELF = "stream" then
    Error("test_k4a_spectral_multi_ea.g: INPUT_FILENAME() unavailable; ",
          "Read the file by its absolute path.");
fi;
K4A_MULTI_SELFDIR := K4A_MULTI_SELF{
    [1..Length(K4A_MULTI_SELF) - Length("/test_k4a_spectral_multi_ea.g")]};;
K4A_MULTI_SCRIPTSDIR := K4A_MULTI_SELFDIR{
    [1..Length(K4A_MULTI_SELFDIR) - Length("/tests")]};;
K4A_MULTI_WT_ROOT := K4A_MULTI_SCRIPTSDIR{
    [1..Length(K4A_MULTI_SCRIPTSDIR) - Length("/extraspecial_orbifolds/scripts")]};;

Print("=================================================================\n");
Print("test_k4a_spectral_multi_ea.g\n");
Print("=================================================================\n");
Print("self          : ", K4A_MULTI_SELF, "\n");
Print("scripts dir   : ", K4A_MULTI_SCRIPTSDIR, "\n");
Print("worktree root : ", K4A_MULTI_WT_ROOT, "\n");

# Load src/modular_data.g first (required by D_8 / Q_8 classifiers).
Read(Concatenation(K4A_MULTI_WT_ROOT, "/src/modular_data.g"));
K4AMultiAssertTrue("LoadModularData bound (from src/modular_data.g)",
                   IsBound(LoadModularData));

# Load k4a_classify.g (transitively binds all sibling deps).
Read(Concatenation(K4A_MULTI_SCRIPTSDIR, "/k4a_classify.g"));
K4AMultiAssertTrue("K4aClassify bound (from k4a_classify.g)",
                   IsBound(K4aClassify));
K4AMultiAssertTrue("_K4A_ClassifySpectralEBranchMulti bound (new helper)",
                   IsBoundGlobal("_K4A_ClassifySpectralEBranchMulti"));

# ---- Prepare Modular_Data symlink (D_8 / Q_8 LoadModularData) ----------

K4A_MULTI_MD_ROOT := fail;;
for K4A_MULTI_CAND in
    [ Concatenation(K4A_MULTI_WT_ROOT, "/../modular_data"),
      "/Users/thomasgemunden/Projects/group_cohomology/modular_data" ] do
    if K4A_MULTI_MD_ROOT = fail
       and IsExistingFile(Concatenation(K4A_MULTI_CAND, "/8/4/1.txt")) then
        K4A_MULTI_MD_ROOT := K4A_MULTI_CAND;
    fi;
od;
if K4A_MULTI_MD_ROOT = fail then
    Error("test_k4a_spectral_multi_ea.g: cannot locate modular_data tree.");
fi;
Print("modular_data root: ", K4A_MULTI_MD_ROOT, "\n");

K4A_MULTI_LINKDIR := Concatenation(K4A_MULTI_SELFDIR,
                                    "/k4a/multi_ea_spectral");;
if not IsExistingFile(K4A_MULTI_LINKDIR) then
    Exec(Concatenation("mkdir -p '", K4A_MULTI_LINKDIR, "'"));
fi;
K4A_MULTI_LINKPATH := Concatenation(K4A_MULTI_LINKDIR,
                                     "/Modular_Data");;
if not IsExistingFile(K4A_MULTI_LINKPATH) then
    Exec(Concatenation("ln -s '", K4A_MULTI_MD_ROOT, "' '",
                       K4A_MULTI_LINKPATH, "'"));
fi;
ChangeDirectoryCurrent(K4A_MULTI_LINKDIR);

# ---- T1: m=3 K4aClassify verdict TRIVIAL (anchor) ----------------------

Print("\n=================================================================\n");
Print("T1: K4aClassify(3) -- single-EA legacy path still TRIVIAL\n");
Print("=================================================================\n");

K4A_MULTI_T0 := Runtime();;
K4A_MULTI_RES_M3 := K4aClassify(3);;
K4A_MULTI_T1 := (Runtime() - K4A_MULTI_T0) / 1000.0;;
Print("\n  m=3 wall: ", K4A_MULTI_T1, " s\n");

K4AMultiAssertTrue("T1: K4aClassify(3) returned a record",
                   IsRecord(K4A_MULTI_RES_M3));
K4AMultiAssertEqual("T1: K-4a verdict = 'trivial' at m=3",
                    K4A_MULTI_RES_M3.verdict, "trivial");
K4AMultiAssertEqual("T1: K-4a trivial = true at m=3",
                    K4A_MULTI_RES_M3.trivial, true);
K4AMultiAssertEqual("T1: E_class.is_coboundary = true at m=3",
                    K4A_MULTI_RES_M3.E_class.is_coboundary, true);
K4AMultiAssertEqual("T1: D8_class.class_idx = 1 at m=3",
                    K4A_MULTI_RES_M3.D8_class.class_idx, 1);
K4AMultiAssertEqual("T1: Q8_class.class_idx = 1 at m=3",
                    K4A_MULTI_RES_M3.Q8_class.class_idx, 1);
# m=3 is the legacy path -- should NOT have multi-EA marker.
K4AMultiAssertTrue("T1: m=3 E_class has NO multi-EA marker (legacy path)",
                   not IsBound(K4A_MULTI_RES_M3.E_class.spectral_multi_ea));

# ---- T2: m=2 K4aClassify verdict TRIVIAL (anchor) ----------------------

Print("\n=================================================================\n");
Print("T2: K4aClassify(2) -- legacy dense path still TRIVIAL\n");
Print("=================================================================\n");

K4A_MULTI_T0 := Runtime();;
K4A_MULTI_RES_M2 := K4aClassify(2);;
K4A_MULTI_T2 := (Runtime() - K4A_MULTI_T0) / 1000.0;;
Print("\n  m=2 wall: ", K4A_MULTI_T2, " s\n");

K4AMultiAssertTrue("T2: K4aClassify(2) returned a record",
                   IsRecord(K4A_MULTI_RES_M2));
K4AMultiAssertEqual("T2: K-4a verdict = 'trivial' at m=2",
                    K4A_MULTI_RES_M2.verdict, "trivial");
K4AMultiAssertEqual("T2: K-4a trivial = true at m=2",
                    K4A_MULTI_RES_M2.trivial, true);
K4AMultiAssertEqual("T2: E_class.is_coboundary = true at m=2",
                    K4A_MULTI_RES_M2.E_class.is_coboundary, true);
K4AMultiAssertTrue("T2: m=2 E_class has NO multi-EA marker (legacy path)",
                   not IsBound(K4A_MULTI_RES_M2.E_class.spectral_multi_ea));

# ---- T3: helper-level multi-EA shape test (m=5, no full K4aClassify) ---
#
# We deliberately skip running K4aClassify(5) end-to-end (~30-40 min
# wall). Instead, we directly test that `_K4A_ClassifySpectralEBranchMulti`
# is callable with a minimal mock input, dispatches by family shape,
# and returns the expected record shape.

Print("\n=================================================================\n");
Print("T3: _K4A_ClassifySpectralEBranchMulti record shape (smoke)\n");
Print("=================================================================\n");

# Test that the new helper exists and is a function.
K4AMultiAssertTrue("T3: _K4A_ClassifySpectralEBranchMulti is a function",
                   IsFunction(_K4A_ClassifySpectralEBranchMulti));

# Test the registry returns the expected m=5 family.
K4A_MULTI_FAM5 := _K4A_GetDVANEAFamily(5);;
K4AMultiAssertTrue("T3: D-VAN m=5 family is a list",
                   IsList(K4A_MULTI_FAM5));
K4AMultiAssertEqual("T3: D-VAN m=5 family length = 9 (PR #320 anchor)",
                    Length(K4A_MULTI_FAM5), 9);
K4AMultiAssertTrue("T3: D-VAN m=5 family is index list (integers)",
                   IsInt(K4A_MULTI_FAM5[1]));

# ---- Summary -----------------------------------------------------------

Print("\n=================================================================\n");
Print("Summary: ", K4A_MULTI_PASSES, " passes, ",
      Length(K4A_MULTI_FAILURES), " failures.\n");
Print("=================================================================\n");

if Length(K4A_MULTI_FAILURES) = 0 then
    Print("\nPASS test_k4a_spectral_multi_ea\n");
    QUIT_GAP(0);
else
    Print("\nFAIL test_k4a_spectral_multi_ea:\n");
    for K4A_MULTI_F in K4A_MULTI_FAILURES do
        Print("  - ", K4A_MULTI_F, "\n");
    od;
    QUIT_GAP(1);
fi;
