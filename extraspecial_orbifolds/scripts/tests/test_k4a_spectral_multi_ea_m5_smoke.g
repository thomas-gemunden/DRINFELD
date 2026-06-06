# test_k4a_spectral_multi_ea_m5_smoke.g
#
# Issue #449 / Multi-EA spectral E-branch dispatch at m=5 (PR:
# multi-ea-spectral-e-branch).
#
# Smoke test that exercises the new `_K4A_ClassifySpectralEBranchMulti`
# helper at m=5 using a CONSTRAINED 2-EA family (so the per-EA loop
# runs in ~15-25 min wall instead of ~80 min for the full 9-EA D-VAN
# minimum family).
#
# Approach: override `_K4A_DVAN_EA_FAMILIES.("5")` to a 2-element subset
# of the D-VAN family before calling `K4aClassify(5)`. This still
# exercises the multi-EA dispatch but bounds the wall time.
#
# What we check
#   T1. K4aClassify(5) returns verdict = "trivial" (matches the PR #421
#       baseline) with the constrained 2-EA family.
#   T2. The E_class record carries `spectral_multi_ea := true` and
#       `family_source := "dvan-min-family"`.
#   T3. The E_class.per_ea_results list has 2 entries (one per overridden
#       EA), each with `is_coboundary = true`.
#
# Run from absolute path (~20-30 min wall):
#   gap -q -b /Users/.../tests/test_k4a_spectral_multi_ea_m5_smoke.g
#
# Skipped by default in the standard test sweep due to wall cost; run
# manually as part of post-PR verification.

# ---- Test bookkeeping --------------------------------------------------

M5MULTI_PASSES   := 0;;
M5MULTI_FAILURES := [];;

M5MultiAssertEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
        M5MULTI_PASSES := M5MULTI_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Print("         expected: ", expected, "\n");
        Print("         got:      ", got, "\n");
        Add(M5MULTI_FAILURES, label);
    fi;
end;;

M5MultiAssertTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
        M5MULTI_PASSES := M5MULTI_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Add(M5MULTI_FAILURES, label);
    fi;
end;;

# ---- Locate worktree, scripts, sibling files ---------------------------

M5MULTI_SELF := INPUT_FILENAME();;
if M5MULTI_SELF = fail or M5MULTI_SELF = "stream" then
    Error("test_k4a_spectral_multi_ea_m5_smoke.g: INPUT_FILENAME() unavailable.");
fi;
M5MULTI_SELFDIR := M5MULTI_SELF{
    [1..Length(M5MULTI_SELF) - Length("/test_k4a_spectral_multi_ea_m5_smoke.g")]};;
M5MULTI_SCRIPTSDIR := M5MULTI_SELFDIR{
    [1..Length(M5MULTI_SELFDIR) - Length("/tests")]};;
M5MULTI_WT_ROOT := M5MULTI_SCRIPTSDIR{
    [1..Length(M5MULTI_SCRIPTSDIR) - Length("/extraspecial_orbifolds/scripts")]};;

Print("=================================================================\n");
Print("test_k4a_spectral_multi_ea_m5_smoke.g (constrained 2-EA family)\n");
Print("=================================================================\n");

# Load src/modular_data.g + k4a_classify.g.
Read(Concatenation(M5MULTI_WT_ROOT, "/src/modular_data.g"));
M5MultiAssertTrue("LoadModularData bound", IsBound(LoadModularData));
Read(Concatenation(M5MULTI_SCRIPTSDIR, "/k4a_classify.g"));
M5MultiAssertTrue("K4aClassify bound", IsBound(K4aClassify));
M5MultiAssertTrue("_K4A_ClassifySpectralEBranchMulti bound",
                   IsBoundGlobal("_K4A_ClassifySpectralEBranchMulti"));

# Modular_Data symlink for D_8 / Q_8 LoadModularData.
M5MULTI_MD_ROOT := fail;;
for M5MULTI_CAND in
    [ Concatenation(M5MULTI_WT_ROOT, "/../modular_data"),
      "/Users/thomasgemunden/Projects/group_cohomology/modular_data" ] do
    if M5MULTI_MD_ROOT = fail
       and IsExistingFile(Concatenation(M5MULTI_CAND, "/8/4/1.txt")) then
        M5MULTI_MD_ROOT := M5MULTI_CAND;
    fi;
od;
if M5MULTI_MD_ROOT = fail then
    Error("test_k4a_spectral_multi_ea_m5_smoke.g: cannot locate modular_data tree.");
fi;

M5MULTI_LINKDIR := Concatenation(M5MULTI_SELFDIR,
                                  "/k4a/multi_ea_m5_smoke");;
if not IsExistingFile(M5MULTI_LINKDIR) then
    Exec(Concatenation("mkdir -p '", M5MULTI_LINKDIR, "'"));
fi;
M5MULTI_LINKPATH := Concatenation(M5MULTI_LINKDIR, "/Modular_Data");;
if not IsExistingFile(M5MULTI_LINKPATH) then
    Exec(Concatenation("ln -s '", M5MULTI_MD_ROOT, "' '",
                       M5MULTI_LINKPATH, "'"));
fi;
ChangeDirectoryCurrent(M5MULTI_LINKDIR);

# ---- Override _K4A_DVAN_EA_FAMILIES.("5") to a 2-EA subset -------------
#
# Original D-VAN m=5 family is [33, 48, 54, 57, 70, 76, 88, 89, 109].
# We pick the first and last for the smoke (to exercise both endpoints
# of the family ordering).

Print("\nT0: overriding _K4A_DVAN_EA_FAMILIES.(\"5\") for fast smoke\n");
M5MULTI_ORIG_FAM := _K4A_DVAN_EA_FAMILIES.("5");;
_K4A_DVAN_EA_FAMILIES.("5") := [33, 109];;
M5MultiAssertEqual("override active",
                    _K4A_GetDVANEAFamily(5), [33, 109]);

# ---- T1: K4aClassify(5) verdict TRIVIAL via 2-EA multi-EA path ---------

Print("\n=================================================================\n");
Print("T1: K4aClassify(5) with 2-EA family -> verdict 'trivial'\n");
Print("=================================================================\n");

M5MULTI_T0 := Runtime();;
M5MULTI_RES := K4aClassify(5);;
M5MULTI_WALL := (Runtime() - M5MULTI_T0) / 1000.0;;
Print("\n  m=5 wall (2-EA): ", M5MULTI_WALL, " s\n");

M5MultiAssertTrue("T1: K4aClassify(5) returned a record",
                   IsRecord(M5MULTI_RES));
M5MultiAssertEqual("T1: K-4a verdict = 'trivial' at m=5 (2-EA family)",
                    M5MULTI_RES.verdict, "trivial");
M5MultiAssertEqual("T1: K-4a trivial = true at m=5 (2-EA family)",
                    M5MULTI_RES.trivial, true);

# ---- T2: E_class records the multi-EA marker ----------------------------

Print("\n=================================================================\n");
Print("T2: E_class.spectral_multi_ea = true + family_source\n");
Print("=================================================================\n");

M5MultiAssertEqual("T2: E_class.spectral_multi_ea = true",
                    IsBound(M5MULTI_RES.E_class.spectral_multi_ea)
                    and M5MULTI_RES.E_class.spectral_multi_ea = true,
                    true);
M5MultiAssertEqual("T2: E_class.family_source = 'dvan-min-family'",
                    M5MULTI_RES.E_class.family_source,
                    "dvan-min-family");
M5MultiAssertEqual("T2: E_class.is_abelian = true",
                    M5MULTI_RES.E_class.is_abelian, true);
M5MultiAssertEqual("T2: E_class.is_coboundary = true",
                    M5MULTI_RES.E_class.is_coboundary, true);

# ---- T3: per_ea_results has 2 entries, all coboundary -------------------

Print("\n=================================================================\n");
Print("T3: per_ea_results sub-shape (2 entries, all coboundary)\n");
Print("=================================================================\n");

M5MultiAssertTrue("T3: per_ea_results is a list",
                   IsList(M5MULTI_RES.E_class.per_ea_results));
M5MultiAssertEqual("T3: per_ea_results length = 2 (overridden family)",
                    Length(M5MULTI_RES.E_class.per_ea_results), 2);

for M5MULTI_PE in M5MULTI_RES.E_class.per_ea_results do
    M5MultiAssertEqual(Concatenation(
                          "T3: per_ea_results[ea_idx ",
                          String(M5MULTI_PE.ea_idx),
                          "].ea_order = 64"),
                        M5MULTI_PE.ea_order, 64);
    M5MultiAssertEqual(Concatenation(
                          "T3: per_ea_results[ea_idx ",
                          String(M5MULTI_PE.ea_idx),
                          "].is_coboundary = true"),
                        M5MULTI_PE.is_coboundary, true);
od;

# ---- Restore original family before exit --------------------------------
_K4A_DVAN_EA_FAMILIES.("5") := M5MULTI_ORIG_FAM;;

# ---- Summary -----------------------------------------------------------

Print("\n=================================================================\n");
Print("Summary: ", M5MULTI_PASSES, " passes, ",
      Length(M5MULTI_FAILURES), " failures.\n");
Print("=================================================================\n");
Print("Total wall: ", M5MULTI_WALL, " s.\n");

if Length(M5MULTI_FAILURES) = 0 then
    Print("\nPASS test_k4a_spectral_multi_ea_m5_smoke\n");
    QUIT_GAP(0);
else
    Print("\nFAIL test_k4a_spectral_multi_ea_m5_smoke:\n");
    for M5MULTI_F in M5MULTI_FAILURES do
        Print("  - ", M5MULTI_F, "\n");
    od;
    QUIT_GAP(1);
fi;
