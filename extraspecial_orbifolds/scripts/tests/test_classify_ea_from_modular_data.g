# test_classify_ea_from_modular_data.g
#
# Issue #486: anchor tests for `ClassifyEAFromModularData(H, S, T)`
# (in `ea_modular_data_classifier.g`).
#
# Acceptance criteria (per issue body):
#
#   (A1) Untwisted self-match: on (Z/2)^3, classify the untwisted
#        modular data of (Z/2)^3 against itself and assert
#        is_trivial = true, class_idx = 1.
#
#   (A2) Non-trivial cocycle: on (Z/2)^2, build the twisted modular
#        data with omega = e_1 (a non-trivial generator of
#        H^3((Z/2)^2; U(1))) and assert is_trivial = false,
#        class_idx = fail.
#
#   (A3) K-4a m=2 end-to-end smoke: after the PR #486 rewiring,
#        K4aClassify(2) still returns verdict = "trivial". m=2 has been
#        GREEN throughout the K-4a workstream and the actual alpha at
#        m=2 genuinely IS a coboundary; if this regresses, that's a
#        bug in PR #486's wiring, not the underlying math.

EAC_PASSES   := 0;;
EAC_FAILURES := [];;

EACAssertEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
        EAC_PASSES := EAC_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Print("         expected: ", expected, "\n");
        Print("         got:      ", got, "\n");
        Add(EAC_FAILURES, label);
    fi;
end;;

EACAssertTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
        EAC_PASSES := EAC_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Add(EAC_FAILURES, label);
    fi;
end;;

# ---- Locate the worktree and dependencies ------------------------------
EAC_SELF := INPUT_FILENAME();;
if EAC_SELF = fail or EAC_SELF = "stream" then
    Error("test_classify_ea_from_modular_data.g: INPUT_FILENAME() ",
          "unavailable; Read the file by its absolute path.");
fi;
EAC_SELFDIR := EAC_SELF{[1..Length(EAC_SELF)
                          - Length("/test_classify_ea_from_modular_data.g")]};;
EAC_SCRIPTSDIR := EAC_SELFDIR{
    [1..Length(EAC_SELFDIR) - Length("/tests")]};;
EAC_WT_ROOT := EAC_SCRIPTSDIR{
    [1..Length(EAC_SCRIPTSDIR) - Length("/extraspecial_orbifolds/scripts")]};;
Print("worktree root: ", EAC_WT_ROOT, "\n");

# Change to the scripts dir so relative Reads ("transgression_kernel.g")
# inside the loaded modules work.
ChangeDirectoryCurrent(EAC_SCRIPTSDIR);

# Load src/modular_data.g first so ComputeModularData (needed for the
# non-trivial-cocycle anchor) is bound.
Read(Concatenation(EAC_WT_ROOT, "/src/modular_data.g"));
EACAssertTrue("ComputeModularData bound (from src/modular_data.g)",
              IsBound(ComputeModularData));

# Load the transgression-kernel helpers so we can synthesise a
# non-trivial 3-cocycle on (Z/2)^2 via the standard cocycle path
# (StandardCocycleOf + SetupCohomology3). This is the same pattern used
# by test_k4a_e_branch_synthetic.g.
Read(Concatenation(EAC_SCRIPTSDIR, "/transgression_kernel.g"));
EACAssertTrue("SetupCohomology3 bound", IsBound(SetupCohomology3));
EACAssertTrue("StandardCocycleOf bound", IsBound(StandardCocycleOf));

# Load the module under test. ea_modular_data_classifier.g auto-loads
# joint_permutation_matcher and untwisted_modular_data siblings.
Read(Concatenation(EAC_SCRIPTSDIR, "/ea_modular_data_classifier.g"));
EACAssertTrue("ClassifyEAFromModularData bound",
              IsBound(ClassifyEAFromModularData));
EACAssertTrue("JointPermutationMatcher bound (transitively)",
              IsBound(JointPermutationMatcher));
EACAssertTrue("ComputeUntwistedModularData bound (transitively)",
              IsBound(ComputeUntwistedModularData));

# ---- Anchor 1: untwisted self-match on (Z/2)^3 -------------------------
Print("\nAnchor 1: untwisted self-match on (Z/2)^3.\n");
EAC_H_A1 := ElementaryAbelianGroup(8);;
EAC_T0 := Runtime();;
EAC_MD_A1 := ComputeUntwistedModularData(EAC_H_A1);;
EAC_RES_A1 := ClassifyEAFromModularData(EAC_H_A1, EAC_MD_A1.S, EAC_MD_A1.T);;
Print("  H = (Z/2)^3, |H| = ", Order(EAC_H_A1),
      ", rank N = |H|^2 = ", Order(EAC_H_A1) ^ 2, "\n");
Print("  build + classify wall: ", Runtime() - EAC_T0, " ms\n");
Print("  res.is_trivial = ", EAC_RES_A1.is_trivial,
      ", res.class_idx = ", EAC_RES_A1.class_idx, "\n");
EACAssertEqual("A1: untwisted self-match: is_trivial = true",
               EAC_RES_A1.is_trivial, true);
EACAssertEqual("A1: untwisted self-match: class_idx = 1",
               EAC_RES_A1.class_idx, 1);
EACAssertEqual("A1: match.ok = true",
               EAC_RES_A1.match.ok, true);
EACAssertTrue("A1: match.pi is a permutation of [1..N]",
              IsList(EAC_RES_A1.match.pi)
              and Length(EAC_RES_A1.match.pi) = Order(EAC_H_A1) ^ 2
              and SortedList(EAC_RES_A1.match.pi) = [1..Order(EAC_H_A1) ^ 2]);
EACAssertTrue("A1: modular_untwisted is bound",
              IsBound(EAC_RES_A1.modular_untwisted));

# ---- Anchor 2: non-trivial cocycle on (Z/2)^2 -> is_trivial = false ----
Print("\nAnchor 2: non-trivial cocycle on (Z/2)^2 -> is_trivial = false.\n");
EAC_H_A2 := ElementaryAbelianGroup(4);;
EAC_SETUP := SetupCohomology3(EAC_H_A2);;
Print("  H = (Z/2)^2, setup.num_generators = ",
      EAC_SETUP.num_generators,
      ", setup.exponent = ", EAC_SETUP.exponent, "\n");
EACAssertTrue("A2: setup.num_generators >= 1 (cocycle basis non-empty)",
              EAC_SETUP.num_generators >= 1);
# Build the e_1 (non-trivial) cocycle via the standard-cocycle path.
EAC_OMEGA_VEC := ListWithIdenticalEntries(EAC_SETUP.num_generators, 0);;
EAC_OMEGA_VEC[1] := 1;;
EAC_OMEGA_FN := StandardCocycleOf(EAC_SETUP, EAC_OMEGA_VEC);;
EAC_VAL := Gcd(Gcd(EAC_OMEGA_VEC), EAC_SETUP.exponent);;
EAC_EXPON := EAC_SETUP.exponent / EAC_VAL;;
Print("  omega = e_1, val = ", EAC_VAL,
      ", expon = ", EAC_EXPON, "\n");
EAC_T0 := Runtime();;
EAC_MD_A2 := ComputeModularData(
    EAC_H_A2, EAC_OMEGA_FN, EAC_VAL, EAC_EXPON);;
EAC_RES_A2 := ClassifyEAFromModularData(
    EAC_H_A2, EAC_MD_A2.S, EAC_MD_A2.T);;
Print("  build + classify wall: ", Runtime() - EAC_T0, " ms\n");
Print("  res.is_trivial = ", EAC_RES_A2.is_trivial,
      ", res.class_idx = ", EAC_RES_A2.class_idx, "\n");
if IsBound(EAC_RES_A2.match.reason) then
    Print("  match.reason = ", EAC_RES_A2.match.reason, "\n");
fi;
EACAssertEqual("A2: non-trivial cocycle: is_trivial = false",
               EAC_RES_A2.is_trivial, false);
EACAssertEqual("A2: non-trivial cocycle: class_idx = fail",
               EAC_RES_A2.class_idx, fail);
EACAssertEqual("A2: match.ok = false",
               EAC_RES_A2.match.ok, false);

# ---- Anchor 3: K-4a m=2 end-to-end smoke ------------------------------
# This validates that PR #486's rewiring of `_K4A_ClassifyAbelianBranch`
# does not regress the K-4a m=2 anchor (which has been GREEN throughout
# and reflects the actual mathematical fact that alpha at m=2 IS a
# coboundary). m=2 is fast (well under 1 minute).
#
# K4aClassify's D_8 / Q_8 branches require the precomputed
# `modular_data/8/{3,4}/*.txt` ground-truth tree visible via a
# `Modular_Data/` symlink (this is GAP's `LoadModularData(8,3,k)`
# convention; see d8_classifier.g and the test_d8_classifier.g loader).
# Set up the symlink here so the K-4a m=2 smoke works end-to-end.
Print("\nAnchor 3: K-4a m=2 end-to-end smoke.\n");
EAC_MD_ROOT := fail;;
for EAC_CAND in
    [ Concatenation(EAC_WT_ROOT, "/../modular_data"),
      "/Users/thomasgemunden/Projects/group_cohomology/modular_data" ] do
    if EAC_MD_ROOT = fail
       and IsExistingFile(Concatenation(EAC_CAND, "/8/3/1.txt")) then
        EAC_MD_ROOT := EAC_CAND;
    fi;
od;
if EAC_MD_ROOT = fail then
    Print("  [SKIP] cannot locate modular_data tree; ",
          "skipping A3 (K-4a m=2 smoke).\n");
else
    Print("  modular_data root: ", EAC_MD_ROOT, "\n");
    EAC_LINKDIR := Concatenation(EAC_SELFDIR, "/k4a/ea_md_classifier");;
    if not IsExistingFile(EAC_LINKDIR) then
        Exec(Concatenation("mkdir -p '", EAC_LINKDIR, "'"));
    fi;
    EAC_LINKPATH := Concatenation(EAC_LINKDIR, "/Modular_Data");;
    if not IsExistingFile(EAC_LINKPATH) then
        Exec(Concatenation("ln -s '", EAC_MD_ROOT, "' '",
                           EAC_LINKPATH, "'"));
    fi;
    ChangeDirectoryCurrent(EAC_LINKDIR);
    # K4aClassify is already loaded (transitively pulled by
    # ea_modular_data_classifier.g via _K4A_LoadSibling). Belt-and-braces:
    Read(Concatenation(EAC_SCRIPTSDIR, "/k4a_classify.g"));
    EACAssertTrue("K4aClassify bound", IsBound(K4aClassify));
    EAC_T0 := Runtime();;
    EAC_K4A_RES := K4aClassify(2);;
    Print("  K4aClassify(2) wall: ", (Runtime() - EAC_T0) / 1000.,
          " s, verdict = ", EAC_K4A_RES.verdict, "\n");
    EACAssertEqual("A3: K-4a m=2 verdict = \"trivial\"",
                   EAC_K4A_RES.verdict, "trivial");
fi;

# ---- Final summary -----------------------------------------------------
Print("\n=== Final summary ===\n");
Print("  passes:   ", EAC_PASSES, "\n");
Print("  failures: ", Length(EAC_FAILURES), "\n");
if Length(EAC_FAILURES) = 0 then
    Print("\ntest_classify_ea_from_modular_data: PASS\n");
else
    Print("\ntest_classify_ea_from_modular_data: FAIL (",
          Length(EAC_FAILURES), "):\n");
    for EAC_F in EAC_FAILURES do
        Print("  - ", EAC_F, "\n");
    od;
fi;

QUIT;
