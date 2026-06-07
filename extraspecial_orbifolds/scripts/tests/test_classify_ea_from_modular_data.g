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

# ---- Anchor 4: (q, b) extraction agrees with cocycle (q, b) (#490) -----
# For (Z/2)^k k in {1, 2, 3}, build a non-trivial cocycle, run both the
# FORWARD direction (cocycle → q, b via ClassifyAbelianBranchFast) and
# the INVERSE direction (modular data → q, b via ExtractQBFromModularData).
# Assert q vectors agree mod N and b matrices agree mod N.
Print("\nAnchor 4: (q, b) extraction agrees with cocycle (q, b) (PR #490).\n");

if not IsBound(ComputeAbelianModularDataFactored) then
    Read(Concatenation(EAC_SCRIPTSDIR, "/abelian_modular_data_closed_form.g"));
fi;
if not IsBound(ClassifyAbelianBranchFast) then
    Read(Concatenation(EAC_SCRIPTSDIR, "/abelian_branch_fast.g"));
fi;
EACAssertTrue("A4: ExtractQBFromModularData bound",
              IsBound(ExtractQBFromModularData));
EACAssertTrue("A4: ComputeAbelianModularDataFactored bound",
              IsBound(ComputeAbelianModularDataFactored));
EACAssertTrue("A4: ClassifyAbelianBranchFast bound",
              IsBound(ClassifyAbelianBranchFast));

EAC_A4_GROUPS := [
    [ "(Z/2)^1", ElementaryAbelianGroup(IsPcGroup, 2) ],
    [ "(Z/2)^2", ElementaryAbelianGroup(IsPcGroup, 4) ],
    [ "(Z/2)^3", ElementaryAbelianGroup(IsPcGroup, 8) ]
];;
for EAC_PAIR in EAC_A4_GROUPS do
    EAC_LBL := EAC_PAIR[1];
    EAC_HA4 := EAC_PAIR[2];
    EAC_SETUP_A4 := SetupCohomology3(EAC_HA4);
    EAC_K_A4 := EAC_SETUP_A4.num_generators;
    Print("  ", EAC_LBL, ": k = ", EAC_K_A4,
          ", exponent = ", EAC_SETUP_A4.exponent, "\n");
    # Try a couple of unit vectors (anchor + e_1 + e_2).
    for EAC_I_A4 in [0, 1, 2] do
        if EAC_I_A4 > EAC_K_A4 then continue; fi;
        EAC_GV_A4 := ListWithIdenticalEntries(EAC_K_A4, 0);
        if EAC_I_A4 >= 1 then
            EAC_GV_A4[EAC_I_A4] := 1;
        fi;
        EAC_OMEGA_A4 := StandardCocycleOf(EAC_SETUP_A4, EAC_GV_A4);
        EAC_VAL_A4 := Maximum(
            Gcd(Gcd(EAC_GV_A4), EAC_SETUP_A4.exponent), 1);
        EAC_EXPON_A4 := EAC_SETUP_A4.exponent / EAC_VAL_A4;
        if EAC_GV_A4 = ListWithIdenticalEntries(EAC_K_A4, 0) then
            EAC_N_A4 := 1;
        else
            EAC_N_A4 := EAC_EXPON_A4;
        fi;

        EAC_MDF_A4 := ComputeAbelianModularDataFactored(
            EAC_HA4, EAC_OMEGA_A4, EAC_N_A4);
        EAC_QB_A4 := ExtractQBFromModularData(EAC_MDF_A4);
        EAC_FAST_A4 := ClassifyAbelianBranchFast(
            EAC_HA4, EAC_OMEGA_A4, EAC_N_A4);

        # Compare q mod N (extraction is mod 2N; fast is mod N).
        EAC_Q_EX_MODN := List(EAC_QB_A4.q, x -> x mod EAC_N_A4);
        EAC_Q_FAST_MODN := List(EAC_FAST_A4.q_omega, x -> x mod EAC_N_A4);
        EACAssertEqual(
            Concatenation("A4: ", EAC_LBL, " gv=", String(EAC_GV_A4),
                          ": q mod N agrees (extraction vs fast)"),
            EAC_Q_EX_MODN, EAC_Q_FAST_MODN);
        # Compare b mod N.
        EAC_B_EX_MODN := List(EAC_QB_A4.b,
            r -> List(r, x -> x mod EAC_N_A4));
        EAC_B_FAST_MODN := List(EAC_FAST_A4.b_omega,
            r -> List(r, x -> x mod EAC_N_A4));
        EACAssertEqual(
            Concatenation("A4: ", EAC_LBL, " gv=", String(EAC_GV_A4),
                          ": b mod N agrees (extraction vs fast)"),
            EAC_B_EX_MODN, EAC_B_FAST_MODN);
        # Classifier verdict agrees with fast path.
        EAC_CF_A4 := ClassifyEAFromModularData(
            EAC_HA4, EAC_MDF_A4, EAC_MDF_A4.T_vec);
        EACAssertEqual(
            Concatenation("A4: ", EAC_LBL, " gv=", String(EAC_GV_A4),
                          ": classify.is_trivial = fast.is_coboundary"),
            EAC_CF_A4.is_trivial, EAC_FAST_A4.is_coboundary);
        EACAssertEqual(
            Concatenation("A4: ", EAC_LBL, " gv=", String(EAC_GV_A4),
                          ": method = qb_extraction"),
            EAC_CF_A4.method, "qb_extraction");
    od;
od;

# ---- Anchor 5: factored input at (Z/2)^8 (PR #490 main use case) ------
# Build factored modular data for Z^omega(Vec_(Z/2)^8) with a non-trivial
# cocycle and assert is_trivial = false. The full S matrix at this scale
# is 65536 x 65536 (~4.3e9 entries) — infeasible. The factored path
# extracts (q, b) in O(|H|^2) S_at queries.
Print("\nAnchor 5: factored input at (Z/2)^8 with non-trivial omega.\n");
EAC_H_A5 := ElementaryAbelianGroup(IsPcGroup, 256);;  # (Z/2)^8
EAC_SETUP_A5 := SetupCohomology3(EAC_H_A5);;
EAC_K_A5 := EAC_SETUP_A5.num_generators;;
Print("  H = (Z/2)^8, |H| = ", Order(EAC_H_A5),
      ", setup.num_generators = ", EAC_K_A5,
      ", exponent = ", EAC_SETUP_A5.exponent, "\n");
EACAssertTrue("A5: setup.num_generators >= 1", EAC_K_A5 >= 1);

# Pick a unit basis vector e_1; this is a non-trivial element of
# H^3((Z/2)^8; U(1)) by construction.
EAC_GV_A5 := ListWithIdenticalEntries(EAC_K_A5, 0);;
EAC_GV_A5[1] := 1;;
EAC_OMEGA_A5 := StandardCocycleOf(EAC_SETUP_A5, EAC_GV_A5);;
EAC_VAL_A5 := Maximum(
    Gcd(Gcd(EAC_GV_A5), EAC_SETUP_A5.exponent), 1);;
EAC_EXPON_A5 := EAC_SETUP_A5.exponent / EAC_VAL_A5;;
Print("  omega = e_1, val = ", EAC_VAL_A5, ", expon = ", EAC_EXPON_A5, "\n");

EAC_T0 := Runtime();;
EAC_MDF_A5 := ComputeAbelianModularDataFactored(
    EAC_H_A5, EAC_OMEGA_A5, EAC_EXPON_A5);;
Print("  factored build wall: ", (Runtime() - EAC_T0) / 1000., " s\n");

EAC_T0 := Runtime();;
EAC_CF_A5 := ClassifyEAFromModularData(
    EAC_H_A5, EAC_MDF_A5, EAC_MDF_A5.T_vec);;
EAC_WALL_A5 := (Runtime() - EAC_T0) / 1000.;;
Print("  classify wall: ", EAC_WALL_A5, " s\n");
Print("  is_trivial = ", EAC_CF_A5.is_trivial,
      ", method = ", EAC_CF_A5.method,
      ", is_q_trivial = ", EAC_CF_A5.is_q_trivial,
      ", is_b_trivial = ", EAC_CF_A5.is_b_trivial, "\n");

EACAssertEqual("A5: (Z/2)^8 e_1 non-trivial: is_trivial = false",
               EAC_CF_A5.is_trivial, false);
EACAssertEqual("A5: method = qb_extraction",
               EAC_CF_A5.method, "qb_extraction");
EACAssertTrue("A5: classify wall < 60 sec (feasibility)",
              EAC_WALL_A5 < 60.0);

# Cross-validation: fast path should agree.
EAC_FAST_A5 := ClassifyAbelianBranchFast(
    EAC_H_A5, EAC_OMEGA_A5, EAC_EXPON_A5);;
EACAssertEqual("A5: is_trivial agrees with ClassifyAbelianBranchFast",
               EAC_CF_A5.is_trivial, EAC_FAST_A5.is_coboundary);

# ---- Anchor 6: backward compat at (Z/2)^k for k <= 4 (PR #486 path) ---
# At k <= 4 the full (S, T) matrix is tractable; the legacy
# `ClassifyEAFromModularData(H, S, T)` path (PATH B / JointPermutationMatcher)
# must give the same triviality verdict as the new factored path (PATH A).
Print("\nAnchor 6: backward compat — legacy full-(S,T) path agrees with ",
      "factored path on (Z/2)^k k <= 4.\n");
EAC_A6_GROUPS := [
    [ "(Z/2)^2", ElementaryAbelianGroup(IsPcGroup, 4) ],
    [ "(Z/2)^3", ElementaryAbelianGroup(IsPcGroup, 8) ],
    [ "(Z/2)^4", ElementaryAbelianGroup(IsPcGroup, 16) ]
];;
for EAC_PAIR in EAC_A6_GROUPS do
    EAC_LBL := EAC_PAIR[1];
    EAC_H_A6 := EAC_PAIR[2];
    EAC_SETUP_A6 := SetupCohomology3(EAC_H_A6);
    EAC_K_A6 := EAC_SETUP_A6.num_generators;
    # Test untwisted + first non-trivial unit vector.
    for EAC_TWIST in [0, 1] do
        EAC_GV_A6 := ListWithIdenticalEntries(EAC_K_A6, 0);
        if EAC_TWIST = 1 and EAC_K_A6 >= 1 then
            EAC_GV_A6[1] := 1;
        fi;
        EAC_OMEGA_A6 := StandardCocycleOf(EAC_SETUP_A6, EAC_GV_A6);
        EAC_VAL_A6 := Maximum(
            Gcd(Gcd(EAC_GV_A6), EAC_SETUP_A6.exponent), 1);
        EAC_EXPON_A6 := EAC_SETUP_A6.exponent / EAC_VAL_A6;
        if EAC_GV_A6 = ListWithIdenticalEntries(EAC_K_A6, 0) then
            EAC_N_A6 := 1;
        else
            EAC_N_A6 := EAC_EXPON_A6;
        fi;

        # PATH A: factored.
        EAC_MDF_A6 := ComputeAbelianModularDataFactored(
            EAC_H_A6, EAC_OMEGA_A6, EAC_N_A6);
        EAC_CF_FAC_A6 := ClassifyEAFromModularData(
            EAC_H_A6, EAC_MDF_A6, EAC_MDF_A6.T_vec);

        # PATH B: legacy full (S, T) via ComputeModularData. Untwisted
        # via ComputeUntwistedModularData.
        if EAC_TWIST = 0 then
            EAC_MD_FULL_A6 := ComputeUntwistedModularData(EAC_H_A6);
            EAC_CF_FULL_A6 := ClassifyEAFromModularData(
                EAC_H_A6, EAC_MD_FULL_A6.S, EAC_MD_FULL_A6.T);
        else
            EAC_MD_FULL_A6 := ComputeModularData(
                EAC_H_A6, EAC_OMEGA_A6, EAC_VAL_A6, EAC_EXPON_A6);
            EAC_CF_FULL_A6 := ClassifyEAFromModularData(
                EAC_H_A6, EAC_MD_FULL_A6.S, EAC_MD_FULL_A6.T);
        fi;

        EACAssertEqual(
            Concatenation("A6: ", EAC_LBL,
                          " twist=", String(EAC_TWIST),
                          ": is_trivial agrees (factored vs full-matrix)"),
            EAC_CF_FAC_A6.is_trivial, EAC_CF_FULL_A6.is_trivial);
    od;
od;

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
