# test_k4b_e2e_sweep_m5.g
#
# Issue #488: e2e classifier-correctness sweep at m=5.
#
# For each non-zero basis vector v of H^3(E_+(5); U(1)) (165 generators
# at m=5: 164 of order 2 + 1 of order 4) plus the half-vector
# 2 * order_4_generator, this test:
#
#   1. Restricts v to each H in the AM04+Quillen detecting family
#      F = {max EAs, D_8, Q_8} via the precomputed restriction
#      matrices in BuildRestrictionMatrices(m, "hap").
#   2. For each H in F:
#        a. If v|_H = 0 in H^3(H; U(1)), this branch cannot detect v
#           and we mark it skipped (other branches must pick it up).
#        b. Otherwise, synthesises the twisted modular data
#           (S^v|_H, T^v|_H) of Z^{v|_H}(Vec_H) via
#           `ComputeModularData(H, omega_H, val, expon)`.
#        c. Runs the K-4b classifier on (S^v|_H, T^v|_H):
#             - EA H: `ClassifyEAFromModularData(H, S, T)` (PR #486).
#             - D_8:  `ClassifyOnD8(S, DiagonalOfMat(T))`.
#             - Q_8:  `ClassifyOnQ8(S, DiagonalOfMat(T))`.
#   3. ASSERTS: at least one branch detected v as non-trivial.
#      A FALSE POSITIVE (every branch trivial on a non-zero v) is a
#      K-4b classifier bug.
#
# The AM04 IV.4-IV.5 + Quillen theorem guarantees the restriction
# H^3(E_+(m); U(1)) -> ⊕_{H in F} H^3(H; U(1)) is INJECTIVE for m >= 2,
# so any non-zero v MUST restrict non-trivially to some H. A failure
# here indicates the classifier integration (PR #485 + #486 + #487 +
# this PR) is mathematically unsound at some omega.
#
# PR scope notes
# --------------
# * We use the generic `ComputeModularData(H, omega_fn, val, expon)`
#   (O(|H|^4)) for the EA branch synthesis rather than the PR #487
#   closed-form `ComputeAbelianModularDataClosedForm`. The closed-form
#   header documents that it is INVALID for some non-decomposable
#   (Z/2)^k k >= 3 cocycles (e.g. Bockstein/Steenrod-type alternating
#   beta_a). At m=5 the EAs are (Z/2)^6, well inside the invalid region
#   for non-decomposable cocycles, so the closed-form would produce
#   modular data that does not match what `ComputeModularData` would
#   build — and the classifier verdict would not test what we claim.
#   |H|^4 = 4096 for (Z/2)^6 (the elements squared, then squared) which
#   is ~16M operations — feasible for a sweep.
# * The D_8 / Q_8 branches use the legacy `ComputeModularData` engine
#   directly. These are the same (S, T) values stored in
#   `modular_data/8/{3,4}/<k>.txt` and matched by `ClassifyOn{D8,Q8}`.
# * The test does NOT route through `K4aClassify(m, opts)`: the
#   `lattice_source := true` path at m=5 runs
#   `BuildKRRSpectralCharactersSparse(5)` (~minutes per call), and the
#   D_8/Q_8 branches at m>=3 use the spectral path that is independent
#   of `omega_vec`, so the orchestrator verdict at m=5 would not be
#   a per-generator test of the restriction-to-H modular data we want.
#
# Refs: PR #485 (zero-stub removal), PR #486 (ClassifyEAFromModularData),
# PR #487 (closed-form abelian (S, T), domain limits documented). User
# directive: "e2e sweep ... so that we are sure that we don't accidentally
# classify a non-trivial class as trivial."
#
# Configurable globals (set on command line via -c '...; Read(...)'):
#   K4B_E2E_M5_TEST_COUNT — number of unit vectors to test (default
#     fail-marker, meaning "full sweep" = k_G + 1 half-vector at m=5
#     = 166 calls). Set to a smaller integer for smoke/anchor runs.
#   K4B_E2E_M5_INCLUDE_HALFVEC — include the 2 * order-4-generator
#     half-vector at the end of the sweep. Default true.
#   K4B_E2E_M5_FROM_INDEX — 1-based starting index for the sweep.
#     Default 1. Useful for resumability after a crash.

# ---- Locate worktree, scripts dir, modular_data tree ------------------

_K4BE2E_SELF := INPUT_FILENAME();;
if _K4BE2E_SELF = fail or _K4BE2E_SELF = "stream" then
    Error("test_k4b_e2e_sweep_m5.g: INPUT_FILENAME() unavailable; ",
          "Read the file by its absolute path.");
fi;
if Length(_K4BE2E_SELF) > 0 and _K4BE2E_SELF[1] <> '/' then
    _K4BE2E_SELF := Filename(DirectoryCurrent(), _K4BE2E_SELF);
fi;
_K4BE2E_SELFDIR := _K4BE2E_SELF{
    [1..Length(_K4BE2E_SELF) - Length("/test_k4b_e2e_sweep_m5.g")]};;
_K4BE2E_SCRIPTSDIR := _K4BE2E_SELFDIR{
    [1..Length(_K4BE2E_SELFDIR) - Length("/tests")]};;
_K4BE2E_WT_ROOT := _K4BE2E_SCRIPTSDIR{
    [1..Length(_K4BE2E_SCRIPTSDIR) - Length("/extraspecial_orbifolds/scripts")]};;

# Many sibling .g files do relative Reads. Chdir to scripts/ first.
ChangeDirectoryCurrent(_K4BE2E_SCRIPTSDIR);

# ---- Load dependencies in the right order ------------------------------

Read(Concatenation(_K4BE2E_WT_ROOT, "/src/modular_data.g"));
Read(Concatenation(_K4BE2E_SCRIPTSDIR, "/untwisted_modular_data.g"));
Read(Concatenation(_K4BE2E_SCRIPTSDIR, "/quillen_detecting_subgroup.g"));
Read(Concatenation(_K4BE2E_SCRIPTSDIR, "/transgression_kernel.g"));
Read(Concatenation(_K4BE2E_SCRIPTSDIR, "/joint_permutation_matcher.g"));
Read(Concatenation(_K4BE2E_SCRIPTSDIR, "/d8_classifier.g"));
Read(Concatenation(_K4BE2E_SCRIPTSDIR, "/q8_classifier.g"));
Read(Concatenation(_K4BE2E_SCRIPTSDIR, "/detecting_family_restriction.g"));
Read(Concatenation(_K4BE2E_SCRIPTSDIR, "/ea_modular_data_classifier.g"));

# ---- Resolve modular_data tree for ClassifyOnD8 / ClassifyOnQ8 --------

_K4BE2E_MD_ROOT := fail;;
for _K4BE2E_CAND in
    [ Concatenation(_K4BE2E_WT_ROOT, "/../modular_data"),
      "/Users/thomasgemunden/Projects/group_cohomology/modular_data" ] do
    if _K4BE2E_MD_ROOT = fail
       and IsExistingFile(Concatenation(_K4BE2E_CAND, "/8/3/1.txt"))
       and IsExistingFile(Concatenation(_K4BE2E_CAND, "/8/4/1.txt")) then
        _K4BE2E_MD_ROOT := _K4BE2E_CAND;
    fi;
od;
if _K4BE2E_MD_ROOT = fail then
    Error("test_k4b_e2e_sweep_m5.g: cannot locate modular_data tree ",
          "containing 8/3/1.txt and 8/4/1.txt.");
fi;
Print("modular_data root: ", _K4BE2E_MD_ROOT, "\n");

_K4BE2E_LINKDIR := Concatenation(_K4BE2E_SELFDIR, "/k4b_e2e_m5");;
if not IsExistingFile(_K4BE2E_LINKDIR) then
    Exec(Concatenation("mkdir -p '", _K4BE2E_LINKDIR, "'"));
fi;
_K4BE2E_LINKPATH := Concatenation(_K4BE2E_LINKDIR, "/Modular_Data");;
if not IsExistingFile(_K4BE2E_LINKPATH) then
    Exec(Concatenation("ln -s '", _K4BE2E_MD_ROOT, "' '",
                       _K4BE2E_LINKPATH, "'"));
fi;
if not IsExistingFile(Concatenation(_K4BE2E_LINKPATH, "/8/3/1.txt")) then
    Error("test_k4b_e2e_sweep_m5.g: Modular_Data symlink at ",
          _K4BE2E_LINKPATH, " does not resolve correctly.");
fi;
ChangeDirectoryCurrent(_K4BE2E_LINKDIR);

# ---- Configurable globals ---------------------------------------------

if not IsBoundGlobal("K4B_E2E_M5_TEST_COUNT") then
    K4B_E2E_M5_TEST_COUNT := fail;  # full sweep
fi;
if not IsBoundGlobal("K4B_E2E_M5_INCLUDE_HALFVEC") then
    K4B_E2E_M5_INCLUDE_HALFVEC := true;
fi;
if not IsBoundGlobal("K4B_E2E_M5_FROM_INDEX") then
    K4B_E2E_M5_FROM_INDEX := 1;
fi;
# Optional override: which m to sweep. Default 5 (the headline target),
# but the same test code runs for m=2, m=3 — useful for smoke / anchor.
if not IsBoundGlobal("K4B_E2E_M") then
    K4B_E2E_M := 5;
fi;

# Optional: restrict to D-VAN minimum-detecting EA subset to cut wall.
# At m=5 this drops from 165 EAs to 9. Default true (faster, equivalent
# for triviality detection by AM04 + D-VAN's empirical final_ker = 1).
if not IsBoundGlobal("K4B_E2E_M5_DVAN_MIN") then
    K4B_E2E_M5_DVAN_MIN := true;
fi;

# D-VAN minimum detecting EA indices into rec_m.H_EA_list (duplicated
# from k4a_classify.g and test_detf_e2e_injectivity.g so the test
# doesn't depend on the K-4a stack at load time).
_K4BE2E_DETECTING_INDICES := rec();;
_K4BE2E_DETECTING_INDICES.("2") := [3, 2, 5];;
_K4BE2E_DETECTING_INDICES.("3") := [4, 6, 7, 11, 16, 22];;
_K4BE2E_DETECTING_INDICES.("5") := [33, 48, 54, 57, 70, 76, 88, 89, 109];;

# ---- Branch dispatch helpers -------------------------------------------
#
# Given an H in the detecting family and a restricted vec v_H on H,
# synthesises (S^v|_H, T^v|_H) and runs the appropriate K-4b classifier.
# Returns rec(skipped, detected_nontrivial, branch_label, reason,
# class_idx/match).

_K4BE2E_BranchDispatch := function(H, setup_H, v_H, branch_label)
    local omega_cocycle, val, expon, modular_ct, class_res;

    if ForAll(v_H, x -> x = 0) then
        return rec(skipped := true, detected_nontrivial := false,
                   branch_label := branch_label, reason := "v_H = 0");
    fi;

    omega_cocycle := StandardCocycleOf(setup_H, v_H);
    val := Gcd(Gcd(v_H), setup_H.exponent);
    expon := setup_H.exponent / val;
    modular_ct := ComputeModularData(H, omega_cocycle, val, expon);

    if branch_label = "D_8" then
        class_res := ClassifyOnD8(modular_ct.S, DiagonalOfMat(modular_ct.T));
        return rec(skipped := false,
                   detected_nontrivial := (class_res.class_idx <> 1),
                   branch_label := branch_label,
                   class_idx := class_res.class_idx,
                   all_matches := class_res.all_matches);
    elif branch_label = "Q_8" then
        class_res := ClassifyOnQ8(modular_ct.S, DiagonalOfMat(modular_ct.T));
        return rec(skipped := false,
                   detected_nontrivial := (class_res.class_idx <> 1),
                   branch_label := branch_label,
                   class_idx := class_res.class_idx,
                   all_matches := class_res.all_matches);
    else
        # EA branch — use PR #486's modular-data-based classifier.
        # Note: ClassifyEAFromModularData expects T as a vector or
        # DiagonalMat — it accepts both per the matcher's contract.
        class_res := ClassifyEAFromModularData(
            H, modular_ct.S, modular_ct.T);
        return rec(skipped := false,
                   detected_nontrivial := (class_res.is_trivial = false),
                   branch_label := branch_label,
                   is_trivial := class_res.is_trivial,
                   match_ok := class_res.match.ok);
    fi;
end;;

# ---- Main sweep --------------------------------------------------------

Print("\n=================================================================\n");
Print("test_k4b_e2e_sweep_m5.g (issue #488)\n");
Print("=================================================================\n");
Print("config: m=", K4B_E2E_M,
      ", test_count=", K4B_E2E_M5_TEST_COUNT,
      ", include_halfvec=", K4B_E2E_M5_INCLUDE_HALFVEC,
      ", from_index=", K4B_E2E_M5_FROM_INDEX,
      ", dvan_min=", K4B_E2E_M5_DVAN_MIN, "\n");

_K4BE2E_T_TOTAL_0 := Runtime();;

Print("\n[setup] BuildRestrictionMatrices(", K4B_E2E_M, ", \"hap\") ...\n");
_K4BE2E_TBUILD := Runtime();
_K4BE2E_REC_M := BuildRestrictionMatrices(K4B_E2E_M, "hap");
Print("[setup] done in ", (Runtime() - _K4BE2E_TBUILD) / 1000., " s\n");

_K4BE2E_SETUP_G := _K4BE2E_REC_M.setup_G;;
_K4BE2E_K_G := _K4BE2E_SETUP_G.num_generators;;
Print("[setup] |G| = ", Order(_K4BE2E_REC_M.G),
      ", k_G = ", _K4BE2E_K_G,
      ", torsion = ", _K4BE2E_SETUP_G.torsion, "\n");
Print("[setup] H_EA_list len = ", Length(_K4BE2E_REC_M.H_EA_list),
      ", Q_8 present = ", _K4BE2E_REC_M.H_Q8 <> fail, "\n");

# Resolve EA subset.
_K4BE2E_M_KEY := String(K4B_E2E_M);;
if K4B_E2E_M5_DVAN_MIN = true
   and IsBound(_K4BE2E_DETECTING_INDICES.(_K4BE2E_M_KEY)) then
    _K4BE2E_EA_INDICES := _K4BE2E_DETECTING_INDICES.(_K4BE2E_M_KEY);
    Print("[setup] using D-VAN min EA subset: ", _K4BE2E_EA_INDICES, "\n");
else
    _K4BE2E_EA_INDICES := [1..Length(_K4BE2E_REC_M.H_EA_list)];
    Print("[setup] using FULL EA family: ", Length(_K4BE2E_EA_INDICES),
          " EAs\n");
fi;

# Precompute per-EA setup_H + labels + torsions + res rows.
_K4BE2E_EA_SUBSET   := List(_K4BE2E_EA_INDICES,
                             j -> _K4BE2E_REC_M.H_EA_list[j]);;
_K4BE2E_EA_SETUPS   := List(_K4BE2E_EA_SUBSET,
                             h -> SetupCohomology3(h));;
_K4BE2E_EA_LABELS   := List(_K4BE2E_EA_INDICES,
                             j -> Concatenation("EA_", String(j)));;
_K4BE2E_EA_TORSIONS := List(_K4BE2E_EA_INDICES,
                             j -> _K4BE2E_REC_M.torsion_EA_list[j]);;
_K4BE2E_EA_RES_T    := List(_K4BE2E_EA_INDICES,
                             j -> _K4BE2E_REC_M.res_EA_list[j]);;
_K4BE2E_SETUP_D8    := SetupCohomology3(_K4BE2E_REC_M.H_D8);;
if _K4BE2E_REC_M.H_Q8 <> fail then
    _K4BE2E_SETUP_Q8 := SetupCohomology3(_K4BE2E_REC_M.H_Q8);
fi;

# Determine final test count.
if K4B_E2E_M5_TEST_COUNT = fail then
    _K4BE2E_TEST_COUNT := _K4BE2E_K_G;
else
    _K4BE2E_TEST_COUNT := Minimum(K4B_E2E_M5_TEST_COUNT, _K4BE2E_K_G);
fi;
Print("[setup] sweeping ", _K4BE2E_TEST_COUNT, " unit vectors",
      " from index ", K4B_E2E_M5_FROM_INDEX, "\n");

# Forward-declare loop locals to suppress syntax warnings.
_K4BE2E_FAILURES := [];;
_K4BE2E_PASSES   := 0;;
_K4BE2E_ROW := fail;;
_K4BE2E_VH := fail;;
_K4BE2E_BR := fail;;
_K4BE2E_BRANCHES_DETECTED := [];;
_K4BE2E_BRANCHES_SKIPPED  := [];;
_K4BE2E_BRANCH_DETS       := [];;
_K4BE2E_JJ := 0;;
_K4BE2E_I  := 0;;
_K4BE2E_TI := 0;;
_K4BE2E_WI := 0.;;
_K4BE2E_F  := fail;;
_K4BE2E_LBL := fail;;
_K4BE2E_FROM := 1;;

# ---- omega = 0 anchor: every branch should report trivial -----------
Print("\n--- omega = 0 anchor ---\n");
_K4BE2E_T_ANCHOR := Runtime();
_K4BE2E_ANCHOR_FAIL := false;;
for _K4BE2E_JJ in [1..Length(_K4BE2E_EA_SUBSET)] do
    _K4BE2E_VH := ListWithIdenticalEntries(
        Length(_K4BE2E_EA_TORSIONS[_K4BE2E_JJ]), 0);
    _K4BE2E_BR := _K4BE2E_BranchDispatch(
        _K4BE2E_EA_SUBSET[_K4BE2E_JJ],
        _K4BE2E_EA_SETUPS[_K4BE2E_JJ],
        _K4BE2E_VH,
        _K4BE2E_EA_LABELS[_K4BE2E_JJ]);
    if _K4BE2E_BR.detected_nontrivial then
        _K4BE2E_ANCHOR_FAIL := true;
        Print("  FAIL: anchor branch ", _K4BE2E_BR.branch_label,
              " reported non-trivial (should be trivial)\n");
    fi;
od;
_K4BE2E_VH := ListWithIdenticalEntries(
    Length(_K4BE2E_REC_M.torsion_D8), 0);
_K4BE2E_BR := _K4BE2E_BranchDispatch(
    _K4BE2E_REC_M.H_D8, _K4BE2E_SETUP_D8, _K4BE2E_VH, "D_8");
if _K4BE2E_BR.detected_nontrivial then
    _K4BE2E_ANCHOR_FAIL := true;
    Print("  FAIL: anchor branch D_8 reported non-trivial\n");
fi;
if _K4BE2E_REC_M.H_Q8 <> fail then
    _K4BE2E_VH := ListWithIdenticalEntries(
        Length(_K4BE2E_REC_M.torsion_Q8), 0);
    _K4BE2E_BR := _K4BE2E_BranchDispatch(
        _K4BE2E_REC_M.H_Q8, _K4BE2E_SETUP_Q8, _K4BE2E_VH, "Q_8");
    if _K4BE2E_BR.detected_nontrivial then
        _K4BE2E_ANCHOR_FAIL := true;
        Print("  FAIL: anchor branch Q_8 reported non-trivial\n");
    fi;
fi;
_K4BE2E_WALL_ANCHOR := (Runtime() - _K4BE2E_T_ANCHOR) / 1000.;
if _K4BE2E_ANCHOR_FAIL then
    Print("  FAIL: omega=0 anchor failed (wall ",
          _K4BE2E_WALL_ANCHOR, " s)\n");
else
    Print("  PASS: omega=0 -> every branch trivial (wall ",
          _K4BE2E_WALL_ANCHOR, " s)\n");
fi;

# ---- Sweep over basis unit vectors -----------------------------------
_K4BE2E_FROM := Maximum(1, K4B_E2E_M5_FROM_INDEX);;
for _K4BE2E_I in [_K4BE2E_FROM .. _K4BE2E_TEST_COUNT] do
    _K4BE2E_TI := Runtime();
    _K4BE2E_BRANCHES_DETECTED := [];
    _K4BE2E_BRANCHES_SKIPPED  := [];
    _K4BE2E_BRANCH_DETS       := [];

    for _K4BE2E_JJ in [1..Length(_K4BE2E_EA_SUBSET)] do
        # For omega_vec = e_i (unit vector), omega_vec * res_K = row i of res_K.
        _K4BE2E_ROW := _K4BE2E_EA_RES_T[_K4BE2E_JJ][_K4BE2E_I];
        _K4BE2E_VH := List([1..Length(_K4BE2E_ROW)],
            k -> _K4BE2E_ROW[k] mod _K4BE2E_EA_TORSIONS[_K4BE2E_JJ][k]);
        _K4BE2E_BR := _K4BE2E_BranchDispatch(
            _K4BE2E_EA_SUBSET[_K4BE2E_JJ],
            _K4BE2E_EA_SETUPS[_K4BE2E_JJ],
            _K4BE2E_VH,
            _K4BE2E_EA_LABELS[_K4BE2E_JJ]);
        Add(_K4BE2E_BRANCH_DETS, _K4BE2E_BR);
        if _K4BE2E_BR.skipped then
            Add(_K4BE2E_BRANCHES_SKIPPED, _K4BE2E_BR.branch_label);
        elif _K4BE2E_BR.detected_nontrivial then
            Add(_K4BE2E_BRANCHES_DETECTED, _K4BE2E_BR.branch_label);
        fi;
    od;

    _K4BE2E_ROW := _K4BE2E_REC_M.res_D8[_K4BE2E_I];
    _K4BE2E_VH := List([1..Length(_K4BE2E_ROW)],
        k -> _K4BE2E_ROW[k] mod _K4BE2E_REC_M.torsion_D8[k]);
    _K4BE2E_BR := _K4BE2E_BranchDispatch(
        _K4BE2E_REC_M.H_D8, _K4BE2E_SETUP_D8, _K4BE2E_VH, "D_8");
    Add(_K4BE2E_BRANCH_DETS, _K4BE2E_BR);
    if _K4BE2E_BR.skipped then
        Add(_K4BE2E_BRANCHES_SKIPPED, _K4BE2E_BR.branch_label);
    elif _K4BE2E_BR.detected_nontrivial then
        Add(_K4BE2E_BRANCHES_DETECTED, _K4BE2E_BR.branch_label);
    fi;

    if _K4BE2E_REC_M.H_Q8 <> fail then
        _K4BE2E_ROW := _K4BE2E_REC_M.res_Q8[_K4BE2E_I];
        _K4BE2E_VH := List([1..Length(_K4BE2E_ROW)],
            k -> _K4BE2E_ROW[k] mod _K4BE2E_REC_M.torsion_Q8[k]);
        _K4BE2E_BR := _K4BE2E_BranchDispatch(
            _K4BE2E_REC_M.H_Q8, _K4BE2E_SETUP_Q8, _K4BE2E_VH, "Q_8");
        Add(_K4BE2E_BRANCH_DETS, _K4BE2E_BR);
        if _K4BE2E_BR.skipped then
            Add(_K4BE2E_BRANCHES_SKIPPED, _K4BE2E_BR.branch_label);
        elif _K4BE2E_BR.detected_nontrivial then
            Add(_K4BE2E_BRANCHES_DETECTED, _K4BE2E_BR.branch_label);
        fi;
    fi;

    _K4BE2E_WI := (Runtime() - _K4BE2E_TI) / 1000.;
    if Length(_K4BE2E_BRANCHES_DETECTED) > 0 then
        _K4BE2E_PASSES := _K4BE2E_PASSES + 1;
        Print("  PASS: e_", _K4BE2E_I, "/", _K4BE2E_TEST_COUNT,
              " -> detected by ", _K4BE2E_BRANCHES_DETECTED,
              " (skipped ", _K4BE2E_BRANCHES_SKIPPED,
              ", wall ", _K4BE2E_WI, " s)\n");
    else
        Add(_K4BE2E_FAILURES, rec(
            idx        := _K4BE2E_I,
            wall       := _K4BE2E_WI,
            skipped    := _K4BE2E_BRANCHES_SKIPPED,
            branch_dets := _K4BE2E_BRANCH_DETS));
        Print("  FAIL: e_", _K4BE2E_I, "/", _K4BE2E_TEST_COUNT,
              " -> ALL branches trivial (skipped ",
              _K4BE2E_BRANCHES_SKIPPED, ", wall ", _K4BE2E_WI, " s)\n");
        Print("       FALSE POSITIVE: non-zero v classified trivial.\n");
        for _K4BE2E_LBL in _K4BE2E_BRANCH_DETS do
            Print("       ", _K4BE2E_LBL.branch_label, ": ");
            if _K4BE2E_LBL.skipped then
                Print("skipped (", _K4BE2E_LBL.reason, ")\n");
            elif IsBound(_K4BE2E_LBL.class_idx) then
                Print("class_idx=", _K4BE2E_LBL.class_idx, "\n");
            else
                Print("is_trivial=", _K4BE2E_LBL.is_trivial, "\n");
            fi;
        od;
    fi;
od;

# ---- Half-vector for the order-4 generator (if any) -------------------
_K4BE2E_DID_HALFVEC := false;
if K4B_E2E_M5_INCLUDE_HALFVEC = true then
    _K4BE2E_ORDER4_IDX := Position(_K4BE2E_SETUP_G.torsion, 4);
    if _K4BE2E_ORDER4_IDX <> fail then
        _K4BE2E_DID_HALFVEC := true;
        Print("\n--- half-vector (2 * order-4 generator at idx ",
              _K4BE2E_ORDER4_IDX, ") ---\n");
        _K4BE2E_TI := Runtime();
        _K4BE2E_BRANCHES_DETECTED := [];
        _K4BE2E_BRANCHES_SKIPPED  := [];
        _K4BE2E_BRANCH_DETS       := [];

        # For omega_vec = 2 * e_idx, omega_vec * res_K = 2 * row idx of res_K.
        for _K4BE2E_JJ in [1..Length(_K4BE2E_EA_SUBSET)] do
            _K4BE2E_ROW := _K4BE2E_EA_RES_T[_K4BE2E_JJ][_K4BE2E_ORDER4_IDX];
            _K4BE2E_VH := List([1..Length(_K4BE2E_ROW)],
                k -> (2 * _K4BE2E_ROW[k]) mod _K4BE2E_EA_TORSIONS[_K4BE2E_JJ][k]);
            _K4BE2E_BR := _K4BE2E_BranchDispatch(
                _K4BE2E_EA_SUBSET[_K4BE2E_JJ],
                _K4BE2E_EA_SETUPS[_K4BE2E_JJ],
                _K4BE2E_VH,
                _K4BE2E_EA_LABELS[_K4BE2E_JJ]);
            Add(_K4BE2E_BRANCH_DETS, _K4BE2E_BR);
            if _K4BE2E_BR.skipped then
                Add(_K4BE2E_BRANCHES_SKIPPED, _K4BE2E_BR.branch_label);
            elif _K4BE2E_BR.detected_nontrivial then
                Add(_K4BE2E_BRANCHES_DETECTED, _K4BE2E_BR.branch_label);
            fi;
        od;
        _K4BE2E_ROW := _K4BE2E_REC_M.res_D8[_K4BE2E_ORDER4_IDX];
        _K4BE2E_VH := List([1..Length(_K4BE2E_ROW)],
            k -> (2 * _K4BE2E_ROW[k]) mod _K4BE2E_REC_M.torsion_D8[k]);
        _K4BE2E_BR := _K4BE2E_BranchDispatch(
            _K4BE2E_REC_M.H_D8, _K4BE2E_SETUP_D8, _K4BE2E_VH, "D_8");
        Add(_K4BE2E_BRANCH_DETS, _K4BE2E_BR);
        if _K4BE2E_BR.skipped then
            Add(_K4BE2E_BRANCHES_SKIPPED, _K4BE2E_BR.branch_label);
        elif _K4BE2E_BR.detected_nontrivial then
            Add(_K4BE2E_BRANCHES_DETECTED, _K4BE2E_BR.branch_label);
        fi;
        if _K4BE2E_REC_M.H_Q8 <> fail then
            _K4BE2E_ROW := _K4BE2E_REC_M.res_Q8[_K4BE2E_ORDER4_IDX];
            _K4BE2E_VH := List([1..Length(_K4BE2E_ROW)],
                k -> (2 * _K4BE2E_ROW[k]) mod _K4BE2E_REC_M.torsion_Q8[k]);
            _K4BE2E_BR := _K4BE2E_BranchDispatch(
                _K4BE2E_REC_M.H_Q8, _K4BE2E_SETUP_Q8, _K4BE2E_VH, "Q_8");
            Add(_K4BE2E_BRANCH_DETS, _K4BE2E_BR);
            if _K4BE2E_BR.skipped then
                Add(_K4BE2E_BRANCHES_SKIPPED, _K4BE2E_BR.branch_label);
            elif _K4BE2E_BR.detected_nontrivial then
                Add(_K4BE2E_BRANCHES_DETECTED, _K4BE2E_BR.branch_label);
            fi;
        fi;
        _K4BE2E_WI := (Runtime() - _K4BE2E_TI) / 1000.;
        if Length(_K4BE2E_BRANCHES_DETECTED) > 0 then
            _K4BE2E_PASSES := _K4BE2E_PASSES + 1;
            Print("  PASS: half-vec -> detected by ", _K4BE2E_BRANCHES_DETECTED,
                  " (skipped ", _K4BE2E_BRANCHES_SKIPPED,
                  ", wall ", _K4BE2E_WI, " s)\n");
        else
            Add(_K4BE2E_FAILURES, rec(
                idx        := "half-vec",
                wall       := _K4BE2E_WI,
                skipped    := _K4BE2E_BRANCHES_SKIPPED,
                branch_dets := _K4BE2E_BRANCH_DETS));
            Print("  FAIL: half-vec -> ALL branches trivial (skipped ",
                  _K4BE2E_BRANCHES_SKIPPED, ", wall ", _K4BE2E_WI, " s)\n");
        fi;
    fi;
fi;

# ---- Summary ----------------------------------------------------------
_K4BE2E_WALL_TOTAL := (Runtime() - _K4BE2E_T_TOTAL_0) / 1000.;;
_K4BE2E_TOTAL_RUN := (_K4BE2E_TEST_COUNT - _K4BE2E_FROM + 1);;
if _K4BE2E_DID_HALFVEC then
    _K4BE2E_TOTAL_RUN := _K4BE2E_TOTAL_RUN + 1;
fi;

Print("\n=================================================================\n");
Print("SUMMARY: m=", K4B_E2E_M, "\n");
Print("=================================================================\n");
Print("Total wall: ", _K4BE2E_WALL_TOTAL, " s\n");
Print("Anchor (omega=0): ",
      If_(_K4BE2E_ANCHOR_FAIL, "FAIL", "PASS"), "\n");
Print("Unit-vec sweep: ", _K4BE2E_PASSES, "/", _K4BE2E_TOTAL_RUN,
      " correctly detected non-trivial\n");
Print("False positives: ", Length(_K4BE2E_FAILURES), "\n");

if Length(_K4BE2E_FAILURES) > 0 then
    Print("\nFALSE-POSITIVE classifier verdicts on:\n");
    for _K4BE2E_F in _K4BE2E_FAILURES do
        Print("  idx ", _K4BE2E_F.idx,
              " (skipped ", _K4BE2E_F.skipped,
              ", wall ", _K4BE2E_F.wall, " s)\n");
    od;
fi;

if Length(_K4BE2E_FAILURES) = 0 and not _K4BE2E_ANCHOR_FAIL then
    Print("\n[GREEN] test_k4b_e2e_sweep_m5 (m=", K4B_E2E_M, ")\n");
    QuitGap(0);
else
    Print("\n[RED] test_k4b_e2e_sweep_m5 (m=", K4B_E2E_M, ")\n");
    QuitGap(1);
fi;
