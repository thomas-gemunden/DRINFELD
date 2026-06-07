# test_k4b_e2e_sweep_m7.g
#
# Issue #489: e2e classifier-correctness sweep at m=7 (production scale).
#
# For each non-zero basis vector v of H^3(E_+(7); U(1)) (454 order-2
# generators + 1 order-4 generator + 1 "half-vector" 2 * order-4_gen
# = 456 vectors), this test:
#
#   1. Restricts v to each H in the AM04+Quillen detecting family
#      F = {max EAs, D_8, Q_8} via per-EA RestrictionMatrixViaHAP and
#      the D_8 / Q_8 restriction matrices (built once upfront).
#   2. For each H in F:
#        a. If v|_H = 0 in H^3(H; U(1)), this branch cannot detect v
#           and we mark it skipped (other branches must pick it up).
#        b. Otherwise:
#             EA H = (Z/2)^8: use the q_omega + b_omega cocycle-eval
#                path `ClassifyAbelianBranchFast(H, omega_cocycle,
#                expon)` (PR #437). The S-matrix synthesis is
#                infeasible at |H|^4 = 4.3e9 entries.
#             D_8 / Q_8: synthesise (S, T) via the generic
#                `ComputeModularData(H, omega_cocycle, val, expon)`
#                (sub-second at |H| = 8) and classify via
#                ClassifyOnD8 / ClassifyOnQ_8.
#   3. ASSERTS: at least one branch detected v as non-trivial.
#
# Mathematical basis. By AM04 IV.4-IV.5 + Quillen the restriction
#     H^3(E_+(m); U(1)) -> (+)_{H in F} H^3(H; U(1))
# is INJECTIVE for m >= 2, so any non-zero v MUST restrict non-trivially
# to some H. A false positive (every branch trivial on a non-zero v) is
# a K-4b classifier bug.
#
# Why `ClassifyAbelianBranchFast` is the right choice on EA at m=7
# ----------------------------------------------------------------
# `ComputeAbelianModularDataClosedForm` (PR #487) materialises the full
# |H|^2 x |H|^2 S-matrix; at H = (Z/2)^8 that is 65536 x 65536 cyclotomic
# entries = 4.3e9 cells, which is INFEASIBLE in memory. The factored
# variant `ComputeAbelianModularDataFactored` is O(|H|^2) memory but
# would need a different classifier (no full S matrix to feed
# `JointPermutationMatcher`).
#
# `ClassifyAbelianBranchFast` (`abelian_branch_fast.g`, PR #437) checks
# the cocycle-level predicate:
#
#     q_omega(a)    := omega(a, a, a) mod N                (quadratic)
#     b_omega(a, b) := q_omega(a*b) - q_omega(a) - q_omega(b) (polarisation)
#     is_coboundary <=> q_omega ≡ 0  AND  b_omega ≡ 0  (mod N)
#
# For ABELIAN H this is mathematically equivalent to triviality of [ω]
# in H^3(H; U(1)) (Naidu-Nikshych / DGNO: H^3(H abelian; U(1)) ≅
# {quadratic forms H -> Q/Z}). It runs in O(|H|^2) cocycle calls —
# 65536 calls at H = (Z/2)^8 — and consumes O(|H|^2) memory.
#
# Same path used by the K-4a production classifier
# (`k4a_classify.g::_K4A_ClassifyEBranchMulti` when
# `_K4A_USE_FAST_ABELIAN_BRANCH = true`) at m=7.
#
# m=7 architecture
# ----------------
# `BuildRestrictionMatrices(7, "hap")` OOMs (it enumerates ~9.8M
# Lagrangians eagerly per detecting_family_restriction.g:1184). We
# bypass that and use only the 8 EAs from D-VAN's persisted
# `ea_generators_exp` (PR #442 / `computed/dvan_min_family/m7/result.g`)
# plus D_8 and Q_8 sections, with per-EA `RestrictionMatrixViaHAP` calls.
#
# Group instance: `_DETF_BuildSetupG_LHS(7).group` is a fresh
# `ExtraspecialGroup(2^15, "+")` instance (via LHSResolutionEPlus's
# internal call). `LoadDVANEAFamily(7)` reconstructs EAs against ANOTHER
# fresh `ExtraspecialGroup` instance (PR #449 perf bypass), which is in
# a DIFFERENT GAP family. `SubgroupInclusion(H, G)` requires gens of H
# to be elements of G — across family instances this fails.
#
# Fix here: we read `result.g` ourselves and reconstruct EAs against
# `setup_G.group` via `PcElementByExponentsNC(FamilyPcgs(setup_G.group),
# exp_tuple)`. Since both groups are `ExtraspecialGroup(2^15, "+")` they
# share the same pc-presentation, so exponent-vector reconstruction is
# instance-portable.
#
# Configurable globals (set on command line via -c '...; Read(...)'):
#   K4B_E2E_M7_TEST_COUNT — number of unit vectors to test. Default
#     fail = "full sweep" = k_G unit vectors + 1 half-vector = 456.
#     Set to a smaller integer for smoke / anchor runs.
#   K4B_E2E_M7_INCLUDE_HALFVEC — include the 2 * order-4-generator
#     half-vector at the end of the sweep. Default true.
#   K4B_E2E_M7_FROM_INDEX — 1-based starting index for the sweep.
#     Default 1. Useful for resumability after a crash.
#
# Refs: PR #488 (m=5 analogue), PR #485 (zero-stub removal),
# PR #486 (ClassifyEAFromModularData), PR #487 (closed-form abelian
# (S, T), domain limits documented). User directive 2026-06-07:
# "e2e sweep over the full set of generators plus the half-vector".

# ---- Locate worktree, scripts dir, modular_data tree ------------------

_K4B7_SELF := INPUT_FILENAME();;
if _K4B7_SELF = fail or _K4B7_SELF = "stream" then
    Error("test_k4b_e2e_sweep_m7.g: INPUT_FILENAME() unavailable; ",
          "Read the file by its absolute path.");
fi;
if Length(_K4B7_SELF) > 0 and _K4B7_SELF[1] <> '/' then
    _K4B7_SELF := Filename(DirectoryCurrent(), _K4B7_SELF);
fi;
_K4B7_SELFDIR := _K4B7_SELF{
    [1..Length(_K4B7_SELF) - Length("/test_k4b_e2e_sweep_m7.g")]};;
_K4B7_SCRIPTSDIR := _K4B7_SELFDIR{
    [1..Length(_K4B7_SELFDIR) - Length("/tests")]};;
_K4B7_WT_ROOT := _K4B7_SCRIPTSDIR{
    [1..Length(_K4B7_SCRIPTSDIR) - Length("/extraspecial_orbifolds/scripts")]};;

# Many sibling .g files do relative Reads. Chdir to scripts/ so they
# resolve. CLAUDE.md "CWD-sensitive relative Read calls" caveat.
ChangeDirectoryCurrent(_K4B7_SCRIPTSDIR);

# ---- Load dependencies in the right order ------------------------------
#
# Order matters:
#   src/modular_data.g       — LoadModularData + ComputeModularData.
#   load_compiled.g          — gac-compiled hot-path modules where
#                              available (PR #440); falls back to .g
#                              when .so missing. Major speed-up for
#                              the per-EA closed-form (S, T) build.
#   quillen_detecting_subgroup.g — for SubgroupCohomologyContext +
#                              SubgroupInclusion + EPlusGroup +
#                              MaximalElementaryAbelian_E_plus.
#   transgression_kernel.g    — SetupCohomology3, StandardCocycleOf.
#   joint_permutation_matcher.g, untwisted_modular_data.g,
#   d8_classifier.g, q8_classifier.g,
#   ea_modular_data_classifier.g (PR #486),
#   abelian_modular_data_closed_form.g (PR #487).
#   detecting_family_restriction.g — BuildRestrictionMatrices for m<=5
#                              (we don't call it at m=7) plus
#                              RestrictionMatrixViaHAP +
#                              _DETF_BuildSetupG_LHS + _DETF_FindD8In +
#                              _DETF_FindQ8In, which we DO call at m=7.
#   k4a_classify.g           — LoadDVANEAFamily (m=7 EA generator
#                              persistence loader, PR #377/#442).

Read(Concatenation(_K4B7_WT_ROOT, "/src/modular_data.g"));

# load_compiled.g (PR #440) opt-in: gac-compiled .so siblings deliver
# 2-5x speedup on the per-EA closed-form (S, T) build. Engage via
# `K4B_E2E_M7_USE_COMPILED := true` BEFORE Reading this test. Default
# OFF — in some worktrees the .so files were compiled with absolute
# paths from a different worktree and re-reading their relative-path
# fallbacks in cross-worktree compiled-cache setups can fail. The
# interpreted-.g path always works.
if IsBoundGlobal("K4B_E2E_M7_USE_COMPILED")
   and ValueGlobal("K4B_E2E_M7_USE_COMPILED") = true then
    Read(Concatenation(_K4B7_SCRIPTSDIR, "/load_compiled.g"));
fi;

Read(Concatenation(_K4B7_SCRIPTSDIR, "/abelian_branch_fast.g"));
Read(Concatenation(_K4B7_SCRIPTSDIR, "/untwisted_modular_data.g"));
Read(Concatenation(_K4B7_SCRIPTSDIR, "/quillen_detecting_subgroup.g"));
Read(Concatenation(_K4B7_SCRIPTSDIR, "/transgression_kernel.g"));
Read(Concatenation(_K4B7_SCRIPTSDIR, "/joint_permutation_matcher.g"));
Read(Concatenation(_K4B7_SCRIPTSDIR, "/d8_classifier.g"));
Read(Concatenation(_K4B7_SCRIPTSDIR, "/q8_classifier.g"));
Read(Concatenation(_K4B7_SCRIPTSDIR, "/detecting_family_restriction.g"));
# k4a_classify.g brings in LoadDVANEAFamily; we don't need it directly
# (we read the persisted result.g ourselves to get exp vectors), but
# loading it is harmless. Omitted to keep the load chain shorter.

# ---- Resolve modular_data tree for ClassifyOnD8 / ClassifyOnQ_8 -------

_K4B7_MD_ROOT := fail;;
for _K4B7_CAND in
    [ Concatenation(_K4B7_WT_ROOT, "/../modular_data"),
      "/Users/thomasgemunden/Projects/group_cohomology/modular_data" ] do
    if _K4B7_MD_ROOT = fail
       and IsExistingFile(Concatenation(_K4B7_CAND, "/8/3/1.txt"))
       and IsExistingFile(Concatenation(_K4B7_CAND, "/8/4/1.txt")) then
        _K4B7_MD_ROOT := _K4B7_CAND;
    fi;
od;
if _K4B7_MD_ROOT = fail then
    Error("test_k4b_e2e_sweep_m7.g: cannot locate modular_data tree ",
          "containing 8/3/1.txt and 8/4/1.txt.");
fi;
Print("modular_data root: ", _K4B7_MD_ROOT, "\n");

_K4B7_LINKDIR := Concatenation(_K4B7_SELFDIR, "/k4b_e2e_m7");;
if not IsExistingFile(_K4B7_LINKDIR) then
    Exec(Concatenation("mkdir -p '", _K4B7_LINKDIR, "'"));
fi;
_K4B7_LINKPATH := Concatenation(_K4B7_LINKDIR, "/Modular_Data");;
if not IsExistingFile(_K4B7_LINKPATH) then
    Exec(Concatenation("ln -s '", _K4B7_MD_ROOT, "' '",
                       _K4B7_LINKPATH, "'"));
fi;
if not IsExistingFile(Concatenation(_K4B7_LINKPATH, "/8/3/1.txt")) then
    Error("test_k4b_e2e_sweep_m7.g: Modular_Data symlink at ",
          _K4B7_LINKPATH, " does not resolve correctly.");
fi;
ChangeDirectoryCurrent(_K4B7_LINKDIR);

# ---- Configurable globals ---------------------------------------------

if not IsBoundGlobal("K4B_E2E_M7_TEST_COUNT") then
    K4B_E2E_M7_TEST_COUNT := fail;  # full sweep
fi;
if not IsBoundGlobal("K4B_E2E_M7_INCLUDE_HALFVEC") then
    K4B_E2E_M7_INCLUDE_HALFVEC := true;
fi;
if not IsBoundGlobal("K4B_E2E_M7_FROM_INDEX") then
    K4B_E2E_M7_FROM_INDEX := 1;
fi;

# ---- Build m=7 setup: setup_G + EA list + D_8 / Q_8 + restrictions ----
#
# Mirrors `_DETFE2E_BuildM7Setup` in test_detf_e2e_injectivity.g. We
# cannot use BuildRestrictionMatrices(7, "hap") because it OOMs on the
# eager 9.8M-Lagrangian enumeration.

_K4B7_BuildSetup := function()
    local setup_G, G, fam_pcgs, dvan_result, ea_generators_exp,
          H_EA_list, gen_tuples, exp_tuple, i,
          H_D8, H_Q8, ctx_EA_list, res_EA_list, torsion_EA_list,
          ctx_D8, res_D8, ctx_Q8, res_Q8, result_path;
    setup_G := _DETF_BuildSetupG_LHS(7);
    G := setup_G.group;
    # Reconstruct EAs from D-VAN's persisted exponent vectors INSIDE
    # setup_G.group. LoadDVANEAFamily(7) reconstructs against a FRESH
    # `ExtraspecialGroup(2^15, "+")` (PR #449's perf bypass), and those
    # are in a different GAP family from setup_G.group, so
    # `SubgroupInclusion(H, G)` fails on H from LoadDVANEAFamily. Read
    # the same persisted result.g locally and pcgs-reconstruct against G.
    result_path := Concatenation(
        _K4B7_WT_ROOT,
        "/extraspecial_orbifolds/computed/dvan_min_family/m7/result.g");
    if not IsExistingFile(result_path) then
        Error("_K4B7_BuildSetup: cannot find ", result_path);
    fi;
    Read(result_path);
    if IsBoundGlobal("dvan_m7_result") then
        dvan_result := ValueGlobal("dvan_m7_result");
    elif IsBoundGlobal("dvan_result") then
        dvan_result := ValueGlobal("dvan_result");
    else
        Error("_K4B7_BuildSetup: result.g did not bind dvan_m7_result ",
              "or dvan_result.");
    fi;
    if not IsBound(dvan_result.ea_generators_exp) then
        Error("_K4B7_BuildSetup: dvan_result lacks ea_generators_exp ",
              "(legacy ea_generators field is incompatible with cross-",
              "instance reconstruction; see PR #449 commentary).");
    fi;
    ea_generators_exp := dvan_result.ea_generators_exp;
    fam_pcgs := FamilyPcgs(G);
    H_EA_list := [];
    for exp_tuple in ea_generators_exp do
        gen_tuples := List(exp_tuple,
            exps -> PcElementByExponentsNC(fam_pcgs, exps));
        Add(H_EA_list, Subgroup(G, gen_tuples));
    od;
    H_D8 := _DETF_FindD8In(G, 7);
    H_Q8 := _DETF_FindQ8In(G, 7);
    ctx_EA_list := [];
    res_EA_list := [];
    for i in [1..Length(H_EA_list)] do
        Add(ctx_EA_list, SubgroupCohomologyContext(H_EA_list[i]));
        Add(res_EA_list, RestrictionMatrixViaHAP(
            setup_G, ctx_EA_list[i],
            SubgroupInclusion(H_EA_list[i], G)));
    od;
    ctx_D8 := SubgroupCohomologyContext(H_D8);
    res_D8 := RestrictionMatrixViaHAP(setup_G, ctx_D8,
                                       SubgroupInclusion(H_D8, G));
    if H_Q8 <> fail then
        ctx_Q8 := SubgroupCohomologyContext(H_Q8);
        res_Q8 := RestrictionMatrixViaHAP(setup_G, ctx_Q8,
                                           SubgroupInclusion(H_Q8, G));
    else
        ctx_Q8 := fail;
        res_Q8 := fail;
    fi;
    torsion_EA_list := List(ctx_EA_list, c -> c.torsion);
    return rec(
        m := 7,
        G := G,
        setup_G := setup_G,
        H_EA_list := H_EA_list,
        ctx_EA_list := ctx_EA_list,
        res_EA_list := res_EA_list,
        torsion_EA_list := torsion_EA_list,
        H_D8 := H_D8,
        ctx_D8 := ctx_D8,
        res_D8 := res_D8,
        torsion_D8 := ctx_D8.torsion,
        H_Q8 := H_Q8,
        ctx_Q8 := ctx_Q8,
        res_Q8 := res_Q8,
        torsion_Q8 := If_(ctx_Q8 = fail, fail, ctx_Q8.torsion)
    );
end;;

# `If_` may not be loaded — define a local fallback.
if not IsBoundGlobal("If_") then
    If_ := function(cond, a, b)
        if cond then return a; else return b; fi;
    end;;
fi;

# ---- Branch dispatch helpers -------------------------------------------
#
# Given an H in the detecting family and a restricted vec v_H on H,
# synthesise (S^v|_H, T^v|_H) and run the appropriate K-4b classifier.
# Returns rec(skipped, detected_nontrivial, branch_label, reason,
# class_idx/match).

_K4B7_BranchDispatch := function(H, setup_H, v_H, branch_label)
    local omega_cocycle, val, expon, modular_ct, class_res;

    if ForAll(v_H, x -> x = 0) then
        return rec(skipped := true, detected_nontrivial := false,
                   branch_label := branch_label, reason := "v_H = 0");
    fi;

    omega_cocycle := StandardCocycleOf(setup_H, v_H);
    val := Gcd(Gcd(v_H), setup_H.exponent);
    expon := setup_H.exponent / val;

    if branch_label = "D_8" then
        # |H| = 8, ComputeModularData is sub-second.
        modular_ct := ComputeModularData(H, omega_cocycle, val, expon);
        class_res := ClassifyOnD8(modular_ct.S,
                                   DiagonalOfMat(modular_ct.T));
        return rec(skipped := false,
                   detected_nontrivial := (class_res.class_idx <> 1),
                   branch_label := branch_label,
                   class_idx := class_res.class_idx,
                   all_matches := class_res.all_matches);
    elif branch_label = "Q_8" then
        modular_ct := ComputeModularData(H, omega_cocycle, val, expon);
        class_res := ClassifyOnQ8(modular_ct.S,
                                   DiagonalOfMat(modular_ct.T));
        return rec(skipped := false,
                   detected_nontrivial := (class_res.class_idx <> 1),
                   branch_label := branch_label,
                   class_idx := class_res.class_idx,
                   all_matches := class_res.all_matches);
    else
        # EA branch. |H_EA| = 256 = 2^8 at m=7. The closed-form
        # ComputeAbelianModularDataClosedForm materialises a 65536 x
        # 65536 cyclotomic S matrix (4.3e9 entries — infeasible). Use
        # the cocycle-level q_omega + b_omega path ClassifyAbelianBranchFast
        # (PR #437): O(|H|^2) cocycle calls = 65536 at |H| = 256.
        # Mathematically equivalent for triviality detection by
        # H^3(H abelian; U(1)) ≅ {quadratic forms H -> Q/Z}.
        class_res := ClassifyAbelianBranchFast(H, omega_cocycle, expon);
        return rec(skipped := false,
                   detected_nontrivial := (class_res.is_coboundary = false),
                   branch_label := branch_label,
                   is_q_trivial := class_res.is_q_trivial,
                   is_b_trivial := class_res.is_b_trivial);
    fi;
end;;

# ---- Main sweep --------------------------------------------------------

Print("\n=================================================================\n");
Print("test_k4b_e2e_sweep_m7.g (issue #489)\n");
Print("=================================================================\n");
Print("config: test_count=", K4B_E2E_M7_TEST_COUNT,
      ", include_halfvec=", K4B_E2E_M7_INCLUDE_HALFVEC,
      ", from_index=", K4B_E2E_M7_FROM_INDEX, "\n");

_K4B7_T_TOTAL_0 := Runtime();;

Print("\n[setup] _K4B7_BuildSetup() ...\n");
_K4B7_TBUILD := Runtime();
_K4B7_REC := _K4B7_BuildSetup();
Print("[setup] done in ", (Runtime() - _K4B7_TBUILD) / 1000., " s\n");
_K4B7_SETUP_G := _K4B7_REC.setup_G;;
_K4B7_K_G := _K4B7_SETUP_G.num_generators;;
Print("[setup] |G| = ", Order(_K4B7_REC.G),
      ", k_G = ", _K4B7_K_G,
      ", torsion = (z2^", Number(_K4B7_SETUP_G.torsion, x -> x = 2),
      ", z4^", Number(_K4B7_SETUP_G.torsion, x -> x = 4), ")\n");
Print("[setup] |EA_list| = ", Length(_K4B7_REC.H_EA_list),
      ", Q_8 present = ", _K4B7_REC.H_Q8 <> fail, "\n");

# Precompute per-EA setup_H + labels + torsions + res rows.
_K4B7_EA_SETUPS   := List(_K4B7_REC.H_EA_list,
                          h -> SetupCohomology3(h));;
_K4B7_EA_LABELS   := List([1..Length(_K4B7_REC.H_EA_list)],
                          j -> Concatenation("EA_", String(j)));;
_K4B7_SETUP_D8    := SetupCohomology3(_K4B7_REC.H_D8);;
if _K4B7_REC.H_Q8 <> fail then
    _K4B7_SETUP_Q8 := SetupCohomology3(_K4B7_REC.H_Q8);
fi;

# Determine final test count.
if K4B_E2E_M7_TEST_COUNT = fail then
    _K4B7_TEST_COUNT := _K4B7_K_G;
else
    _K4B7_TEST_COUNT := Minimum(K4B_E2E_M7_TEST_COUNT, _K4B7_K_G);
fi;
Print("[setup] sweeping ", _K4B7_TEST_COUNT, " unit vectors",
      " from index ", K4B_E2E_M7_FROM_INDEX, "\n");

# Forward-declare loop locals to suppress syntax warnings.
_K4B7_FAILURES := [];;
_K4B7_PASSES   := 0;;
_K4B7_ROW := fail;;
_K4B7_VH := fail;;
_K4B7_BR := fail;;
_K4B7_BRANCHES_DETECTED := [];;
_K4B7_BRANCHES_SKIPPED  := [];;
_K4B7_BRANCH_DETS       := [];;
_K4B7_JJ := 0;;
_K4B7_I  := 0;;
_K4B7_TI := 0;;
_K4B7_WI := 0.;;
_K4B7_F  := fail;;
_K4B7_LBL := fail;;
_K4B7_FROM := 1;;
_K4B7_DID_HALFVEC := false;;
_K4B7_ORDER4_IDX := fail;;
_K4B7_ANCHOR_FAIL := false;;
_K4B7_WALL_ANCHOR := 0.;;

# ---- omega = 0 anchor: every branch should report trivial -----------
Print("\n--- omega = 0 anchor ---\n");
_K4B7_T_ANCHOR := Runtime();
for _K4B7_JJ in [1..Length(_K4B7_REC.H_EA_list)] do
    _K4B7_VH := ListWithIdenticalEntries(
        Length(_K4B7_REC.torsion_EA_list[_K4B7_JJ]), 0);
    _K4B7_BR := _K4B7_BranchDispatch(
        _K4B7_REC.H_EA_list[_K4B7_JJ],
        _K4B7_EA_SETUPS[_K4B7_JJ],
        _K4B7_VH,
        _K4B7_EA_LABELS[_K4B7_JJ]);
    if _K4B7_BR.detected_nontrivial then
        _K4B7_ANCHOR_FAIL := true;
        Print("  FAIL: anchor branch ", _K4B7_BR.branch_label,
              " reported non-trivial (should be trivial)\n");
    fi;
od;
_K4B7_VH := ListWithIdenticalEntries(
    Length(_K4B7_REC.torsion_D8), 0);
_K4B7_BR := _K4B7_BranchDispatch(
    _K4B7_REC.H_D8, _K4B7_SETUP_D8, _K4B7_VH, "D_8");
if _K4B7_BR.detected_nontrivial then
    _K4B7_ANCHOR_FAIL := true;
    Print("  FAIL: anchor branch D_8 reported non-trivial\n");
fi;
if _K4B7_REC.H_Q8 <> fail then
    _K4B7_VH := ListWithIdenticalEntries(
        Length(_K4B7_REC.torsion_Q8), 0);
    _K4B7_BR := _K4B7_BranchDispatch(
        _K4B7_REC.H_Q8, _K4B7_SETUP_Q8, _K4B7_VH, "Q_8");
    if _K4B7_BR.detected_nontrivial then
        _K4B7_ANCHOR_FAIL := true;
        Print("  FAIL: anchor branch Q_8 reported non-trivial\n");
    fi;
fi;
_K4B7_WALL_ANCHOR := (Runtime() - _K4B7_T_ANCHOR) / 1000.;
if _K4B7_ANCHOR_FAIL then
    Print("  FAIL: omega=0 anchor failed (wall ",
          _K4B7_WALL_ANCHOR, " s)\n");
else
    Print("  PASS: omega=0 -> every branch trivial (wall ",
          _K4B7_WALL_ANCHOR, " s)\n");
fi;

# ---- Sweep over basis unit vectors -----------------------------------
_K4B7_FROM := Maximum(1, K4B_E2E_M7_FROM_INDEX);;
for _K4B7_I in [_K4B7_FROM .. _K4B7_TEST_COUNT] do
    _K4B7_TI := Runtime();
    _K4B7_BRANCHES_DETECTED := [];
    _K4B7_BRANCHES_SKIPPED  := [];
    _K4B7_BRANCH_DETS       := [];

    for _K4B7_JJ in [1..Length(_K4B7_REC.H_EA_list)] do
        # For omega_vec = e_i (unit vector), omega_vec * res_K = row i.
        _K4B7_ROW := _K4B7_REC.res_EA_list[_K4B7_JJ][_K4B7_I];
        _K4B7_VH := List([1..Length(_K4B7_ROW)],
            k -> _K4B7_ROW[k] mod _K4B7_REC.torsion_EA_list[_K4B7_JJ][k]);
        _K4B7_BR := _K4B7_BranchDispatch(
            _K4B7_REC.H_EA_list[_K4B7_JJ],
            _K4B7_EA_SETUPS[_K4B7_JJ],
            _K4B7_VH,
            _K4B7_EA_LABELS[_K4B7_JJ]);
        Add(_K4B7_BRANCH_DETS, _K4B7_BR);
        if _K4B7_BR.skipped then
            Add(_K4B7_BRANCHES_SKIPPED, _K4B7_BR.branch_label);
        elif _K4B7_BR.detected_nontrivial then
            Add(_K4B7_BRANCHES_DETECTED, _K4B7_BR.branch_label);
        fi;
    od;

    _K4B7_ROW := _K4B7_REC.res_D8[_K4B7_I];
    _K4B7_VH := List([1..Length(_K4B7_ROW)],
        k -> _K4B7_ROW[k] mod _K4B7_REC.torsion_D8[k]);
    _K4B7_BR := _K4B7_BranchDispatch(
        _K4B7_REC.H_D8, _K4B7_SETUP_D8, _K4B7_VH, "D_8");
    Add(_K4B7_BRANCH_DETS, _K4B7_BR);
    if _K4B7_BR.skipped then
        Add(_K4B7_BRANCHES_SKIPPED, _K4B7_BR.branch_label);
    elif _K4B7_BR.detected_nontrivial then
        Add(_K4B7_BRANCHES_DETECTED, _K4B7_BR.branch_label);
    fi;

    if _K4B7_REC.H_Q8 <> fail then
        _K4B7_ROW := _K4B7_REC.res_Q8[_K4B7_I];
        _K4B7_VH := List([1..Length(_K4B7_ROW)],
            k -> _K4B7_ROW[k] mod _K4B7_REC.torsion_Q8[k]);
        _K4B7_BR := _K4B7_BranchDispatch(
            _K4B7_REC.H_Q8, _K4B7_SETUP_Q8, _K4B7_VH, "Q_8");
        Add(_K4B7_BRANCH_DETS, _K4B7_BR);
        if _K4B7_BR.skipped then
            Add(_K4B7_BRANCHES_SKIPPED, _K4B7_BR.branch_label);
        elif _K4B7_BR.detected_nontrivial then
            Add(_K4B7_BRANCHES_DETECTED, _K4B7_BR.branch_label);
        fi;
    fi;

    _K4B7_WI := (Runtime() - _K4B7_TI) / 1000.;
    if Length(_K4B7_BRANCHES_DETECTED) > 0 then
        _K4B7_PASSES := _K4B7_PASSES + 1;
        Print("  PASS: e_", _K4B7_I, "/", _K4B7_TEST_COUNT,
              " -> detected by ", _K4B7_BRANCHES_DETECTED,
              " (skipped ", _K4B7_BRANCHES_SKIPPED,
              ", wall ", _K4B7_WI, " s)\n");
    else
        Add(_K4B7_FAILURES, rec(
            idx        := _K4B7_I,
            wall       := _K4B7_WI,
            skipped    := _K4B7_BRANCHES_SKIPPED,
            branch_dets := _K4B7_BRANCH_DETS));
        Print("  FAIL: e_", _K4B7_I, "/", _K4B7_TEST_COUNT,
              " -> ALL branches trivial (skipped ",
              _K4B7_BRANCHES_SKIPPED, ", wall ", _K4B7_WI, " s)\n");
        Print("       FALSE POSITIVE: non-zero v classified trivial.\n");
        for _K4B7_LBL in _K4B7_BRANCH_DETS do
            Print("       ", _K4B7_LBL.branch_label, ": ");
            if _K4B7_LBL.skipped then
                Print("skipped (", _K4B7_LBL.reason, ")\n");
            elif IsBound(_K4B7_LBL.class_idx) then
                Print("class_idx=", _K4B7_LBL.class_idx, "\n");
            else
                Print("is_q_trivial=", _K4B7_LBL.is_q_trivial,
                      ", is_b_trivial=", _K4B7_LBL.is_b_trivial, "\n");
            fi;
        od;
    fi;
od;

# ---- Half-vector for the order-4 generator (if any) -------------------
if K4B_E2E_M7_INCLUDE_HALFVEC = true then
    _K4B7_ORDER4_IDX := Position(_K4B7_SETUP_G.torsion, 4);
    if _K4B7_ORDER4_IDX <> fail then
        _K4B7_DID_HALFVEC := true;
        Print("\n--- half-vector (2 * order-4 generator at idx ",
              _K4B7_ORDER4_IDX, ") ---\n");
        _K4B7_TI := Runtime();
        _K4B7_BRANCHES_DETECTED := [];
        _K4B7_BRANCHES_SKIPPED  := [];
        _K4B7_BRANCH_DETS       := [];

        # For omega_vec = 2 * e_idx, omega_vec * res_K = 2 * row idx of res_K.
        for _K4B7_JJ in [1..Length(_K4B7_REC.H_EA_list)] do
            _K4B7_ROW := _K4B7_REC.res_EA_list[_K4B7_JJ][_K4B7_ORDER4_IDX];
            _K4B7_VH := List([1..Length(_K4B7_ROW)],
                k -> (2 * _K4B7_ROW[k])
                       mod _K4B7_REC.torsion_EA_list[_K4B7_JJ][k]);
            _K4B7_BR := _K4B7_BranchDispatch(
                _K4B7_REC.H_EA_list[_K4B7_JJ],
                _K4B7_EA_SETUPS[_K4B7_JJ],
                _K4B7_VH,
                _K4B7_EA_LABELS[_K4B7_JJ]);
            Add(_K4B7_BRANCH_DETS, _K4B7_BR);
            if _K4B7_BR.skipped then
                Add(_K4B7_BRANCHES_SKIPPED, _K4B7_BR.branch_label);
            elif _K4B7_BR.detected_nontrivial then
                Add(_K4B7_BRANCHES_DETECTED, _K4B7_BR.branch_label);
            fi;
        od;
        _K4B7_ROW := _K4B7_REC.res_D8[_K4B7_ORDER4_IDX];
        _K4B7_VH := List([1..Length(_K4B7_ROW)],
            k -> (2 * _K4B7_ROW[k]) mod _K4B7_REC.torsion_D8[k]);
        _K4B7_BR := _K4B7_BranchDispatch(
            _K4B7_REC.H_D8, _K4B7_SETUP_D8, _K4B7_VH, "D_8");
        Add(_K4B7_BRANCH_DETS, _K4B7_BR);
        if _K4B7_BR.skipped then
            Add(_K4B7_BRANCHES_SKIPPED, _K4B7_BR.branch_label);
        elif _K4B7_BR.detected_nontrivial then
            Add(_K4B7_BRANCHES_DETECTED, _K4B7_BR.branch_label);
        fi;
        if _K4B7_REC.H_Q8 <> fail then
            _K4B7_ROW := _K4B7_REC.res_Q8[_K4B7_ORDER4_IDX];
            _K4B7_VH := List([1..Length(_K4B7_ROW)],
                k -> (2 * _K4B7_ROW[k]) mod _K4B7_REC.torsion_Q8[k]);
            _K4B7_BR := _K4B7_BranchDispatch(
                _K4B7_REC.H_Q8, _K4B7_SETUP_Q8, _K4B7_VH, "Q_8");
            Add(_K4B7_BRANCH_DETS, _K4B7_BR);
            if _K4B7_BR.skipped then
                Add(_K4B7_BRANCHES_SKIPPED, _K4B7_BR.branch_label);
            elif _K4B7_BR.detected_nontrivial then
                Add(_K4B7_BRANCHES_DETECTED, _K4B7_BR.branch_label);
            fi;
        fi;
        _K4B7_WI := (Runtime() - _K4B7_TI) / 1000.;
        if Length(_K4B7_BRANCHES_DETECTED) > 0 then
            _K4B7_PASSES := _K4B7_PASSES + 1;
            Print("  PASS: half-vec -> detected by ",
                  _K4B7_BRANCHES_DETECTED,
                  " (skipped ", _K4B7_BRANCHES_SKIPPED,
                  ", wall ", _K4B7_WI, " s)\n");
        else
            Add(_K4B7_FAILURES, rec(
                idx        := "half-vec",
                wall       := _K4B7_WI,
                skipped    := _K4B7_BRANCHES_SKIPPED,
                branch_dets := _K4B7_BRANCH_DETS));
            Print("  FAIL: half-vec -> ALL branches trivial (skipped ",
                  _K4B7_BRANCHES_SKIPPED, ", wall ", _K4B7_WI, " s)\n");
        fi;
    fi;
fi;

# ---- Summary ----------------------------------------------------------
_K4B7_WALL_TOTAL := (Runtime() - _K4B7_T_TOTAL_0) / 1000.;;
_K4B7_TOTAL_RUN := (_K4B7_TEST_COUNT - _K4B7_FROM + 1);;
if _K4B7_DID_HALFVEC then
    _K4B7_TOTAL_RUN := _K4B7_TOTAL_RUN + 1;
fi;

Print("\n=================================================================\n");
Print("SUMMARY: m=7\n");
Print("=================================================================\n");
Print("Total wall: ", _K4B7_WALL_TOTAL, " s\n");
Print("Anchor (omega=0): ",
      If_(_K4B7_ANCHOR_FAIL, "FAIL", "PASS"), "\n");
Print("Unit-vec + halfvec sweep: ", _K4B7_PASSES, "/", _K4B7_TOTAL_RUN,
      " correctly detected non-trivial\n");
Print("False positives: ", Length(_K4B7_FAILURES), "\n");

if Length(_K4B7_FAILURES) > 0 then
    Print("\nFALSE-POSITIVE classifier verdicts on:\n");
    for _K4B7_F in _K4B7_FAILURES do
        Print("  idx ", _K4B7_F.idx,
              " (skipped ", _K4B7_F.skipped,
              ", wall ", _K4B7_F.wall, " s)\n");
    od;
fi;

if Length(_K4B7_FAILURES) = 0 and not _K4B7_ANCHOR_FAIL then
    Print("\n[GREEN] test_k4b_e2e_sweep_m7\n");
    QuitGap(0);
else
    Print("\n[RED] test_k4b_e2e_sweep_m7\n");
    QuitGap(1);
fi;
