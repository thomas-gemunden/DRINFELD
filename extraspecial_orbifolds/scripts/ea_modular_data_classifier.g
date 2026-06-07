# ea_modular_data_classifier.g
#
# Issue #486: modular-data-based EA-branch classifier for K-4b.
#
# `ClassifyEAFromModularData(H, S, T)` is the modular-data analogue of
# `ClassifyOnD8` / `ClassifyOnQ_8` for the elementary-abelian branch of
# the AM04 + Quillen detecting family for E_+(m). It takes the modular
# data of a twisted Drinfeld double Z(Vec_H^omega) for some abelian H and
# decides whether [omega] is the trivial class in H^3(H; U(1)).
#
# Modular data in, triviality verdict out — the same architecture as the
# D_8/Q_8 classifiers. This completes the architectural fix begun in
# PR #485 (which removed the zero-cocycle stub that previously made the
# K-4b EA-branch verdict mathematically vacuous).
#
# Public API
# ----------
#   ClassifyEAFromModularData(H, S, T)
#
# Input
#   H — an abelian group (in practice an EA 2-group, |H| = 2^(m+1)).
#   S, T — the modular data of Z^omega(Vec_H) for some omega in
#          H^3(H; U(1)). S is an N x N matrix of cyclotomics; T may be
#          either a length-N vector or a DiagonalMat of length N. For
#          abelian H we have N = |H|^2.
#
# Output (record)
#   .is_trivial   : <bool>  true iff (S, T) ≅ untwisted Z(Vec_H).
#   .class_idx    : 1 (when is_trivial) or `fail` (otherwise). Following
#                   the D_8/Q_8 convention, class_idx = 1 denotes the
#                   trivial cohomology class. We do not enumerate
#                   non-trivial classes for EA H (there is no
#                   ground-truth lookup table for H^3(H; U(1)) on EA);
#                   for the K-4b workstream only the is_trivial signal
#                   is required.
#   .match        : the `JointPermutationMatcher(...)` record (.ok, .pi,
#                   .reason). Useful for diagnostics on FAIL paths.
#   .modular_untwisted : `rec(S, T)` returned by `ComputeUntwistedModularData(H)`,
#                   surfaced so consumers (in particular
#                   `_K4A_ClassifyAbelianBranch`) can attach it to their
#                   own diagnostic record without recomputing.
#   .wall_ms      : runtime in milliseconds.
#
# Mechanism
# ---------
# Compute the untwisted modular data of H (closed-form for abelian H via
# `ComputeUntwistedModularData`) and match (S, T) against it via
# `JointPermutationMatcher`. Returns is_trivial = true iff equivalent.
#
# Refs
# ----
# * PR #485 — removed three zero-cocycle / untwisted-override shortcuts
#   from `_K4A_ClassifySpectralEBranchMulti` so the spectral restriction
#   IS actually performed at default opts. This PR provides the
#   correctness-preserving classifier the new restricted record needs.
# * PR #487 (planned) — closed-form (q, b) -> (S, T) for abelian H may
#   eventually replace the `ComputeUntwistedModularData(H)` call here
#   with a much cheaper one.
# * Issue #486 — this PR.
# * User directive 2026-06-07: "K-4b should test modular data and not
#   cocycles" (memory MEMORY.md `feedback_no_downscope_for_krr_verification.md`).

# ---- Resolve and load dependencies -------------------------------------
#
# Auto-load JointPermutationMatcher and ComputeUntwistedModularData from
# alongside this file. Uses INPUT_FILENAME() to find our directory, with
# a small list of relative fallbacks for callers that Read this file from
# the wrong cwd.

_eamc_loaded_jpm := false;;
_eamc_loaded_umd := false;;
_eamc_self := INPUT_FILENAME();;
if _eamc_self <> fail and _eamc_self <> "stream" then
    _eamc_dir := _eamc_self{[1..Length(_eamc_self)
                              - Length("/ea_modular_data_classifier.g")]};;
    _eamc_jpm_cand := Concatenation(_eamc_dir,
                                     "/joint_permutation_matcher.g");;
    if (not IsBound(JointPermutationMatcher))
       and IsExistingFile(_eamc_jpm_cand) then
        Read(_eamc_jpm_cand);
    fi;
    _eamc_loaded_jpm := IsBound(JointPermutationMatcher);
    _eamc_umd_cand := Concatenation(_eamc_dir,
                                     "/untwisted_modular_data.g");;
    if (not IsBound(ComputeUntwistedModularData))
       and IsExistingFile(_eamc_umd_cand) then
        Read(_eamc_umd_cand);
    fi;
    _eamc_loaded_umd := IsBound(ComputeUntwistedModularData);
fi;
if not _eamc_loaded_jpm then
    for _eamc_p in [ "joint_permutation_matcher.g",
                     "./joint_permutation_matcher.g",
                     "../joint_permutation_matcher.g",
                     "extraspecial_orbifolds/scripts/joint_permutation_matcher.g" ] do
        if (not IsBound(JointPermutationMatcher))
           and IsExistingFile(_eamc_p) then
            Read(_eamc_p);
        fi;
    od;
fi;
if not _eamc_loaded_umd then
    for _eamc_p in [ "untwisted_modular_data.g",
                     "./untwisted_modular_data.g",
                     "../untwisted_modular_data.g",
                     "extraspecial_orbifolds/scripts/untwisted_modular_data.g" ] do
        if (not IsBound(ComputeUntwistedModularData))
           and IsExistingFile(_eamc_p) then
            Read(_eamc_p);
        fi;
    od;
fi;
if not IsBound(JointPermutationMatcher) then
    Error("ea_modular_data_classifier.g: cannot locate ",
          "joint_permutation_matcher.g; ensure it sits alongside this ",
          "file in extraspecial_orbifolds/scripts/.");
fi;
if not IsBound(ComputeUntwistedModularData) then
    Error("ea_modular_data_classifier.g: cannot locate ",
          "untwisted_modular_data.g; ensure it sits alongside this ",
          "file in extraspecial_orbifolds/scripts/.");
fi;

# ---- ClassifyEAFromModularData -----------------------------------------

DeclareGlobalFunction("ClassifyEAFromModularData");

InstallGlobalFunction(ClassifyEAFromModularData, function(H, S, T)
    local t0, untwisted, match, is_trivial, class_idx;

    t0 := Runtime();

    if not IsGroup(H) then
        Error("ClassifyEAFromModularData: H must be a group; got ", H);
    fi;
    if not IsAbelian(H) then
        Error("ClassifyEAFromModularData: H must be abelian; got ",
              StructureDescription(H));
    fi;

    # ComputeUntwistedModularData(H) returns rec(S, T, idx) with T as a
    # raw vector (the diag). JointPermutationMatcher accepts vectors and
    # DiagonalMats on either side (see joint_permutation_matcher.g
    # docstring); we pass things through without normalisation.
    untwisted := ComputeUntwistedModularData(H);
    match := JointPermutationMatcher(S, T, untwisted.S, untwisted.T);

    is_trivial := match.ok;
    if is_trivial then
        class_idx := 1;
    else
        class_idx := fail;
    fi;

    return rec(
        is_trivial         := is_trivial,
        class_idx          := class_idx,
        match              := match,
        modular_untwisted  := untwisted,
        wall_ms            := Runtime() - t0
    );
end);

if IsBoundGlobal("_LogStamped") then
    _LogStamped("Loaded ea_modular_data_classifier.g (#486).");
else
    Print("Loaded ea_modular_data_classifier.g (#486).\n");
fi;
