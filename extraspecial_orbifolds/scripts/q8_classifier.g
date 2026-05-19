# q8_classifier.g
#
# K-4a-T1 (issue #192): given the modular data (S, T) of a twisted
# Drinfeld double Z(Vec_{Q_8}^{alpha}) for some 3-cocycle
# alpha in Z^3(Q_8; U(1)), determine which of the 8 Aut(Q_8)-orbits in
# H^3(Q_8; U(1)) the class [alpha] sits in by matching against
# `LoadModularData(8, 4, k)` for k = 1..8.
#
# H^3(Q_8; U(1)) = Z/8 (one cyclic summand). The 8 cohomology classes
# are pairwise inequivalent at the level of (S, T) — see
# `q8_extension_type/writeup.md` (combined with Mignard-Schauenburg,
# arXiv:1708.06538, which proves that for |G| < 32 the modular data is
# a complete invariant of Z(C(G, omega))). So at most one of the 8
# matches succeeds, and if the input is itself the modular data of
# Z(Vec_{Q_8}^{omega_k}) for some k then exactly one matches and it is
# the class index k.
#
# This classifier is the first concrete consumer of the K-4a KR-Bridge
# (issue #188) scaffold: when KRR's lattice-intertwiner-derived alpha
# is restricted to Q_8 (one of the three D-VAN-FIX/#151 detecting
# subgroups for E_+(m)), feeding the resulting (S^Keller|_{Q_8},
# T^Keller|_{Q_8}) into ClassifyOnQ8 reads off the Q_8 component of
# the cohomology class. The Keller prediction alpha|_{Q_8} = 0
# corresponds to class_idx = 1 (the trivial cocycle).
#
# PUBLIC API
# ----------
#   ClassifyOnQ8(S, T)
#
# Input: a pair (S, T) of modular data, with S a rank-N square matrix
# of cyclotomics and T either a vector or a DiagonalMat of length N.
# For Z(Vec_{Q_8}^{*}) we always have N = 22.
#
# Returns a record with fields
#     class_idx   -- the k in {1, ..., 8} for which (S, T) matches
#                    LoadModularData(8, 4, k), or `fail` if no class
#                    matches.
#     pi          -- the matching permutation (list, entry i = pi(i))
#                    when class_idx <> fail; `fail` otherwise.
#     all_matches -- the list of all k in {1, ..., 8} that matched.
#                    Since all 8 stored classes are pairwise inequivalent
#                    this should have length 0 or 1; longer lists would
#                    indicate either a stale precomputed data tree or a
#                    bug in the matcher.
#
# DEPENDENCIES
# ------------
# * `JointPermutationMatcher` from joint_permutation_matcher.g (in this
#   directory).
# * `LoadModularData` from ../../src/modular_data.g, which in turn loads
#   the precomputed tree under `Modular_Data/8/4/{1..8}.txt` (relative
#   to GAP's current working directory). Callers are responsible for
#   making this tree visible — typically via a symlink
#   `Modular_Data -> ../../../modular_data` (see
#   `q8_extension_type/scripts/setup.sh` for the canonical version,
#   and the `tests/k4a/q8/` test-side symlink used by the test suite).

# ---- Resolve and load JointPermutationMatcher --------------------------
#
# The matcher lives alongside this file in
# `extraspecial_orbifolds/scripts/`. We use INPUT_FILENAME() to locate
# our own path, then derive the sibling. If INPUT_FILENAME is not
# available (rare — `Read` always sets it) fall back to a small list of
# relative candidates so a caller invoking us from the wrong cwd still
# works.
_q8c_loaded := false;;
_q8c_self := INPUT_FILENAME();;
if _q8c_self <> fail and _q8c_self <> "stream" then
    _q8c_dir := _q8c_self{[1..Length(_q8c_self)
                            - Length("/q8_classifier.g")]};;
    _q8c_cand := Concatenation(_q8c_dir,
                               "/joint_permutation_matcher.g");;
    if IsExistingFile(_q8c_cand) then
        Read(_q8c_cand);
        _q8c_loaded := true;
    fi;
fi;
if not _q8c_loaded then
    for _q8c_p in [ "joint_permutation_matcher.g",
                    "./joint_permutation_matcher.g",
                    "../joint_permutation_matcher.g",
                    "extraspecial_orbifolds/scripts/joint_permutation_matcher.g" ] do
        if (not _q8c_loaded) and IsExistingFile(_q8c_p) then
            Read(_q8c_p);
            _q8c_loaded := true;
        fi;
    od;
fi;
if not _q8c_loaded then
    Error("q8_classifier.g: cannot locate joint_permutation_matcher.g; ",
          "ensure it sits alongside this file in ",
          "extraspecial_orbifolds/scripts/.");
fi;

# Sanity check: matcher present.
if not IsBound(JointPermutationMatcher) then
    Error("q8_classifier.g: JointPermutationMatcher was not bound by ",
          "joint_permutation_matcher.g.");
fi;

# ---- Sanity check: LoadModularData available ---------------------------
#
# We do not Read modular_data.g here because (per CLAUDE.md) it shares
# global names like `ComplementIntMatWithTransforms` and
# `ProjectiveCharacters` with `universal_coefficients.g`, and reading
# both in the same session clobbers some of them. We require the caller
# to have already loaded modular_data.g.
if not IsBound(LoadModularData) then
    Error("q8_classifier.g: LoadModularData is not bound; ",
          "Read(\"src/modular_data.g\") before loading this file.");
fi;

# ---- ClassifyOnQ8 ------------------------------------------------------

ClassifyOnQ8 := function(S, T)
    local Tvec, all_matches, match_pi, k, stored, storedTvec, match;

    # Normalise input T (DiagonalMat -> vector) just like the matcher
    # does internally; we use Tvec only for the cheap pre-checks below.
    if IsMatrix(T) then
        Tvec := DiagonalOfMat(T);
    else
        Tvec := T;
    fi;

    # The rank check is not strictly necessary (the matcher rejects
    # rank-mismatched inputs) but produces a clearer error than letting
    # 22 attempted matches each fail on rank.
    if Length(Tvec) <> 22 then
        Error("ClassifyOnQ8: expected rank-22 modular data ",
              "(Z(Vec_{Q_8}^{*})), got rank ", Length(Tvec), ".");
    fi;

    all_matches := [];
    match_pi    := fail;

    for k in [1..8] do
        stored := LoadModularData(8, 4, k);
        if stored = fail or not IsBound(stored.S) then
            Error("ClassifyOnQ8: LoadModularData(8, 4, ", k,
                  ") failed; is the Modular_Data tree visible?");
        fi;
        # LoadModularData wraps the on-disk diagonal back into a
        # DiagonalMat (see src/modular_data.g :: LoadModularData), so we
        # extract the vector before calling the matcher. The matcher
        # would accept the DiagonalMat too — we strip it here mostly for
        # clarity and to match the explicit pattern used in
        # q8_extension_type/scripts/find_permutation.g.
        storedTvec := DiagonalOfMat(stored.T);
        match := JointPermutationMatcher(stored.S, storedTvec, S, Tvec);
        if match.ok then
            Add(all_matches, k);
            if match_pi = fail then
                match_pi := match.pi;
            fi;
        fi;
    od;

    if all_matches = [] then
        return rec(
            class_idx   := fail,
            pi          := fail,
            all_matches := []
        );
    else
        return rec(
            class_idx   := all_matches[1],
            pi          := match_pi,
            all_matches := all_matches
        );
    fi;
end;;
