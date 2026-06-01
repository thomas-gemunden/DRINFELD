# k4a_classify.g
#
# K-4a-T6 (issue #200): orchestrator that runs the K-4a Phase 2
# detecting-family pipeline end-to-end for E_+(m) at a given m. Aggregates
# the three branch classifiers
#   * `ClassifyOn3CocycleE` (abelian E branch, K-4a-T3 / #195)
#   * `ClassifyOnD8`        (D_8 branch,         K-4a-T2 / #194)
#   * `ClassifyOnQ8`        (Q_8 branch,         K-4a-T1 / #192)
# into a single verdict on whether KRR's lattice-derived 3-cocycle
# alpha on E_+(m) is trivial in H^3(E_+(m); U(1)). By Adem-Milgram-style
# detecting-family injectivity (see `quillen_detecting_subgroup.g` and
# the writeup citation chain there), the AND of the three branch
# verdicts is the verdict on G itself.
#
# This file also serves as the K-4a-T7 anchor (#201) at m = 3: the
# m = 3 test in `tests/test_k4a_classify.g` reproduces Keller's
# verified-trivial case end-to-end through the orchestrator. If that
# test passes, the K-4a Phase 2 acceptance criterion at m = 3 is met.
#
# PUBLIC API
# ----------
#   K4aClassify(m)
#
# Inputs: m in {2, 3, 5}. (m = 7 remains blocked: the sparse
# `BuildKRRSpectralCharactersSparse` Gauss-sum codepath at m = 7 is a
# stub — see krr_spectral_characters_sparse.g :: `TraceOnOmega0Gauss`,
# tracked at issue #236.)
#
# Returns a record with fields
#   .m              : the input m
#   .group          : `EmGroup(m)` (matrix realisation; informational —
#                     the branches use `EPlusGroup(m)` instances via
#                     `MaximalElementaryAbelian_E_plus(m).parent` etc.
#                     because each detecting-subgroup constructor builds
#                     its own `EPlusGroup(m)` family.)
#   .spectral_data  : record describing the alpha source used:
#                       * For m in {2, 3} (Keller alpha = 0 verified):
#                         `rec(source := "untwisted_baseline", ...)`.
#                         Each branch's restriction used
#                         `BuildIntertwinerDataUntwisted(branch.parent)`.
#                         At these m's the spectral / untwisted choices
#                         are observationally identical, so the cheaper
#                         untwisted baseline is preferred.
#                       * For m = 5 (Keller alpha unverified, the K-4b
#                         production target):
#                         `rec(source := "krr-sparse",
#                              spectral_call_skipped := false,
#                              sparse := <BuildKRRSpectralCharactersSparse(5)
#                                          record>,
#                              ...)`.
#                         The sparse spectral data is computed once via
#                         `BuildKRRSpectralCharactersSparse(m)` and
#                         recorded in `.sparse` for downstream
#                         inspection. The per-branch CT modular data
#                         (under the T4a downscope `epsilon = 1`) is
#                         determined by H's own character functional —
#                         the parent-G spectral data does not propagate
#                         through `RestrictTraceOnWToSubgroup` because
#                         the family of `BuildKRRSpectralCharactersSparse`'s
#                         underlying `EmUnimodGroup(m)` does not match
#                         the `EPlusGroup(m)` family carried by the
#                         detecting-subgroup constructors. The KRR
#                         spectral computation is performed regardless
#                         to genuinely exercise the trace machinery
#                         and provide the actual KRR-derived character
#                         multiplicities for documentation. See the
#                         K-4b verdict note for the full discussion.
#   .E_class        : output of the E-branch check:
#                       rec(
#                         is_abelian   := true,
#                         is_coboundary:= bool  -- alpha|_E coboundary?
#                         match        := <JointPermutationMatcher rec>
#                       )
#                     Uses the modular-data approach (ComputeCTModularData
#                     vs ComputeUntwistedModularData) per the K-4a-T6
#                     spec: "if the modular data is equivalent to
#                     untwisted, then alpha is a coboundary; if not,
#                     it's not."
#   .D8_class       : output of `ClassifyOnD8(...)` on the
#                     ComputeCTModularData of the D_8 restriction.
#                     Trivial corresponds to class_idx = 1 (the
#                     all-zero stored 3-cocycle vector in
#                     modular_data/8/3/1.txt).
#   .Q8_class       : output of `ClassifyOnQ8(...)` likewise. Trivial
#                     is class_idx = 1 (modular_data/8/4/1.txt).
#   .trivial        : conjunction of three triviality flags:
#                       E_class.is_coboundary AND
#                       D8_class.class_idx = 1 AND
#                       Q8_class.class_idx = 1.
#                     `true`  -> alpha is detected-trivial (verdict
#                                "trivial")
#                     `false` -> alpha is detected non-trivial on at
#                                least one branch (verdict "non-trivial")
#                     `fail`  -> at least one branch returned a fail/
#                                deferred answer (verdict "incomplete")
#   .verdict        : human-readable "trivial" | "non-trivial" |
#                     "incomplete"
#   .timing         : rec(.wall_seconds, ..., per-branch breakdown.
#
# DEFERRAL POLICY (m >= 6)
# ------------------------
# m = 5 is supported via the sparse trace path
# (`krr_spectral_characters_sparse.g`, issue #220 / PR #235). The dense
# `BuildKRRSpectralCharacters` at m = 5 would require ~3.7 years of CPU
# for ONE T_h matrix (per the header note in `krr_spectral_characters.g`),
# whereas the sparse / trace-only `BuildKRRSpectralCharactersSparse(5)`
# computes the central-class trace table in ~30 minutes via character-
# orthogonality reduction.
#
# m = 7 remains blocked: the sparse builder's `TraceOnOmega0Gauss`
# Gauss-sum closed-form codepath is a stub at the time of this writing
# (issue #236). Until it lands, K4aClassify errors out at m >= 6 with a
# clear message pointing at #236.
#
# DEPENDENCIES
# ============
# Reads (or expects already in scope) the following sibling files:
#   * untwisted_modular_data.g  (BuildSimpleIndex, ComputeUntwistedModularData)
#   * krr_projector.g           (BuildIntertwinerDataUntwisted,
#                                BuildIntertwinerDataUntwistedLazy)
#   * joint_permutation_matcher.g (JointPermutationMatcher)
#   * q8_classifier.g           (ClassifyOnQ8)
#   * d8_classifier.g           (ClassifyOnD8)
#   * abelian_e_form_check.g    (ClassifyOn3CocycleE — referenced for
#                                forward-compat; the m=3 anchor path
#                                uses the modular-data approach above)
#   * restrict_to_subgroup.g    (RestrictTraceOnWToSubgroup)
#   * quillen_detecting_subgroup.g
#                                (MaximalElementaryAbelian_E_plus,
#                                D8Section_E_plus, Q8Section_E_plus)
#   * ct_modular_data.g         (ComputeCTModularData)
#   * em_construction.g         (EmGroup)
#
# Plus the parent src tree (loaded via the dependents):
#   * ../../src/modular_data.g  (LoadModularData — pulled in by the
#                                D_8/Q_8 classifiers via their loader
#                                preconditions, but the orchestrator
#                                doesn't Read it directly; callers
#                                supply via the test harness or
#                                run_k4a.sh-style driver.)
#
# For m = 5 only, additionally loaded on demand by `K4aClassify(5)`:
#   * krr_spectral_characters.g            (EmUnimodGroup,
#                                           NormaliseIntertwiner —
#                                           reused by the sparse variant)
#   * krr_spectral_characters_sparse.g     (BuildKRRSpectralCharactersSparse,
#                                           the issue #220 sparse trace
#                                           path)
#   * bw_lattice.g, em_construction.g, twisted_group_algebra.g,
#     qforms_f2.g, defect_rep_minus_id.g, defect_rep_minus_id_optim.g
#                                          (transitive deps of the
#                                           sparse / dense KRR builders)


# ---- Load siblings using INPUT_FILENAME() pattern ----------------------
# Mirrors the loader pattern used by q8_classifier.g et al.

_k4a_self := INPUT_FILENAME();;
_k4a_dir := fail;;
if _k4a_self <> fail and _k4a_self <> "stream" then
    _k4a_dir := _k4a_self{[1..Length(_k4a_self)
                            - Length("/k4a_classify.g")]};
fi;;

# Helper: try to Read a sibling file if a given global is not yet bound.
_K4A_LoadSibling := function(global_name, filename)
    local cand, p;
    if IsBoundGlobal(global_name) then
        return true;
    fi;
    if _k4a_dir <> fail then
        cand := Concatenation(_k4a_dir, "/", filename);
        if IsExistingFile(cand) then
            Read(cand);
            return true;
        fi;
    fi;
    # CWD-relative fallbacks.
    for p in [ filename,
               Concatenation("./", filename),
               Concatenation("../", filename),
               Concatenation("extraspecial_orbifolds/scripts/", filename) ] do
        if IsExistingFile(p) then
            Read(p);
            return true;
        fi;
    od;
    return false;
end;;

if not _K4A_LoadSibling("BuildSimpleIndex", "untwisted_modular_data.g") then
    Error("k4a_classify.g: cannot locate untwisted_modular_data.g");
fi;
if not _K4A_LoadSibling("BuildIntertwinerDataUntwisted",
                         "krr_projector.g") then
    Error("k4a_classify.g: cannot locate krr_projector.g");
fi;
if not _K4A_LoadSibling("JointPermutationMatcher",
                         "joint_permutation_matcher.g") then
    Error("k4a_classify.g: cannot locate joint_permutation_matcher.g");
fi;
if not _K4A_LoadSibling("RestrictTraceOnWToSubgroup",
                         "restrict_to_subgroup.g") then
    Error("k4a_classify.g: cannot locate restrict_to_subgroup.g");
fi;
if not _K4A_LoadSibling("ComputeCTModularData", "ct_modular_data.g") then
    Error("k4a_classify.g: cannot locate ct_modular_data.g");
fi;
if not _K4A_LoadSibling("MaximalElementaryAbelian_E_plus",
                         "quillen_detecting_subgroup.g") then
    Error("k4a_classify.g: cannot locate quillen_detecting_subgroup.g");
fi;
if not _K4A_LoadSibling("EmGroup", "em_construction.g") then
    Error("k4a_classify.g: cannot locate em_construction.g");
fi;

# The D_8 / Q_8 classifiers require `LoadModularData` to be bound already
# (they Error on load otherwise). We do not Read src/modular_data.g here
# because per CLAUDE.md it shares globals with universal_coefficients.g;
# the caller (test harness, run_k4a.sh) is responsible for pre-loading
# it. Defer the actual `Read` of the classifiers to a moment when
# `LoadModularData` exists; we accomplish that with a runtime check
# inside `K4aClassify` rather than at file-load time.
if IsBound(LoadModularData) then
    if not _K4A_LoadSibling("ClassifyOnD8", "d8_classifier.g") then
        Error("k4a_classify.g: cannot locate d8_classifier.g");
    fi;
    if not _K4A_LoadSibling("ClassifyOnQ8", "q8_classifier.g") then
        Error("k4a_classify.g: cannot locate q8_classifier.g");
    fi;
fi;


# ---- Helpers -----------------------------------------------------------

# Convert a wall-time delta in GAP Runtime() units (milliseconds) to
# seconds (Float).
_K4A_SecsSince := function(t0)
    return (Runtime() - t0) / 1000.0;
end;;

# Issue #333 followup: D-VAN's minimum-detecting-family EA indices per m.
# K-4a's original single-EA choice (`MaximalElementaryAbelian_E_plus(m).subgroup`,
# i.e. `candidates[1]`) is NOT enough for injectivity at m >= 3 — the m=3
# sweep showed 11/36 basis vectors of H^3(E_+(3); U(1)) restrict to zero on
# the single chosen E (kernel includes e_4, 8, 12, 14, 17, 20, 22, 23, 31,
# 32, 33). D-VAN's per-m minimum family (greedy-tightened in PR #320, with
# final_ker = 1 verified at m <= 5) does detect every non-zero cocycle.
#
# These indices are into `BuildRestrictionMatrices(m, "hap").H_EA_list`.
_K4A_DVAN_EA_FAMILIES := rec();;
_K4A_DVAN_EA_FAMILIES.("2") := [3, 2, 5];;
_K4A_DVAN_EA_FAMILIES.("3") := [4, 6, 7, 11, 16, 22];;
# m=5: PR #320 minimum-detecting-family, indices into BuildRestrictionMatrices(5, "hap").H_EA_list.
# Verified `final_ker = 1` at m=5 via streaming greedy + drop-one tightening.
_K4A_DVAN_EA_FAMILIES.("5") := [33, 48, 54, 57, 70, 76, 88, 89, 109];;
# m=7: D-VAN m=7 production landed via PR #361 with greedy_log
# ea = [1, 3, 6, 12, 10, 122, 765, 2], final_ker = 1, locally_tight = true.
# These indices are NOT directly usable here: they index into the
# streaming-greedy 1000-Lagrangian sample (not the 9 845 550 eager
# enumeration that `BuildRestrictionMatrices(7, "lhs")` would use, which
# is explicitly errored OOM at detecting_family_restriction.g:1184).
# Issue #377 resolves this by persisting the chosen EAs' generator
# tuples in result.g and providing a loader (LoadDVANEAFamily below)
# that returns reconstructed subgroups instead of indices.

# Issue #377: load D-VAN's per-m minimum detecting family from disk by
# reconstructing the EA subgroups from `result.ea_generators`. The
# result file is `computed/dvan_min_family/m<m>/result.g` and is
# produced by `_DETF_TrimmedFamily_m7_streaming` (for m=7) or by the
# eager `_DETF_TrimmedFamily` driver (for m <= 5).
#
# Returns: list of EA subgroups of `_DETF_BuildSetupG_LHS(m).group`,
# or `fail` if (a) the file does not exist, (b) the file lacks
# `ea_generators`, or (c) the LHS setup helper is unavailable.
#
# Note: the loader requires the SAME `EPlusGroup` presentation that
# produced the file. `_DETF_BuildSetupG_LHS(m)` is deterministic given
# `m`, so a fresh call reconstructs a compatible parent group.
LoadDVANEAFamily := function(m)
    local result_path, dvan_result, setup_G, G, subgroups;
    if _k4a_dir = fail then
        return fail;
    fi;
    result_path := Concatenation(
        _k4a_dir,
        "/../computed/dvan_min_family/m", String(m), "/result.g");
    if not IsExistingFile(result_path) then
        return fail;
    fi;
    # The file binds a top-level `dvan_m<m>_result` global (e.g.
    # `dvan_m7_result`) when Read; for forward compat we also check
    # the generic `dvan_result` name.
    Read(result_path);
    dvan_result := fail;
    if IsBoundGlobal(Concatenation("dvan_m", String(m), "_result")) then
        dvan_result := ValueGlobal(
            Concatenation("dvan_m", String(m), "_result"));
    elif IsBoundGlobal("dvan_result") then
        dvan_result := ValueGlobal("dvan_result");
    fi;
    if dvan_result = fail then
        return fail;
    fi;
    if not IsRecord(dvan_result)
       or not IsBound(dvan_result.ea_generators) then
        return fail;
    fi;
    # Lazy-load the LHS setup helper.
    if not _K4A_LoadSibling("_DETF_BuildSetupG_LHS",
                             "detecting_family_restriction.g") then
        return fail;
    fi;
    setup_G := _DETF_BuildSetupG_LHS(m);
    G := setup_G.group;
    subgroups := List(dvan_result.ea_generators,
                      gen_tuple -> Subgroup(G, gen_tuple));
    return subgroups;
end;;

_K4A_GetDVANEAFamily := function(m)
    local key, loaded;
    key := String(m);
    if IsBound(_K4A_DVAN_EA_FAMILIES.(key)) then
        return _K4A_DVAN_EA_FAMILIES.(key);
    fi;
    # No hardcoded index family for this m — try the loader. The loader
    # returns a list of subgroups (not indices). `_K4A_ClassifyEBranchMulti`
    # dispatches on the input shape (integer indices vs subgroups).
    loaded := LoadDVANEAFamily(m);
    if loaded <> fail then
        return loaded;
    fi;
    return fail;
end;;

# Given an `H` (abelian subgroup) and a restricted intertwiner_data,
# compute the CT modular data and the H-untwisted modular data, then
# call JointPermutationMatcher. Return rec(is_abelian, is_coboundary,
# match, modular_ct, modular_untwisted, wall_seconds).
_K4A_ClassifyAbelianBranch := function(restricted, H)
    local t0, modular_ct, modular_untwisted, match;
    t0 := Runtime();
    # Issue #333: at omega != 0 the projective consumption downstream of
    # RestrictTraceOnWToSubgroupProjective produces a (S, T) that does
    # not match the ground-truth Z(Vec^{omega|_H}_H) modular data. When
    # _K4A_RestrictForBranch attaches `modular_ct_override` (computed
    # via direct ComputeModularData(H, omega|_H, val, exp)), prefer it.
    if IsBound(restricted.modular_ct_override) then
        modular_ct := restricted.modular_ct_override;
    else
        modular_ct := ComputeCTModularData(restricted, H);
    fi;
    modular_untwisted := ComputeUntwistedModularData(H);
    # Matcher arg order doesn't matter (it's symmetric in the (S, T)
    # comparison up to relabelling), but for readability we put the
    # "reference" (untwisted) first and the "candidate" (CT) second.
    # Note on T shapes: ComputeUntwistedModularData returns T as a raw
    # vector (the diag), while ComputeCTModularData wraps it via
    # DiagonalMat. JointPermutationMatcher accepts both forms (see
    # joint_permutation_matcher.g docstring) and normalises internally.
    match := JointPermutationMatcher(
        modular_untwisted.S, modular_untwisted.T,
        modular_ct.S, modular_ct.T);
    return rec(
        is_abelian          := true,
        is_coboundary       := match.ok,
        match               := match,
        modular_ct          := modular_ct,
        modular_untwisted   := modular_untwisted,
        wall_seconds        := _K4A_SecsSince(t0)
    );
end;;

# Given a non-abelian H (D_8 or Q_8) and a restricted intertwiner_data,
# compute the CT modular data and call the appropriate classifier.
# `classifier` is the callable (ClassifyOnD8 or ClassifyOnQ8).
_K4A_ClassifyNonAbelianBranch := function(restricted, H, classifier)
    local t0, modular_ct, class_res;
    t0 := Runtime();
    # Issue #333: prefer ground-truth (S, T) from direct ComputeModularData
    # over the broken projective consumption. See _K4A_RestrictForBranch.
    if IsBound(restricted.modular_ct_override) then
        modular_ct := restricted.modular_ct_override;
    else
        modular_ct := ComputeCTModularData(restricted, H);
    fi;
    class_res := classifier(modular_ct.S, DiagonalOfMat(modular_ct.T));
    return rec(
        is_abelian      := false,
        modular_ct      := modular_ct,
        class_idx       := class_res.class_idx,
        pi              := class_res.pi,
        all_matches     := class_res.all_matches,
        wall_seconds    := _K4A_SecsSince(t0)
    );
end;;


# Issue #333 followup: E-branch classifier over D-VAN's minimum detecting
# family of maximal EAs. Replaces the single-EA `_K4A_ClassifyAbelianBranch`
# when `opts.lattice_source = true` and `omega_vec != 0`. At single-EA the
# kernel of restriction to {E_chosen, D_8, Q_8} is non-trivial at m >= 3
# (e_31, e_32, e_33 at m=3 are in the kernel — verified empirically),
# producing false-negative `trivial` verdicts. Multi-EA over D-VAN's per-m
# minimum family has trivial kernel (D-VAN at m <= 5 has `final_ker = 1`).
#
# Inputs:
#   opts       : the K4aClassify opts record (must have lattice_source +
#                omega_vec set and non-zero for this path to trigger).
#   m          : positive integer.
#   ea_family  : either
#                  (a) a list of integers — D-VAN EA indices into
#                      `BuildRestrictionMatrices(m, "hap").H_EA_list`.
#                      This is the m <= 5 path: BuildRestrictionMatrices
#                      is feasible and indexes into a hardcoded family.
#                  (b) a list of Group objects — D-VAN EA subgroups loaded
#                      via `LoadDVANEAFamily(m)` (issue #377). This is
#                      the m=7 path: BuildRestrictionMatrices(7, *) OOMs,
#                      so we build setup_G via `_DETF_BuildSetupG_LHS(m)`
#                      and use the supplied subgroups directly.
#                Dispatch is by checking whether the first element is
#                an integer or a group.
#
# Returns: rec(is_abelian := true, is_coboundary := AND over all EAs,
# per_ea_results := [list of {ea_idx, is_coboundary} recs], wall_seconds,
# family_source := "dvan-min-family").
_K4A_ClassifyEBranchMulti := function(opts, m, ea_family)
    local t0, restmats, setup_G, omega_G, omega_H_fn, val, expon,
          per_ea, is_coboundary_all, ea_entry, H_EA, modular_ct,
          modular_untwisted, match, ea_idx, is_index_input;
    t0 := Runtime();
    # Detect input shape. The two paths differ only in (i) how setup_G is
    # obtained and (ii) how H_EA is extracted from each ea_family entry.
    is_index_input := not IsEmpty(ea_family) and IsInt(ea_family[1]);
    if is_index_input then
        restmats := BuildRestrictionMatrices(m, "hap");
        setup_G := restmats.setup_G;
    else
        # Subgroup-input path (m=7). Lazy-load _DETF_BuildSetupG_LHS.
        if not _K4A_LoadSibling("_DETF_BuildSetupG_LHS",
                                 "detecting_family_restriction.g") then
            Error("_K4A_ClassifyEBranchMulti: cannot locate ",
                  "detecting_family_restriction.g for subgroup-input path");
        fi;
        setup_G := _DETF_BuildSetupG_LHS(m);
        restmats := fail;
    fi;
    omega_G := StandardCocycleOf(setup_G, opts.omega_vec);
    omega_H_fn := function(x, y, z) return omega_G(x, y, z); end;
    val := Gcd(Gcd(opts.omega_vec), setup_G.exponent);
    expon := setup_G.exponent / val;
    per_ea := [];
    is_coboundary_all := true;
    ea_idx := 0;
    for ea_entry in ea_family do
        ea_idx := ea_idx + 1;
        if is_index_input then
            H_EA := restmats.H_EA_list[ea_entry];
        else
            H_EA := ea_entry;
        fi;
        modular_ct := ComputeModularData(H_EA, omega_H_fn, val, expon);
        modular_untwisted := ComputeUntwistedModularData(H_EA);
        match := JointPermutationMatcher(
            modular_untwisted.S, modular_untwisted.T,
            modular_ct.S, modular_ct.T);
        Add(per_ea, rec(
            ea_idx        := If_(is_index_input, ea_entry, ea_idx),
            ea_order      := Order(H_EA),
            is_coboundary := match.ok
        ));
        if not match.ok then
            is_coboundary_all := false;
        fi;
        if opts.verbose then
            Print("  [_K4A_ClassifyEBranchMulti] EA #",
                  If_(is_index_input, ea_entry, ea_idx),
                  " (|EA| = ", Order(H_EA),
                  "): is_coboundary = ", match.ok, "\n");
        fi;
    od;
    return rec(
        is_abelian      := true,
        is_coboundary   := is_coboundary_all,
        per_ea_results  := per_ea,
        family_source   := "dvan-min-family",
        wall_seconds    := _K4A_SecsSince(t0)
    );
end;;


# `_K4A_BuildBranchData(opts, m, H_parent)`:
# Build the per-branch `intertwiner_data` record. Routes to either
# `BuildIntertwinerDataUntwisted(H_parent)` (the legacy K-4a default)
# or `BuildKRRIntertwinerData(m, H_parent, opts_for_krr)` (the
# lattice-source path added in #316). At opts.omega_vec = fail the
# two routes are numerically identical for the consumers
# (ComputeCTModularData / RestrictTraceOnWToSubgroup).
_K4A_BuildBranchData := function(opts, m, H_parent)
    local krr_opts;
    if not opts.lattice_source then
        return BuildIntertwinerDataUntwisted(H_parent);
    fi;
    # Lattice-source path. Lazy-load build_krr_intertwiner_data.g if
    # not yet bound.
    if not IsBoundGlobal("BuildKRRIntertwinerData") then
        if not _K4A_LoadSibling("BuildKRRIntertwinerData",
                                 "build_krr_intertwiner_data.g") then
            Error("K4aClassify: lattice_source = true but ",
                  "build_krr_intertwiner_data.g could not be located.");
        fi;
    fi;
    # Note: the loader above may bind a stale scaffold version of
    # BuildKRRIntertwinerData from kr_intertwiner_bridge.g. Force the
    # production version by re-Reading build_krr_intertwiner_data.g if
    # the loaded function takes only 2 args (the scaffold) rather than
    # variable args (the production version). We detect that via a
    # probe call's error signature. For now we just trust the load
    # order — build_krr_intertwiner_data.g is the LAST sibling to bind
    # the name, so it wins.
    krr_opts := rec(
        spectral_source := opts.spectral_source,
        verbose         := opts.verbose
    );
    if opts.omega_vec <> fail then
        krr_opts.omega_vec := opts.omega_vec;
        # When the user supplies a non-zero omega_vec the "lite" trace
        # (= EvalIrr) is mathematically WRONG (it returns ordinary,
        # not projective, character values); the resulting G-level
        # data also wouldn't bind `projective_data`, so the per-branch
        # dispatcher `_K4A_RestrictForBranch` would silently fall
        # through to `RestrictTraceOnWToSubgroup` — exactly the bug
        # this issue (#328) fixes at the H-level. Route through
        # the projective path explicitly here so the dispatcher sees
        # the right parent data shape.
        if opts.spectral_source = "lite" then
            krr_opts.spectral_source := "projective";
        elif opts.spectral_source = "auto" then
            # "auto" already routes to "projective" at ω ≠ 0 inside
            # BuildKRRIntertwinerData; leave alone.
            ;
        fi;
    fi;
    return BuildKRRIntertwinerData(m, H_parent, krr_opts);
end;;


# `_K4A_RestrictForBranch(opts, data, H_subgroup)`:
# Pick the right restriction variant based on the orchestrator opts.
# If `opts.lattice_source = true and opts.omega_vec is non-zero`, route
# through the per-branch projective restriction (issue #328) so the
# H-level CT modular data reflects the slant 2-cocycle of ω by each
# H-class rep. Otherwise fall back to the legacy untwisted-baseline
# restriction (RestrictTraceOnWToSubgroup) which is the K-4a anchor.
_K4A_OmegaIsZero := function(omega_vec)
    local x;
    if omega_vec = fail or omega_vec = [] then return true; fi;
    for x in omega_vec do
        if x <> 0 then return false; fi;
    od;
    return true;
end;;

_K4A_RestrictForBranch := function(opts, data, H_subgroup)
    local restricted, parent_G, setup_G_full, omega_G_cocycle, omega_H,
          val, expon;
    if opts.lattice_source
       and (not _K4A_OmegaIsZero(opts.omega_vec))
       and IsBoundGlobal("RestrictTraceOnWToSubgroupProjective") then
        if opts.verbose then
            Print("  [_K4A_RestrictForBranch] routing through ",
                  "RestrictTraceOnWToSubgroupProjective (#328)\n");
        fi;
        restricted := RestrictTraceOnWToSubgroupProjective(data, H_subgroup);
        # Issue #333: the projective trace consumed by
        # ComputeCTModularData(restricted, H) produces (S, T) that does
        # NOT match any stored Aut-orbit rep via JointPermutationMatcher.
        # The ground-truth Z(Vec^{omega|_H}_H) (S, T), computed directly
        # via StandardCocycleOf + ComputeModularData, DOES match. Attach
        # it here as `modular_ct_override` so the abelian and non-abelian
        # branch classifiers consume the correct (S, T).
        parent_G := data.group;
        if opts.verbose then
            Print("  [_K4A_RestrictForBranch] computing ground-truth ",
                  "(S, T) via ComputeModularData(H, omega|_H, val, exp) ",
                  "(#333)\n");
        fi;
        setup_G_full := SetupCohomology3(parent_G);
        omega_G_cocycle := StandardCocycleOf(setup_G_full, opts.omega_vec);
        omega_H := function(x, y, z) return omega_G_cocycle(x, y, z); end;
        val := Gcd(Gcd(opts.omega_vec), setup_G_full.exponent);
        expon := setup_G_full.exponent / val;
        restricted.modular_ct_override := ComputeModularData(
            H_subgroup, omega_H, val, expon);
        return restricted;
    fi;
    return RestrictTraceOnWToSubgroup(data, H_subgroup);
end;;


# ---- Public: K4aClassify(m [, opts]) -----------------------------------
#
# OPTIONAL `opts` RECORD
# ----------------------
# `opts` (optional, second arg) is a record. Recognised fields:
#   .lattice_source : if true, the per-branch `data_X` records are
#                     built via `BuildKRRIntertwinerData(m, X.parent)`
#                     (K-4a-T4b / PR #309) instead of the legacy
#                     `BuildIntertwinerDataUntwisted(X.parent)`. At
#                     omega = 0 the two are numerically identical (the
#                     KR-bridge research note §3.2 / Test 1 of
#                     `test_build_krr_intertwiner_data.g`), so the
#                     K-4a verdicts are unchanged. The lattice path
#                     becomes meaningful once V-1 (#14) is exercised
#                     by passing a non-zero `opts.omega_vec` (which is
#                     then threaded into `BuildKRRIntertwinerData`).
#                     Default: false (legacy untwisted-baseline path).
#   .omega_vec      : non-trivial 3-cocycle on E_+(m). Only consumed
#                     when `lattice_source = true`; threaded through
#                     to `BuildKRRIntertwinerData`'s `opts.omega_vec`,
#                     which routes through V-1's `EpsilonOmegaPhase`
#                     for ε and PR #327 / #323's projective character
#                     table for trace_on_W on G. At ω ≠ 0 and
#                     m < 5 the orchestrator routes the per-branch
#                     restriction through
#                     `RestrictTraceOnWToSubgroupProjective` (issue
#                     #328), so the H-level CT modular data reflects
#                     the slant 2-cocycle of ω by each H-class rep.
#                     At ω = 0 the projective path collapses to the
#                     untwisted baseline byte-for-byte (acceptance
#                     criterion 1 of #328), so this default-omega
#                     case is unchanged from earlier K-4a runs.
#                     Default: fail (omega = 0).
#   .spectral_source: forwarded to `BuildKRRIntertwinerData`. Default
#                     "lite" (numerically equivalent to untwisted
#                     baseline at omega = 0, per the research note).
#   .verbose        : forwarded to `BuildKRRIntertwinerData`.
#                     Default false.
#
# At default opts (no `lattice_source`), behaviour is unchanged from
# pre-#316.

K4aClassify := function(arg)
    local m, user_opts, opts, n_max_supported, t_total_0, G_em,
          ea_rec, d8_rec, q8_rec,
          data_E, data_D8, data_Q8, restricted_E, restricted_D8,
          restricted_Q8, E_class, D8_class, Q8_class, trivial, verdict,
          spectral_data, sparse_data, t_branch_0, t_E_branch,
          t_D8_branch, t_Q8_branch, t_total, t_spectral, fld;

    # ---- Argument validation -----------------------------------------
    if Length(arg) < 1 then
        Error("K4aClassify: usage K4aClassify(m [, opts]).");
    fi;
    m := arg[1];
    user_opts := fail;
    if Length(arg) >= 2 then
        user_opts := arg[2];
    fi;
    # Normalise opts. Default = legacy (lattice_source = false).
    opts := rec(
        lattice_source  := false,
        omega_vec       := fail,
        spectral_source := "lite",
        verbose         := false
    );
    if user_opts <> fail then
        if not IsRecord(user_opts) then
            Error("K4aClassify: opts must be a record or fail; got ",
                  user_opts);
        fi;
        for fld in ["lattice_source", "omega_vec",
                    "spectral_source", "verbose"] do
            if IsBound(user_opts.(fld)) then
                opts.(fld) := user_opts.(fld);
            fi;
        od;
    fi;
    # Sanity: omega_vec only meaningful with lattice_source.
    if opts.omega_vec <> fail and not opts.lattice_source then
        Error("K4aClassify: opts.omega_vec is set but ",
              "opts.lattice_source = false. The untwisted-baseline path ",
              "does not consume omega_vec. Set lattice_source := true ",
              "to route through BuildKRRIntertwinerData (V-1 / KR-bridge).");
    fi;
    if not (IsInt(m) and m >= 1) then
        Error("K4aClassify: m must be a positive integer; got ", m);
    fi;

    n_max_supported := 5;
    if m > n_max_supported then
        Error(
            "K4aClassify: m = ", m, " is not yet supported. ",
            "At m = 5 the sparse trace path ",
            "(BuildKRRSpectralCharactersSparse, issue #220 / PR #235) ",
            "is wired through. At m = 7 the sparse builder's ",
            "TraceOnOmega0Gauss closed-form codepath is still a stub ",
            "(issue #236). Until #236 lands, K4aClassify supports m ",
            "in {2, 3, 5} only.");
    fi;
    if m = 4 then
        Error(
            "K4aClassify: m = 4 is mathematically meaningful but the ",
            "BW(4) lattice does not give a KRR Phi extension (the ",
            "extraspecial 2-group E_+(4) is not the automorphism group ",
            "of the standard BW(4) lattice's even sub-VOA). The K-4 ",
            "EPIC targets m in {2, 3, 5, 7}; intermediate m = 4 is not ",
            "in scope. Use m = 5 instead.");
    fi;

    # Runtime check: the D_8 / Q_8 classifiers expect LoadModularData
    # to be in scope. If the caller hasn't Read src/modular_data.g, that
    # is a hard error here — we cannot proceed to D_8 / Q_8 branches.
    if not IsBound(LoadModularData) then
        Error(
            "K4aClassify: LoadModularData is not bound. Read \"",
            "src/modular_data.g\" before calling K4aClassify(m). See ",
            "run_k4a.sh / tests/test_k4a_classify.g for the canonical ",
            "load sequence.");
    fi;
    # Now lazy-Read the classifiers (they assert on LoadModularData
    # presence at load time).
    if not IsBound(ClassifyOnD8) then
        if not _K4A_LoadSibling("ClassifyOnD8", "d8_classifier.g") then
            Error("K4aClassify: cannot locate d8_classifier.g");
        fi;
    fi;
    if not IsBound(ClassifyOnQ8) then
        if not _K4A_LoadSibling("ClassifyOnQ8", "q8_classifier.g") then
            Error("K4aClassify: cannot locate q8_classifier.g");
        fi;
    fi;

    # The Q_8 section only exists for m >= 2 (E_+(1) = D_8 has no Q_8
    # subgroup). For m = 1 we'd need a different orchestrator (or just
    # skip the Q_8 branch); not implementing that here since the
    # K-4a-T7 anchor and acceptance criteria are at m = 3.
    if m = 1 then
        Error(
            "K4aClassify: m = 1 (E_+(1) = D_8) has no Q_8 section ",
            "and the AM04 detecting-family argument simplifies to the ",
            "D_8 case alone. Use ClassifyOnD8(...) directly for m = 1.");
    fi;

    t_total_0 := Runtime();

    # ---- Construct G_em informational handle ------------------------
    # The matrix-realisation E_+(m) (`EmGroup(m)`) is what KRR's
    # lattice-intertwiner machinery operates on. Each detecting-subgroup
    # constructor below builds its own `EPlusGroup(m) =
    # ExtraspecialGroup(2^(2m+1), "+")` instance (different GAP family
    # from `EmGroup(m)` though isomorphic) and stores it in `.parent`.
    # We keep both for the verdict record.
    G_em := EmGroup(m);

    # ---- spectral_data: choose source per m -------------------------
    # m in {2, 3}: Keller alpha = 0 verified, untwisted_baseline is
    #   observationally identical to the KRR spectral characters; use
    #   the cheap path for speed.
    # m = 5: K-4b production target, Keller alpha unverified. Compute
    #   the sparse spectral data via `BuildKRRSpectralCharactersSparse`
    #   to genuinely exercise the KRR trace machinery and record the
    #   actual character multiplicities for downstream documentation.
    #   The per-branch CT modular data still uses H's own untwisted
    #   baseline (per T4a's epsilon = 1 downscope, and because the
    #   sparse builder operates on the `EmUnimodGroup(m)` family which
    #   does not match the `EPlusGroup(m)` family carried by the
    #   detecting-subgroup constructors).
    if m = 5 then
        # Load sparse builder and its transitive deps. The sparse file
        # itself does not contain loader logic; we load the chain
        # explicitly here.
        if not IsBound(BuildKRRSpectralCharactersSparse) then
            if not _K4A_LoadSibling("EmGroup", "em_construction.g") then
                Error("K4aClassify: cannot locate em_construction.g");
            fi;
            if not _K4A_LoadSibling("BWGram", "bw_lattice.g") then
                Error("K4aClassify: cannot locate bw_lattice.g");
            fi;
            if not _K4A_LoadSibling("UnimodSigma", "twisted_group_algebra.g") then
                Error("K4aClassify: cannot locate twisted_group_algebra.g");
            fi;
            # qforms_f2.g loads F2 quadratic-form helpers used by the
            # KRR optim closed-form (transitively); F2Mod is its
            # most stable load-marker.
            if not _K4A_LoadSibling("F2Mod", "qforms_f2.g") then
                Error("K4aClassify: cannot locate qforms_f2.g");
            fi;
            if not _K4A_LoadSibling("BuildIntertwiner",
                                     "defect_rep_minus_id.g") then
                Error("K4aClassify: cannot locate defect_rep_minus_id.g");
            fi;
            if not _K4A_LoadSibling("HardCodeShortComputeInterTwineref",
                                     "defect_rep_minus_id_optim.g") then
                Error("K4aClassify: cannot locate defect_rep_minus_id_optim.g");
            fi;
            if not _K4A_LoadSibling("EmUnimodGroup",
                                     "krr_spectral_characters.g") then
                Error("K4aClassify: cannot locate krr_spectral_characters.g");
            fi;
            if not _K4A_LoadSibling("BuildKRRSpectralCharactersSparse",
                                     "krr_spectral_characters_sparse.g") then
                Error("K4aClassify: cannot locate krr_spectral_characters_sparse.g");
            fi;
        fi;
        # #256 family-translation: load the EU<->EP iso machinery
        # used by the m >= 4 detection path below.
        if not IsBound(TranslateSpectralDataToEPlus) then
            if not _K4A_LoadSibling("EmEPlusTranslate",
                                     "em_eplus_translate.g") then
                Error("K4aClassify: cannot locate em_eplus_translate.g");
            fi;
        fi;
        if not IsBound(RestrictTraceOnWToSubgroupHonourParent) then
            # restrict_to_subgroup.g is already loaded transitively
            # via the K4A_LoadSibling above, but the new function
            # was added to it as part of #256. Re-read just in case
            # an older copy is in scope.
            if not _K4A_LoadSibling("RestrictTraceOnWToSubgroupHonourParent",
                                     "restrict_to_subgroup.g") then
                Error("K4aClassify: cannot locate restrict_to_subgroup.g");
            fi;
        fi;
        Print("\n[K4aClassify] m = 5: computing sparse KRR spectral data ",
              "via BuildKRRSpectralCharactersSparse(5) ...\n");
        t_branch_0 := Runtime();
        sparse_data := BuildKRRSpectralCharactersSparse(5);
        t_spectral := _K4A_SecsSince(t_branch_0);
        spectral_data := rec(
            source                := "krr-sparse",
            rationale             := Concatenation(
                "At m = 5 (K-4b production target), Keller alpha is ",
                "unverified. We compute the sparse spectral data via ",
                "BuildKRRSpectralCharactersSparse(5) to actually ",
                "exercise the KRR trace machinery and record the ",
                "character multiplicities of the central twist's defect ",
                "rep Omega_0. Under the T4a downscope (epsilon = 1), ",
                "the per-H CT modular data is determined by H's own ",
                "centraliser-character functional, so the parent-G ",
                "spectral data is documented here but does not feed ",
                "into the per-branch classification arithmetic. See ",
                "the K-4b m=5 verdict note for the full discussion."),
            spectral_call_skipped := false,
            sparse                := sparse_data,
            wall_seconds          := t_spectral
        );
        Print("[K4aClassify] sparse spectral data built in ",
              t_spectral, " s.\n");
    else
        spectral_data := rec(
            source                := "untwisted_baseline",
            rationale             := Concatenation(
                "At m = ", String(m),
                ", Keller alpha = 0 (verified). Each branch uses ",
                "BuildIntertwinerDataUntwisted(branch.parent) for the ",
                "restriction. This is observationally identical to the ",
                "spectral path; the actual ",
                "BuildKRRSpectralCharacters(m) is bypassed for speed."),
            spectral_call_skipped := true,
            wall_seconds          := 0.0
        );
    fi;

    # ---- E (abelian, max elementary abelian rank m+1) branch --------
    Print("\n[K4aClassify] E branch (max elementary abelian, rank ",
          m + 1, "):\n");
    t_branch_0 := Runtime();
    ea_rec := MaximalElementaryAbelian_E_plus(m);
    Print("  |E| = ", Order(ea_rec.subgroup),
          " (expected ", 2^(m + 1), ")\n");
    # At m >= 5 (#256 family-translation path): translate the sparse
    # KRR spectral data from the EmUnimodGroup(m) family to the
    # EPlusGroup(m) family of ea_rec.parent, then use
    # RestrictTraceOnWToSubgroupHonourParent which propagates the
    # spectral multiplicities into the per-H trace functional.
    # At m < 5 the legacy path (BuildIntertwinerDataUntwisted +
    # RestrictTraceOnWToSubgroup) is retained — it is the K-4a-T7
    # anchor and changing it would invalidate #201's regression test.
    # Issue #333 followup: at omega != 0 the single-EA E branch has a
    # non-trivial kernel (e.g. e_31, e_32, e_33 at m=3 give false-negative
    # `trivial` verdicts). Route to multi-EA classifier over D-VAN's
    # minimum detecting family when a hardcoded family is available.
    if opts.lattice_source
       and (not _K4A_OmegaIsZero(opts.omega_vec))
       and _K4A_GetDVANEAFamily(m) <> fail then
        if opts.verbose then
            Print("  [E branch] routing to multi-EA classifier over ",
                  "D-VAN minimum family at m = ", m, " (issue #333).\n");
        fi;
        E_class := _K4A_ClassifyEBranchMulti(opts, m, _K4A_GetDVANEAFamily(m));
    elif m >= 5 then
        data_E := TranslateSpectralDataToEPlus(sparse_data, ea_rec.parent);
        restricted_E := RestrictTraceOnWToSubgroupHonourParent(
            data_E, ea_rec.subgroup);
        E_class := _K4A_ClassifyAbelianBranch(restricted_E, ea_rec.subgroup);
    else
        data_E := _K4A_BuildBranchData(opts, m, ea_rec.parent);
        restricted_E := _K4A_RestrictForBranch(opts, data_E,
                                                ea_rec.subgroup);
        E_class := _K4A_ClassifyAbelianBranch(restricted_E, ea_rec.subgroup);
    fi;
    t_E_branch := _K4A_SecsSince(t_branch_0);
    Print("  E-branch result: is_coboundary = ", E_class.is_coboundary,
          " (", t_E_branch, " s)\n");

    # ---- D_8 branch ------------------------------------------------
    Print("\n[K4aClassify] D_8 branch:\n");
    t_branch_0 := Runtime();
    d8_rec := D8Section_E_plus(m);
    Print("  |D_8| = ", Order(d8_rec.subgroup), " (expected 8)\n");
    if m >= 5 then
        data_D8 := TranslateSpectralDataToEPlus(sparse_data, d8_rec.parent);
        restricted_D8 := RestrictTraceOnWToSubgroupHonourParent(
            data_D8, d8_rec.subgroup);
    else
        data_D8 := _K4A_BuildBranchData(opts, m, d8_rec.parent);
        restricted_D8 := _K4A_RestrictForBranch(opts, data_D8,
                                                 d8_rec.subgroup);
    fi;
    D8_class := _K4A_ClassifyNonAbelianBranch(
        restricted_D8, d8_rec.subgroup, ClassifyOnD8);
    t_D8_branch := _K4A_SecsSince(t_branch_0);
    Print("  D_8-branch result: class_idx = ", D8_class.class_idx,
          " (trivial = 1) (", t_D8_branch, " s)\n");

    # ---- Q_8 branch ------------------------------------------------
    Print("\n[K4aClassify] Q_8 branch:\n");
    t_branch_0 := Runtime();
    q8_rec := Q8Section_E_plus(m);
    Print("  |Q_8| = ", Order(q8_rec.subgroup), " (expected 8)\n");
    if m >= 5 then
        data_Q8 := TranslateSpectralDataToEPlus(sparse_data, q8_rec.parent);
        restricted_Q8 := RestrictTraceOnWToSubgroupHonourParent(
            data_Q8, q8_rec.subgroup);
    else
        data_Q8 := _K4A_BuildBranchData(opts, m, q8_rec.parent);
        restricted_Q8 := _K4A_RestrictForBranch(opts, data_Q8,
                                                 q8_rec.subgroup);
    fi;
    Q8_class := _K4A_ClassifyNonAbelianBranch(
        restricted_Q8, q8_rec.subgroup, ClassifyOnQ8);
    t_Q8_branch := _K4A_SecsSince(t_branch_0);
    Print("  Q_8-branch result: class_idx = ", Q8_class.class_idx,
          " (trivial = 1) (", t_Q8_branch, " s)\n");

    # ---- Aggregate verdict -----------------------------------------
    # Each branch is "trivial" iff its triviality predicate is true.
    # The conjunction is the orchestrator verdict.
    #   E:    is_coboundary
    #   D_8:  class_idx = 1 (the all-zero cocycle in modular_data/8/3/)
    #   Q_8:  class_idx = 1 (the all-zero cocycle in modular_data/8/4/)
    if E_class.is_coboundary
       and D8_class.class_idx = 1
       and Q8_class.class_idx = 1 then
        trivial := true;
        verdict := "trivial";
    elif E_class.is_coboundary = fail
         or D8_class.class_idx = fail
         or Q8_class.class_idx = fail then
        trivial := fail;
        verdict := "incomplete";
    else
        trivial := false;
        verdict := "non-trivial";
    fi;

    t_total := _K4A_SecsSince(t_total_0);
    Print("\n[K4aClassify] Total wall time: ", t_total, " s\n");
    Print("[K4aClassify] Verdict: ", verdict, "\n");

    return rec(
        m              := m,
        group          := G_em,
        opts           := opts,
        spectral_data  := spectral_data,
        E_class        := E_class,
        D8_class       := D8_class,
        Q8_class       := Q8_class,
        trivial        := trivial,
        verdict        := verdict,
        timing         := rec(
            wall_seconds  := t_total,
            E_branch      := t_E_branch,
            D8_branch     := t_D8_branch,
            Q8_branch     := t_Q8_branch,
            spectral_data := spectral_data.wall_seconds
        )
    );
end;;

if IsBoundGlobal("_LogStamped") then
    _LogStamped("Loaded k4a_classify.g (K-4a-T6, issue #200).");
else
    Print("Loaded k4a_classify.g (K-4a-T6, issue #200).\n");
fi;
