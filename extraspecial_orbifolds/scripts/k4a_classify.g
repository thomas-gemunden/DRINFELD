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

# Given an `H` (abelian subgroup) and a restricted intertwiner_data,
# compute the CT modular data and the H-untwisted modular data, then
# call JointPermutationMatcher. Return rec(is_abelian, is_coboundary,
# match, modular_ct, modular_untwisted, wall_seconds).
_K4A_ClassifyAbelianBranch := function(restricted, H)
    local t0, modular_ct, modular_untwisted, match;
    t0 := Runtime();
    modular_ct := ComputeCTModularData(restricted, H);
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
    modular_ct := ComputeCTModularData(restricted, H);
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


# ---- Public: K4aClassify(m) -------------------------------------------

K4aClassify := function(m)
    local n_max_supported, t_total_0, G_em, ea_rec, d8_rec, q8_rec,
          data_E, data_D8, data_Q8, restricted_E, restricted_D8,
          restricted_Q8, E_class, D8_class, Q8_class, trivial, verdict,
          spectral_data, sparse_data, t_branch_0, t_E_branch,
          t_D8_branch, t_Q8_branch, t_total, t_spectral;

    # ---- Argument validation -----------------------------------------
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
    # Build intertwiner_data on the SAME EPlusGroup(m) instance that
    # constructed ea_rec.subgroup, so the family-equality check in
    # RestrictTraceOnWToSubgroup passes. At m = 5 the parent group has
    # 1025 conjugacy classes; the eager `BuildIntertwinerDataUntwisted`
    # builds all 1025 CharacterTables up front (~100 s wall), whereas
    # the lazy variant defers per-class CT builds (~34 s wall on the
    # same hardware). Use lazy when m >= 5.
    if m >= 5 then
        data_E := BuildIntertwinerDataUntwistedLazy(ea_rec.parent);
    else
        data_E := BuildIntertwinerDataUntwisted(ea_rec.parent);
    fi;
    restricted_E := RestrictTraceOnWToSubgroup(data_E, ea_rec.subgroup);
    E_class := _K4A_ClassifyAbelianBranch(restricted_E, ea_rec.subgroup);
    t_E_branch := _K4A_SecsSince(t_branch_0);
    Print("  E-branch result: is_coboundary = ", E_class.is_coboundary,
          " (", t_E_branch, " s)\n");

    # ---- D_8 branch ------------------------------------------------
    Print("\n[K4aClassify] D_8 branch:\n");
    t_branch_0 := Runtime();
    d8_rec := D8Section_E_plus(m);
    Print("  |D_8| = ", Order(d8_rec.subgroup), " (expected 8)\n");
    if m >= 5 then
        data_D8 := BuildIntertwinerDataUntwistedLazy(d8_rec.parent);
    else
        data_D8 := BuildIntertwinerDataUntwisted(d8_rec.parent);
    fi;
    restricted_D8 := RestrictTraceOnWToSubgroup(data_D8, d8_rec.subgroup);
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
        data_Q8 := BuildIntertwinerDataUntwistedLazy(q8_rec.parent);
    else
        data_Q8 := BuildIntertwinerDataUntwisted(q8_rec.parent);
    fi;
    restricted_Q8 := RestrictTraceOnWToSubgroup(data_Q8, q8_rec.subgroup);
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

Print("Loaded k4a_classify.g (K-4a-T6, issue #200).\n");
