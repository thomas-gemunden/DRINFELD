# restrict_to_subgroup.g — K-4a-T5a (issue #199).
#
# Restrict an `intertwiner_data_G` record (the K-1 / krr_projector.g
# shape) for a finite group G to a subgroup H <= G. The output is a
# record consumable by `ProjectorFormula`, `MakeWg`, etc., that
# describes the modular data of `Z(Vec_H^{omega|_H})` under the
# H-class structure.
#
# DOWNSCOPE PER T4a (PR #206)
# ===========================
# The original Phase 2 spec
# (docs/superpowers/specs/2026-05-17-k4a-phase2-implementation-spec.md
# §T5a) asks for `RestrictEpsilonToSubgroup(epsilon_data_G, H)`
# returning a `.epsilon(class_idx_H, h) -> root of unity` callable.
# T4a's research note
# (docs/superpowers/research/2026-05-17-epsilon-extraction-from-krr.md)
# concluded that for KRR's CT case (cochain-level beta_a = 0) the
# correct gauge is the trivial cochain epsilon_a == 1: per CGR's
# remark after (5.22), the modular data is independent of the
# 1-cochain choice up to relabelling characters, and trivial is the
# canonical pick.
#
# So there is no per-element epsilon to restrict. T5a collapses to a
# CLASS-STRUCTURE HELPER: we rebuild H's own simple-object index via
# `BuildIntertwinerDataUntwisted(H)`, then add a `class_to_G` mapping
# (each H-class -> the G-class containing its rep, plus a conjugator
# in G that takes the H-rep to the G-rep) for downstream cross-checks.
# `trace_on_W` falls back to H's own `Irr(C_H(a))`-character evaluator
# (which is correct under epsilon == 1 and the omega = 0 baseline);
# `epsilon` is the constant function 1 from T4a.
#
# CONSUMERS
# =========
# K-4a-T4c (#208, BuildKRRSpectralCharacters) will produce a parent G
# version of this record with a non-trivial `trace_on_W` derived from
# the lattice intertwiners; T5a's output is the restriction to H of
# that record, suitable for feeding into the per-H modular-data
# pipeline (T5b, #198 in the issue tree).
#
# PUBLIC API
# ==========
#   RestrictTraceOnWToSubgroup(intertwiner_data_G, H)
#       -- main entry. See below for shape.
#
# RECORD SHAPE
# ============
# Returned record fields (matching the K-1 intertwiner_data contract
# plus a few diagnostic extras):
#   .group       : H (the subgroup; same semantic role as
#                  intertwiner_data_G.group)
#   .idx         : BuildSimpleIndex(H)
#   .transport   : BuildTransports(H's idx)
#   .trace_on_W  : function(class_idx_H, irrep_idx, h) -> chi(h)
#                  where chi is the irrep_idx-th irrep of C_H(a_H).
#                  This is the omega = 0 baseline; T4c may replace it
#                  for the spectral-character case (out of scope for
#                  T5a).
#   .epsilon     : function(g1, g2, a, b) -> 1
#                  (per T4a; epsilon == 1 is gauge-correct for KRR CT).
#   .class_to_G  : list, length = |classes(H)|. class_to_G[k_H] is
#                  rec(k_G        : index of the G-class containing
#                                   idx_H.reps[k_H],
#                      conj       : conj in G with
#                                   conj * idx_H.reps[k_H] * conj^-1
#                                   = idx_G.reps[k_G]).
#   .parent_G    : the G originally passed in (= intertwiner_data_G.group).
#   .parent_data : the original intertwiner_data_G, retained for
#                  downstream consumers that need to query G-level
#                  data alongside the H restriction.
#
# DEPENDENCIES
# ============
# * untwisted_modular_data.g (BuildSimpleIndex, BuildTransports, EvalIrr)
# * krr_projector.g          (BuildIntertwinerDataUntwisted)
# * quillen_detecting_subgroup.g
#                            (D8Section_E_plus, Q8Section_E_plus,
#                             MaximalElementaryAbelian_E_plus —
#                             not required for the function itself,
#                             but tests use them and the tests sit
#                             beside this file).

# ---- Load helpers using INPUT_FILENAME() pattern -----------------------
#
# Mirrors the loader pattern used by q8_classifier.g and
# kr_intertwiner_bridge.g: try `INPUT_FILENAME()` first to derive the
# sibling-script directory, then fall back to a small list of
# relative paths so callers from the wrong CWD still work.
_rts_loaded_um := IsBoundGlobal("BuildSimpleIndex");;
_rts_loaded_kp := IsBoundGlobal("BuildIntertwinerDataUntwisted");;

_rts_self := INPUT_FILENAME();;
if _rts_self <> fail and _rts_self <> "stream" then
    _rts_dir := _rts_self{[1..Length(_rts_self)
                            - Length("/restrict_to_subgroup.g")]};;
    if not _rts_loaded_um then
        _rts_um_cand := Concatenation(_rts_dir,
                                       "/untwisted_modular_data.g");;
        if IsExistingFile(_rts_um_cand) then
            Read(_rts_um_cand);
            _rts_loaded_um := true;
        fi;
    fi;
    if not _rts_loaded_kp then
        _rts_kp_cand := Concatenation(_rts_dir, "/krr_projector.g");;
        if IsExistingFile(_rts_kp_cand) then
            Read(_rts_kp_cand);
            _rts_loaded_kp := true;
        fi;
    fi;
fi;
if not _rts_loaded_um then
    for _rts_p in [ "untwisted_modular_data.g",
                    "./untwisted_modular_data.g",
                    "../untwisted_modular_data.g",
                    "extraspecial_orbifolds/scripts/untwisted_modular_data.g" ] do
        if (not _rts_loaded_um) and IsExistingFile(_rts_p) then
            Read(_rts_p);
            _rts_loaded_um := true;
        fi;
    od;
fi;
if not _rts_loaded_kp then
    for _rts_p in [ "krr_projector.g",
                    "./krr_projector.g",
                    "../krr_projector.g",
                    "extraspecial_orbifolds/scripts/krr_projector.g" ] do
        if (not _rts_loaded_kp) and IsExistingFile(_rts_p) then
            Read(_rts_p);
            _rts_loaded_kp := true;
        fi;
    od;
fi;
if not _rts_loaded_um then
    Error("restrict_to_subgroup.g: cannot locate ",
          "untwisted_modular_data.g; ensure it sits alongside this ",
          "file in extraspecial_orbifolds/scripts/.");
fi;
if not _rts_loaded_kp then
    Error("restrict_to_subgroup.g: cannot locate krr_projector.g; ",
          "ensure it sits alongside this file in ",
          "extraspecial_orbifolds/scripts/.");
fi;

# Sanity checks.
if not IsBound(BuildSimpleIndex) then
    Error("restrict_to_subgroup.g: BuildSimpleIndex not bound after ",
          "loading untwisted_modular_data.g.");
fi;
if not IsBound(BuildIntertwinerDataUntwisted) then
    Error("restrict_to_subgroup.g: BuildIntertwinerDataUntwisted not ",
          "bound after loading krr_projector.g.");
fi;


# ============================================================
# Internal: map an H-class rep to (k_G, conj) inside G.
# ============================================================
#
# Given the G-side `idx_G` (BuildSimpleIndex output) and an element
# `a_H` of G (in practice the rep of an H-class), find the G-class
# index `k_G` whose conjugacy class contains a_H, and a conjugator
# `conj` in G with
#       conj * a_H * conj^-1 = idx_G.reps[k_G].
#
# Implementation:
#   1. Iterate G-classes; the first one containing a_H is k_G.
#      (Use `a_H in idx_G.classes[k]`.)
#   2. Compute conj via `RepresentativeAction(G, a_H, idx_G.reps[k_G])`.
#
# Returns a record rec(k_G := ..., conj := ...).
# Errors if a_H is not in any G-class (shouldn't happen if H <= G).
_RTS_FindGClassOf := function(idx_G, a_H, G)
    local k, conj;
    for k in [1..Length(idx_G.classes)] do
        if a_H in idx_G.classes[k] then
            # RepresentativeAction returns g in G with
            #   g * a_H * g^-1 = idx_G.reps[k]
            # under GAP's default left-action convention for
            # conjugation; on group elements, the action is
            #   ConjugacyClass action: x ^ g = g^-1 x g
            # so RepresentativeAction(G, src, dst, OnPoints) finds g
            # with src ^ g = dst, i.e. g^-1 src g = dst. We want
            # `conj * a_H * conj^-1 = idx_G.reps[k]`, i.e.
            # `a_H ^ conj^-1 = idx_G.reps[k]`, so conj^-1 is what
            # RepresentativeAction returns, hence:
            conj := RepresentativeAction(G, a_H, idx_G.reps[k]);
            if conj = fail then
                Error("_RTS_FindGClassOf: RepresentativeAction(G, ",
                      a_H, ", ", idx_G.reps[k], ") = fail despite ",
                      "a_H in class ", k, ". GAP convention mismatch?");
            fi;
            # Confirm: RepresentativeAction returns g with a_H ^ g
            # = idx_G.reps[k], i.e. g^-1 a_H g = idx_G.reps[k], so
            # the conjugator we want (conj satisfying
            # conj * a_H * conj^-1 = idx_G.reps[k]) is g^-1.
            conj := conj ^ -1;
            return rec(k_G := k, conj := conj);
        fi;
    od;
    Error("_RTS_FindGClassOf: element ", a_H,
          " is not in any G-conjugacy class.");
end;;


# ============================================================
# Public: RestrictTraceOnWToSubgroup
# ============================================================
#
# Restrict intertwiner_data_G to a subgroup H. See header for
# semantics and downscope rationale.
#
# Inputs:
#   intertwiner_data_G : record from `BuildIntertwinerDataUntwisted(G)`
#                        (or T4c's `BuildKRRSpectralCharacters(m)`),
#                        with fields .group, .idx, .transport,
#                        .trace_on_W, .epsilon.
#   H                  : a subgroup of intertwiner_data_G.group.
#
# Returns a record (see file header).
#
# Edge cases:
#   * H = G: the result is equivalent to intertwiner_data_G (same
#     class structure, identity conj maps).
#   * H abelian: every H-class has size 1, conjugators are in C_G(a)
#     (typically the identity).
#   * Q_8 / D_8 sections of E_+(m): G has more conjugating elements
#     than H, so the H-conjugacy class of a is a subset of the
#     G-conjugacy class of a. Hence each H-class sits inside exactly
#     one G-class, possibly along with other H-classes (when the
#     G-class splits into multiple H-orbits). The class_to_G map is
#     well-defined (every H-class maps to a unique G-class) but
#     many-to-one on the k_G side.
RestrictTraceOnWToSubgroup := function(intertwiner_data_G, H)
    local G, idx_H, transport_H, idx_G, class_to_G, k_H, a_H, mapping,
          base_data, gens_H, bad_gen;
    G := intertwiner_data_G.group;
    # Element-level subgroup check. We do NOT use `IsSubgroup(G, H)`:
    # for groups built by `ExtraspecialGroup(...)` etc., two calls
    # return groups in DIFFERENT GAP families even though they are
    # mathematically isomorphic, and `IsSubgroup` returns false even
    # when H's elements actually appear inside the matrix/PC realisation
    # of G. The element-level test below (generators of H all in G) is
    # the operational condition `_RTS_FindGClassOf` needs.
    gens_H := GeneratorsOfGroup(H);
    bad_gen := First(gens_H, g -> not (g in G));
    if bad_gen <> fail then
        Error("RestrictTraceOnWToSubgroup: H has a generator ", bad_gen,
              " not in intertwiner_data_G.group. If H came from ",
              "D8Section_E_plus(m) etc., use the rec's `.parent` field ",
              "as G to ensure family compatibility.");
    fi;
    # Build H's own simple-object index via the same machinery as the
    # parent-G record. This gives us H's own (a_H, chi) labelling,
    # transports, etc., independent of G's.
    base_data := BuildIntertwinerDataUntwisted(H);
    idx_H := base_data.idx;
    transport_H := base_data.transport;
    # Build the H-class -> (G-class, conjugator) mapping.
    idx_G := intertwiner_data_G.idx;
    class_to_G := [];
    for k_H in [1..Length(idx_H.reps)] do
        a_H := idx_H.reps[k_H];
        mapping := _RTS_FindGClassOf(idx_G, a_H, G);
        Add(class_to_G, mapping);
    od;
    return rec(
        group        := H,
        idx          := idx_H,
        transport    := transport_H,
        trace_on_W   := base_data.trace_on_W,
        epsilon      := base_data.epsilon,
        class_to_G   := class_to_G,
        parent_G     := G,
        parent_data  := intertwiner_data_G
    );
end;;


# ============================================================
# Public: RestrictTraceOnWToSubgroupHonourParent  (#256)
# ============================================================
#
# Variant of RestrictTraceOnWToSubgroup that PROPAGATES the parent's
# spectral multiplicities into the H-side restricted record. The
# H-character functional itself stays H's untwisted (which is the
# mathematically correct chi_H(h) value); the multiplicity factor
# mult from the parent's KRR spectral data is applied as a scalar
# weighting per H-class / H-irrep.
#
# WHY THIS EXISTS
# ---------------
# The original RestrictTraceOnWToSubgroup (per K-4a-T5a downscope)
# discards the parent's trace_on_W in favour of H's untwisted
# baseline. This was correct under the omega = 0 / epsilon = 1
# downscope for K-4a-T5b (#198), but it has the side-effect that any
# downstream `ComputeCTModularData(restricted, H)` produces
# H-untwisted modular data regardless of the parent's spectral
# characters. At m = 5 (K-4b production target) this is precisely
# the structural-trivial caveat documented in
# docs/superpowers/research/2026-05-17-k4b-m5-verdict.md Section 4.4.
#
# DESIGN: multiplicity-weighted baseline
# ---------------------------------------
# KRR's spectral trace_on_W (BuildKRRSpectralCharactersSparse) returns
#   spectral.trace_on_W(k, j, h) = mult_{k,j} * chi_{k,j}(h)
# where chi_{k,j} is the j-th irrep of C_G(a_k) and mult_{k,j} is the
# multiplicity in the central twist's defect rep Omega_0. For the
# trivial cocycle / untwisted baseline, mult_{k,j} = 1 (Omega_0
# decomposes as the regular C_G(-I) rep, so each chi appears once).
#
# Under the K-4a T4a downscope (epsilon = 1), the H-level CT modular
# data is determined by H's own character functional WEIGHTED by
# the inherited multiplicities. The H-side trace_on_W therefore is
#   trace_on_W_H(k_H, j_H, h_H) = mult_{k_G, j_G} * chi_H[j_H](h_H)
# where k_G = class_to_G[k_H].k_G is the G-class containing a_H, and
# j_G is the irrep_idx_G "associated" to j_H by the
# irrep_index_translation table (dimension matching, see below).
#
# This is the right object because:
#   * For omega = 0 (mult = 1 everywhere), it reduces to H's untwisted
#     character, recovering the K-4a-T5a baseline.
#   * For a non-trivial mult inherited from KRR's central-twist
#     Omega_0 decomposition, the per-irrep multiplicities propagate
#     to the H-side T-matrix entries (T = chi(a)/chi(e), so a
#     mult factor cancels in the ratio — but it survives in any
#     spectral weighting that the downstream pipeline applies).
#
# IRREP-INDEX TRANSLATION
# -----------------------
# We pre-compute irrep_idx_H -> irrep_idx_G by dimension matching.
# For abelian C_H(a_H) (which holds for the rank-(m+1) elementary
# abelian E-branch and the abelian centralisers of non-central
# classes in D_8 / Q_8) all irreps are linear (dim 1), so the
# match is unambiguous up to the GAP enumeration order.
#
# For non-abelian centralisers and non-linear irreps the matching
# is heuristic. The mult-weighted design above means that whenever
# mult = 1 (the baseline) the irrep index choice does not affect
# the trace value, so the choice is mathematically inert in the
# omega = 0 case. For non-trivial mult, the choice picks WHICH
# G-irrep's multiplicity to inherit — a follow-up may need a
# more careful per-irrep restriction-decomposition.
#
# PARENT'S MULTIPLICITY FIELD
# ---------------------------
# We look for parent_data.multiplicities (a list indexed by
# class_idx_G, each entry a list aligned with idx.irreps[k_G]'s
# Irr ordering). If absent or `fail` at the relevant class, we
# fall back to mult = 1.
#
# Output: A record with the same shape as RestrictTraceOnWToSubgroup
#         output, plus:
#   .trace_on_W            : multiplicity-weighted H character
#                             functional, NOT raw H untwisted.
#   .irrep_index_translation
#                          : list of length |classes(H)|, each entry
#                             is a list of length num_irreps_H[k_H]
#                             mapping irrep_idx_H to irrep_idx_G.
#   .multiplicity_lookup   : function(k_H, j_H) -> cyclotomic, the
#                             mult factor used for that (k_H, j_H).
RestrictTraceOnWToSubgroupHonourParent := function(intertwiner_data_G, H)
    local G, idx_H, transport_H, idx_G, class_to_G, k_H, a_H, mapping,
          base_data, gens_H, bad_gen, parent_data, irrep_index_translation,
          k_G_idx, irr_H, irr_G, j_H,
          new_trace_on_W, new_epsilon, multiplicity_lookup,
          has_mults;
    G := intertwiner_data_G.group;
    gens_H := GeneratorsOfGroup(H);
    bad_gen := First(gens_H, g -> not (g in G));
    if bad_gen <> fail then
        Error("RestrictTraceOnWToSubgroupHonourParent: H has a generator ",
              bad_gen, " not in intertwiner_data_G.group.");
    fi;
    base_data := BuildIntertwinerDataUntwisted(H);
    idx_H := base_data.idx;
    transport_H := base_data.transport;
    idx_G := intertwiner_data_G.idx;
    parent_data := intertwiner_data_G;

    # H-class -> G-class, conjugator.
    class_to_G := [];
    for k_H in [1..Length(idx_H.reps)] do
        a_H := idx_H.reps[k_H];
        mapping := _RTS_FindGClassOf(idx_G, a_H, G);
        Add(class_to_G, mapping);
    od;

    # Per-H-class irrep_idx_H -> irrep_idx_G translation table
    # via dimension matching.
    irrep_index_translation := [];
    for k_H in [1..Length(idx_H.reps)] do
        k_G_idx := class_to_G[k_H].k_G;
        _EnsureClassData(idx_H, k_H);
        _EnsureClassData(idx_G, k_G_idx);
        irr_H := idx_H.irreps[k_H];
        irr_G := idx_G.irreps[k_G_idx];
        Add(irrep_index_translation,
            List([1..Length(irr_H)], j_H ->
                (function()
                    local d_H, found;
                    d_H := irr_H[j_H][1];
                    found := First([1..Length(irr_G)],
                                    j_G -> irr_G[j_G][1] = d_H);
                    if found = fail then
                        return j_H;
                    fi;
                    return found;
                end)()));
    od;

    # Does the parent carry .multiplicities (the KRR spectral builder
    # marker)? If so we use it; otherwise we treat mult = 1 (the
    # untwisted baseline).
    has_mults := IsBound(parent_data.multiplicities);
    multiplicity_lookup := function(k_H_arg, j_H_arg)
        local k_G, j_G, mults;
        if not has_mults then return 1; fi;
        k_G := class_to_G[k_H_arg].k_G;
        mults := parent_data.multiplicities[k_G];
        if mults = fail or mults = [] then return 1; fi;
        j_G := irrep_index_translation[k_H_arg][j_H_arg];
        if j_G < 1 or j_G > Length(mults) then return 1; fi;
        if mults[j_G] = fail then return 1; fi;
        return mults[j_G];
    end;

    # Multiplicity-weighted H character functional.
    new_trace_on_W := function(k_H_arg, irrep_idx_H, h_H)
        local mult, chi_val;
        mult := multiplicity_lookup(k_H_arg, irrep_idx_H);
        chi_val := base_data.trace_on_W(k_H_arg, irrep_idx_H, h_H);
        return mult * chi_val;
    end;

    new_epsilon := function(g1, g2, a, b)
        return parent_data.epsilon(g1, g2, a, b);
    end;

    return rec(
        group        := H,
        idx          := idx_H,
        transport    := transport_H,
        trace_on_W   := new_trace_on_W,
        epsilon      := new_epsilon,
        class_to_G   := class_to_G,
        irrep_index_translation := irrep_index_translation,
        multiplicity_lookup := multiplicity_lookup,
        parent_G     := G,
        parent_data  := parent_data,
        # Diagnostic: keep H's untwisted baseline available for
        # comparison.
        baseline_trace_on_W := base_data.trace_on_W,
        baseline_epsilon := base_data.epsilon
    );
end;;
