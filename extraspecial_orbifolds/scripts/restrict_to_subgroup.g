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
# Public: RestrictedIrrepDecomposition (#275)
# ============================================================
#
# Compute the multiplicities a_l of the H-irreps in the restriction
# of a G-irrep to the subgroup H, where here "G" is the parent
# centraliser C_G(a_G) and "H" is the subgroup centraliser C_H(a_H),
# with a_G = conj * a_H * conj^-1.
#
# MATH
# ----
# For each parent G-class k_G with rep a_G and H-class k_H with rep
# a_H = conj^-1 * a_G * conj (equivalently a_G = conj * a_H * conj^-1
# given the convention in `_RTS_FindGClassOf`), the parent character
# chi_{j_G} in Irr(C_G(a_G)) restricts to C_H(a_H) via the embedding
#
#   phi : C_H(a_H) -> C_G(a_G),  h -> conj * h * conj^-1.
#
# C_H(a_H) is a subgroup of C_G(a_H), and conjugation by `conj` maps
# C_G(a_H) onto C_G(a_G) (since x*a_H = a_H*x  iff
# conj*x*a_H*conj^-1 = conj*a_H*x*conj^-1, i.e.
# (conj*x*conj^-1) * a_G = a_G * (conj*x*conj^-1)).  So
# phi(C_H(a_H)) is indeed a subgroup of C_G(a_G).
#
# The character chi_{j_G} restricted via phi decomposes in
# Irr(C_H(a_H)):
#
#   (Res_{C_H} chi_{j_G})(h) := chi_{j_G}(phi(h))
#                             = sum_{l=1}^{|Irr(C_H(a_H))|}
#                                   a_l * chi_{l_H}(h)
#
# where the multiplicity a_l is given by the inner product on
# C_H(a_H):
#
#   a_l = <Res chi_{j_G}, chi_{l_H}>_{C_H}
#       = (1 / |C_H(a_H)|)
#         * sum_{h in C_H(a_H)}
#               chi_{j_G}(phi(h)) * conj_complex(chi_{l_H}(h))
#       = (1 / |C_H(a_H)|)
#         * sum_{H-classes [h] in C_H(a_H)}
#               |[h]| * chi_{j_G}(phi(rep_h)) * \bar{chi_{l_H}(rep_h)}
#
# Each a_l is a NON-NEGATIVE INTEGER (the multiplicity of chi_{l_H}
# in Res chi_{j_G}).
#
# CONVENTIONS
# -----------
# * `idx_G` / `idx_H`: BuildSimpleIndex(Lazy) records.
# * `k_G`, `k_H`: class indices into idx_G / idx_H.
# * `conj`: conjugator with conj * a_H * conj^-1 = a_G, drawn from
#   class_to_G[k_H].conj (which is what _RTS_FindGClassOf returns).
# * `j_G`: parent-irrep index into idx_G.irreps[k_G].
#
# RETURNS: a list of length |Irr(C_H(a_H))| = idx_H.num_irreps[k_H]
#          giving a_l for each l_H = 1..num_irreps[k_H].
#
# Each a_l is computed as an INTEGER (cyclotomic-arithmetic exact;
# no floats). If a_l is non-integral up to rounding, an Error is
# raised: that means either phi is not actually into C_G(a_G), or
# the character/class indexing is inconsistent.
RestrictedIrrepDecomposition := function(idx_G, idx_H, k_G, k_H, conj)
    local C_H, ct_H, cc_H, irr_H, num_irreps_H, n_classes_H,
          chi_G_phi_values, j, rep_h, phi_rep, class_size_h,
          cls_H, normaliser, cls_idx_G, decomposition_fn;
    _EnsureClassData(idx_G, k_G);
    _EnsureClassData(idx_H, k_H);
    C_H := idx_H.centralisers[k_H];
    ct_H := idx_H.ct_centraliser[k_H];
    cc_H := idx_H.cc_centraliser[k_H];
    irr_H := idx_H.irreps[k_H];
    num_irreps_H := idx_H.num_irreps[k_H];
    n_classes_H := Length(cc_H);
    normaliser := Order(C_H);

    # Pre-compute the class index in C_G(a_G) of phi(rep_h) for each
    # conjugacy class [h] of C_H(a_H), and also |[h]|. The
    # phi-images are used by every j_G in the per-irrep decomposition
    # so we amortise the conjugation + class-lookup work.
    chi_G_phi_values := [];
    class_size_h := [];
    for j in [1..n_classes_H] do
        cls_H := cc_H[j];
        rep_h := Representative(cls_H);
        phi_rep := conj * rep_h * conj^-1;
        # ClassIndexInCentraliser auto-materialises idx_G data for k_G.
        cls_idx_G := ClassIndexInCentraliser(idx_G, k_G, phi_rep);
        Add(chi_G_phi_values, cls_idx_G);
        Add(class_size_h, Size(cls_H));
    od;

    # Helper closure: given j_G, return the length-num_irreps_H
    # vector of multiplicities a_l.
    decomposition_fn := function(j_G_arg)
        local chi_G_vals, t, val_chi_g, val_chi_l, acc, l_H, chi_l_H,
              result;
        # chi_{j_G}(phi(rep_h)) per H-class, precomputed.
        chi_G_vals := List([1..n_classes_H],
            t -> idx_G.irreps[k_G][j_G_arg][chi_G_phi_values[t]]);
        result := [];
        for l_H in [1..num_irreps_H] do
            acc := 0;
            chi_l_H := irr_H[l_H];
            for t in [1..n_classes_H] do
                val_chi_g := chi_G_vals[t];
                val_chi_l := chi_l_H[t];
                acc := acc + class_size_h[t] * val_chi_g
                            * ComplexConjugate(val_chi_l);
            od;
            acc := acc / normaliser;
            # Sanity check: must be a non-negative integer.
            if not IsInt(acc) then
                Error("RestrictedIrrepDecomposition: ",
                      "non-integer multiplicity ", acc,
                      " for (k_G=", k_G, ", k_H=", k_H,
                      ", j_G=", j_G_arg, ", l_H=", l_H,
                      "). Likely cause: conj does not actually ",
                      "embed C_H(a_H) into C_G(a_G), or the ",
                      "characters disagree.");
            fi;
            if acc < 0 then
                Error("RestrictedIrrepDecomposition: ",
                      "negative multiplicity ", acc,
                      " for (k_G=", k_G, ", k_H=", k_H,
                      ", j_G=", j_G_arg, ", l_H=", l_H,
                      "). This should never happen for true ",
                      "characters.");
            fi;
            Add(result, acc);
        od;
        return result;
    end;

    return rec(
        # Per-H-class phi-image class index in C_G(a_G).
        phi_class_index_G := chi_G_phi_values,
        # Per-H-class size (for the inner-product weighting).
        h_class_sizes := class_size_h,
        # Helper closure: see above.
        decomposition := decomposition_fn
    );
end;;

# ============================================================
# Public: RestrictTraceOnWToSubgroupHonourParent  (#256, #275)
# ============================================================
#
# Variant of RestrictTraceOnWToSubgroup that exposes the parent's
# spectral multiplicities as a DIAGNOSTIC field on the restricted
# record. The trace_on_W functional returned by this variant is the
# H-untwisted baseline character (chi_{l_H}(h_H)) -- it is *not*
# scaled by the parent's spectral multiplicities.
#
# NORMALISATION RECONCILIATION (#275)
# -----------------------------------
# An earlier iteration of this function (the K-4 mult>0 predecessor)
# multiplied the H-side trace by an "effective mult" computed from
# the parent's spectral data via the restriction-decomposition
# formula
#   mult_eff(k_H, l_H) = sum_{j_G} a_{l_H, j_G} * mult_parent[k_G, j_G].
# That scaling pushed the CGR/Bantay S-formula at
# `_CTComputeSBlock` into a NORMALISATION different from the one
# used by the Gruen/Morrison stored (S, T) tables in
# `modular_data/{8/3, 8/4, ...}`: each S entry picked up a
# mult_i * mult_j factor that the stored tables do not have. The
# `JointPermutationMatcher` (which compares per-entry up to a
# permutation) therefore failed to detect equivalence even on cases
# where alpha was a coboundary, producing spurious "non-trivial"
# or "fail" verdicts.
#
# The CORRECT semantics per CGR/Bantay (and the K-4a-T4a research
# note `2026-05-17-epsilon-extraction-from-krr.md` §5.5) is that
# `mult_chi` is a CATEGORICAL LABELING -- it counts how many copies
# of chi-isotypic component appear in Omega_0 -- and does NOT enter
# the S/T formulae as a scalar weight. Each distinct (a, chi)
# simple has CGR S/T entries built from chi alone:
#   T_{(a, chi)} = chi(a) / chi(e),
#   S_{(a_i, chi_k), (a_j, chi_l)}
#     = (1/|H|) sum_{ab=ba, a in cl_i, b in cl_j}
#                eps * chi_k(b_tilde)^* * chi_l(a_tilde)^*.
# The multiplicities are useful diagnostically (e.g. to detect that
# omega|_H is genuinely non-trivial by mult_chi = 0 cases) but are
# not part of the S/T arithmetic.
#
# At m = 3 (the K-4a-T7 anchor) the parent path uses
# `RestrictTraceOnWToSubgroup` (the non-honour variant), so this
# change is invisible there. At m = 5 (K-4a production target) the
# orchestrator uses this variant; with the scaling stripped, the
# CT modular data on each detecting subgroup is in the same
# normalisation as the stored Gruen/Morrison tables and the matcher
# can correctly classify alpha|_H against them.
#
# CALLERS WHO NEED THE MULTIPLICITY INFORMATION
# ---------------------------------------------
# Consumers that want to INSPECT the spectral structure (for
# diagnostics, debugging, or to detect mult=0 simples) can read
# `multiplicity_lookup(k_H, j_H)` on the returned record. The
# trace_on_W functional itself ignores this.
#
# IRREP-INDEX TRANSLATION (legacy field)
# ---------------------------------------
# We retain the .irrep_index_translation field (dim-matching, one
# j_G per j_H) for backward compatibility with downstream code that
# may inspect the mapping. It is no longer used by trace_on_W
# itself.
#
# PARENT'S MULTIPLICITY FIELD
# ---------------------------
# We look for parent_data.multiplicities (a list indexed by
# class_idx_G, each entry a list aligned with idx.irreps[k_G]'s
# Irr ordering). If absent or `fail` at the relevant class, we
# treat per-irrep mult as 1 within the decomposition sum (only used
# by the diagnostic multiplicity_lookup).
#
# Output: A record with the same shape as RestrictTraceOnWToSubgroup
#         output, plus:
#   .trace_on_W              : H-untwisted character functional
#                              (chi_{l_H}(h_H); UNCHANGED from
#                              base_data.trace_on_W). See the
#                              normalisation reconciliation note
#                              above for why this dropped the mult
#                              scaling.
#   .irrep_index_translation : legacy dim-matching map (kept for
#                              backward compat / inspection).
#   .irrep_decomposition     : list of length |classes(H)|, each
#                              entry is a matrix of size
#                              num_irreps_H[k_H] x num_irreps_G[k_G]
#                              giving a_{l_H, j_G} multiplicities
#                              (diagnostic; not used by trace_on_W).
#   .multiplicity_lookup     : function(k_H, j_H) -> cyclotomic, the
#                              EFFECTIVE mult factor for inspection:
#                                sum_{j_G} a_{j_H, j_G}
#                                          * mult_parent[k_G, j_G].
#                              Diagnostic only.
RestrictTraceOnWToSubgroupHonourParent := function(intertwiner_data_G, H)
    local G, idx_H, transport_H, idx_G, class_to_G, k_H, a_H, mapping,
          base_data, gens_H, bad_gen, parent_data, irrep_index_translation,
          k_G_idx, irr_H, irr_G, j_H,
          new_trace_on_W, new_epsilon, multiplicity_lookup,
          has_mults, irrep_decomposition, decomp_rec, num_irreps_G,
          dec_matrix, j_G_loop, row, conj_k;
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

    # Does the parent carry .multiplicities (the KRR spectral builder
    # marker)? If so we use it; otherwise we treat mult = 1 (the
    # untwisted baseline). When NOT present, we bypass the
    # decomposition entirely to recover the original mult = 1 (no-op)
    # behaviour at the K-4a m in {2, 3} anchor.
    has_mults := IsBound(parent_data.multiplicities);

    # Per-H-class irrep_idx_H -> irrep_idx_G translation table
    # via dimension matching (LEGACY, kept for backward compat).
    irrep_index_translation := [];
    irrep_decomposition := [];
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
        # Build the proper restriction decomposition matrix only when
        # has_mults is true AND parent_data.multiplicities[k_G] is a
        # real (non-`fail`, non-empty) list. At mult = 1 / no-mults
        # or when the parent's mults entry at this k_G is `fail` we
        # short-circuit the multiplicity_lookup to 1 and avoid the
        # ~O(num_irreps_G * num_classes_C_H) decomposition cost. At
        # m=5 the parent has 1025 classes and only one (the central)
        # carries a real mults list, so this short-circuit is the
        # difference between O(1) class touches and O(num_classes) for
        # the restriction-decomposition build.
        if has_mults
           and k_G_idx <= Length(parent_data.multiplicities)
           and parent_data.multiplicities[k_G_idx] <> fail
           and parent_data.multiplicities[k_G_idx] <> [] then
            conj_k := class_to_G[k_H].conj;
            decomp_rec := RestrictedIrrepDecomposition(
                idx_G, idx_H, k_G_idx, k_H, conj_k);
            num_irreps_G := idx_G.num_irreps[k_G_idx];
            dec_matrix := [];
            for j_G_loop in [1..num_irreps_G] do
                # decomp_rec.decomposition(j_G) returns length
                # num_irreps_H. We store as a matrix indexed
                # [l_H][j_G] so that dec_matrix[l_H] is the per-G-irrep
                # multiplicity vector for the l_H-th H-irrep.
                row := decomp_rec.decomposition(j_G_loop);
                # row is length num_irreps_H; we want to add this
                # as a column at index j_G_loop.
                for j_H in [1..Length(row)] do
                    if not IsBound(dec_matrix[j_H]) then
                        dec_matrix[j_H] := [];
                    fi;
                    dec_matrix[j_H][j_G_loop] := row[j_H];
                od;
            od;
            Add(irrep_decomposition, dec_matrix);
        else
            Add(irrep_decomposition, fail);
        fi;
    od;

    # multiplicity_lookup(k_H, j_H):
    #   If has_mults = false: return 1 (matches old behaviour and the
    #                         baseline mult=1 case at the K-4a m in
    #                         {2, 3} anchor).
    #   If has_mults = true and parent_data.multiplicities[k_G] = fail
    #     (or absent): return 1. Rationale: the sparse builder marks
    #     non-central classes with `fail`, meaning "no spectral
    #     character is computed here; the trivial baseline applies".
    #     The trivial baseline at H is `chi_{l_H}(h_H)` (mult = 1).
    #     This matches the OLD dim-matching heuristic's behaviour at
    #     non-central classes and preserves the m=3 anchor in the
    #     event that some downstream caller sets `.multiplicities`
    #     with only the central entry populated.
    #   If has_mults = true and parent_data.multiplicities[k_G] is a
    #     real list of cyclotomics: return
    #       sum_{j_G} mult[k_G, j_G] * a_{j_H, j_G}
    #     where a is the restriction-decomposition matrix. Per-irrep
    #     `fail` entries inside the list are treated as 0 (no
    #     contribution from that j_G), since `fail` here means
    #     "this irrep was not computed" which is operationally the
    #     same as zero multiplicity in the central twist's defect
    #     representation Omega_0 at that j_G.
    multiplicity_lookup := function(k_H_arg, j_H_arg)
        local k_G, mults, mat, total, j_G;
        if not has_mults then return 1; fi;
        k_G := class_to_G[k_H_arg].k_G;
        mat := irrep_decomposition[k_H_arg];
        if mat = fail then return 1; fi;
        # Parent-side mults entry can be:
        #   * fail / absent / []  -> baseline (mult = 1, skip decomp).
        #   * a list of cyclotomics -> use the decomposition formula.
        if k_G > Length(parent_data.multiplicities) then return 1; fi;
        mults := parent_data.multiplicities[k_G];
        if mults = fail or mults = [] then return 1; fi;
        total := 0;
        for j_G in [1..Length(mat[j_H_arg])] do
            if j_G > Length(mults) then
                # mults shorter than expected; treat tail as 0 (no
                # contribution).
                continue;
            elif mults[j_G] = fail then
                # Per-irrep `fail` inside a real list: treat as 0.
                continue;
            else
                total := total + mat[j_H_arg][j_G] * mults[j_G];
            fi;
        od;
        return total;
    end;

    # H character functional WITHOUT spectral multiplicity scaling
    # (#275 normalisation reconciliation).
    #
    # PREVIOUS BEHAVIOUR (incorrect): the predecessor implementation
    # returned `mult * chi_val`, where `mult` was the effective
    # multiplicity sum_{j_G} a_{j_H, j_G} * mult_parent[k_G, j_G].
    # This scaling broke the matcher comparison against the stored
    # (S, T) tables in modular_data/{8/3, 8/4, ...}, because those
    # tables were generated by Gruen/Morrison using the unscaled
    # Bantay/CGR S-formula with chi (not mult * chi). Concretely,
    # the S-block sweep at _CTComputeSBlock computes
    #   M[k][l] += eps * conj(trace_on_W(i,k,b_tilde))
    #                  * conj(trace_on_W(j,l,a_tilde))
    # which under mult-scaling picks up a mult_i * mult_j factor per
    # (k_H, l_H) pair, so S entries differ from the stored data by
    # this product. The T-matrix is invariant (T = chi_a / chi_e,
    # and mult cancels in the ratio).
    #
    # CORRECT INTERPRETATION (per CGR/Bantay and the K-4a-T4a research
    # note 2026-05-17-epsilon-extraction-from-krr.md §5.5): the
    # CGR S-formula uses the irreducible character chi_{i,k} on
    # C_H(a) directly, not the spectral trace functional. The KRR
    # spectral data records mult_chi as a CATEGORICAL LABELING that
    # counts how many isotypic copies of chi appear in Omega_0; it
    # does NOT enter the modular-data S/T formulae as a scalar weight.
    # Per the K-4a-T6 design (k4a_classify.g) the matcher compares
    # against Gruen/Morrison's unscaled tables, so the H trace must
    # be unscaled.
    #
    # The `multiplicity_lookup` callable is retained as a diagnostic
    # so consumers can inspect the parent's spectral structure if
    # needed; trace_on_W ignores it.
    new_trace_on_W := function(k_H_arg, irrep_idx_H, h_H)
        return base_data.trace_on_W(k_H_arg, irrep_idx_H, h_H);
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
        irrep_decomposition := irrep_decomposition,
        multiplicity_lookup := multiplicity_lookup,
        parent_G     := G,
        parent_data  := parent_data,
        # Diagnostic: keep H's untwisted baseline available for
        # comparison.
        baseline_trace_on_W := base_data.trace_on_W,
        baseline_epsilon := base_data.epsilon
    );
end;;
