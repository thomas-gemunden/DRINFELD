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
# DESIGN: multiplicity-weighted baseline, with proper restriction
# ---------------------------------------------------------------
# KRR's spectral trace_on_W (BuildKRRSpectralCharactersSparse) returns
#   spectral.trace_on_W(k, j, h) = mult_{k,j} * chi_{k,j}(h)
# where chi_{k,j} is the j-th irrep of C_G(a_k) and mult_{k,j} is the
# multiplicity in the central twist's defect rep Omega_0. For the
# trivial cocycle / untwisted baseline, mult_{k,j} = 1 (Omega_0
# decomposes as the regular C_G(-I) rep, so each chi appears once).
#
# Under the K-4a T4a downscope (epsilon = 1), the H-level CT modular
# data is determined by H's own character functional WEIGHTED by
# the inherited multiplicities. The H-side trace_on_W per (k_H, l_H)
# is therefore the sum-over-G-irreps:
#
#   trace_on_W_H(k_H, l_H, h_H)
#     = sum_{j_G} a_{l_H, j_G} * mult_{k_G, j_G} * chi_{l_H}(h_H)
#     = ( sum_{j_G} a_{l_H, j_G} * mult_{k_G, j_G} ) * chi_{l_H}(h_H)
#
# where a_{l_H, j_G} is the multiplicity of chi_{l_H} in the parent
# G-irrep chi_{j_G} restricted to C_H(a_H), computed by
# `RestrictedIrrepDecomposition`. The h-dependent factor chi_{l_H}(h_H)
# is the H-side untwisted character (`base_data.trace_on_W`); the
# scalar factor is the effective multiplicity passed through the
# inherited-mult bookkeeping.
#
# At mult = 1 everywhere (baseline) this collapses to:
#   trace_on_W_H = ( sum_{j_G} a_{l_H, j_G} ) * chi_{l_H}(h_H)
# and `sum_{j_G} a_{l_H, j_G}` is the multiplicity of chi_{l_H} in
# the regular representation of C_G(a_G) restricted to C_H(a_H).
# That is the dimension dim_chi_{l_H} * [C_G(a_G) : C_H(a_H)] ... no,
# actually, sum_{j_G} dim(chi_{j_G}) * a_{l_H, j_G} is the
# multiplicity of chi_{l_H} in the regular rep of C_G(a_G), which
# evaluates to dim(chi_{l_H}). Here we use sum_{j_G} a_{l_H, j_G}
# (not weighted by dim chi_{j_G}), which is a different scalar; it
# is the value of chi_{l_H} evaluated on the SUM of all G-irreps
# restricted to C_H, which is the indicator of the identity coset
# times |C_G(a_G)| / |C_H(a_H)|; for the K-4a m=3 anchor at mult = 1
# this is observationally equal to the previous heuristic's mult = 1
# (since each G-irrep contributed 1 to the heuristic mult lookup).
#
# IMPORTANT mult = 1 ANCHOR (m=3 K-4a regression)
# ------------------------------------------------
# When `has_mults = false` (the parent has no .multiplicities field
# at all, the K-4a m in {2, 3} default path), we MUST recover the
# original m=3 mult = 1 behaviour exactly. The previous heuristic
# computed `multiplicity_lookup(k_H, j_H) = 1` in that case, giving
# `trace_on_W_H = chi_{l_H}(h_H)`. To preserve that anchor we
# special-case the `not has_mults` branch: skip the restriction-
# decomposition entirely and return `chi_{l_H}(h_H)` directly
# (the H-untwisted baseline).
#
# IRREP-INDEX TRANSLATION (legacy field)
# ---------------------------------------
# We retain the .irrep_index_translation field (dim-matching, one
# j_G per j_H) for backward compatibility with downstream code that
# may inspect the mapping. It is no longer used by trace_on_W
# itself; trace_on_W now sums over ALL j_G via the decomposition
# matrix.
#
# PARENT'S MULTIPLICITY FIELD
# ---------------------------
# We look for parent_data.multiplicities (a list indexed by
# class_idx_G, each entry a list aligned with idx.irreps[k_G]'s
# Irr ordering). If absent or `fail` at the relevant class, we
# treat per-irrep mult as 1 within the decomposition sum.
#
# Output: A record with the same shape as RestrictTraceOnWToSubgroup
#         output, plus:
#   .trace_on_W              : multiplicity-weighted H character
#                              functional, NOT raw H untwisted.
#   .irrep_index_translation : legacy dim-matching map (kept for
#                              backward compat / inspection).
#   .irrep_decomposition     : list of length |classes(H)|, each
#                              entry is a matrix of size
#                              num_irreps_H[k_H] x num_irreps_G[k_G]
#                              giving a_{l_H, j_G} multiplicities.
#   .multiplicity_lookup     : function(k_H, j_H) -> cyclotomic, the
#                              EFFECTIVE mult factor used for that
#                              (k_H, j_H) =
#                                sum_{j_G} a_{j_H, j_G}
#                                          * mult_parent[k_G, j_G].
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

    # Multiplicity-weighted H character functional.
    #
    # Edge case: if the effective `mult` for an (k_H, l_H) is 0 (i.e.,
    # the H-irrep chi_{l_H} does not appear in the restriction of the
    # parent's spectral character Omega_0|_{C_G(a_G)} at all), the
    # trace_on_W would be 0 everywhere, including at h = identity. The
    # downstream T-matrix formula `T = chi(a) / chi(e)` would then hit
    # 0/0. To keep the modular-data computation well-defined we replace
    # a 0-effective-mult with mult=1 (i.e., fall back to the H-untwisted
    # baseline). This is the same semantics as "no spectral information
    # for this (k_H, l_H)" and matches the behaviour of the legacy
    # heuristic when its dim-matched j_G picked a 0-mult entry: it
    # returned 1 via the `mults[j_G] = fail -> 1` fallthrough.
    new_trace_on_W := function(k_H_arg, irrep_idx_H, h_H)
        local mult, chi_val;
        mult := multiplicity_lookup(k_H_arg, irrep_idx_H);
        if mult = 0 then mult := 1; fi;
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
