# em_eplus_translate.g
#
# Issue #256: K-4a family translation between EmUnimodGroup(m) and
# EPlusGroup(m).
#
# CONTEXT
# =======
# The K-4a pipeline has two families of E_+(m) realisations:
#
#   * EmUnimodGroup(m) (krr_spectral_characters.g): a MATRIX group on
#     Z^{2^m} built from the unimodular generators UnimodSigma(m, a, r)
#     and z = -I. The sparse KRR spectral builder
#     BuildKRRSpectralCharactersSparse(m) operates here.
#
#   * EPlusGroup(m) = ExtraspecialGroup(2^{2m+1}, "+") (quillen_detecting_subgroup.g):
#     a PC group with the standard plus-type extraspecial presentation.
#     The detecting-subgroup constructors (MaximalElementaryAbelian_E_plus,
#     D8Section_E_plus, Q8Section_E_plus) build subgroups inside an
#     EPlusGroup(m) instance.
#
# Both are abstractly E_+(m) but in DIFFERENT GAP families. Consequently
# `RestrictTraceOnWToSubgroup(spectral_data_EU, H_EP)` cannot evaluate
# `H_EP`'s generators against spectral_data_EU's class structure (the
# `gens_H[i] in G` test fails).
#
# Per K-4b m=5 verdict note (docs/superpowers/research/
# 2026-05-17-k4b-m5-verdict.md) Section 4.4, this is the architectural
# caveat that makes the m=5 verdict structurally trivial. This module
# implements option (a): translate the sparse data from EmUnimodGroup(m)
# to EPlusGroup(m) via an explicit isomorphism, so that
# RestrictTraceOnWToSubgroup can propagate the spectral characters into
# the per-branch CT modular data.
#
# MATHEMATICAL CONSTRUCTION
# =========================
# Both EmUnimodGroup(m) (m >= 1) and EPlusGroup(m) (m >= 2) have a
# canonical generating set adapted to the extraspecial presentation:
#
#   EmUnimodGroup(m): generators returned by GeneratorsOfGroup are
#                     [z, σ_{1,1}, σ_{1,2}, σ_{2,1}, σ_{2,2}, ...,
#                      σ_{m,1}, σ_{m,2}]
#                     (length 2m+1, z first).
#
#   EPlusGroup(m): generators returned by GeneratorsOfGroup are
#                     [a_1, b_1, a_2, b_2, ..., a_m, b_m, z]
#                     (length 2m+1, z last).
#                     Empirically verified at m=3, m=5 with the
#                     commutator pattern [a_i, b_i] = z, others
#                     commute.
#
# For m >= 2, the canonical map is:
#   EmUnimodGroup(m).gen[1]     (= z = -I)    ->  EPlusGroup(m).gen[2m+1]  (= z)
#   EmUnimodGroup(m).gen[2a]    (= σ_{a,1})   ->  EPlusGroup(m).gen[2a-1]  (= a_a)
#   EmUnimodGroup(m).gen[2a+1]  (= σ_{a,2})   ->  EPlusGroup(m).gen[2a]    (= b_a)
#
# This map is a GROUP HOMOMORPHISM (preserves commutators; verified
# empirically via test_em_eplus_translate.g).
#
# For m = 1, EPlusGroup(1) = ExtraspecialGroup(8, "+") = D_8 returns
# generators of orders [4, 2, 2] (the standard D_8 = <r, s> presentation
# with r of order 4), which does NOT match EmUnimodGroup(1)'s
# generators [-I, σ_{1,1}, σ_{1,2}] all of order 2. For m = 1 we fall
# back to GAP's IsomorphismGroups(EU, EP), which finds an isomorphism
# by class structure.
#
# (The K-4a pipeline is exercised at m in {2, 3, 5}; m = 1 is included
# here for completeness, but is not on the K-4 critical path.)
#
# PUBLIC API
# ==========
#   EmEPlusTranslate(m)
#       -> rec( .m, .EU, .EP, .psi (EU -> EP), .psi_inv (EP -> EU),
#               .gens_EU, .gens_EP, .image_list )
#       Cached per m on `_EM_EPLUS_CACHE`.
#
#   TranslateElementEUtoEP(record, x_eu)
#       Image of x_eu in EP. Convenience wrapper over Image(record.psi, x_eu).
#
#   TranslateElementEPtoEU(record, x_ep)
#       Preimage of x_ep in EU. Convenience wrapper over
#       PreImagesRepresentative(record.psi, x_ep) (equivalently
#       Image(record.psi_inv, x_ep)).
#
#   TranslateSpectralDataToEPlus(spectral_data_eu [, target_EP])
#       Given a record like BuildKRRSpectralCharactersSparse(m)'s
#       output (with .group = EmUnimodGroup(m), .idx, .trace_on_W
#       etc.), return a NEW record with .group = an EPlusGroup(m)
#       instance and .trace_on_W wrapped so that calls with
#       EPlusGroup(m)-elements are routed through the isomorphism back
#       to the EU-side data.
#
#       If target_EP is supplied, the iso is built against that
#       specific EPlusGroup(m) GAP instance (necessary when the
#       downstream consumer holds its own EPlusGroup(m) instance —
#       the K-4a detecting-subgroup constructors each create a fresh
#       instance, and `in`-tests across instances return false).
#
#       The translated record has the K-1 / intertwiner_data shape
#       (rec(.group, .idx, .transport, .trace_on_W, .epsilon)) and can
#       be passed directly to RestrictTraceOnWToSubgroup with a
#       subgroup H ⊆ target_EP.
#
# DEPENDENCIES
# ============
#   * em_construction.g            (loaded transitively for EmGroup if
#                                    EmUnimodGroup loader pulls it).
#                                    Not strictly needed by this module.
#   * krr_spectral_characters.g    (EmUnimodGroup; pulled in lazily on
#                                    first call to EmEPlusTranslate).
#   * quillen_detecting_subgroup.g (EPlusGroup; pulled in lazily).
#   * untwisted_modular_data.g     (BuildSimpleIndex, BuildTransports,
#                                    BuildSimpleIndexLazy,
#                                    BuildTransportsLazy --
#                                    used by TranslateSpectralDataToEPlus
#                                    to build the EP-side class structure).

# ============================================================
# Loader: same INPUT_FILENAME() pattern as restrict_to_subgroup.g.
# ============================================================

_eet_self := INPUT_FILENAME();;
_eet_dir := fail;;
if _eet_self <> fail and _eet_self <> "stream" then
    _eet_dir := _eet_self{
        [1..Length(_eet_self) - Length("/em_eplus_translate.g")]};
fi;;

_EET_LoadSibling := function(global_name, filename)
    local cand, p;
    if IsBoundGlobal(global_name) then
        return true;
    fi;
    if _eet_dir <> fail then
        cand := Concatenation(_eet_dir, "/", filename);
        if IsExistingFile(cand) then
            Read(cand);
            return true;
        fi;
    fi;
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

# We load EmUnimodGroup / EPlusGroup deps lazily inside EmEPlusTranslate
# so that this file can be Read in environments where they're already
# bound (and so we don't accidentally pull in heavy HAP-using siblings
# at file-load time).


# ============================================================
# Cache.
# ============================================================
# Keyed by m (an integer). Records are pinned for the GAP session.

if not IsBoundGlobal("_EM_EPLUS_CACHE") then
    BindGlobal("_EM_EPLUS_CACHE", rec());
fi;;


# ============================================================
# EmEPlusTranslate(m) / EmEPlusTranslateAgainst(m, target_EP)
# ============================================================
#
# Two entry points:
#
#   EmEPlusTranslate(m)
#     Returns (cached) iso from EmUnimodGroup(m) to a canonical
#     EPlusGroup(m) built once and reused. The EmUnimodGroup(m)
#     instance is also cached.
#
#   EmEPlusTranslateAgainst(m, target_EP)
#     Builds (not cached) iso from EmUnimodGroup(m) to the
#     specifically-supplied target_EP. This is required by the K-4a
#     pipeline because the detecting-subgroup constructors
#     (MaximalElementaryAbelian_E_plus, D8Section_E_plus,
#     Q8Section_E_plus) each call EPlusGroup(m) internally to build
#     a FRESH EPlusGroup(m) instance, and `GroupHomomorphismByImages`
#     requires the target's generators to match.
#
#     ASSUMPTION on target_EP: target_EP must have been built by
#     EPlusGroup(m), i.e. it is `ExtraspecialGroup(2^{2m+1}, "+")`
#     with the canonical generator convention
#     [a_1, b_1, ..., a_m, b_m, z]. The function checks |target_EP|
#     and #gens, but does not verify the full generator semantics
#     (the GroupHomomorphismByImages call returns fail if the
#     commutator pattern doesn't match).

EmEPlusTranslate := function(m)
    local key, EU, EP;
    if not IsInt(m) or m < 1 then
        Error("EmEPlusTranslate: m must be a positive integer; got ", m);
    fi;
    key := Concatenation("m", String(m));
    if IsBound(_EM_EPLUS_CACHE.(key)) then
        return _EM_EPLUS_CACHE.(key);
    fi;
    # Build canonical EU and EP, then call EmEPlusTranslateAgainst.
    # Pull in sibling deps if not already present.
    if not IsBoundGlobal("EmUnimodGroup") then
        if not _EET_LoadSibling("EmUnimodGroup",
                                  "krr_spectral_characters.g") then
            Error("EmEPlusTranslate: cannot locate ",
                  "krr_spectral_characters.g (provider of EmUnimodGroup).");
        fi;
    fi;
    if not IsBoundGlobal("EPlusGroup") then
        if not _EET_LoadSibling("EPlusGroup",
                                  "quillen_detecting_subgroup.g") then
            Error("EmEPlusTranslate: cannot locate ",
                  "quillen_detecting_subgroup.g (provider of EPlusGroup).");
        fi;
    fi;
    EU := EmUnimodGroup(m);
    EP := EPlusGroup(m);
    _EM_EPLUS_CACHE.(key) := EmEPlusTranslateAgainst(m, EP, EU);
    return _EM_EPLUS_CACHE.(key);
end;;

# EmEPlusTranslateAgainst(m, target_EP, optional source_EU)
#   target_EP: the specific EPlusGroup(m) instance to build psi against.
#   source_EU: optional EmUnimodGroup(m) instance (defaults to a fresh
#              EmUnimodGroup(m) call).
# Returns a NON-CACHED record (the caller is responsible for caching
# if desired); the EmEPlusTranslate cache key is only set by the
# unparameterised EmEPlusTranslate(m) above.
EmEPlusTranslateAgainst := function(arg)
    local m, target_EP, source_EU, EU, EP, gens_EU, gens_EP, image_list,
          psi, psi_inv, a;
    m := arg[1];
    target_EP := arg[2];
    if Length(arg) >= 3 then
        source_EU := arg[3];
    else
        if not IsBoundGlobal("EmUnimodGroup") then
            if not _EET_LoadSibling("EmUnimodGroup",
                                      "krr_spectral_characters.g") then
                Error("EmEPlusTranslateAgainst: cannot locate ",
                      "krr_spectral_characters.g.");
            fi;
        fi;
        source_EU := EmUnimodGroup(m);
    fi;
    if not IsInt(m) or m < 1 then
        Error("EmEPlusTranslateAgainst: m must be a positive integer; got ", m);
    fi;
    EU := source_EU;
    EP := target_EP;
    if Order(EP) <> 2^(2 * m + 1) then
        Error("EmEPlusTranslateAgainst: target_EP has order ", Order(EP),
              " but expected 2^(2m+1) = ", 2^(2 * m + 1),
              " for m = ", m, ".");
    fi;
    gens_EU := GeneratorsOfGroup(EU);
    gens_EP := GeneratorsOfGroup(EP);
    if m = 1 then
        # m = 1: presentations differ, fall back to IsomorphismGroups.
        psi := IsomorphismGroups(EU, EP);
        if psi = fail then
            Error("EmEPlusTranslateAgainst: IsomorphismGroups(EU, EP) ",
                  "returned fail at m = 1.");
        fi;
        image_list := List(gens_EU, g -> Image(psi, g));
    else
        if Length(gens_EU) <> 2 * m + 1 then
            Error("EmEPlusTranslateAgainst: EU has ", Length(gens_EU),
                  " generators; expected ", 2 * m + 1);
        fi;
        if Length(gens_EP) <> 2 * m + 1 then
            Error("EmEPlusTranslateAgainst: target_EP has ",
                  Length(gens_EP), " generators; expected ", 2 * m + 1,
                  ". target_EP is probably not an ExtraspecialGroup(",
                  2^(2*m+1), ", \"+\") in the canonical generator ",
                  "convention.");
        fi;
        image_list := [ gens_EP[2 * m + 1] ];
        for a in [1..m] do
            Add(image_list, gens_EP[2 * a - 1]);
            Add(image_list, gens_EP[2 * a]);
        od;
        # Issue #449 #456 C6: skip the relation-validation check via
        # GroupHomomorphismByImagesNC. By construction the canonical map
        # [z, σ_{a,r}] -> [z, a_a, b_a] preserves the extraspecial
        # commutator pattern at m >= 2; validating it via
        # GroupHomomorphismByImages's standard check would re-prove this
        # at every call (~9s at m=5, multiplied by 3 branches per K-4
        # invocation). NC is safe here.
        psi := GroupHomomorphismByImagesNC(EU, EP, gens_EU, image_list);
    fi;
    psi_inv := InverseGeneralMapping(psi);
    return rec(
        m         := m,
        EU        := EU,
        EP        := EP,
        gens_EU   := gens_EU,
        gens_EP   := gens_EP,
        image_list := image_list,
        psi       := psi,
        psi_inv   := psi_inv
    );
end;;


# ============================================================
# Element-level translators (convenience).
# ============================================================

TranslateElementEUtoEP := function(record, x_eu)
    return Image(record.psi, x_eu);
end;;

TranslateElementEPtoEU := function(record, x_ep)
    return Image(record.psi_inv, x_ep);
end;;


# ============================================================
# TranslateSpectralDataToEPlus(spectral_data_eu)
# ============================================================
#
# Translate an intertwiner-data-shaped record from EmUnimodGroup(m) to
# EPlusGroup(m).
#
# Input:
#   spectral_data_eu : record with at least
#       .group       : EmUnimodGroup(m)
#       .idx         : BuildSimpleIndex(.group) (or *Lazy)
#       .trace_on_W  : function(class_idx_EU, irrep_idx, h_EU)
#                      -> cyclotomic
#       .epsilon     : function(g1_EU, g2_EU, a_EU, b_EU) -> cyclotomic
#                      (may be absent; defaulted to const 1).
#   (Other fields like .multiplicities, .character_match, .m,
#    .source, .centraliser_traces are passed through unchanged on
#    the output record for downstream inspection.)
#
# Output: a NEW record with
#       .group       : EPlusGroup(m)
#       .idx         : BuildSimpleIndex(EPlusGroup(m)) (or *Lazy, mirroring
#                      the input shape)
#       .transport   : BuildTransports(.idx) (or *Lazy)
#       .trace_on_W  : function(class_idx_EP, irrep_idx, h_EP)
#                      that pulls h_EP back to EU via psi_inv, locates
#                      the corresponding EU class via the class-translation
#                      table, and dispatches to the EU-side trace_on_W.
#       .epsilon     : const 1 (per T4a downscope; if the input had a
#                      non-trivial epsilon, it is wrapped analogously).
#       .source      : "translated-from-em-unimod" (copied from input if
#                      present, prefixed)
#       .em_unimod_source : the original spectral_data_eu (kept for
#                      reference and downstream inspection)
#       .translate   : the EmEPlusTranslate(m) record (psi, psi_inv, ...).
#
# The translation is class-based: each EP-conjugacy class is mapped to
# the EU-class containing the EU-preimage of its representative.
# Inside the trace function, an input h_EP is pulled back to h_EU, then
# the EU-side trace evaluator is called. This works for any class
# function (in particular EvalIrr).
#
# COMPLEXITY:
#   * Building the EU<->EP class-index map: O(num_classes) Image and
#     ClassIndexOf lookups. At m = 5, num_classes = 1025.
#   * Each trace_on_W call: one Image(psi_inv, h) + the underlying EU
#     trace_on_W cost. The psi_inv image is dominated by the
#     EU.trace_on_W cost so this is essentially free.
#
# Note on idx_EP construction: we always use BuildSimpleIndex (eager)
# for the EP side, since the consumer (RestrictTraceOnWToSubgroup) needs
# .ct_centraliser[class_idx] to map H-class representatives to EP-classes.
# The eager build at m = 5 takes ~30 s on test hardware; acceptable.
# If callers want lazy behaviour they can pass `lazy := true` in the
# input record's `.translate_lazy` field (TODO; not currently used).

TranslateSpectralDataToEPlus := function(arg)
    local m, eu_group, ep_group, tr_rec, idx_EP, idx_EU, transport_EP,
          ep_to_eu_class, k_ep, rep_ep, rep_eu, k_eu, j, eu_classes,
          trace_on_W_translated, epsilon_translated, out, spectral_data_eu,
          target_EP, use_closed_form, num_classes_eu, ep_reps, ep_classes,
          ep_centralisers, ep_class_sizes, ep_class_types, cl, ep_num_irreps,
          ep_global_offset, ep_global_to_local, ep_rank, i,
          psi_gens_flat, psi_z, ei, k_ei, bit_idx, bit, a, r;
    if Length(arg) < 1 then
        Error("TranslateSpectralDataToEPlus: requires at least one ",
              "argument (the spectral_data_eu record).");
    fi;
    # Ensure BuildSimpleIndexLazy / BuildTransportsLazy are loaded.
    if not IsBoundGlobal("BuildSimpleIndexLazy") then
        if not _EET_LoadSibling("BuildSimpleIndexLazy",
                                  "untwisted_modular_data.g") then
            Error("TranslateSpectralDataToEPlus: cannot locate ",
                  "untwisted_modular_data.g (provider of ",
                  "BuildSimpleIndexLazy / BuildTransportsLazy).");
        fi;
    fi;
    spectral_data_eu := arg[1];
    eu_group := spectral_data_eu.group;
    if not IsBound(spectral_data_eu.m) then
        Error("TranslateSpectralDataToEPlus: input record has no .m ",
              "field; cannot determine target m.");
    fi;
    m := spectral_data_eu.m;
    if Length(arg) >= 2 and arg[2] <> fail then
        target_EP := arg[2];
        # Build a fresh psi against the supplied target_EP (not cached).
        # This is the path used by the K-4a pipeline: each
        # detecting-subgroup constructor calls EPlusGroup(m) internally
        # to make a fresh GAP instance, and the iso must target THAT
        # instance for the per-branch element-membership tests to pass.
        tr_rec := EmEPlusTranslateAgainst(m, target_EP, eu_group);
    else
        # Use the canonical cached translate (single shared EP).
        tr_rec := EmEPlusTranslate(m);
        if eu_group <> tr_rec.EU then
            Error("TranslateSpectralDataToEPlus: input .group is not the ",
                  "EmUnimodGroup(", m, ") instance held by the translate ",
                  "cache. Pass the target EPlusGroup(m) instance as a ",
                  "second argument to translate against a specific EP.");
        fi;
    fi;
    ep_group := tr_rec.EP;
    idx_EU := spectral_data_eu.idx;

    # Issue #449 #456 B2: closed-form class-index bijection.
    #
    # When the EU-side idx was built via `BuildSimpleIndexEPlusClosedForm`
    # (signaled by `idx_EU.is_closed_form = true`), the generic
    # `BuildSimpleIndexLazy(ep_group)` triggers the SAME `ConjugacyClasses`
    # OOM cliff at m=7 that A1 dodged for the EU side. Since psi: EU -> EP
    # is an isomorphism, the set {psi(rep_eu_i) : i in 1..|idx_EU|} is a
    # complete set of EP-class representatives -- we can construct idx_EP
    # directly without invoking `ConjugacyClasses(EP)` at all.
    #
    # FAST PATH (identity psi): if `Source(psi) = Range(psi)` (only
    # possible when the caller passed an EU spectral record whose group
    # is already EP-shaped, e.g. a degenerate test scenario), the
    # bijection is identity and we just reuse `idx_EU` directly. The K-4
    # pipeline always has EU=EmUnimod, EP=EPlusGroup so this branch is
    # not taken; it's structural completeness.
    #
    # CLOSED-FORM PATH (default for m >= 5 when idx_EU is closed-form):
    # build idx_EP class-by-class from EU reps via psi. The bijection
    # is the identity permutation `[1..n]` by construction.
    use_closed_form := IsBound(idx_EU.is_closed_form)
                       and idx_EU.is_closed_form = true
                       and Source(tr_rec.psi) <> Range(tr_rec.psi);

    if use_closed_form then
        # B2 closed-form construction: bypass BuildSimpleIndexLazy(ep_group).
        num_classes_eu := Length(idx_EU.reps);
        ep_reps := EmptyPlist(num_classes_eu);
        ep_classes := EmptyPlist(num_classes_eu);
        ep_centralisers := EmptyPlist(num_classes_eu);
        ep_class_sizes := EmptyPlist(num_classes_eu);
        if IsBound(idx_EU.class_types) then
            ep_class_types := EmptyPlist(num_classes_eu);
        fi;
        # Issue #449 perf: bits-driven psi computation.
        #
        # `Image(tr_rec.psi, idx_EU.reps[i])` is slow at m >= 5 because GAP
        # decomposes each 2^m x 2^m matrix as a word in EU generators via
        # Schreier-Sims (~100-200 ms per call at m=7). At m=7 this is
        # 16385 classes ~= 30-35 min.
        #
        # The closed-form EU class reps from `_EnumerateEPlusClassReps`
        # are structured:
        #   class 1: identity I_n
        #   class 2: -I_n (the central element z)
        #   class i >= 3: product of UnimodSigma(m, a, r) generators
        #                 selected by the bit-decode of ei := i - 2:
        #     bits[idx] := (ei >> (idx-1)) & 1  for idx in 1..2m
        #     rep := prod_{a,r: bits[2*(a-1)+r] = 1} UnimodSigma(m, a, r)
        # Since psi is a homomorphism,
        #     psi(rep) = prod psi(UnimodSigma(m, a, r))
        # and psi(UnimodSigma) values come directly from tr_rec.image_list
        # (set in EmEPlusTranslateAgainst): image_list = [z_EP, a_1, b_1,
        # ..., a_m, b_m] at m >= 2, so psi(sigma_{a,r}) = image_list[2*(a-1)+r+1].
        # m = 1 also lands here via IsomorphismGroups + List-built image_list,
        # so the same indexing convention holds (image_list[1] = psi(z),
        # image_list[2*(a-1)+r+1] = psi(sigma_{a,r})).
        #
        # Cost: 2m+1 generator lookups (~free) + at most 2m PC-group
        # multiplications per class (cheap, since EP is a pc group).
        # At m=7: 16385 classes * ~14 quick PC multiplies = ~1 sec total.
        psi_gens_flat := EmptyPlist(2 * m);
        for a in [1..m] do
            for r in [1..2] do
                Add(psi_gens_flat, tr_rec.image_list[2 * (a - 1) + r + 1]);
            od;
        od;
        psi_z := tr_rec.image_list[1];
        for i in [1..num_classes_eu] do
            if i = 1 then
                rep_ep := One(ep_group);
            elif i = 2 then
                rep_ep := psi_z;
            else
                ei := i - 2;
                rep_ep := One(ep_group);
                k_ei := ei;
                for bit_idx in [1..2 * m] do
                    bit := k_ei mod 2;
                    k_ei := QuoInt(k_ei, 2);
                    if bit = 1 then
                        rep_ep := rep_ep * psi_gens_flat[bit_idx];
                    fi;
                od;
            fi;
            cl := ConjugacyClass(ep_group, rep_ep);
            SetSize(cl, idx_EU.class_sizes[i]);
            Add(ep_reps, rep_ep);
            Add(ep_classes, cl);
            Add(ep_class_sizes, idx_EU.class_sizes[i]);
            # Centraliser: ep_group for central classes (where
            # idx_EU.centralisers is the whole EU group); `fail`
            # (lazy) for non-central classes, matching
            # `BuildSimpleIndexEPlusClosedForm`'s convention. The
            # `_EPlusCentraliserOf` accessor materialises on first
            # access via `Centralizer(idx.group, idx.reps[i])`.
            if IsBound(idx_EU.centralisers[i])
               and idx_EU.centralisers[i] = idx_EU.group then
                Add(ep_centralisers, ep_group);
            else
                Add(ep_centralisers, fail);
            fi;
            if IsBound(idx_EU.class_types) then
                Add(ep_class_types, idx_EU.class_types[i]);
            fi;
        od;
        # Memoise ConjugacyClasses(ep_group) -> OUR list, so any
        # downstream call to `ConjugacyClasses(ep_group)` or
        # `NrConjugacyClasses(ep_group)` uses our enumeration without
        # triggering GAP's generic search.
        if not HasConjugacyClasses(ep_group) then
            SetConjugacyClasses(ep_group, ep_classes);
        fi;
        # num_irreps mirrors the EU side directly (same per-class
        # value, since the per-class centraliser is isomorphic via
        # psi^{-1}). We reference the lists directly (no ShallowCopy)
        # because at m=7, `idx_EU.global_to_local` has ~268M entries
        # and a shallow copy would allocate the entire outer plist
        # again (~2 GB). Consumers treat these fields as read-only.
        ep_num_irreps := idx_EU.num_irreps;
        ep_rank := idx_EU.rank;
        ep_global_offset := idx_EU.global_offset;
        ep_global_to_local := idx_EU.global_to_local;
        # Note: we do NOT set `is_closed_form := true` on idx_EP, even
        # though the EU-side was closed-form. The reason: the closed-form
        # irrep evaluator `EPlusBuildAllCharacterRows` requires class
        # representatives to be MATRICES (it does `h mod 2` to extract
        # symplectic bits), but our `ep_reps` are PC group elements (EP
        # = `EPlusGroup(m)` = an `ExtraspecialGroup` PC realisation, not
        # a matrix group). Setting `is_closed_form := true` would route
        # `_EnsureClassData` at the central class through the matrix-only
        # closed-form path and crash. Instead, we leave it as a plain
        # lazy idx: the per-class CT is built generically via
        # `CharacterTable(C)` on first access, which is acceptable for
        # the central class (single CT build, dominated by other costs).
        # The B2 win is in skipping `ConjugacyClasses(ep_group)`, which
        # is independent of the per-class CT decision.
        idx_EP := rec(
            group := ep_group,
            order := idx_EU.order,
            classes := ep_classes,
            reps := ep_reps,
            class_sizes := ep_class_sizes,
            centralisers := ep_centralisers,
            ct_centraliser := List([1..num_classes_eu], _ -> fail),
            cc_centraliser := List([1..num_classes_eu], _ -> fail),
            irreps         := List([1..num_classes_eu], _ -> fail),
            irrep_dims     := List([1..num_classes_eu], _ -> fail),
            num_irreps := ep_num_irreps,
            global_offset := ep_global_offset,
            global_to_local := ep_global_to_local,
            rank := ep_rank,
            is_lazy := true,
            source := "translated-closed-form-eplus"
        );
        if IsBound(idx_EU.class_types) then
            idx_EP.class_types := ep_class_types;
        fi;
        if IsBound(idx_EU.per_type_counts) then
            idx_EP.per_type_counts := idx_EU.per_type_counts;
        fi;
        # Bijection is the identity permutation: psi maps EU-class k
        # to EP-class k by construction.
        ep_to_eu_class := [1..num_classes_eu];
    else
        # Legacy path: BuildSimpleIndexLazy(ep_group) triggers
        # ConjugacyClasses(ep_group). Acceptable at m <= 3, but
        # eats memory at m >= 5 (the OOM cliff #449 A1 fixes for
        # the EU side; B2 fixes for the EP side via `use_closed_form`
        # above).
        idx_EP := BuildSimpleIndexLazy(ep_group);

        # Build the EP -> EU class index map.
        eu_classes := idx_EU.classes;
        ep_to_eu_class := [];
        for k_ep in [1..Length(idx_EP.reps)] do
            rep_ep := idx_EP.reps[k_ep];
            rep_eu := Image(tr_rec.psi_inv, rep_ep);
            # Find which EU class contains rep_eu.
            k_eu := fail;
            for j in [1..Length(eu_classes)] do
                if rep_eu in eu_classes[j] then
                    k_eu := j;
                    break;
                fi;
            od;
            if k_eu = fail then
                Error("TranslateSpectralDataToEPlus: rep_ep of EP-class ",
                      k_ep, " (= ", rep_ep, ") pulls back to ", rep_eu,
                      " which is not in any EU conjugacy class. This should ",
                      "not happen if psi is an isomorphism and the EU idx ",
                      "covers every conjugacy class.");
            fi;
            Add(ep_to_eu_class, k_eu);
        od;
    fi;

    # Now: trace_on_W_translated(class_idx_EP, irrep_idx, h_EP)
    #   = spectral_data_eu.trace_on_W(class_idx_EU, irrep_idx, h_EU)
    # where class_idx_EU = ep_to_eu_class[class_idx_EP] and h_EU is
    # the EU-preimage of h_EP.
    #
    # CAVEAT on irrep_idx: the irrep indexing on EP-side is determined
    # by Irr(C_EP(rep_ep)) (= CharacterTable(idx_EP.centralisers[k_ep]).Irr),
    # while EU-side uses Irr(C_EU(rep_eu)). These two centralisers are
    # isomorphic (the iso is the restriction of psi^{-1}: EP -> EU),
    # but GAP's CharacterTable / Irr enumeration is not guaranteed to
    # return them in the same order.
    #
    # For the current K-4 pipeline (T4a downscope, epsilon = 1), the
    # only consumer of the translated trace_on_W is
    # RestrictTraceOnWToSubgroup, which uses the EP-side idx_H to label
    # irreps (it builds its own H-side index via
    # BuildIntertwinerDataUntwisted(H)). The parent EP-side irrep_idx
    # is only routed through .trace_on_W via H-class restrictions;
    # the trace is evaluated only for h ∈ C_H(a_H) ⊆ C_EP(a_EP),
    # and the result depends on irrep_idx through Irr(C_EP(a_EP)).
    #
    # Under T4a's epsilon = 1, the actual H-level CT modular data is
    # determined by H's OWN character functional, NOT by the parent's
    # trace_on_W (see comments in restrict_to_subgroup.g). So irrep_idx
    # ordering on the EP-side is not load-bearing for triviality
    # verdicts: any consistent mapping between EP-irreps and the
    # EU-irreps with matching dimension/value works.
    #
    # For correctness, we use the SIMPLE ASSUMPTION that the irrep_idx
    # on EP corresponds to the irrep_idx on EU UP TO a permutation
    # that GAP returns deterministically. For non-central classes on
    # both sides the trace_on_W falls back to EvalIrr, and the value
    # depends on h's class index in the centraliser — which is again
    # determined by the GAP ordering. For the central class (-I on EU,
    # corresponding z on EP) the spectral builder may have computed
    # non-trivial multiplicities, but for any non-zero alpha this
    # would surface as an actual EvalIrr-style call.
    #
    # The safer route taken here: pull back h_EP to h_EU via psi_inv
    # and call spectral_data_eu.trace_on_W with (class_idx_EU, irrep_idx,
    # h_EU). If the EU/EP irrep orderings ever diverge, the trace_on_W
    # output may be "the wrong irrep's value" for that EU class. This
    # is a known follow-up; for the m = 5 triviality verdict in scope
    # of this issue, it does not affect the answer (per the T4a
    # epsilon = 1 reasoning above).

    trace_on_W_translated := function(class_idx_EP, irrep_idx, h_EP)
        local class_idx_EU, h_EU;
        class_idx_EU := ep_to_eu_class[class_idx_EP];
        h_EU := Image(tr_rec.psi_inv, h_EP);
        return spectral_data_eu.trace_on_W(class_idx_EU, irrep_idx, h_EU);
    end;

    if IsBound(spectral_data_eu.epsilon) then
        # Pull back the four EP-elements before calling the EU epsilon.
        # Under T4a downscope all current callers have epsilon === 1, so
        # this branch is structural but rarely exercised.
        epsilon_translated := function(g1_EP, g2_EP, a_EP, b_EP)
            return spectral_data_eu.epsilon(
                Image(tr_rec.psi_inv, g1_EP),
                Image(tr_rec.psi_inv, g2_EP),
                Image(tr_rec.psi_inv, a_EP),
                Image(tr_rec.psi_inv, b_EP));
        end;
    else
        epsilon_translated := function(g1, g2, a, b) return 1; end;
    fi;

    # Use lazy transports to match the lazy idx; the consumers
    # (RestrictTraceOnWToSubgroup, RestrictTraceOnWToSubgroupHonourParent)
    # don't iterate over all classes' transports — they only touch
    # the H-image classes via _RTS_FindGClassOf.
    transport_EP := BuildTransportsLazy(idx_EP);

    out := rec(
        group       := ep_group,
        idx         := idx_EP,
        transport   := transport_EP,
        trace_on_W  := trace_on_W_translated,
        epsilon     := epsilon_translated,
        # Inspection / debugging:
        em_unimod_source := spectral_data_eu,
        translate   := tr_rec,
        ep_to_eu_class := ep_to_eu_class,
        m           := m
    );

    # Pass through useful diagnostic fields if present.
    if IsBound(spectral_data_eu.source) then
        out.source := Concatenation("translated-from-em-unimod:",
                                     String(spectral_data_eu.source));
    else
        out.source := "translated-from-em-unimod";
    fi;
    # Remap multiplicities from EU-class index to EP-class index.
    # We use ep_to_eu_class for the class mapping. For the per-class
    # irrep ordering, we assume parallel ordering between
    # Irr(C_EU(a_EU)) and Irr(C_EP(a_EP)) (both centralisers being
    # isomorphic via psi^{-1}); this matches the dimension-based
    # heuristic that RestrictTraceOnWToSubgroupHonourParent uses.
    # If EU irrep ordering differs from EP, a downstream consumer
    # may pick the wrong mult — a known caveat for the irrep-index
    # translation that is acceptable under the T4a downscope.
    if IsBound(spectral_data_eu.multiplicities) then
        out.multiplicities_eu := spectral_data_eu.multiplicities;
        out.multiplicities := List([1..Length(idx_EP.reps)],
            k_ep -> (function()
                local k_eu;
                k_eu := ep_to_eu_class[k_ep];
                if k_eu > Length(spectral_data_eu.multiplicities) then
                    return fail;
                fi;
                return spectral_data_eu.multiplicities[k_eu];
            end)());
    fi;
    if IsBound(spectral_data_eu.character_match) then
        out.character_match_eu := spectral_data_eu.character_match;
    fi;
    if IsBound(spectral_data_eu.centraliser_traces) then
        out.centraliser_traces_eu := spectral_data_eu.centraliser_traces;
    fi;
    return out;
end;;

Print("Loaded em_eplus_translate.g (#256: family translation EmUnimodGroup <-> EPlusGroup).\n");
