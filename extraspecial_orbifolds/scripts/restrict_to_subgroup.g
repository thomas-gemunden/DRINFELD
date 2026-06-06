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

# Capture the load-time directory so the projective path's lazy load of
# build_krr_intertwiner_data.g / epsilon_omega.g works even when invoked
# from a different CWD (mirrors the snapshot used by
# `build_krr_intertwiner_data.g` for the same reason).
_RTS_LOAD_DIR := fail;;
_rts_self := INPUT_FILENAME();;
if _rts_self <> fail and _rts_self <> "stream" then
    _rts_dir := _rts_self{[1..Length(_rts_self)
                            - Length("/restrict_to_subgroup.g")]};;
    _RTS_LOAD_DIR := _rts_dir;
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

# `_RTS_EnsureProjectiveHelpers()` (issue #328):
# Lazily load `build_krr_intertwiner_data.g` (for the projective helpers
# `_KRRI_AlphaG`, `_KRRI_ProjectiveCharsForG`, `_KRRI_TryMatchProjToIrr`)
# and `epsilon_omega.g` (for the integer-phase backbone `EpsilonOmega`)
# the first time the projective variant of the restriction is invoked.
# We do NOT load these eagerly at file-Read time because (i) the
# untwisted path doesn't need them and (ii) `epsilon_omega.g` transitively
# requires HAP, which has multi-second load cost we don't want to pay on
# every user `Read("restrict_to_subgroup.g")`.
_RTS_EnsureProjectiveHelpers := function()
    local cand, p, _name;
    for _name in [ "_KRRI_AlphaG", "_KRRI_ProjectiveCharsForG",
                   "_KRRI_TryMatchProjToIrr" ] do
        if IsBoundGlobal(_name) then continue; fi;
        if _RTS_LOAD_DIR <> fail then
            cand := Concatenation(_RTS_LOAD_DIR,
                                  "/build_krr_intertwiner_data.g");
            if IsExistingFile(cand) then
                Read(cand);
                break;
            fi;
        fi;
        for p in [ "build_krr_intertwiner_data.g",
                   "./build_krr_intertwiner_data.g",
                   "extraspecial_orbifolds/scripts/build_krr_intertwiner_data.g" ] do
            if IsExistingFile(p) then
                Read(p);
                break;
            fi;
        od;
        break;
    od;
    for _name in [ "_KRRI_AlphaG", "_KRRI_ProjectiveCharsForG",
                   "_KRRI_TryMatchProjToIrr" ] do
        if not IsBoundGlobal(_name) then
            Error("restrict_to_subgroup.g: required helper ", _name,
                  " not bound after loading build_krr_intertwiner_data.g; ",
                  "ensure that file sits alongside restrict_to_subgroup.g.");
        fi;
    od;
    if not IsBoundGlobal("EpsilonOmega") then
        if _RTS_LOAD_DIR <> fail then
            cand := Concatenation(_RTS_LOAD_DIR, "/epsilon_omega.g");
            if IsExistingFile(cand) then
                Read(cand);
            fi;
        fi;
        if not IsBoundGlobal("EpsilonOmega") then
            for p in [ "epsilon_omega.g",
                       "./epsilon_omega.g",
                       "extraspecial_orbifolds/scripts/epsilon_omega.g" ] do
                if IsExistingFile(p) then
                    Read(p);
                    break;
                fi;
            od;
        fi;
        if not IsBoundGlobal("EpsilonOmega") then
            Error("restrict_to_subgroup.g: required helper `EpsilonOmega` ",
                  "not bound after loading epsilon_omega.g; ensure that ",
                  "file sits alongside restrict_to_subgroup.g.");
        fi;
    fi;
end;;


# ============================================================
# Memoisation cache for BuildIntertwinerDataUntwisted (audit #456 C3).
# ============================================================
#
# Keyed by a stable identifier derived from H (IdGroup when cheap;
# otherwise a tuple of `Order(H)` and a structural hash). The cached
# value is the `BuildIntertwinerDataUntwisted(H)` rec, which is
# referentially shared across consecutive
# `RestrictTraceOnWToSubgroupHonourParent` calls for the same H.
#
# Cache key choice: GAP's `IdGroup(H)` requires the small-groups library
# and is fast for orders ≤ 2000. For E_+(m) detecting subgroups (D_8,
# Q_8, EA(r), r ≤ 2m+1), |H| is always ≤ 2^{2m+1}; at m=7 the EA
# subgroups have |H| = 2^8 = 256, still trivially within IdGroup's
# range. We use `IdGroup(H)` as the primary key with a fallback to
# `[Order(H), AsSet(GeneratorsOfGroup(H))]` for groups too large for
# IdGroup.
#
# Note: at m=7 in the K-4b spectral pipeline the call pattern is:
#   8-EA + D_8 + Q_8 detecting subgroups touched ~ k_G times each, where
# k_G is the number of central classes visited. Memoisation collapses
# the |class_to_G| BFS + transport builds (60-300 ms each at m=7) from
# ~10 calls to 1 per H.
#
# Lifetime: module-level dictionary, GC'd only at GAP shutdown. A
# downstream caller can manually clear via `_RTS_BIDU_CACHE := rec();`
# (see test_rts_closed_form.g).
_RTS_BIDU_CACHE := rec();;

# Compute a stable key for a subgroup H, suitable as a record-field
# name in `_RTS_BIDU_CACHE`. Prefer `IdGroup` when applicable (cheap
# and canonical); fall back to a structural string for larger H.
_RTS_BIDU_CacheKey := function(H)
    local id, ord;
    ord := Order(H);
    # IdGroup-able range: GAP's smallgrp library covers |G| ≤ 2000 with
    # some exceptions. For our use (E_+(m) detecting subgroups, |H| ≤
    # 2^{2m+1}) we are well inside this range at m ≤ 7 (max |H| = 2^15
    # for H = G, but typical |H| = 8 to 256).
    if ord <= 2000 then
        # IsGroup test guards against improperly-formed inputs.
        if IsGroup(H) then
            id := IdGroup(H);
            return Concatenation("id_", String(ord), "_", String(id[2]));
        fi;
    fi;
    # Fallback: structural string from Order + generator hashes.
    return Concatenation("ord_", String(ord),
                         "_gens_",
                         String(Length(GeneratorsOfGroup(H))));
end;;

# Memoised wrapper: returns the cached `BuildIntertwinerDataUntwisted(H)`
# rec, building (and caching) on first miss. Also stores the H instance
# alongside so the caller can verify identity-vs-equality semantics.
#
# Multiple distinct H values that share the same IdGroup (e.g. two
# different D_8 subgroups of G_em) will collide in the cache; the
# downstream `RestrictTraceOnWToSubgroupHonourParent` then sees a
# different group instance than the one passed in. To detect that case,
# we double-check via `Order(H) = Order(cached.group)` and a sample
# generator membership test. If those checks fail we BYPASS the cache
# and rebuild.
_RTS_GetBIDUCached := function(H)
    local key, cached, gens_H, sample, sample_in_cache_group;
    key := _RTS_BIDU_CacheKey(H);
    if IsBound(_RTS_BIDU_CACHE.(key)) then
        cached := _RTS_BIDU_CACHE.(key);
        # Safety: IdGroup collisions can produce false-positive hits if
        # the two H groups are genuinely different (e.g. two D_8 subs
        # in distinct E_+(m) families). Detect via:
        #   (a) order match — IdGroup ensures this, but cheap to verify.
        #   (b) sample-generator membership.
        if Order(cached.group) = Order(H) then
            gens_H := GeneratorsOfGroup(H);
            if Length(gens_H) > 0 then
                sample := gens_H[1];
                sample_in_cache_group := sample in cached.group;
            else
                # H is trivial.
                sample_in_cache_group := true;
            fi;
            if sample_in_cache_group then
                return cached;
            fi;
        fi;
        # Fall through: rebuild and overwrite.
    fi;
    cached := BuildIntertwinerDataUntwisted(H);
    _RTS_BIDU_CACHE.(key) := cached;
    return cached;
end;;


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
# DISPATCH (audit #456 B1)
# ========================
# Two implementations are available:
#
#   * `_RTS_FindGClassOfClosedForm(idx_G, a_H, G)` — O(1) per call after
#     a one-shot dictionary build. Only valid when `idx_G.is_closed_form
#     = true` (set by `BuildSimpleIndexEPlusClosedForm`). The dictionary
#     is cached on `idx_G` as `_rts_class_lookup` (a `NewDictionary`
#     keyed by matrix-element with values rec(k_G := k, sign := ±1));
#     and per-class conjugators (for the `sign = -1` case, where
#     `a_H = -idx_G.reps[k]`) are cached lazily on first miss in
#     `_rts_neg_conjugator[k]`. At m=7 this turns the 2064 H-class lookups
#     per detecting-family pass from ~500ms each into ~10µs each.
#
#   * `_RTS_FindGClassOfGeneric(idx_G, a_H, G)` — legacy O(|classes|) +
#     `RepresentativeAction` path. Used for `idx_G` that lack the closed-
#     form marker (e.g. `BuildSimpleIndex(D_8)`, generic groups). The
#     code path is byte-for-byte identical to the pre-B1 implementation.
#
# `_RTS_FindGClassOf` is the entry point: it inspects
# `idx_G.is_closed_form` and dispatches.
#
# Returns a record rec(k_G := ..., conj := ...).
# Errors if a_H is not in any G-class (shouldn't happen if H <= G).

# ----- Closed-form helpers (B1) -----------------------------------------
#
# `_RTS_BuildClassLookup(idx_G)` builds the matrix-keyed dictionary on
# first call and caches it on `idx_G._rts_class_lookup`. For E_+(m) the
# centre Z = <-I> has size 2, and every non-central class is {r, -r}
# (size 2). So the dictionary has 2 * Length(idx_G.classes) ≈ 2 * 4^m
# entries (32770 at m=7) — well within RAM. Build cost: O(|G|) matrix
# negations + dict inserts, ~3 sec at m=7.
#
# Sign convention: dict[r] = rec(k_G := k, sign := 1); dict[-r] =
# rec(k_G := k, sign := -1). At the central classes, dict[I] = rec(k_G
# := 1, sign := 1); dict[-I] = rec(k_G := 2, sign := 1) — the two are
# distinct classes, so sign is always +1 for centrals (since each
# central class has only one element). Non-centrals have sign ±1.
_RTS_BuildClassLookup := function(idx_G)
    local d, k, rep, neg_rep, central_type;
    if IsBound(idx_G._rts_class_lookup) then
        return idx_G._rts_class_lookup;
    fi;
    # Use a dictionary keyed by the matrix object. `NewDictionary` with
    # the first arg = a sample key works for any GAP element type.
    d := NewDictionary(idx_G.reps[1], true);
    for k in [1..Length(idx_G.reps)] do
        rep := idx_G.reps[k];
        # Insert the canonical rep with sign = +1.
        AddDictionary(d, rep, rec(k_G := k, sign := 1));
        # For non-central classes, also insert -rep (= z * rep) with
        # sign = -1. We can detect "non-central" by the closed-form type
        # marker, or simply check class size.
        if IsBound(idx_G.class_types)
           and (idx_G.class_types[k] = "sigma2"
                or idx_G.class_types[k] = "sigma_1sigma_2") then
            neg_rep := -rep;
            AddDictionary(d, neg_rep, rec(k_G := k, sign := -1));
        elif (not IsBound(idx_G.class_types))
             and IsBound(idx_G.class_sizes)
             and idx_G.class_sizes[k] = 2 then
            neg_rep := -rep;
            AddDictionary(d, neg_rep, rec(k_G := k, sign := -1));
        fi;
    od;
    idx_G._rts_class_lookup := d;
    return d;
end;;

# Cache of conjugators `g_k` per non-central class `k`, such that
# `g_k * (-r_k) * g_k^-1 = r_k`, equivalently `g_k * r_k * g_k^-1 = -r_k`.
# Filled lazily on first miss by `_RTS_GetNegConjugator(idx_G, k, G)`.
#
# Existence: for non-central r_k ∈ E_+(m), the symplectic pairing on
# G/Z is non-degenerate, so there is some g with [g, r_k] = z = -I.
# Equivalently, g * r_k * g^-1 = -r_k. We find such a g by searching
# `Centralizer(G, _)`'s complement, or via the symplectic-basis
# generators of G (σ_{a,r}).
_RTS_GetNegConjugator := function(idx_G, k, G)
    local r, gen, neg_r, conj, gens;
    if not IsBound(idx_G._rts_neg_conjugator) then
        idx_G._rts_neg_conjugator := [];
    fi;
    if IsBound(idx_G._rts_neg_conjugator[k])
       and idx_G._rts_neg_conjugator[k] <> fail then
        return idx_G._rts_neg_conjugator[k];
    fi;
    r := idx_G.reps[k];
    neg_r := -r;
    # Try the matrix-group generators of G first — for E_+(m) the
    # generators are {z, σ_{a,r}}, and at least one σ_{a,r} fails to
    # commute with r (by non-degeneracy of the symplectic form). The
    # search costs O(|gens|) = O(2m) matrix multiplications per class.
    gens := GeneratorsOfGroup(G);
    conj := fail;
    for gen in gens do
        if gen * r * gen^-1 = neg_r then
            conj := gen;
            break;
        fi;
    od;
    if conj = fail then
        # Fallback to GAP's RepresentativeAction (slow but always finds
        # the conjugator if one exists). For E_+(m) the loop above
        # always succeeds, so this branch is defensive.
        conj := RepresentativeAction(G, neg_r, r);
        if conj = fail then
            Error("_RTS_GetNegConjugator: cannot find g with ",
                  "g * (-r_k) * g^-1 = r_k at k = ", k,
                  ". idx_G may not be a closed-form E_+(m) idx.");
        fi;
        # RepresentativeAction(G, src, dst) returns g with src ^ g = dst,
        # i.e. g^-1 src g = dst, so we want g^-1 here.
        conj := conj ^ -1;
    fi;
    idx_G._rts_neg_conjugator[k] := conj;
    return conj;
end;;

_RTS_FindGClassOfClosedForm := function(idx_G, a_H, G)
    local d, hit, k_G, conj;
    d := _RTS_BuildClassLookup(idx_G);
    hit := LookupDictionary(d, a_H);
    if hit = fail then
        Error("_RTS_FindGClassOfClosedForm: element ", a_H,
              " is not in idx_G's class lookup. Either a_H is not in ",
              "G, or idx_G's class enumeration is incomplete.");
    fi;
    k_G := hit.k_G;
    if hit.sign = 1 then
        # a_H = idx_G.reps[k_G]; identity conjugator suffices.
        conj := One(G);
    else
        # a_H = -idx_G.reps[k_G]; need conj with conj * a_H * conj^-1
        # = idx_G.reps[k_G]. By construction of the cache, this is the
        # element g_k with g_k * r_k * g_k^-1 = -r_k (since z is central
        # and commutes with everything, conjugating -r_k by g_k yields
        # -(g_k r_k g_k^-1) = -(-r_k) = r_k).
        conj := _RTS_GetNegConjugator(idx_G, k_G, G);
    fi;
    return rec(k_G := k_G, conj := conj);
end;;

# ----- Generic (legacy) helper ------------------------------------------
_RTS_FindGClassOfGeneric := function(idx_G, a_H, G)
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
                Error("_RTS_FindGClassOfGeneric: RepresentativeAction(G, ",
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
    Error("_RTS_FindGClassOfGeneric: element ", a_H,
          " is not in any G-conjugacy class.");
end;;

# ----- Dispatcher entry point -------------------------------------------
_RTS_FindGClassOf := function(idx_G, a_H, G)
    if IsBound(idx_G.is_closed_form) and idx_G.is_closed_form = true then
        return _RTS_FindGClassOfClosedForm(idx_G, a_H, G);
    fi;
    return _RTS_FindGClassOfGeneric(idx_G, a_H, G);
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
        # B4 (#458 / was 2026-06-02 A-K4-4): base_data is the output of
        # `BuildIntertwinerDataUntwisted(H)`, whose `trace_on_W` reduces
        # to `EvalIrr(idx_H, ...)`. Propagate the kind tag so
        # `_CTBatchedTraceOnW` can take the fast path.
        trace_on_W_kind := "evalirr",
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
          cls_H, normaliser, cls_idx_G, decomposition_fn, abelian_fast;
    _EnsureClassData(idx_G, k_G);
    _EnsureClassData(idx_H, k_H);
    # Issue #449 A1': lazy centraliser materialisation for closed-form
    # E_+(m) idxs. idx_H is typically a subgroup (D_8 / Q_8 / EA) built
    # via BuildSimpleIndexLazy so this is usually a no-op; routed here
    # for safety in case a future caller passes a closed-form idx_H.
    if IsBoundGlobal("_EPlusCentraliserOf") then
        C_H := _EPlusCentraliserOf(idx_H, k_H);
    else
        C_H := idx_H.centralisers[k_H];
    fi;
    ct_H := idx_H.ct_centraliser[k_H];
    cc_H := idx_H.cc_centraliser[k_H];
    irr_H := idx_H.irreps[k_H];
    num_irreps_H := idx_H.num_irreps[k_H];
    n_classes_H := Length(cc_H);
    normaliser := Order(C_H);

    # Audit #456 B3: detect abelian C_H(a_H) and engage the Pontryagin
    # fast path. For abelian C_H, every class is a singleton (n_classes_H
    # = |C_H|), every irrep is 1-dim, and |class_size_h[t]| = 1 for all
    # t. We can skip the `Size(cls_H)` and `Representative(cls_H)` calls
    # and read elements + multiplicities directly. The math is unchanged
    # (Frobenius reciprocity on abelian C_H), but with fewer function
    # dispatches.
    abelian_fast := IsAbelian(C_H);

    # Pre-compute the class index in C_G(a_G) of phi(rep_h) for each
    # conjugacy class [h] of C_H(a_H), and also |[h]|. The
    # phi-images are used by every j_G in the per-irrep decomposition
    # so we amortise the conjugation + class-lookup work.
    chi_G_phi_values := [];
    class_size_h := [];
    if abelian_fast then
        # Abelian path: cc_H[j] is a singleton ConjugacyClass; we still
        # need `Representative(cc_H[j])` to get the matrix, but we can
        # skip the `Size(cls_H)` dispatch (always 1 for abelian).
        for j in [1..n_classes_H] do
            rep_h := Representative(cc_H[j]);
            phi_rep := conj * rep_h * conj^-1;
            cls_idx_G := ClassIndexInCentraliser(idx_G, k_G, phi_rep);
            Add(chi_G_phi_values, cls_idx_G);
            Add(class_size_h, 1);
        od;
    else
        for j in [1..n_classes_H] do
            cls_H := cc_H[j];
            rep_h := Representative(cls_H);
            phi_rep := conj * rep_h * conj^-1;
            # ClassIndexInCentraliser auto-materialises idx_G data for k_G.
            cls_idx_G := ClassIndexInCentraliser(idx_G, k_G, phi_rep);
            Add(chi_G_phi_values, cls_idx_G);
            Add(class_size_h, Size(cls_H));
        od;
    fi;

    # Helper closure: given j_G, return the length-num_irreps_H
    # vector of multiplicities a_l.
    #
    # For abelian C_H the inner sum is the Pontryagin dual evaluation:
    #   mult(chi_l_H) = (1/|H|) * sum_{h in C_H} chi_G(phi(h)) * conj(chi_l_H(h))
    # which is O(|H|) per chi_l_H. Total cost stays O(num_irreps_H *
    # n_classes_H) = O(|H|^2) for abelian H. The constant-factor saving
    # comes from avoiding `Size(cls_H)` lookups in the inner loop.
    decomposition_fn := function(j_G_arg)
        local chi_G_vals, t, val_chi_g, val_chi_l, acc, l_H, chi_l_H,
              result;
        # chi_{j_G}(phi(rep_h)) per H-class, precomputed.
        chi_G_vals := List([1..n_classes_H],
            t -> idx_G.irreps[k_G][j_G_arg][chi_G_phi_values[t]]);
        result := [];
        if abelian_fast then
            # Inner loop without `class_size_h[t]` multiplications (it's
            # always 1 for abelian H).
            for l_H in [1..num_irreps_H] do
                acc := 0;
                chi_l_H := irr_H[l_H];
                for t in [1..n_classes_H] do
                    acc := acc + chi_G_vals[t]
                                * ComplexConjugate(chi_l_H[t]);
                od;
                acc := acc / normaliser;
                if not IsInt(acc) then
                    Error("RestrictedIrrepDecomposition (abelian): ",
                          "non-integer multiplicity ", acc,
                          " for (k_G=", k_G, ", k_H=", k_H,
                          ", j_G=", j_G_arg, ", l_H=", l_H, ").");
                fi;
                if acc < 0 then
                    Error("RestrictedIrrepDecomposition (abelian): ",
                          "negative multiplicity ", acc,
                          " for (k_G=", k_G, ", k_H=", k_H,
                          ", j_G=", j_G_arg, ", l_H=", l_H, ").");
                fi;
                Add(result, acc);
            od;
        else
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
        fi;
        return result;
    end;

    return rec(
        # Per-H-class phi-image class index in C_G(a_G).
        phi_class_index_G := chi_G_phi_values,
        # Per-H-class size (for the inner-product weighting).
        h_class_sizes := class_size_h,
        # Helper closure: see above.
        decomposition := decomposition_fn,
        # Diagnostic: which path was used.
        abelian_fast := abelian_fast
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
    # Audit #456 C3: memoise BuildIntertwinerDataUntwisted(H) per
    # IdGroup(H). At m=7 in the K-4b spectral pipeline this saves
    # ~60-300 ms × |central-classes-of-G| per detecting subgroup.
    base_data := _RTS_GetBIDUCached(H);
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
        # B4 (#458 / was 2026-06-02 A-K4-4): `new_trace_on_W` is a thin
        # wrapper that calls `base_data.trace_on_W(k_H_arg, irrep_idx_H, h_H)`
        # (see #275 unscaling note above). `base_data` is from
        # `BuildIntertwinerDataUntwisted(H)`, so `trace_on_W` reduces to
        # `EvalIrr(idx_H, ...)`. Propagate the kind tag for batched lookup.
        trace_on_W_kind := "evalirr",
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


# ============================================================
# Public: RestrictTraceOnWToSubgroupProjective  (issue #328)
# ============================================================
#
# Per-branch projective restriction of a G-level intertwiner_data record
# carrying non-trivial omega-cocycle context to a subgroup H. This is the
# direct counterpart of `RestrictTraceOnWToSubgroup` but preserves the
# projective character information from the G-level slant 2-cocycle
# instead of substituting in the untwisted H baseline (the bug fixed by
# this issue).
#
# WHEN TO USE
# -----------
# Use this variant when the parent record was produced by
# `BuildKRRIntertwinerData(m, G, opts)` with a non-zero `opts.omega_vec`
# (i.e. it carries a `.projective_data` field bound by PR #327 / #323).
# In that case the G-level `trace_on_W` evaluates projective characters
# of `(C_G(a_G), α_{a_G}^G)`; the corresponding H-level restriction must
# evaluate projective characters of `(C_H(a_H), α_{a_H}^H)` for the
# pulled-back 2-cocycle, NOT the ordinary characters of C_H(a_H) as the
# untwisted baseline would give.
#
# At ω = 0 (or when `.projective_data` is absent / omega_vec is zero or
# fail), this function delegates to `RestrictTraceOnWToSubgroup` for
# byte-for-byte identical output (acceptance criterion 1 of #328).
#
# MATH
# ----
# Given the G-level slant 2-cocycle
#
#   α_{a_G}^G(x, y) := ω(x, y, a_G)
#                    − ω(x, y · a_G · y^{-1}, y)
#                    + ω(x · y · a_G · y^{-1} · x^{-1}, x, y)
#
# (the CGR/Mignard–Schauenburg slant of ω by the class rep a_G; the
# exact convention used by `_KRRI_AlphaG` in build_krr_intertwiner_data.g),
# and a conjugator `conj ∈ G` with `conj · a_H · conj^{-1} = a_G`, the
# H-level slant 2-cocycle on `C_H(a_H)` is the pullback
#
#   α_{a_H}^H(x_H, y_H) := α_{a_G}^G(conj · x_H · conj^{-1},
#                                     conj · y_H · conj^{-1})
#
# where x_H, y_H ∈ C_H(a_H). This is a 2-cocycle on `C_H(a_H)` because:
#
#   * conjugation by `conj` is a group homomorphism G → G whose
#     restriction maps `C_G(a_H) → C_G(a_G)` bijectively;
#   * `C_H(a_H) ⊆ C_G(a_H)`, so `conj · C_H(a_H) · conj^{-1} ⊆ C_G(a_G)`;
#   * α_{a_G}^G is a 2-cocycle on `C_G(a_G)` by the standard slant
#     identity (CGR §4, derived from ω's 3-cocycle equation), so its
#     pullback along a homomorphism is again a 2-cocycle.
#
# We then build the central extension of `C_H(a_H)` by `Z/m_omega` along
# α_{a_H}^H and pick the genuinely α-projective characters via the same
# helpers used at G-level (`_KRRI_BuildCentralExtension`,
# `_KRRI_ProjectiveCharsForG`, `_KRRI_TryMatchProjToIrr`). The result is
# memoised per H-class index.
#
# H-LEVEL EPSILON
# ---------------
# The K-1 / CT-modular-data formula in `ct_modular_data.g` uses
# `intertwiner_data.epsilon(g_i, g_j, a, b)` with sections t_a, s_b
# obtained from the transport list of the *underlying* index — for the
# H restriction this is the H-transport, i.e. `RepresentativeAction(H, ·)`.
# To stay consistent we wire the H-level epsilon through `EpsilonOmega`
# (the integer-phase backbone in epsilon_omega.g) with G replaced by H:
#
#   epsilon_H(g1, g2, a, b) := E(m_omega)^{
#       EpsilonOmega(H, omega_cb, g1, g2, a, b, m_omega) }
#
# where `omega_cb` is the cached G-level callable from the parent's
# projective context. Since H-elements are also G-elements, evaluating
# `omega_cb` on H-triples is just the inclusion-pullback `i^* ω` (same
# numerical formula). The sections t_a, s_b are picked from H, matching
# the convention used by `BuildTransports(idx_H)` in `_CTComputeSBlock`.
#
# INPUTS
# ------
#   intertwiner_data_G : record from BuildKRRIntertwinerData(m, G, opts)
#                        with `opts.omega_vec` non-zero. Must carry
#                        `.projective_data` (with `.ctx`,
#                        `.omega_vec`) and `.idx`. If `.projective_data`
#                        is absent or `omega_vec` is zero / fail, the
#                        call delegates to `RestrictTraceOnWToSubgroup`.
#   H                  : subgroup of intertwiner_data_G.group.
#
# OUTPUT RECORD
# -------------
# Same shape as `RestrictTraceOnWToSubgroup` plus a `.projective_data_H`
# diagnostic field:
#
#   .group         : H
#   .idx           : BuildSimpleIndex(H)
#   .transport     : BuildTransports(idx_H)
#   .trace_on_W    : function(k_H, irrep_idx_H, h_H) -> cyclotomic
#                    -- projective character of (C_H(a_H), α_{a_H}^H).
#   .epsilon       : function(g1, g2, a, b) -> cyclotomic
#                    -- H-level CGR phase via EpsilonOmega(H, ...).
#   .class_to_G    : per-H-class mapping (k_G, conj) as in
#                    RestrictTraceOnWToSubgroup.
#   .parent_G      : G.
#   .parent_data   : the original intertwiner_data_G.
#   .projective_data_H : rec(
#                    .ctx            -- parent's projective ctx
#                                       (omega_cb, m_omega, ...)
#                    .per_class      -- length |classes(H)|, lazy
#                                       projective records per H-class
#                    .per_class_perm -- length |classes(H)|, lazy
#                                       align permutation or "intrinsic"
#                    .proj_for_class -- callable: k_H -> proj record).
#   .source        : "projective-restriction".
#
RestrictTraceOnWToSubgroupProjective := function(intertwiner_data_G, H)
    local G, idx_H, transport_H, idx_G, class_to_G, k_H, a_H, mapping,
          base_data, gens_H, bad_gen, has_proj, omega_vec, ctx, omega_cb,
          m_omega, per_class, per_class_perm, proj_for_class,
          new_trace_on_W, new_epsilon, parent_data;
    G := intertwiner_data_G.group;
    gens_H := GeneratorsOfGroup(H);
    bad_gen := First(gens_H, g -> not (g in G));
    if bad_gen <> fail then
        Error("RestrictTraceOnWToSubgroupProjective: H has a generator ",
              bad_gen, " not in intertwiner_data_G.group.");
    fi;
    parent_data := intertwiner_data_G;
    # Decide whether the parent record actually carries non-trivial
    # projective context. If not, fall back to the untwisted variant
    # so callers can route everything through this function safely.
    has_proj := IsBound(parent_data.projective_data)
                and parent_data.projective_data <> fail;
    if has_proj then
        omega_vec := parent_data.projective_data.omega_vec;
        if omega_vec = fail then
            has_proj := false;
        elif Length(omega_vec) > 0 and ForAll(omega_vec, x -> x = 0) then
            # All-zero omega_vec is mathematically α ≡ 0, which gives
            # back the untwisted characters byte-for-byte (via
            # `_KRRI_TryMatchProjToIrr`'s alignment). But the projective
            # path is the slow option; the fast equivalent is to
            # delegate to the untwisted restriction. Both produce
            # byte-for-byte identical CT modular data, by the same
            # alignment property used in the G-level projective tests
            # (see test_build_krr_intertwiner_data_projective.g P1).
            has_proj := false;
        fi;
    fi;
    if not has_proj then
        return RestrictTraceOnWToSubgroup(intertwiner_data_G, H);
    fi;

    _RTS_EnsureProjectiveHelpers();

    # Build H-side simple index + transports the same way the untwisted
    # restriction does.
    base_data := BuildIntertwinerDataUntwisted(H);
    idx_H := base_data.idx;
    transport_H := base_data.transport;
    idx_G := intertwiner_data_G.idx;

    # Build the H-class -> (G-class, conjugator) mapping.
    class_to_G := [];
    for k_H in [1..Length(idx_H.reps)] do
        a_H := idx_H.reps[k_H];
        mapping := _RTS_FindGClassOf(idx_G, a_H, G);
        Add(class_to_G, mapping);
    od;

    ctx := parent_data.projective_data.ctx;
    omega_cb := ctx.omega_cb;
    m_omega := ctx.m_omega;

    # Per-H-class projective table cache. Each entry, on first query,
    # holds the rec returned by `_KRRI_ProjectiveCharsForG(C_H,
    # alpha_H_a, m_omega)`. The corresponding `per_class_perm[k_H]` is:
    #   * a permutation list  perm : Irr(C_H(a_H)) -> proj.table  when
    #     α_{a_H}^H is a coboundary on C_H(a_H);
    #   * the symbol "intrinsic" when α_{a_H}^H is genuinely non-trivial
    #     in H^2(C_H(a_H); Z/m_omega) (the projective characters cannot
    #     be aligned with the ordinary ones).
    per_class := List([1..Length(idx_H.classes)], _ -> fail);
    per_class_perm := List([1..Length(idx_H.classes)], _ -> fail);

    proj_for_class := function(k_H_arg)
        local a_H_loc, conj_loc, a_G_loc, C_H, alpha_H_a, proj, perm;
        if per_class[k_H_arg] <> fail then
            return per_class[k_H_arg];
        fi;
        a_H_loc := idx_H.reps[k_H_arg];
        conj_loc := class_to_G[k_H_arg].conj;
        a_G_loc := idx_G.reps[class_to_G[k_H_arg].k_G];
        # Issue #449 A1': lazy centraliser materialisation (no-op for
        # non-closed-form idxs; see RestrictedIrrepDecomposition note).
        if IsBoundGlobal("_EPlusCentraliserOf") then
            C_H := _EPlusCentraliserOf(idx_H, k_H_arg);
        else
            C_H := idx_H.centralisers[k_H_arg];
        fi;
        # Pullback closure: α_{a_H}^H(x_H, y_H) =
        #   α_{a_G}^G(conj · x_H · conj^{-1}, conj · y_H · conj^{-1}).
        # _KRRI_AlphaG takes g = a_G and the (already-G-conjugated) x, y.
        alpha_H_a := function(x_H, y_H)
            return _KRRI_AlphaG(omega_cb, m_omega, a_G_loc,
                                 conj_loc * x_H * conj_loc^-1,
                                 conj_loc * y_H * conj_loc^-1);
        end;
        proj := _KRRI_ProjectiveCharsForG(C_H, alpha_H_a, m_omega);
        per_class[k_H_arg] := proj;
        # Align with Irr(C_H(a_H)) when α is a coboundary; "intrinsic"
        # otherwise. _EnsureClassData materialises lazy idx_H slices
        # (no-op for eager).
        _EnsureClassData(idx_H, k_H_arg);
        perm := _KRRI_TryMatchProjToIrr(
            proj, C_H, idx_H.irreps[k_H_arg], idx_H.cc_centraliser[k_H_arg]);
        if perm = fail then
            per_class_perm[k_H_arg] := "intrinsic";
        else
            per_class_perm[k_H_arg] := perm;
        fi;
        return proj;
    end;

    new_trace_on_W := function(k_H_arg, irrep_idx_arg, h_arg)
        local proj, perm, j;
        proj := proj_for_class(k_H_arg);
        perm := per_class_perm[k_H_arg];
        if perm = "intrinsic" then
            j := irrep_idx_arg;
        else
            j := perm[irrep_idx_arg];
        fi;
        if j < 1 or j > Length(proj.table) then
            Error("RestrictTraceOnWToSubgroupProjective: ",
                  "irrep_idx ", irrep_idx_arg, " (mapped to ", j,
                  ") out of bounds for k_H = ", k_H_arg,
                  " (|proj.table| = ", Length(proj.table), ").");
        fi;
        return proj.lift(h_arg) ^ proj.table[j];
    end;

    # H-level epsilon: pull back ω from G to H via the inclusion, then
    # use the standard integer-phase backbone. We use H (not G) as the
    # ambient group for `RepresentativeAction` to stay consistent with
    # the H-side transport list used by `_CTComputeSBlock`.
    new_epsilon := function(g1, g2, a, b)
        local int_phase;
        int_phase := EpsilonOmega(H, omega_cb, g1, g2, a, b, m_omega);
        return E(m_omega) ^ int_phase;
    end;

    return rec(
        group        := H,
        idx          := idx_H,
        transport    := transport_H,
        trace_on_W   := new_trace_on_W,
        epsilon      := new_epsilon,
        class_to_G   := class_to_G,
        parent_G     := G,
        parent_data  := parent_data,
        source       := "projective-restriction",
        projective_data_H := rec(
            ctx              := ctx,
            per_class        := per_class,
            per_class_perm   := per_class_perm,
            proj_for_class   := proj_for_class,
            omega_vec        := omega_vec
        )
    );
end;;
