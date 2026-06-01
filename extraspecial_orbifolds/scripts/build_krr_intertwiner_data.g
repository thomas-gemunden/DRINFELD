# build_krr_intertwiner_data.g
#
# K-4a-T4b ("KR-Bridge"): real KRR lattice intertwiner data for K-4.
# Closes #188.
#
# PUBLIC ENTRY POINT
# ==================
#
#   BuildKRRIntertwinerData(m, G [, opts])
#       -> rec(group, idx, transport, trace_on_W, epsilon, source, ...)
#
# Returns a record matching the API shape of `BuildIntertwinerDataUntwisted`
# (in krr_projector.g), so the result is directly consumable by K-1's
# `ProjectorFormula(W_g1, W_g2, intertwiner_data)`.
#
# In contrast to `BuildIntertwinerDataUntwisted` (which produces the
# trivial omega = 0 baseline by definition), this builder declares its
# *lattice provenance*: the trace_on_W / epsilon it returns derive from
# the Barnes-Wall lattice intertwiners T_h on the Bakalov-Kac defect
# representation Omega_0 (per KRR §4, arXiv:2411.13646).
#
# For the KRR CT case (cocycle c_g trivial as a cochain, verified by KRR
# at m in {3, 5, 7} -- see `test_defect_rep_optim.g` Tests 3 + 4), CGR's
# gauge-freedom argument (CGR p.25 after eq 5.22) lets us fix
#       epsilon_a ≡ 1     (CT-gauge),
# and the lattice spectral decomposition coincides numerically with
# GAP's Irr(C_G(a)) ordering, so
#       trace_on_W(class_idx, irrep_idx, h) = chi_{irrep_idx}(h)
# matching the standard centraliser-character functional. See the
# research note at
#   docs/superpowers/research/2026-05-17-epsilon-extraction-from-krr.md
# (Section 3.2 and Section 5) for the derivation that
# ε ≡ 1 and trace_on_W = EvalIrr is the mathematically correct choice
# for ω = 0 in the KRR CT case.
#
# CONSEQUENCE: at omega = 0, `BuildKRRIntertwinerData(m, G)` produces the
# SAME numeric output as `BuildIntertwinerDataUntwisted(G)` (modulo the
# extra `.source` / `.spectral_data` provenance fields). This is the
# correctness witness: the K-3 anchor passes by construction.
#
# WHEN THIS FUNCTION BECOMES NON-TRIVIAL
# ======================================
# For non-trivial omega (V-1, issue #14) the CT-gauge choice breaks
# down: `epsilon` becomes the actual omega-derived CGR phase (PR #321,
# wiring shipped 2026-05-20 via #316), and `trace_on_W` returns
# PROJECTIVE character values for the slant 2-cocycle α_g (issue
# #323, shipped 2026-05-20). Both hooks are exposed via the
# `omega_vec` option below; on a non-zero `omega_vec` the
# `spectral_source = "auto"` mode routes to "projective" regardless
# of m.
#
# Original (issue #188) comment retained for context: at the time of
# writing #188, KRR conjecture ω = 0 (KRR §5.3); only the lite /
# spectral paths were filled in. The ω ≠ 0 paths were stubs.
#
# OPTIONS RECORD
# ==============
# `opts` (optional, third argument) is a record. Recognised fields:
#   .omega_vec       : H^3 cocycle for non-trivial twist (default: ω = 0).
#                      If provided as an integer vector, epsilon switches
#                      to V-1's `EpsilonOmegaPhase` (#14) AND trace_on_W
#                      switches to the projective-character path (#323).
#                      For ω = 0 (or omega_vec absent / a zero vector)
#                      epsilon ≡ 1 and trace_on_W uses the centraliser-
#                      character functional (EvalIrr).
#   .spectral_source : one of:
#       "auto"     : at ω = 0, use lattice eigenspace data at m = 3
#                    (where dense T_h is feasible) and the standard
#                    character functional at m ≥ 5. At ω ≠ 0, route to
#                    the projective-character path (issue #323) regardless
#                    of m. DEFAULT.
#       "lite"     : always use the standard character functional
#                    (`EvalIrr`). Identical to `BuildIntertwinerDataUntwisted`
#                    numerically when ω = 0. At ω ≠ 0 this is
#                    mathematically WRONG (returns regular characters
#                    instead of projective ones); the option is retained
#                    for diagnostic comparison only.
#       "dense_spectral" : run `BuildKRRSpectralCharacters(m)` and use
#                    its `trace_on_W` directly. Only feasible at m = 3
#                    (dense Omega_0 = 16-dim). Ignored at ω ≠ 0 (the
#                    projective path takes over).
#       "sparse_spectral" : run `BuildKRRSpectralCharactersSparse(m)`.
#                    For m = 5 use the lattice-multiplicities path;
#                    for m = 7 falls back to "lite" with a diagnostic
#                    warning (the Gauss-sum path is a future workstream).
#                    Ignored at ω ≠ 0 (the projective path takes over).
#       "projective": always use the projective-character path (issue
#                    #323). At ω = 0 this is mathematically equivalent
#                    to "lite" (the projective table for the trivial
#                    cocycle is the ordinary character table, byte-for-
#                    byte after re-indexing); useful as a sanity check
#                    of the projective machinery. At ω ≠ 0 this is the
#                    only mathematically correct mode.
#   .verbose         : print build progress / decisions. Default false.
#   .lazy            : if true, use BuildSimpleIndexLazy +
#                      BuildTransportsLazy from K-2c (#129) to defer
#                      per-class CharacterTable + transport BFS work
#                      until queried. REQUIRED at m >= 7 (eager idx
#                      build is intractable for |classes| ~ 16K).
#                      Default false.
#
# RETURNED RECORD FIELDS
# ======================
#   .group         : G                       (as passed in)
#   .idx           : BuildSimpleIndex(G)
#   .transport     : BuildTransports(idx)
#   .trace_on_W    : function(class_idx, irrep_idx, h) -> cyclotomic
#   .epsilon       : function(g1, g2, a, b) -> cyclotomic
#   .source        : "krr-lattice" (provenance marker)
#   .source_detail : Concatenation("spectral_source=", spectral_source,
#                                    ", omega_vec=", String(omega_vec))
#   .m             : m
#   .omega_is_zero : true iff omega_vec is absent or all-zero
#   .spectral_data : (only when `spectral_source` ∈ {"dense_spectral",
#                    "sparse_spectral"}) the underlying spectral record
#                    from `BuildKRRSpectralCharacters[Sparse]`.
#
# DEPENDENCIES
# ============
# We assume the consumer has Read (in any order before this file):
#   * untwisted_modular_data.g    (BuildSimpleIndex, BuildTransports,
#                                    EvalIrr, ClassIndexInCentraliser)
#   * krr_projector.g             (BuildIntertwinerDataUntwisted — only
#                                    referenced from comments / fallback
#                                    rationale; not strictly required)
# Optional (only loaded if needed by the requested `spectral_source`):
#   * krr_spectral_characters.g       (BuildKRRSpectralCharacters at m=3)
#   * krr_spectral_characters_sparse.g (BuildKRRSpectralCharactersSparse
#                                         at m=5)
#   * epsilon_omega_phase.g           (EpsilonOmegaPhase for omega ≠ 0,
#                                       V-1 / #14)
#
# Per the codebase convention, this file does NOT auto-Read its optional
# deps; the consumer / driver must Read them in advance if a non-default
# `spectral_source` is requested. The function raises a clear Error if a
# requested function is missing.


# ============================================================
# Capture this file's directory at load time. INPUT_FILENAME() returns
# whatever GAP is currently reading at *call* time (not at function-
# definition time), so for any auto-Read fallback used inside a
# closure-returning helper (e.g. `_KRRI_BuildEpsilon` -> V-1 wiring),
# we need to snapshot the directory now, while the file is being
# Read'd, and reference the snapshot from inside the helper.
# ============================================================

_BUILDKRR_LOAD_DIR := fail;;
_BUILDKRR_LOAD_SELF := INPUT_FILENAME();;
if _BUILDKRR_LOAD_SELF <> fail and _BUILDKRR_LOAD_SELF <> "stream" then
    _BUILDKRR_LOAD_DIR := _BUILDKRR_LOAD_SELF{
        [1..Length(_BUILDKRR_LOAD_SELF)
            - Length("/build_krr_intertwiner_data.g")]};
fi;;


# ============================================================
# Helper: is a vector all-zero (treating GF(2) or Z elements uniformly)?
# ============================================================

_KRRI_IsZeroVec := function(v)
    local x;
    if v = fail or v = [] then return true; fi;
    for x in v do
        if x <> 0 and x <> 0 * x then
            return false;
        fi;
    od;
    return true;
end;;


# ============================================================
# Helper: resolve and validate the `opts` record.
# ============================================================

_KRRI_DefaultOpts := function(m)
    return rec(
        omega_vec       := fail,
        spectral_source := "auto",
        verbose         := false,
        lazy            := false   # m >= 7 callers should set true.
    );
end;;

_KRRI_NormaliseOpts := function(m, user_opts)
    local opts, recognised, fld;
    opts := _KRRI_DefaultOpts(m);
    if user_opts = fail then
        return opts;
    fi;
    if not IsRecord(user_opts) then
        Error("BuildKRRIntertwinerData: `opts` must be a record or fail; got ",
              user_opts);
    fi;
    recognised := ["omega_vec", "spectral_source", "verbose", "lazy"];
    for fld in recognised do
        if IsBound(user_opts.(fld)) then
            opts.(fld) := user_opts.(fld);
        fi;
    od;
    if not opts.spectral_source in
            ["auto", "lite", "dense_spectral", "sparse_spectral",
             "projective"] then
        Error("BuildKRRIntertwinerData: opts.spectral_source must be one of ",
              "\"auto\", \"lite\", \"dense_spectral\", \"sparse_spectral\", ",
              "\"projective\"; got ", opts.spectral_source);
    fi;
    return opts;
end;;


# ============================================================
# Helper: pick the spectral_source under "auto" given m.
#
# At ω ≠ 0 the auto-resolver is overridden upstream (in
# `BuildKRRIntertwinerData`) to route to the projective path
# regardless of m. This helper is only consulted in the ω = 0
# branch, where lattice mode selection by m is meaningful.
# ============================================================

_KRRI_ResolveAutoSource := function(m)
    if m = 3 then
        # Dense Omega_0 = 16-dim — feasible. Only use dense_spectral if
        # the spectral builder is loaded; otherwise fall back to lite
        # (which is numerically equivalent for ω = 0 per the T4a
        # research note Section 3.2).
        if IsBoundGlobal("BuildKRRSpectralCharacters") then
            return "dense_spectral";
        fi;
        return "lite";
    elif m = 5 then
        # Dense is infeasible (2^16-dim); use sparse if available.
        if IsBoundGlobal("BuildKRRSpectralCharactersSparse") then
            return "sparse_spectral";
        fi;
        return "lite";
    elif m = 7 then
        # Dense is infeasible (2^64-dim); sparse uses TraceOnOmega0Gauss
        # internally (issue #236, integrated 2026-05-20 via #316). At m=7
        # the per-class trace path is poly-time per class; the dominant
        # cost is BuildSimpleIndexLazy + per-class CT loads (~hours total),
        # so by default we still fall back to lite. Set spectral_source
        # := "sparse_spectral" explicitly to opt in.
        return "lite";
    else
        # Larger m: never use spectral; lite mode (ε = 1, trace = EvalIrr)
        # is the mathematically correct ω = 0 choice per the T4a research
        # note (Section 3.2).
        return "lite";
    fi;
end;;


# ============================================================
# Build the trace_on_W and epsilon callables for a given mode.
# ============================================================

# "Lite" mode: standard centraliser-character functional, ε = 1. This
# is the ω = 0 KRR-CT baseline AND is mathematically identical to
# `BuildIntertwinerDataUntwisted(G)`.
_KRRI_BuildLiteCallables := function(idx)
    return rec(
        trace_on_W := function(class_idx, irrep_idx, h)
            return EvalIrr(idx, class_idx, irrep_idx, h);
        end,
        epsilon    := function(g1, g2, a, b) return 1; end,
        spectral_data := fail
    );
end;;

# "Dense spectral" mode: at m = 3 we can build all T_h matrices on the
# 16-dim Omega_0 and run the joint-eigendecomposition. The resulting
# `trace_on_W` honours the lattice spectral multiplicities.
#
# *** WARNING — K-1 INDEX-SHAPE MISMATCH ***
# The spectral builder (BuildKRRSpectralCharacters) uses a different
# `irrep_idx` convention from BuildSimpleIndex: for the central class
# (a = -I), spectral indexes the joint EIGENSPACES (one per linear
# character actually appearing in Omega_0; e.g. 12 for m = 3), whereas
# BuildSimpleIndex uses GAP's full `Irr(C_G(a))` (e.g. 65 for m = 3 of
# which only the linear characters can appear in Omega_0). Calling
# `ProjectorFormula` with `irrep_idx > Length(eigenspaces)` for the
# central class will Error.
#
# Use dense_spectral mode for DIAGNOSTIC inspection of the lattice
# spectral decomposition. For K-1-compatible omega = 0 work, use
# spectral_source := "lite" — the T4a research note (Section 3.2)
# proves the lite mode produces the mathematically correct trace
# values for KRR's CT case.
#
# CAVEAT 2: BuildKRRSpectralCharacters uses `EmUnimodGroup(m)` as its
# group. If the caller's G is in a DIFFERENT GAP family (e.g.
# EmGroup(m) or its pc-group), we go through the translation layer
# (em_eplus_translate.g) to wrap the trace_on_W in the consumer's
# class structure.
_KRRI_BuildDenseSpectralCallables := function(m, G, idx, verbose)
    local sd, tr_rec, g_to_em_class, k_g, k_eu, j, em_classes,
          translate_h, same_underlying_group, sd_gens, G_gens, i;
    if not IsBoundGlobal("BuildKRRSpectralCharacters") then
        Error("BuildKRRIntertwinerData: spectral_source = \"dense_spectral\" ",
              "requires `BuildKRRSpectralCharacters` to be in scope. ",
              "Read(\"krr_spectral_characters.g\") first.");
    fi;
    if verbose then
        Print("[BuildKRRIntertwinerData] m = ", m,
              ": building dense spectral data via ",
              "BuildKRRSpectralCharacters(", m, ")...\n");
    fi;
    sd := BuildKRRSpectralCharacters(m);
    # sd.group is a fresh EmUnimodGroup(m); sd.idx is its BuildSimpleIndex.
    # We need to align G's class indices with sd.idx's class indices,
    # and convert h in G to h in sd.group for trace_on_W queries.
    #
    # Three cases:
    # (1) G IS sd.group (same GAP instance) — no work needed.
    # (2) G is an isomorphic matrix group with the same generator set
    #     (e.g. caller passed a fresh EmUnimodGroup(m)) — same matrices
    #     give an identity element-level "translation".
    # (3) G is in a different family (EPlusGroup, IsomorphismPcGroup
    #     image) — need a proper isomorphism. Use EmEPlusTranslateAgainst
    #     when G is EPlusGroup-shaped, otherwise GAP's IsomorphismGroups.
    if G = sd.group then
        return rec(
            trace_on_W := sd.trace_on_W,
            epsilon    := function(g1, g2, a, b) return 1; end,
            spectral_data := sd
        );
    fi;
    # Same matrix group representation? Test by generator-set equality.
    sd_gens := GeneratorsOfGroup(sd.group);
    G_gens := GeneratorsOfGroup(G);
    same_underlying_group := Length(sd_gens) = Length(G_gens);
    if same_underlying_group then
        for i in [1..Length(sd_gens)] do
            if sd_gens[i] <> G_gens[i] then
                same_underlying_group := false;
                break;
            fi;
        od;
    fi;
    if same_underlying_group then
        # Generators match — elements are interchangeable as F2 matrices.
        # Just remap class indices.
        em_classes := sd.idx.classes;
        g_to_em_class := [];
        for k_g in [1..Length(idx.reps)] do
            k_eu := fail;
            for j in [1..Length(em_classes)] do
                if idx.reps[k_g] in em_classes[j] then
                    k_eu := j;
                    break;
                fi;
            od;
            if k_eu = fail then
                Error("BuildKRRIntertwinerData: G class ", k_g,
                      " rep ", idx.reps[k_g],
                      " not found in any spectral idx class. ",
                      "(EmUnimodGroup classes may have shifted ordering.)");
            fi;
            Add(g_to_em_class, k_eu);
        od;
        # h-level: identity, since the underlying matrix representation is shared.
        translate_h := h -> h;
        return rec(
            trace_on_W := function(class_idx, irrep_idx, h)
                return sd.trace_on_W(g_to_em_class[class_idx], irrep_idx,
                                      translate_h(h));
            end,
            epsilon    := function(g1, g2, a, b) return 1; end,
            spectral_data := sd,
            g_to_em_class := g_to_em_class
        );
    fi;
    # Different family. Try EmEPlusTranslateAgainst if applicable.
    if IsBoundGlobal("EmEPlusTranslateAgainst")
       and IsBoundGlobal("EPlusGroup")
       and Order(G) = Order(EPlusGroup(m)) then
        tr_rec := EmEPlusTranslateAgainst(m, G, sd.group);
        em_classes := sd.idx.classes;
        g_to_em_class := [];
        for k_g in [1..Length(idx.reps)] do
            k_eu := fail;
            for j in [1..Length(em_classes)] do
                if Image(tr_rec.psi_inv, idx.reps[k_g]) in em_classes[j] then
                    k_eu := j;
                    break;
                fi;
            od;
            if k_eu = fail then
                Error("BuildKRRIntertwinerData: G class ", k_g,
                      " has no preimage in EmUnimodGroup(", m, ")'s classes ",
                      "— iso may be wrong.");
            fi;
            Add(g_to_em_class, k_eu);
        od;
        return rec(
            trace_on_W := function(class_idx, irrep_idx, h)
                local cu, hu;
                cu := g_to_em_class[class_idx];
                hu := Image(tr_rec.psi_inv, h);
                return sd.trace_on_W(cu, irrep_idx, hu);
            end,
            epsilon    := function(g1, g2, a, b) return 1; end,
            spectral_data := sd,
            translate := tr_rec,
            g_to_em_class := g_to_em_class
        );
    fi;
    # Fallback: G is neither sd.group nor EPlusGroup(m). Use lite mode.
    if verbose then
        Print("[BuildKRRIntertwinerData] G is not EmUnimodGroup(", m,
              ") or EPlusGroup(", m,
              "); falling back to lite mode for trace_on_W.\n");
    fi;
    return _KRRI_BuildLiteCallables(idx);
end;;

# "Sparse spectral" mode: at m = 5 the dense matrix is 65536x65536 per
# h; use `BuildKRRSpectralCharactersSparse(m)` which has the same record
# shape as the dense version but computes traces via the closed-form
# Schur sum (krr_spectral_characters_sparse.g). At m = 7 the entry-
# enumeration path is infeasible (2^64 entries per trace); the sparse
# builder dispatches to `TraceOnOmega0Gauss` (issue #236, verified at
# m=3 and m=5 cross-validation in `tests/test_krr_gauss_sum.g`).
#
# #316 follow-up: previously this function short-circuited m = 7 to
# lite mode with a "future work" notice. The Gauss-sum branch has
# landed (TraceOnOmega0Gauss is fully implemented and tested at
# m={3,5}); we now route m = 7 through the sparse path normally. The
# wall-time at m = 7 is dominated by the per-class CT load (~1-2 min
# per centraliser × 16K classes in the lazy-idx fallback, though only
# the central class actually exercises the sparse trace).
_KRRI_BuildSparseSpectralCallables := function(m, G, idx, verbose)
    local sd;
    if not IsBoundGlobal("BuildKRRSpectralCharactersSparse") then
        Error("BuildKRRIntertwinerData: spectral_source = \"sparse_spectral\" ",
              "requires `BuildKRRSpectralCharactersSparse` to be in scope. ",
              "Read(\"krr_spectral_characters_sparse.g\") first.");
    fi;
    if verbose then
        Print("[BuildKRRIntertwinerData] m = ", m,
              ": building sparse spectral data via ",
              "BuildKRRSpectralCharactersSparse(", m, ")...\n");
    fi;
    sd := BuildKRRSpectralCharactersSparse(m);
    if G = sd.group then
        return rec(
            trace_on_W := sd.trace_on_W,
            epsilon    := function(g1, g2, a, b) return 1; end,
            spectral_data := sd
        );
    fi;
    # G ≠ sd.group: defer to the established translation layer
    # (TranslateSpectralDataToEPlus). This requires em_eplus_translate.g
    # to be loaded.
    if not IsBoundGlobal("TranslateSpectralDataToEPlus") then
        Error("BuildKRRIntertwinerData: G is not the EmUnimodGroup(", m,
              ") instance held by the spectral builder, AND ",
              "`TranslateSpectralDataToEPlus` (the family-translation ",
              "bridge) is not bound. Read(\"em_eplus_translate.g\") first.");
    fi;
    sd := TranslateSpectralDataToEPlus(sd, G);
    return rec(
        trace_on_W := sd.trace_on_W,
        epsilon    := sd.epsilon,    # already wrapped to ε ≡ 1 by translate
        spectral_data := sd
    );
end;;


# ============================================================
# Projective-character path (K-4a-T4c projective, issue #323).
#
# At ω ≠ 0 the centraliser representation that K-1's `ProjectorFormula`
# sees on each W_g is a GENUINE projective representation (not a linear
# one), with 2-cocycle α_g obtained from ω by the standard CGR slant:
#
#   α_g(x, y) := ω(x, y, g)
#              − ω(x, y g y^{-1}, y)
#              + ω(x y g y^{-1} x^{-1}, x, y).                  (*)
#
# This matches `alphag(g)(f)(x, y)` in `src/universal_coefficients.g`
# (which is the Mignard-Schauenburg / CGR convention). The trace
# `trace_on_W(class_idx, irrep_idx, h)` must therefore return the
# projective-character value
#
#   χ_{irrep_idx}^{α_g}(h)
#
# of C_G(g) for the α_g-projective character of index `irrep_idx`.
#
# Implementation. We avoid loading `fsi_wrapper.g` here (which would
# clobber `UniversalCoefficientsTheorem` from `src/modular_data.g`)
# and write self-contained `_KRRI_BuildCentralExtension` /
# `_KRRI_ProjectiveCharsForG` helpers patterned after that file's
# `BuildCentralExtension` / `ProjectiveCharactersDirect`.
#
# Cocycle source. We compute α_g on the fly using the cached omega
# callable from `epsilon_omega_phase.g` (`_EOP_GetContext`). One
# `_EOP_GetContext(omega_vec, G)` call per `BuildKRRIntertwinerData`
# invocation gives us the bar 3-cocycle callable `ctx.omega_cb`; α_g
# is then a 2-arg closure over (g, ctx.omega_cb, ctx.m_omega).
#
# Caching. Per class index we build the central extension and pick
# the projective character table lazily (on first `trace_on_W` query
# for that class). The cache lives in a closure variable
# `proj_table_cache` keyed by class_idx.
#
# Cost. The dominant cost is `BuildCentralExtension(C, α_g, m_omega)`,
# which is O(|C|² · m_omega) permutation arithmetic to enumerate the
# group, plus `Irr(Gaa)` for `Gaa` of order |C| · m_omega (so the CT
# build is the bottleneck at large centralisers). The pi-style cache
# is keyed at class-idx granularity; calling `trace_on_W` repeatedly
# for the same class is O(1) after the first.
# ============================================================

# Helper: integer α_g(x, y) for the centraliser cocycle slant of ω by g.
# Returns an integer in [0, m_omega) (mod m_omega). `omega_cb` is the bar
# 3-cocycle callable returned by HAP's `StandardCocycle`, i.e. a function
# (a, b, c) -> integer in Z/m_omega.
_KRRI_AlphaG := function(omega_cb, m_omega, g, x, y)
    local v;
    v := omega_cb(x, y, g)
       - omega_cb(x, y*g*y^-1, y)
       + omega_cb(x*y*g*y^-1*x^-1, x, y);
    return v mod m_omega;
end;;

# Helper: build the central extension of C by Z/o along α as a concrete
# permutation group, plus the section lift. `alpha(x, y) -> int` returns
# an additive Z/o exponent (i.e. in [0, o)). This is a direct port of
# `BuildCentralExtension` from `fsi_wrapper.g` lines 220-283, isolated
# under a private name to avoid clobbering that wrapper's definition.
_KRRI_BuildCentralExtension := function(C, alpha, o)
    local elemsC, baseSize, n, embed, t_perm, b_perms, b, b_img, lift,
          Caa, fibreGen;
    elemsC := Elements(C);
    baseSize := Size(C);
    n := baseSize * o;
    embed := function(gIdx, a)
        return (gIdx - 1) * o + (a mod o) + 1;
    end;
    t_perm := PermList(List([1..n], function(k)
        local gIdx, a;
        a := ((k - 1) mod o);
        gIdx := QuoInt(k - 1, o) + 1;
        return embed(gIdx, a + 1);
    end));
    b_perms := [];
    for b in GeneratorsOfGroup(C) do
        b_img := List([1..n], function(k)
            local gIdx, a, g, gb, gbIdx, exp;
            a := (k - 1) mod o;
            gIdx := QuoInt(k - 1, o) + 1;
            g := elemsC[gIdx];
            gb := g * b;
            gbIdx := Position(elemsC, gb);
            exp := alpha(g, b);
            return embed(gbIdx, a + exp);
        end);
        Add(b_perms, PermList(b_img));
    od;
    Caa := Group(Concatenation([t_perm], b_perms));
    lift := function(g)
        local img;
        img := List([1..n], function(k)
            local gIdx, a, g0, gg, ggIdx, exp;
            a := (k - 1) mod o;
            gIdx := QuoInt(k - 1, o) + 1;
            g0 := elemsC[gIdx];
            gg := g0 * g;
            ggIdx := Position(elemsC, gg);
            exp := alpha(g0, g);
            return embed(ggIdx, a + exp);
        end);
        return PermList(img);
    end;
    fibreGen := t_perm;
    return rec(
        Caa := Caa,
        lift := lift,
        fibreGen := fibreGen,
        Base := C,
        FibreOrder := o,
        ExtensionSize := n
    );
end;;

# Helper: project the irreducible characters of Caa down to projective
# characters of C with cocycle α. A character chi of Caa is a projective
# character of C iff chi(t)/chi(1) = E(o) where t is the central
# generator (of order o).
_KRRI_ProjectiveCharsForG := function(C, alpha, o)
    local ext, ire, proj_table, chi, dim, fibre_val, target;
    ext := _KRRI_BuildCentralExtension(C, alpha, o);
    ire := Irr(ext.Caa);
    proj_table := [];
    for chi in ire do
        dim := One(ext.Caa) ^ chi;
        fibre_val := (ext.fibreGen) ^ chi;
        target := E(o) * dim;
        if fibre_val = target then
            Add(proj_table, chi);
        fi;
    od;
    return rec(
        Caa := ext.Caa,
        lift := ext.lift,
        table := proj_table,
        fibreGen := ext.fibreGen,
        FibreOrder := o,
        Base := C
    );
end;;

# Helper: when α is a coboundary (in particular when ω = 0 so α ≡ 0
# pointwise), the projective characters of C ARE the ordinary characters
# of C (up to the central extension's gauge). We attempt to MATCH each
# entry of `proj.table` against `irreps_of_C` (= GAP's Irr(C)) so that
# the resulting `chi_lookup[k] = proj.table[k']` evaluated at lift(h)
# equals `irreps_of_C[k](h)`. If matching fails for any k, returns fail
# (caller can then use the intrinsic order).
#
# Matching algorithm: for each ordinary character k of C, find the j ∈
# [1..|proj.table|] such that  chi(lift(rep)) = irreps_of_C[k](rep)  for
# every conjugacy-class representative of C. Returns the permutation
# pi: k -> j, or fail if no consistent assignment exists.
#
# This is used ONLY for the byte-for-byte sanity test at ω = 0 (or more
# generally when α is a coboundary). At genuinely non-trivial cohomology
# class the projective characters cannot be matched to ordinary ones
# (their dimensions divide |C| but their values at non-class-1 elements
# differ), and we return fail.
_KRRI_TryMatchProjToIrr := function(proj, C, irreps_of_C, cc_of_C)
    local cls_reps, perm, k, j, chi_proj, chi_ord, matched, all_match,
          rep, val_proj, val_ord;
    cls_reps := List(cc_of_C, Representative);
    if Length(proj.table) <> Length(irreps_of_C) then
        return fail;
    fi;
    perm := [];
    for k in [1..Length(irreps_of_C)] do
        chi_ord := irreps_of_C[k];
        matched := fail;
        for j in [1..Length(proj.table)] do
            if j in perm then continue; fi;
            chi_proj := proj.table[j];
            all_match := true;
            for rep in cls_reps do
                val_proj := proj.lift(rep) ^ chi_proj;
                val_ord := rep ^ chi_ord;
                if val_proj <> val_ord then
                    all_match := false;
                    break;
                fi;
            od;
            if all_match then
                matched := j;
                break;
            fi;
        od;
        if matched = fail then
            return fail;
        fi;
        perm[k] := matched;
    od;
    return perm;
end;;

# Build the projective trace_on_W callable for a given (omega_vec, G).
# Returns a record:
#   .trace_on_W(class_idx, irrep_idx, h) -> cyclotomic
#   .epsilon                              (the V-1 callable already
#                                          wired by the main builder
#                                          path -- not duplicated here)
#   .spectral_data := fail
#   .projective_data := rec(
#       ctx                 := _EOP_GetContext(omega_vec, G),
#       per_class           := list of fail (lazy) | proj record (built),
#       per_class_perm      := list of fail | permutation | "intrinsic",
#       proj_for_class      := callable class_idx -> proj record (lazy
#                              materialisation; deterministic per
#                              instance)
#   )
_KRRI_BuildProjectiveCallables := function(omega_vec, G, m, idx, verbose)
    local ctx, omega_cb, m_omega, per_class, per_class_perm,
          proj_for_class, trace_fn, _cand;
    if not IsBoundGlobal("_EOP_GetContext") then
        # Auto-load epsilon_omega_phase.g if not already in scope.
        if _BUILDKRR_LOAD_DIR <> fail then
            _cand := Concatenation(_BUILDKRR_LOAD_DIR,
                                    "/epsilon_omega_phase.g");
            if IsExistingFile(_cand) then
                Read(_cand);
            fi;
        fi;
    fi;
    if not IsBoundGlobal("_EOP_GetContext") then
        Error("BuildKRRIntertwinerData: spectral_source = \"projective\" ",
              "(or omega != 0 auto-routing) requires `_EOP_GetContext` from ",
              "`epsilon_omega_phase.g`. Read that file first.");
    fi;
    if verbose then
        Print("[BuildKRRIntertwinerData] omega != 0: building projective ",
              "character path (CGR slant alpha_g, issue #323).\n");
    fi;
    ctx := _EOP_GetContext(omega_vec, G);
    omega_cb := ctx.omega_cb;
    m_omega := ctx.m_omega;
    per_class := List([1..Length(idx.classes)], _ -> fail);
    per_class_perm := List([1..Length(idx.classes)], _ -> fail);

    # Build the projective char table at class i. Memoised in
    # per_class[i] and per_class_perm[i]. per_class_perm[i] is:
    #   * a permutation list  perm : Irr(C_G(g_i)) -> proj.table
    #     when alpha_g is a coboundary (e.g. for the trivial class or
    #     when omega_vec is all-zero); then
    #         trace = proj.table[perm[irrep_idx]](lift(h))
    #     gives Irr-aligned values byte-for-byte.
    #   * the symbol "intrinsic" when alpha_g is non-trivial; then
    #         trace = proj.table[irrep_idx](lift(h))
    #     and the irrep_idx convention is intrinsic to proj.table.
    proj_for_class := function(class_idx)
        local g, C, alpha, proj, perm;
        if per_class[class_idx] <> fail then
            return per_class[class_idx];
        fi;
        g := idx.reps[class_idx];
        C := idx.centralisers[class_idx];
        alpha := function(x, y)
            return _KRRI_AlphaG(omega_cb, m_omega, g, x, y);
        end;
        if verbose then
            Print("[BuildKRRIntertwinerData]   class ", class_idx,
                  ": building projective char table for |C_G(g)| = ",
                  Order(C), " (ext order ", Order(C) * m_omega, ") ...\n");
        fi;
        proj := _KRRI_ProjectiveCharsForG(C, alpha, m_omega);
        per_class[class_idx] := proj;
        # Try to align with the linear Irr(C) ordering (succeeds when
        # alpha is a coboundary; otherwise yields intrinsic order).
        _EnsureClassData(idx, class_idx);
        perm := _KRRI_TryMatchProjToIrr(
            proj, C, idx.irreps[class_idx], idx.cc_centraliser[class_idx]);
        if perm = fail then
            per_class_perm[class_idx] := "intrinsic";
        else
            per_class_perm[class_idx] := perm;
        fi;
        if verbose then
            Print("[BuildKRRIntertwinerData]     -> ", Length(proj.table),
                  " projective chars",
                  ", alignment = ", per_class_perm[class_idx], "\n");
        fi;
        return proj;
    end;

    trace_fn := function(class_idx, irrep_idx, h)
        local proj, j, perm;
        proj := proj_for_class(class_idx);
        perm := per_class_perm[class_idx];
        if perm = "intrinsic" then
            j := irrep_idx;
        else
            j := perm[irrep_idx];
        fi;
        if j < 1 or j > Length(proj.table) then
            Error("BuildKRRIntertwinerData: projective trace_on_W: ",
                  "irrep_idx ", irrep_idx, " (mapped to ", j, ") is out ",
                  "of bounds for class ", class_idx, " (|proj.table| = ",
                  Length(proj.table), ").");
        fi;
        return proj.lift(h) ^ proj.table[j];
    end;

    return rec(
        trace_on_W := trace_fn,
        epsilon    := fail,    # set by the main builder via _KRRI_BuildEpsilon
        spectral_data := fail,
        projective_data := rec(
            ctx              := ctx,
            per_class        := per_class,
            per_class_perm   := per_class_perm,
            proj_for_class   := proj_for_class,
            omega_vec        := omega_vec
        )
    );
end;;


# ============================================================
# Build the epsilon callable. For ω = 0 (the K-4a CT case) this is
# constant 1. For ω ≠ 0 we wire in V-1's `EpsilonOmegaPhase` (#14)
# if it is in scope; otherwise raise.
# ============================================================

_KRRI_BuildEpsilon := function(omega_vec, G, m, verbose)
    local cand;
    if omega_vec = fail or _KRRI_IsZeroVec(omega_vec) then
        if verbose then
            Print("[BuildKRRIntertwinerData] omega = 0: epsilon ≡ 1 ",
                  "(CGR CT-gauge per research note §3.2).\n");
        fi;
        return function(g1, g2, a, b) return 1; end;
    fi;
    # V-1 (#14, shipped 2026-05-20 via #316): try to auto-load the
    # production wiring file `epsilon_omega_phase.g` if `EpsilonOmegaPhase`
    # is not yet bound. This mirrors the loader pattern used by the
    # k4a_classify.g sibling chain. We use the FILE-LOAD-TIME directory
    # snapshot `_BUILDKRR_LOAD_DIR` (captured at the top of this file)
    # rather than INPUT_FILENAME() at call time, since the latter
    # returns the caller's input file, not ours.
    if not IsBoundGlobal("EpsilonOmegaPhase") then
        if _BUILDKRR_LOAD_DIR <> fail then
            cand := Concatenation(_BUILDKRR_LOAD_DIR, "/epsilon_omega_phase.g");
            if IsExistingFile(cand) then
                Read(cand);
            fi;
        fi;
        if not IsBoundGlobal("EpsilonOmegaPhase") then
            for cand in [ "epsilon_omega_phase.g",
                          "./epsilon_omega_phase.g",
                          "extraspecial_orbifolds/scripts/epsilon_omega_phase.g" ] do
                if IsExistingFile(cand) then
                    Read(cand);
                    break;
                fi;
            od;
        fi;
    fi;
    if not IsBoundGlobal("EpsilonOmegaPhase") then
        Error("BuildKRRIntertwinerData: omega_vec is non-zero but ",
              "`EpsilonOmegaPhase` (V-1, #14) is not in scope and ",
              "`epsilon_omega_phase.g` could not be auto-located. ",
              "Read(\"epsilon_omega_phase.g\") first, or omit omega_vec ",
              "for the omega = 0 baseline.");
    fi;
    if verbose then
        Print("[BuildKRRIntertwinerData] omega ≠ 0: routing through ",
              "EpsilonOmegaPhase (V-1, CGR §4 convention).\n");
    fi;
    # Delegate to V-1. EpsilonOmegaPhase caches (R, UCT, omega_cb) per
    # (G, omega_vec) on first invocation, so the per-call cost is just
    # the integer-slant sum + a cyclotomic exponentiation.
    return function(g1, g2, a, b)
        return EpsilonOmegaPhase(omega_vec, G, m, g1, g2, a, b);
    end;
end;;


# ============================================================
# The public entry point: BuildKRRIntertwinerData(m, G [, opts]).
# ============================================================

BuildKRRIntertwinerData := function(arg)
    local m, G, user_opts, opts, idx, transport, callables, eps_callable,
          out, spectral_source_resolved, omega_is_zero;
    if Length(arg) < 2 then
        Error("BuildKRRIntertwinerData: usage ",
              "BuildKRRIntertwinerData(m, G [, opts]).");
    fi;
    m := arg[1];
    G := arg[2];
    user_opts := fail;
    if Length(arg) >= 3 then
        user_opts := arg[3];
    fi;
    if not IsInt(m) or m < 1 then
        Error("BuildKRRIntertwinerData: m must be a positive integer; got ", m);
    fi;
    if not IsGroup(G) then
        Error("BuildKRRIntertwinerData: G must be a GAP group; got ", G);
    fi;
    opts := _KRRI_NormaliseOpts(m, user_opts);
    omega_is_zero :=
        opts.omega_vec = fail or _KRRI_IsZeroVec(opts.omega_vec);

    # Build the common index + transports. Lazy variant is required at
    # m >= 7 (eager BuildSimpleIndex over ~16K classes is intractable);
    # K-2c's lazy index / transports give O(1) per query.
    if opts.verbose then
        if opts.lazy then
            Print("[BuildKRRIntertwinerData] Building lazy idx/transports ",
                  "for |G| = ", Order(G), "...\n");
        else
            Print("[BuildKRRIntertwinerData] Building eager idx/transports ",
                  "for |G| = ", Order(G), "...\n");
        fi;
    fi;
    if opts.lazy then
        if not IsBoundGlobal("BuildSimpleIndexLazy")
           or not IsBoundGlobal("BuildTransportsLazy") then
            Error("BuildKRRIntertwinerData: opts.lazy = true requires ",
                  "`BuildSimpleIndexLazy` and `BuildTransportsLazy` ",
                  "(from untwisted_modular_data.g) to be in scope.");
        fi;
        idx := BuildSimpleIndexLazy(G);
        transport := BuildTransportsLazy(idx);
    else
        idx := BuildSimpleIndex(G);
        transport := BuildTransports(idx);
    fi;

    # Resolve the spectral_source if "auto".
    spectral_source_resolved := opts.spectral_source;
    if spectral_source_resolved = "auto" then
        if omega_is_zero then
            # ω = 0: standard lattice mode by m (research-note §3.2).
            spectral_source_resolved := _KRRI_ResolveAutoSource(m);
        else
            # ω ≠ 0 (K-4a-T4c projective, issue #323): the regular-
            # character path is mathematically WRONG; the lattice
            # spectral paths give the trivial cocycle's spectrum too.
            # Route to the projective-character path regardless of m.
            spectral_source_resolved := "projective";
        fi;
    fi;

    # Dispatch to the requested mode for trace_on_W.
    if spectral_source_resolved = "lite" then
        callables := _KRRI_BuildLiteCallables(idx);
    elif spectral_source_resolved = "dense_spectral" then
        callables := _KRRI_BuildDenseSpectralCallables(
            m, G, idx, opts.verbose);
    elif spectral_source_resolved = "sparse_spectral" then
        callables := _KRRI_BuildSparseSpectralCallables(
            m, G, idx, opts.verbose);
    elif spectral_source_resolved = "projective" then
        # K-4a-T4c projective (issue #323). At ω = 0 this is
        # mathematically equivalent to "lite" (the projective table
        # for the trivial cocycle is the ordinary character table,
        # byte-for-byte after re-indexing — see _KRRI_TryMatchProjToIrr).
        # At ω ≠ 0 this is the mathematically correct mode.
        if opts.omega_vec = fail then
            # No omega_vec provided. Treat as omega = 0 R-cocycle vec
            # (so the projective code path can still run for diagnostic
            # / cross-validation use). We pass a length-0 sentinel down
            # via _EOP_BuildContext which will Error since neither
            # hombasis nor R!.dimension(3) is 0. Resolve by routing
            # through _KRRI_BuildLiteCallables (numerically equivalent
            # at omega = 0; no projective harness needed).
            if opts.verbose then
                Print("[BuildKRRIntertwinerData] spectral_source = ",
                      "\"projective\" with omega_vec = fail: routing to ",
                      "lite (numerically equivalent at omega = 0).\n");
            fi;
            callables := _KRRI_BuildLiteCallables(idx);
        else
            callables := _KRRI_BuildProjectiveCallables(
                opts.omega_vec, G, m, idx, opts.verbose);
        fi;
    else
        Error("BuildKRRIntertwinerData: internal: unrecognised ",
              "resolved spectral_source = ", spectral_source_resolved);
    fi;

    # Build the epsilon callable. For ω = 0 this overrides any spectral-
    # mode-bundled epsilon (which under T4a downscope is also ≡ 1, but
    # we don't want the trace_on_W spectral wrapper to leak a different
    # epsilon convention here).
    if omega_is_zero then
        eps_callable := function(g1, g2, a, b) return 1; end;
    else
        eps_callable := _KRRI_BuildEpsilon(
            opts.omega_vec, G, m, opts.verbose);
    fi;

    out := rec(
        group         := G,
        idx           := idx,
        transport     := transport,
        trace_on_W    := callables.trace_on_W,
        epsilon       := eps_callable,
        source        := "krr-lattice",
        source_detail := Concatenation(
            "spectral_source=", spectral_source_resolved,
            ", omega_is_zero=", String(omega_is_zero)),
        m             := m,
        omega_is_zero := omega_is_zero,
        omega_vec     := opts.omega_vec,
        spectral_source_resolved := spectral_source_resolved
    );
    if callables.spectral_data <> fail then
        out.spectral_data := callables.spectral_data;
    fi;
    if IsBound(callables.projective_data) and
       callables.projective_data <> fail then
        out.projective_data := callables.projective_data;
    fi;
    if IsBound(callables.translate) then
        out.translate := callables.translate;
    fi;
    if IsBound(callables.g_to_em_class) then
        out.g_to_em_class := callables.g_to_em_class;
    fi;

    if opts.verbose then
        Print("[BuildKRRIntertwinerData] Done. source_detail = ",
              out.source_detail, "\n");
    fi;
    return out;
end;;


if IsBoundGlobal("_LogStamped") then
    _LogStamped("Loaded build_krr_intertwiner_data.g ",
                "(K-4a-T4b #188 + projective trace #323).");
else
    Print("Loaded build_krr_intertwiner_data.g ",
          "(K-4a-T4b #188 + projective trace #323).\n");
fi;
