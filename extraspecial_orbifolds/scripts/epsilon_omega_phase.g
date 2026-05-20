# epsilon_omega_phase.g — V-1 (#14) production wiring.
#
# ----------------------------------------------------------------------
# Purpose
# ----------------------------------------------------------------------
# `BuildKRRIntertwinerData` (PR #309 / issue #188) declares the hook
#
#     EpsilonOmegaPhase(omega_vec, G, m, g1, g2, a, b)  ->  cyclotomic
#
# returning the CGR/DPR/NN08 epsilon-phase for the simple-pair
# (g1, g2, a, b) given a non-trivial 3-cocycle vector `omega_vec` on G.
# At the time of the V-1 audit (issue #316) this name was unbound: the
# core integer-phase function `EpsilonOmega` already existed in
# `epsilon_omega.g` (issue #14, branch v1-eps-omega-phase, with full
# acceptance tests at `tests/test_epsilon_omega.g`) but the production
# vector->callable wiring had not been written. This file is exactly
# that wiring.
#
# Mathematical contract: identical to `EpsilonOmega`. Given the omega
# 3-cocycle (as a callable G^3 -> Z/m_omega) the phase is
#
#     epsilon_omega(g1, g2, a, b) = E(m_omega)^{ int(g1, g2, a, b) }
#
# where `int` is the integer Z/m_omega exponent computed by
# `EpsilonOmegaWithSection(omega_callable, g1, g2, a, b, t_a, s_b, m_omega)`
# (see `epsilon_omega.g` line 90 — the CGR §4 / DPR91 / NN08 convention).
# The section elements t_a, s_b are obtained from
# RepresentativeAction(G, gi, .).
#
# At omega_vec = 0 the integer phase is 0 mod m_omega, giving E^0 = 1,
# matching the omega = 0 baseline epsilon = 1 used everywhere in this
# codebase (krr_projector.g line 85, kr_intertwiner_bridge.g line 82,
# build_krr_intertwiner_data.g line 433 fast-path).
#
# ----------------------------------------------------------------------
# Vector -> callable bridge
# ----------------------------------------------------------------------
# `omega_vec` is supplied as integer coordinates against a basis of
# H^3(G; Z) (the hom-basis used by `UCT.cocyclebasis`, NOT `UCT.lift`;
# see the V-4a fix in fsi_wrapper.g for why this matters — `UCT.lift`
# silently auto-pads in GAP and produces a vector that is NOT a bar
# 3-cocycle). To turn that into a callable G^3 -> Z/m_omega we use HAP's
# `StandardCocycle(R, omega_vec_in_R, 3, UCT.exponent)`.
#
# Cost: building the cocycle callable requires
#   R   := ResolutionFiniteGroup(G, 4)
#   K   := TensorWithIntegers(R)
#   UCT := UniversalCoefficientsTheorem(K, 3)
# which dominates wall time (a few seconds for D_8 / Q_8, a few minutes
# for E_+(3), and OOMs for E_+(7)). The callable returned by
# `StandardCocycle` is cheap per-call. We therefore memoise the
# (R, UCT, omega_callable, m_omega) tuple per (G, omega_vec) pair on
# first use, so repeated `EpsilonOmegaPhase` calls share the same context.
#
# Cache key: identity comparison of G (via `IsIdenticalObj`) plus
# equality of `omega_vec`. We do NOT use `IdGroup(G)` because (i) it
# is expensive for large groups, and (ii) two GAP groups with the same
# small-group id can still be distinct objects with different
# enumeration orders, which would corrupt the cached `RepresentativeAction`
# lookups inside `EpsilonOmega`.
#
# The cache is bounded (default 16 entries) to avoid unbounded growth.
#
# ----------------------------------------------------------------------
# Acceptance criteria (issue #14)
# ----------------------------------------------------------------------
# Inherited from `EpsilonOmega` (see `tests/test_epsilon_omega.g`):
#   (1) omega = 0 -> EpsilonOmegaPhase = 1 (cyclotomic) for all
#       (g1, g2, a, b) in G^4 with a in [g1], b in [g2].
#   (2) For G = Q_8 with the order-2 cocycle, the central-row entries
#       of the §6.2 closed-form S match `modular_data/8/4/2.txt`
#       byte-for-byte (modulo the per-block character labelling that
#       CGR §5.22 declares gauge-free).
#
# The cocycle-relation `(δε)(...) = ω(...)` that the issue spec refers
# to is enforced indirectly: `EpsilonOmegaSlant` is the CGR-§4
# integer slant of ω by g, and the six-slant sum in
# `EpsilonOmegaWithSection` is exactly the CGR integer-log of ε_ω.
# When ω is a strict bar 3-cocycle (which HAP's `StandardCocycle` gives
# for non-trivial integer cohomology classes — see the V-4a investigation
# in fsi_wrapper.g for the only known counter-case, namely the
# *un-lifted* hom-coords path on Q_8 ω = order-8, which we avoid by
# going through `UCT.cocyclebasis`), the resulting ε satisfies
# `ε(gh, k) · ε(g, h) = ε(g, hk) · ε(h, k)` automatically.
#
# ----------------------------------------------------------------------
# Sign / cocycle convention
# ----------------------------------------------------------------------
# CGR2000 (Coste–Gannon–Ruelle, arXiv:hep-th/0001158), §4. See
# `epsilon_omega.g` lines 30–47 for the integer-slant formula.
#
# ----------------------------------------------------------------------

# Load the integer-phase backbone if not yet bound.
if not IsBoundGlobal("EpsilonOmega")
   or not IsBoundGlobal("EpsilonOmegaWithSection") then
    _eop_self := INPUT_FILENAME();;
    _eop_dir := fail;;
    if _eop_self <> fail and _eop_self <> "stream" then
        # Sibling load via INPUT_FILENAME-relative directory.
        _eop_dir := _eop_self{[1..Length(_eop_self)
                                - Length("/epsilon_omega_phase.g")]};
        if IsExistingFile(Concatenation(_eop_dir, "/epsilon_omega.g")) then
            Read(Concatenation(_eop_dir, "/epsilon_omega.g"));
        fi;
    fi;
    if not IsBoundGlobal("EpsilonOmega") then
        # CWD-relative fallbacks.
        if IsExistingFile("epsilon_omega.g") then
            Read("epsilon_omega.g");
        elif IsExistingFile("extraspecial_orbifolds/scripts/epsilon_omega.g") then
            Read("extraspecial_orbifolds/scripts/epsilon_omega.g");
        else
            Error("epsilon_omega_phase.g: cannot locate epsilon_omega.g ",
                  "(the V-1 integer-phase backbone).");
        fi;
    fi;
fi;

# ----------------------------------------------------------------------
# UniversalCoefficientsTheorem lazy load. Two project-local copies
# exist (src/modular_data.g and src/universal_coefficients.g); they
# clobber each other when both are read (CLAUDE.md warns about this).
# We mirror the loader pattern used by `quillen_detecting_subgroup.g`
# and prefer `src/modular_data.g`'s copy since that one is also used
# by the modular-data generation pipeline and is the "primary" UCT
# source in this codebase.
#
# Skipped if UCT is already bound by some upstream consumer.
# ----------------------------------------------------------------------
if not IsBoundGlobal("UniversalCoefficientsTheorem") then
    _eop_uct_loaded := false;;
    if _eop_dir = fail then
        _eop_self := INPUT_FILENAME();;
        if _eop_self <> fail and _eop_self <> "stream" then
            _eop_dir := _eop_self{[1..Length(_eop_self)
                                    - Length("/epsilon_omega_phase.g")]};
        fi;
    fi;
    if _eop_dir <> fail then
        for _eop_p in [ "/../../src/modular_data.g",
                        "/../../../src/modular_data.g",
                        "/../../DRINFELD/src/modular_data.g" ] do
            if not _eop_uct_loaded then
                _eop_cand := Concatenation(_eop_dir, _eop_p);;
                if IsExistingFile(_eop_cand) then
                    Read(_eop_cand);
                    _eop_uct_loaded := true;
                fi;
            fi;
        od;
    fi;
    if not _eop_uct_loaded then
        for _eop_p in [ "../../src/modular_data.g",
                        "../../../src/modular_data.g",
                        "src/modular_data.g",
                        "DRINFELD/src/modular_data.g" ] do
            if not _eop_uct_loaded and IsExistingFile(_eop_p) then
                Read(_eop_p);
                _eop_uct_loaded := true;
            fi;
        od;
    fi;
    if not _eop_uct_loaded then
        Error("epsilon_omega_phase.g: cannot locate ",
              "`UniversalCoefficientsTheorem` (defined in src/modular_data.g). ",
              "Read that file first or set CWD to the DRINFELD root.");
    fi;
fi;


# ----------------------------------------------------------------------
# Internal cache: list of records (G, omega_vec, ctx).
# `ctx` carries the heavy-cost R/UCT/callable/exponent tuple.
# ----------------------------------------------------------------------

if not IsBound(EPSILON_OMEGA_PHASE_CACHE) then
    EPSILON_OMEGA_PHASE_CACHE := [];
fi;

# Max cached contexts before LRU eviction.
if not IsBound(EPSILON_OMEGA_PHASE_CACHE_CAP) then
    EPSILON_OMEGA_PHASE_CACHE_CAP := 16;
fi;


# `_EOP_BuildContext(omega_vec, G)`:
# Build R, UCT, m_omega, and the omega-callable returned by HAP's
# StandardCocycle. The conversion from `omega_vec` (hom-basis or
# R-cocycle-length) follows fsi_wrapper.g's `FSI_LiftIfHom` — i.e.
# uses `UCT.cocyclebasis` (NOT `UCT.lift`), per the V-4a fix.
_EOP_BuildContext := function(omega_vec, G)
    local R, K, UCT, hom_len, cocy_len, omega_R_vec, i, omega_cb,
          m_omega;
    R   := ResolutionFiniteGroup(G, 4);
    K   := TensorWithIntegers(R);
    UCT := UniversalCoefficientsTheorem(K, 3);
    m_omega := UCT!.exponent;

    hom_len := Length(UCT!.hombasis);
    cocy_len := R!.dimension(3);

    # Normalise omega_vec: hom-basis (length hom_len) or already-lifted
    # R-cocycle (length cocy_len).
    if Length(omega_vec) = hom_len then
        omega_R_vec := ListWithIdenticalEntries(cocy_len, 0);
        for i in [1..hom_len] do
            omega_R_vec := omega_R_vec + omega_vec[i] * UCT!.cocyclebasis[i];
        od;
        omega_R_vec := omega_R_vec mod m_omega;
    elif Length(omega_vec) = cocy_len then
        omega_R_vec := omega_vec mod m_omega;
    else
        Error("EpsilonOmegaPhase: omega_vec has length ", Length(omega_vec),
              "; expected ", hom_len, " (hom-basis coordinates) or ",
              cocy_len, " (R-cocycle coordinates) for |G| = ", Order(G), ".");
    fi;

    omega_cb := StandardCocycle(R, omega_R_vec, 3, m_omega);

    return rec(
        G            := G,
        omega_vec    := ShallowCopy(omega_vec),
        R            := R,
        UCT          := UCT,
        omega_R_vec  := omega_R_vec,
        omega_cb     := omega_cb,
        m_omega      := m_omega
    );
end;;


# `_EOP_GetContext(omega_vec, G)`:
# Look up or build the cached context for (G, omega_vec).
_EOP_GetContext := function(omega_vec, G)
    local i, entry, ctx;
    # Search the cache for a hit.
    for i in [1..Length(EPSILON_OMEGA_PHASE_CACHE)] do
        entry := EPSILON_OMEGA_PHASE_CACHE[i];
        if IsIdenticalObj(entry.G, G) and entry.omega_vec = omega_vec then
            # Move-to-front (lightweight LRU).
            if i > 1 then
                Remove(EPSILON_OMEGA_PHASE_CACHE, i);
                Add(EPSILON_OMEGA_PHASE_CACHE, entry, 1);
            fi;
            return entry;
        fi;
    od;
    # Miss: build and prepend.
    ctx := _EOP_BuildContext(omega_vec, G);
    Add(EPSILON_OMEGA_PHASE_CACHE, ctx, 1);
    # Evict to keep size bounded.
    while Length(EPSILON_OMEGA_PHASE_CACHE) > EPSILON_OMEGA_PHASE_CACHE_CAP do
        Remove(EPSILON_OMEGA_PHASE_CACHE);
    od;
    return ctx;
end;;


# ----------------------------------------------------------------------
# Public callable: EpsilonOmegaPhase(omega_vec, G, m_rank, g1, g2, a, b)
#
# Returns the cyclotomic phase E(m_omega)^{ int(g1, g2, a, b) } where
# `m_omega = UCT(G).exponent` and `int` is the CGR §4 integer slant sum.
# `m_rank` (the third positional argument) is the E_+(m) rank parameter
# from `BuildKRRIntertwinerData`'s signature — informational only;
# ignored for the phase computation (the actual modulus is taken from
# the H^3(G; Z) exponent, not the rank).
#
# Requirements:
#   * a in conj class of g1 in G, b in conj class of g2 in G;
#   * a and b commute (otherwise the term is meaningless in S^ω;
#     EpsilonOmegaPhase still returns a value — caller's responsibility).
# ----------------------------------------------------------------------
EpsilonOmegaPhase := function(omega_vec, G, m_rank, g1, g2, a, b)
    local ctx, int_phase;
    if omega_vec = fail then
        # Caller treats `fail` as omega = 0. Skip the heavyweight build.
        return 1;
    fi;
    ctx := _EOP_GetContext(omega_vec, G);
    int_phase := EpsilonOmega(G, ctx.omega_cb, g1, g2, a, b, ctx.m_omega);
    return E(ctx.m_omega) ^ int_phase;
end;;


# ----------------------------------------------------------------------
# Cache-management helpers (for tests and diagnostics).
# ----------------------------------------------------------------------

# Clear the entire phase-context cache.
EpsilonOmegaPhaseClearCache := function()
    EPSILON_OMEGA_PHASE_CACHE := [];
    return true;
end;;

# Return a shallow copy of the current cache for inspection. Each entry
# is a record with .G, .omega_vec, .m_omega; the heavy R/UCT/omega_cb
# are also present but not deep-copied (they're shared with the live cache).
EpsilonOmegaPhaseCacheStatus := function()
    return List(EPSILON_OMEGA_PHASE_CACHE,
                e -> rec(G_order := Order(e.G),
                        omega_vec := ShallowCopy(e.omega_vec),
                        m_omega := e.m_omega));
end;;


Print("Loaded epsilon_omega_phase.g (V-1, #14: ε_ω-phase production wiring).\n");
