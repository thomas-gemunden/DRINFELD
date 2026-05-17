# kr_intertwiner_bridge.g — K-4a (issue #188).
#
# Builds a K-1-compatible `intertwiner_data` record from KRR's lattice
# intertwiner pipeline (defect_rep_minus_id.g + defect_rep_minus_id_optim.g
# + defect_rep_other.g), as opposed to the regular-character / omega=0
# baseline produced by `BuildIntertwinerDataUntwisted` in krr_projector.g.
#
# Parent: #187 (K-4 EPIC).
#
# ## Math observation that simplifies the bridge
#
# For Keller's lattice orbifold KRR have verified c_g = 0 in cohomology
# for all g (the projective rep on the twisted module W_g lifts to a
# genuine rep). With c_g = 0, the simple objects (g, χ) of the
# resulting MTC carry GENUINE characters χ ∈ Irr(C_G(g)) — same as
# the untwisted Drinfeld center D(Vec_G).
#
# Consequence: `trace_on_W(i, k, h)` is **the same callable as in the
# untwisted baseline** (regular character via `EvalIrr`).
#
# The only thing that distinguishes S^Keller from S^0 is `epsilon` —
# the cocycle-phase factor α(g_1, g_2, a, b) appearing in KRR §2.1
# eq (2.1.2). For ω = 0 (Keller's conjectured case), α ≡ 1 and
# S^Keller = S^0 identically. For ω ≠ 0, α encodes the cocycle phase.
#
# ## Where the gap is
#
# To extract α from KRR's lattice data without going through an
# explicit ω-vector, we need to evaluate α(g_1, g_2, a, b) directly
# from the lattice's associativity / Pontryagin-pairing structure.
# KRR §2.1 + Appendix A give the formula, but the **explicit
# evaluation** (input: g_1, g_2, a, b ∈ E_+(m) elements; output: a
# root of unity) is not yet implemented in this repo. That's the
# next piece. See `_KR_EpsilonAlphaTBD` below.
#
# For now this file provides:
#   - `BuildKRRIntertwinerData(m, G)` returning a record with the
#     correct shape, `epsilon := function(g1, g2, a, b) return 1; end`
#     (placeholder = untwisted), and a clear TODO at the call site.
#   - `KRRSanityAtM3()` — confirms that with the placeholder epsilon
#     this reproduces `BuildIntertwinerDataUntwisted(EmGroup(3))` and
#     therefore K-3 (#40)'s S^0 central-row anchor.
#
# Once the α derivation lands, only `epsilon` swaps and downstream
# K-2 / K-4b / K-4c stays unchanged.

if not IsBoundGlobal("EpsilonOmega") then
    Read("epsilon_omega.g");           # V-1 fallback if ω-vec available
fi;
if not IsBoundGlobal("BuildSimpleIndex") then
    Read("untwisted_modular_data.g");
fi;
if not IsBoundGlobal("BuildIntertwinerDataUntwisted") then
    Read("krr_projector.g");
fi;

# ------------------------------------------------------------------
# Placeholder for the lattice-derived epsilon phase.
#
# KRR §2.1 eq (2.1.2) and Appendix A define
#   α : (g_1, g_2, a, b) -> µ_n,
# the cocycle phase that distinguishes S^Keller from S^0 when ω ≠ 0.
# KRR construct α algebraically from the BW lattice's associativity
# data (without first extracting an explicit cohomology class).
#
# To compute α from m, G, and (g_1, g_2, a, b):
#   1. Evaluate the lattice 2-cocycle on the (a, b) commuting pair
#      under the diagonal embedding of E_+(m) into Aut(BW lattice).
#   2. Multiply by the (g_1, g_2)-dependent phase from KRR eq (2.1.2).
#
# Until this is implemented, we use the untwisted placeholder
# `() -> 1`, which makes BuildKRRIntertwinerData produce output
# IDENTICAL to BuildIntertwinerDataUntwisted. That preserves the
# K-3 (#40) cross-check anchor; the lattice-derived α only changes
# things when c_g = 0 but ω ≠ 0.
# ------------------------------------------------------------------

_KR_EpsilonAlphaTBD := function(m, G)
    # Returns a callable (g_1, g_2, a, b) -> µ_n.
    # TODO (#188 follow-up): implement from KRR §2.1 + Appendix A.
    # The signature mirrors `intertwiner_data.epsilon`.
    return function(g_1, g_2, a, b) return 1; end;
end;;

# ------------------------------------------------------------------
# BuildKRRIntertwinerData(m, G)
#
# Returns a record consumable by K-1's `ProjectorFormula` and K-2's
# `SKeller`. With the placeholder `_KR_EpsilonAlphaTBD`, this is
# observationally identical to `BuildIntertwinerDataUntwisted(G)`.
# Once the lattice-derived α lands, S^Keller will diverge from S^0
# precisely when KRR's ω is non-zero.
# ------------------------------------------------------------------

BuildKRRIntertwinerData := function(m, G)
    local idx, transport, eps_alpha;
    idx := BuildSimpleIndex(G);
    transport := BuildTransports(idx);
    eps_alpha := _KR_EpsilonAlphaTBD(m, G);
    return rec(
        group       := G,
        idx         := idx,
        transport   := transport,
        # For c_g = 0 (verified by KRR for m ∈ {3, 5, 7}), the genuine
        # characters of C_G(g_i) are the right `trace_on_W` values.
        trace_on_W  := function(class_idx, irrep_idx, h)
            return EvalIrr(idx, class_idx, irrep_idx, h);
        end,
        # Lattice-derived α: placeholder = 1 until #188 follow-up.
        epsilon     := eps_alpha,
        # Marker so callers can distinguish KRR-source from untwisted-baseline.
        source      := "krr-lattice",
        # Marker for whether the α implementation is the placeholder or real.
        epsilon_is_placeholder := true
    );
end;;

# ------------------------------------------------------------------
# KRRSanityAtM3()
#
# Confirms that, with the placeholder epsilon, `BuildKRRIntertwinerData`
# produces a record observationally equal (on the K-1 inputs we care
# about) to `BuildIntertwinerDataUntwisted` at m=3. This is the K-3
# (#40) cross-check anchor.
#
# Test logic: build both records on E_+(3); spot-check ProjectorFormula
# output on a central-row pair.
# ------------------------------------------------------------------

KRRSanityAtM3 := function()
    local G, krr_data, untwisted_data, idx, central_idx, k1, k2,
          W_g1_krr, W_g2_krr, W_g1_unt, W_g2_unt, val_krr, val_unt;
    G := EmGroup(3);
    krr_data := BuildKRRIntertwinerData(3, G);
    untwisted_data := BuildIntertwinerDataUntwisted(G);
    idx := krr_data.idx;
    # Find a central-class index (|class| = 1).
    central_idx := First([1..Length(idx.classes)],
                         i -> idx.class_sizes[i] = 1);
    if central_idx = fail then
        Error("KRRSanityAtM3: no central class found in idx — unexpected");
    fi;
    # Test the (1, 1) entry of the central row (first irrep of each).
    k1 := 1; k2 := 1;
    W_g1_krr := MakeWg(krr_data, central_idx, k1);
    W_g2_krr := MakeWg(krr_data, central_idx, k2);
    W_g1_unt := MakeWg(untwisted_data, central_idx, k1);
    W_g2_unt := MakeWg(untwisted_data, central_idx, k2);
    val_krr := ProjectorFormula(W_g1_krr, W_g2_krr, krr_data);
    val_unt := ProjectorFormula(W_g1_unt, W_g2_unt, untwisted_data);
    return rec(
        val_krr := val_krr,
        val_unt := val_unt,
        match := val_krr = val_unt,
        central_idx := central_idx
    );
end;;

Print("Loaded kr_intertwiner_bridge.g (K-4a scaffold; ",
      "epsilon placeholder = 1 until KRR §2.1 α landed).\n");
