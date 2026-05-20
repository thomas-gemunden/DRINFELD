# detecting_family_restriction.g — D-VAN-2 (issue TBD-D-VAN-2).
#
# Builds and caches the restriction matrices
#
#     Res_E   : H^3(G; U(1)) -> H^3(E;   U(1))
#     Res_D8  : H^3(G; U(1)) -> H^3(D_8; U(1))
#
# for G = E_+(m), E = maximal rank-(m+1) elementary abelian, D_8 = the
# pinned conjugacy class representative D_8 section returned by
# D8Section_E_plus.
#
# Phase 1 (this file) uses HAP's EquivariantChainMap to compute the
# matrices; Phase 2 will add a "quillen" source for the m=7 path
# (gated on Q-int A2/A3, issue #136).
#
# Spec: docs/superpowers/specs/2026-05-15-detecting-family-vanishing-test-design.md
#
# Reused infrastructure:
#   * MaximalElementaryAbelian_E_plus, D8Section_E_plus, EPlusGroup
#     from quillen_detecting_subgroup.g.
#   * SetupCohomology3 from transgression_kernel.g.
#   * H3MatrixOfAutomorphism in brw_h3_action.g is the precedent for
#     this kind of cohomology-matrix construction (same EquivariantChainMap
#     + GroupCohomologyFunctor pattern, with phi: G -> G replaced by
#     phi: H -> G).

LoadPackage("hap");

# --- dependencies -----------------------------------------------------

if not IsBoundGlobal("MaximalElementaryAbelian_E_plus") then
    Read("quillen_detecting_subgroup.g");
fi;
if not IsBoundGlobal("SetupCohomology3") then
    Read("transgression_kernel.g");
fi;

# Local ternary, matching repo convention.
If_ := function(c, a, b) if c then return a; else return b; fi; end;;

# --- module-level cache ----------------------------------------------
#
# Keyed by Concatenation("m", String(m), "_", source).
# Each entry stores the full rec returned by BuildRestrictionMatrices.

_DETF_CACHE := rec();;

# Forward declaration; real implementation appended below the helpers.
BuildRestrictionMatrices := fail;;

# --- helpers ----------------------------------------------------------

# Build the cohomology context (R, K, UCT) for a subgroup. Thin wrapper
# around SetupCohomology3 that documents the intent. Returns the same
# rec shape so downstream code is uniform.
SubgroupCohomologyContext := function(H)
    return SetupCohomology3(H);
end;;

# Build the inclusion homomorphism phi: H -> G where H <= G.
# GAP's GroupHomomorphismByImages handles this when given the
# generators of H mapped to themselves (as elements of G).
#
# This is the homomorphism object that HAP's EquivariantChainMap needs.
SubgroupInclusion := function(H, G)
    local gens_H, phi;
    gens_H := GeneratorsOfGroup(H);
    phi := GroupHomomorphismByImages(H, G, gens_H, gens_H);
    if phi = fail then
        Error("SubgroupInclusion: H = ", H,
              " is not a subgroup of G = ", G,
              " (GroupHomomorphismByImages returned fail)");
    fi;
    return phi;
end;;

# Compute the restriction matrix H^3(G; U(1)) -> H^3(H; U(1)) using
# HAP's EquivariantChainMap. Pattern mirrors H3MatrixOfAutomorphism
# (brw_h3_action.g) but with phi: H -> G (subgroup inclusion) replacing
# phi: G -> G (automorphism).
#
# Returns a k_G x k_H integer matrix whose (i, j) entry is the j-th
# H-side hom-basis coordinate of the image of the i-th G-side hom-basis
# generator under restriction. Entries are reduced mod torsion_H[j].
#
# Why this matches H3MatrixOfAutomorphism's structure:
#
#   * EquivariantChainMap(R_H, R_G, phi) builds a chain map R_H -> R_G.
#   * TensorWithIntegers descends to a Z-chain map K_H -> K_G.
#   * GroupCohomologyFunctor(K_H, K_G, chainmap, 3) gives F such that
#     F[i] is the image of Z_3(K_H)[i] in Z_3(K_G) coords.
#   * On hom-vectors phi^* acts by right-mult by TransposedMat(F):
#     phi^*(hombasis_G[i]) has length |ZZ_H|, integer-valued.
#
# CRITICAL DETAIL — coefficient ring (D-VAN-FIX #151 + Q_8 extension #154):
#
#   The autom case has exp_G = exp_H. For subgroup inclusion the two
#   can differ either way:
#
#     * Max EA / D_8: exp_H | exp_G (typically). E.g., m=2:
#       exp_G = 8, exp_E = 2.
#     * Q_8 sections at m=3: exp_G = 4, exp_H = 8 — exp_G | exp_H,
#       the OPPOSITE direction. The earlier exp_H | exp_G assertion
#       blocked this case, which is exactly the one needed to close
#       the integer-cohomology detection gap (#153, #154).
#
#   Unified fix: work in Z/L where L = Lcm(exp_G, exp_H). Rescale
#   hombasis_G by L/exp_G and hombasis_H by L/exp_H so both live in
#   Z/L representation. The augmented matrix's slack is L * I. Solving
#   `x * aug = image mod L` gives coords; reduce by torsion_H[j].
#
#   For exp_H | exp_G this gives L = exp_G, rescale_G = 1, rescale_H =
#   exp_G/exp_H — recovers the prior partial-fix arithmetic exactly.
#   For exp_G | exp_H this gives L = exp_H, rescale_G = exp_H/exp_G,
#   rescale_H = 1 — the new Q_8 case.
RestrictionMatrixViaHAP := function(setup_G, ctx_H, phi_HG)
    local R_G, K_G, UCT_G, exp_G, k_G, hombasis_G,
          R_H, K_H, UCT_H, exp_H, k_H, torsion_H, hombasis_H, hb_len_H,
          L, rescale_G, rescale_H,
          chainmap, gcf, F, autmat, hombasis_H_rescaled,
          aug_matrix, i, hom_G_rescaled, image_modL, sol, col_coeffs,
          res_mat, j;

    R_G := setup_G.R;
    K_G := setup_G.K;
    UCT_G := setup_G.UCT;
    exp_G := setup_G.exponent;
    k_G := setup_G.num_generators;
    hombasis_G := UCT_G.hombasis;

    R_H := ctx_H.R;
    K_H := ctx_H.K;
    UCT_H := ctx_H.UCT;
    exp_H := ctx_H.exponent;
    k_H := ctx_H.num_generators;
    torsion_H := ctx_H.torsion;
    hombasis_H := UCT_H.hombasis;
    hb_len_H := Length(hombasis_H[1]);

    # Work in Z/L where L = lcm(exp_G, exp_H). Generalises the prior
    # `exp_H | exp_G` rescale strategy to cover all cases:
    #
    #   * exp_H | exp_G  (max EA / D_8 sections at m=2,3,5):
    #     L = exp_G, rescale_G = 1, rescale_H = exp_G/exp_H. Recovers
    #     the prior partial-fix arithmetic exactly.
    #   * exp_G | exp_H  (Q_8 sections at m=3: exp_G=4, exp_H=8):
    #     L = exp_H, rescale_G = exp_H/exp_G, rescale_H = 1. Q_8 has
    #     H^3 = Z/8 which natively holds order-4 elements; restriction
    #     to Q_8 distinguishes them from the order-2 sub-element. The
    #     prior `exp_H | exp_G` assertion erroneously blocked this case.
    #   * neither divides the other: L = Lcm. Both rescales nontrivial.
    L := Lcm(exp_G, exp_H);
    rescale_G := L / exp_G;
    rescale_H := L / exp_H;

    chainmap := TensorWithIntegers(EquivariantChainMap(R_H, R_G, phi_HG));
    gcf := GroupCohomologyFunctor(K_H, K_G, chainmap, 3);
    F := gcf!.matrix;
    autmat := TransposedMat(F);

    # Rescale hombasis_H to Z/L; build augmented matrix with slack L * I.
    hombasis_H_rescaled := List(hombasis_H,
        h -> List(h, x -> x * rescale_H));
    aug_matrix := Concatenation(
        hombasis_H_rescaled,
        List([1..hb_len_H], r -> List([1..hb_len_H], c ->
            If_(r = c, L, 0))));

    res_mat := NullMat(k_G, k_H);
    for i in [1..k_G] do
        # Rescale G-side hom from Z/exp_G to Z/L, restrict via autmat,
        # reduce mod L, project onto hombasis_H_rescaled.
        hom_G_rescaled := List(hombasis_G[i], x -> x * rescale_G);
        image_modL := List(hom_G_rescaled * autmat, x -> x mod L);
        sol := SolutionIntMat(aug_matrix, image_modL);
        if sol = fail then
            Error("RestrictionMatrixViaHAP: could not project image of ",
                  "hombasis_G[", i, "] onto hombasis_H_rescaled ",
                  "(L = ", L, "). Possible cause: phi is not actually ",
                  "a homomorphism, or hombasis_H doesn't span the right ",
                  "submodule of H^3(H; Z/L).");
        fi;
        col_coeffs := sol{[1..k_H]};
        for j in [1..k_H] do
            res_mat[i][j] := col_coeffs[j] mod torsion_H[j];
        od;
    od;

    return res_mat;
end;;

# Find a D_8 section inside a GIVEN G (matching the quillen_detecting_subgroup
# logic but parameterised by the parent so callers can pin both H_E and H_D8
# inside the same instance of E_+(m); each call to EPlusGroup(m) builds a
# fresh GAP group, so re-using one ea_rec.parent throughout is necessary
# for SubgroupInclusion to work).
#
# Strategy by m (D-VAN m=5 OOM fix, issue #287):
#
#   * m <= 3: full ConjugacyClassesSubgroups enumeration. Tractable
#     (|G| <= 128 subgroup lattice <~ 700 classes) and preserves
#     bit-for-bit backward compatibility with m=2/m=3 anchor tests
#     (which assert specific verdict patterns on the picked D_8).
#   * m >= 4: direct construction. ConjugacyClassesSubgroups(E_+(m))
#     OOMs at 32 GB for m=5 (|G|=2048). Mirroring
#     D8Section_E_plus(m >= 4) in quillen_detecting_subgroup.g, the
#     E_+(m) PC presentation pairs adjacent non-central generators as
#     (a_1, b_1, a_2, b_2, ..., z); their pairwise subgroup
#     <a_1, b_1> is exactly the first central-product factor and is
#     a canonical D_8 section.
_DETF_FindD8In := function(G, m)
    local maxsub, candidates, gens_G, H;
    if m = 1 then return G; fi;
    if m >= 4 then
        # Direct construction matching D8Section_E_plus(m >= 4):
        # <gens_G[1], gens_G[2]> is the first central-product factor,
        # which is canonically D_8 = E_+(1).
        gens_G := GeneratorsOfGroup(G);
        H := Subgroup(G, [gens_G[1], gens_G[2]]);
        if Order(H) <> 8 or IdGroup(H) <> [8, 3] then
            Error("_DETF_FindD8In: direct construction at m = ", m,
                  " did not yield D_8 (order ", Order(H), ", id ",
                  IdGroup(H), "). PC-generator convention changed? ",
                  "Falling back to ConjugacyClassesSubgroups is not ",
                  "feasible at this m (OOM at m=5).");
        fi;
        return H;
    fi;
    # m in {2, 3}: full enumeration path (bit-for-bit anchor preservation).
    maxsub := List(ConjugacyClassesSubgroups(G), Representative);
    candidates := Filtered(maxsub,
                           S -> Order(S) = 8
                                and not IsAbelian(S)
                                and IdGroup(S) = [8, 3]);
    if Length(candidates) = 0 then
        Error("_DETF_FindD8In: no D_8 section in G for m = ", m);
    fi;
    return candidates[1];
end;;

# Find a Q_8 section inside G. Returns the first conj class rep with
# IdGroup = [8, 4] (= Q_8). Returns `fail` if no Q_8 subgroup exists
# (e.g., m=1: G = D_8 itself contains no Q_8).
#
# Why Q_8 matters (#154): per Harada & Kono 1987 Theorem 1.1, the
# cyclic summand A(4) of H^3(E_+(m); U(1)) has order Z/4 at m≥3 (Z/8
# at m=2). Restriction to D_8 sections fails to distinguish the
# order-2 sub-element 2·A(4)_gen from 0 (8/8 D_8 spike at m=3 confirms
# the structural ceiling from t∘r = 2^h). Q_8 has H^3(Q_8) = Z/8, is
# NOT a Q-isotropic preimage, and empirically detects 2·A(4)_gen
# faithfully: res(A(4)_gen) ∈ {2, 6} mod 8 across the 8 sampled Q_8
# conj classes at m=3, so res(2·A(4)_gen) = 4 ≠ 0 = res(0).
#
# Empirical counts of Q_8 conj classes (via ConjugacyClassesSubgroups):
#   m=1: 0 (D_8 itself; no Q_8)
#   m=2: 2
#   m=3: 56
#   m=5, m=7: TBD via runtime check
#
# Strategy by m (D-VAN m=5 OOM fix, issue #287):
#
#   * m <= 3: full ConjugacyClassesSubgroups enumeration. Preserves
#     bit-for-bit backward compatibility with m=2/m=3 anchors.
#   * m >= 4: direct construction. ConjugacyClassesSubgroups on E_+(m)
#     OOMs at m=5. Mirroring Q8Section_E_plus(m >= 4) in
#     quillen_detecting_subgroup.g, we build the E_+(2) subgroup
#     <gens_G[1..4]> (order 32) and enumerate ITS subgroups — that
#     lattice has ~50 classes and is trivial to walk. Any Q_8 inside
#     E_+(2) is also a Q_8 inside E_+(m).
_DETF_FindQ8In := function(G, m)
    local maxsub, candidates, gens_G, H_eplus2, eplus2_subs, q8_in_eplus2;
    if m = 1 then return fail; fi;
    if m >= 4 then
        # Direct construction: locate a Q_8 inside the E_+(2) subgroup
        # generated by the first 4 non-central PC generators.
        gens_G := GeneratorsOfGroup(G);
        H_eplus2 := Subgroup(G, [gens_G[1], gens_G[2],
                                   gens_G[3], gens_G[4]]);
        if Order(H_eplus2) <> 32 then
            Error("_DETF_FindQ8In: direct E_+(2) subgroup at m = ", m,
                  " has order ", Order(H_eplus2),
                  " (expected 32). PC-generator convention changed?");
        fi;
        eplus2_subs := List(ConjugacyClassesSubgroups(H_eplus2),
                             Representative);
        q8_in_eplus2 := Filtered(eplus2_subs,
            S -> Order(S) = 8 and not IsAbelian(S)
                 and IdGroup(S) = [8, 4]);
        if Length(q8_in_eplus2) = 0 then
            Error("_DETF_FindQ8In: no Q_8 inside the E_+(2) subgroup ",
                  "of E_+(", m, "). PC-generator convention changed?");
        fi;
        return q8_in_eplus2[1];
    fi;
    # m in {2, 3}: full enumeration path (bit-for-bit anchor preservation).
    maxsub := List(ConjugacyClassesSubgroups(G), Representative);
    candidates := Filtered(maxsub,
                           S -> Order(S) = 8
                                and IdGroup(S) = [8, 4]);
    if Length(candidates) = 0 then return fail; fi;
    return candidates[1];
end;;

# Helper: extract the k-th bit of a non-negative integer n (k starts at 0).
# Used by _DETF_AllMaxEAsIn's Lagrangian-selection enumeration at m >= 4.
_DETF_BinaryDigit := function(n, k)
    return QuoInt(n, 2^k) mod 2;
end;;

# Enumerate ALL conjugacy class representatives of maximal elementary
# abelians (rank m+1) inside G. Per Quillen 1971, the family of these
# conj-class reps is what detects H^*(G; F_2) mod nilpotents in low
# degrees. Using a SINGLE representative (the prior simplification)
# left a large kernel in the restriction map — D-VAN-FIX (#151).
#
# Strategy by m (D-VAN m=5 OOM fix, issue #287):
#
#   * m <= 3: full ConjugacyClassesSubgroups enumeration. At m=2 this
#     gives 6 reps; m=3 gives 30. Preserves bit-for-bit backward
#     compatibility with m=2/m=3 anchors.
#   * m >= 4: direct Lagrangian-style enumeration. ConjugacyClassesSubgroups
#     on E_+(5) (|G|=2048) OOMs at 32 GB. We enumerate maximal
#     elementary abelians by:
#     (a) Axis-aligned Lagrangians: for each (s_1, ..., s_m) ∈ F_2^m,
#         pick generator gens_G[2i-1] if s_i = 0, else gens_G[2i]. Plus
#         z. The 2^m selections give 2^m distinct max EAs.
#     (b) Diagonal pair-swap Lagrangians: for each unordered pair of
#         pair-indices {a, b} ⊂ {1..m}, replace pair_a + pair_b's two
#         elements with their "diagonal" sums
#             gens_G[2a-1] + gens_G[2b],
#             gens_G[2a]   + gens_G[2b-1]
#         (these commute and are q-isotropic). The other m-2 pair halves
#         are picked independently. This adds 2^{m-2} * binomial(m, 2)
#         further EAs, e.g., 80 at m=5.
#     Total: 2^m + 2^{m-2} * binomial(m, 2) Lagrangians. At m=5: 32 + 80
#     = 112 out of N_+(5, 2) = 4590 type-+ Lagrangians. Empirically
#     determined to be sufficient for per-class restriction-injectivity
#     at m=5 (verified during issue #287; 0/165 false trivials).
#     SOUNDNESS CAVEAT (per #289 audit, corrected #291): this is
#     112/4590 of the full Quillen-theorem detecting family at m=5,
#     so the enumeration is sound (restriction to a subset can only
#     introduce false NON-trivials, never false trivials) but
#     theoretically incomplete. The full Quillen 5.10 detecting
#     family at m has N_+(m, 2) = prod_{i=0..m-1}(2^i + 1) maximal
#     elementary abelians (= 6, 30, 270, 4590, 75582, 9845550 at
#     m = 1..7). One-per-Aut-orbit is NOT sufficient (refuted at
#     m=2). The 112 chosen here are 32 axis-aligned + 80 diagonal
#     pair-swap; "triple-diagonal" Lagrangians involving three pairs
#     at once are omitted. If per-class detection ever fails on
#     some unit generator at m >= 4, extend by adding higher-order
#     diagonals; for m=7 the partial-enumeration gap widens further
#     (axis+pair-swap pattern would give ~296 of 9.8M) and warrants
#     Witt-decomposition systematic enumeration (writeup §7,
#     issue #290). See `docs/superpowers/research/2026-05-19-d-van-
#     detecting-family-correctness.md` for the full reconciliation.
_DETF_AllMaxEAsIn := function(G, m)
    local expected_order, reps, candidates, H, Z_G, z, gens_G, n_pairs,
          sel_bits, sel, basis, i, ea, ea_list,
          a, b, other_pairs, other_sel_bits, oj, idx;
    expected_order := 2 ^ (m + 1);
    if m >= 4 then
        Z_G := Centre(G);
        z := First(AsList(Z_G), x -> not IsOne(x));
        gens_G := Filtered(GeneratorsOfGroup(G), g -> not (g in Z_G));
        if Length(gens_G) < 2*m then
            for H in AsList(G) do
                if not (H in Z_G) and Length(gens_G) < 2*m then
                    Add(gens_G, H);
                fi;
            od;
        fi;
        gens_G := gens_G{[1..2*m]};
        ea_list := [];

        # (a) Axis-aligned Lagrangians: 2^m selections.
        for sel_bits in [0..(2^m - 1)] do
            sel := List([1..m], i -> If_(_DETF_BinaryDigit(sel_bits, i - 1) = 0,
                                          gens_G[2*i - 1],
                                          gens_G[2*i]));
            basis := Concatenation([z], sel);
            ea := Subgroup(G, basis);
            if Order(ea) = expected_order and IsElementaryAbelian(ea) then
                Add(ea_list, ea);
            fi;
        od;

        # (b) Diagonal pair-swap Lagrangians: for each pair (a, b) with
        # a < b, the swapped basis includes the two diagonals
        #   d1 = gens_G[2a-1] + gens_G[2b],
        #   d2 = gens_G[2a]   + gens_G[2b-1]
        # (replacing pairs a and b's four elements with two q-isotropic
        # mutually commuting diagonals), plus one of (gens_G[2c-1],
        # gens_G[2c]) for each c ∈ {1..m} \ {a, b}.
        for a in [1..(m - 1)] do
            for b in [(a + 1)..m] do
                other_pairs := Filtered([1..m], c -> c <> a and c <> b);
                for other_sel_bits in [0..(2^(m - 2) - 1)] do
                    sel := [];
                    Add(sel, gens_G[2*a - 1] * gens_G[2*b]);
                    Add(sel, gens_G[2*a] * gens_G[2*b - 1]);
                    for oj in [1..(m - 2)] do
                        idx := other_pairs[oj];
                        if _DETF_BinaryDigit(other_sel_bits, oj - 1) = 0 then
                            Add(sel, gens_G[2*idx - 1]);
                        else
                            Add(sel, gens_G[2*idx]);
                        fi;
                    od;
                    basis := Concatenation([z], sel);
                    ea := Subgroup(G, basis);
                    if Order(ea) = expected_order
                       and IsElementaryAbelian(ea) then
                        Add(ea_list, ea);
                    fi;
                od;
            od;
        od;

        if Length(ea_list) = 0 then
            Error("_DETF_AllMaxEAsIn: direct Lagrangian enumeration at ",
                  "m = ", m, " produced no valid max EAs. ",
                  "PC-generator convention changed?");
        fi;
        return ea_list;
    fi;
    # m in {2, 3}: full enumeration path (bit-for-bit anchor preservation).
    reps := List(ConjugacyClassesSubgroups(G), Representative);
    candidates := Filtered(reps,
                           S -> IsElementaryAbelian(S)
                                and Order(S) = expected_order);
    if Length(candidates) = 0 then
        Error("_DETF_AllMaxEAsIn: no rank-", m + 1,
              " elementary abelian in G");
    fi;
    return candidates;
end;;


# Public entry point. Phase 1 supports source = "hap" for m in {2, 3, 5}.
# m = 7 + "hap" errors (would invoke ResolutionFiniteGroup(E_+(7), 4) which
# OOMs). source = "quillen" is Phase 2, gated on Q-int A2/A3 (#136), and
# currently errors.
#
# Iterative D-VAN-FIX (#151 → #154 → #153 closed):
#
#   #151: ALL max EA conj classes (not just one); detects F_2 part by
#         Quillen. Closes the m=2/m=3 unit-generator failure.
#   #154: Add the pinned D_8 section. Captures the cyclic A(4) summand
#         for m=2 (where A(4) = Z/8 and D_8's H^3 Z/4 catches the order-4
#         lift). Insufficient at m≥3 where A(4) = Z/4 — every D_8 conj
#         class gives res_D8[exp_idx][Z/4 coord] ∈ {0, 2}, killing the
#         order-2 sub-element on doubling.
#   #153 closure: Add a pinned Q_8 section. Q_8 has H^3 = Z/8, is NOT a
#         Q-isotropic preimage (so the Harada-Kono transfer-restriction
#         t∘r = 2^{h(Q)} formula doesn't bind it), and empirically gives
#         res(A(4)_gen) ∈ {2, 6} mod 8 → distinguishes 0 vs 2·A(4)_gen.
#         The Q_8 section may not exist at m=1 (no Q_8 in D_8); in that
#         degenerate case ctx_Q8 = fail and the trivial-class question
#         at m=1 collapses to "is ω the zero class in H^3(D_8; U(1))?"
#         answerable by the D_8 = G itself check anyway.
#
# Returns rec(
#   m, source ("hap" | "quillen"),
#   H_EA_list       : list of GAP subgroups, one per conj class of max EA
#   ctx_EA_list     : parallel list of SubgroupCohomologyContext recs
#   res_EA_list     : parallel list of k_G x k_{E_i} restriction matrices
#   torsion_EA_list : parallel list of subgroup torsion vectors
#   exp_EA_list     : parallel list of subgroup exponents
#   H_D8, ctx_D8, res_D8, torsion_D8, exp_D8 : pinned D_8 section
#   H_Q8, ctx_Q8, res_Q8, torsion_Q8, exp_Q8 : pinned Q_8 section
#                                              (may be fail at m=1)
#   torsion_G, exp_G, setup_G, G  : G-side data
#   Backward-compat aliases (point at the FIRST EA, equal to the old
#   single-EA result at this index): res_E, ctx_E, torsion_E, exp_E, H_E.
# ). Cached at module level by (m, source) in _DETF_CACHE.
BuildRestrictionMatrices := function(m, source)
    local key, ea_rec, G, H_D8, setup_G, ctx_D8, phi_D8, res_D8,
          H_EA_list, ctx_EA_list, res_EA_list, i, result,
          H_Q8, ctx_Q8, phi_Q8, res_Q8;

    if not (IsInt(m) and m >= 1) then
        Error("BuildRestrictionMatrices: m must be a positive integer; got ",
              m);
    fi;
    if not (source in ["hap", "quillen"]) then
        Error("BuildRestrictionMatrices: source must be \"hap\" or ",
              "\"quillen\"; got ", source);
    fi;

    # Phase 1 supports source = hap for m <= 5; m = 7 + hap is the trap we
    # explicitly want to prevent (would invoke ResolutionFiniteGroup(E_+(7), 4)).
    if source = "hap" and m > 5 then
        Error("BuildRestrictionMatrices: source=\"hap\" is not supported ",
              "for m > 5 because ResolutionFiniteGroup(E_+(", m, "), 4) ",
              "OOMs. Use source=\"quillen\" (Phase 2, gated on Q-int ",
              "A2/A3, issue #136). At m = ", m, ".");
    fi;
    if source = "quillen" then
        Error("BuildRestrictionMatrices: source=\"quillen\" is Phase 2 ",
              "and not yet implemented. Gated on Q-int A2/A3 (issue ",
              "#136). At m = ", m, ".");
    fi;

    key := Concatenation("m", String(m), "_", source);
    if IsBound(_DETF_CACHE.(key)) then
        return _DETF_CACHE.(key);
    fi;

    # Pin a single G instance via the first MaximalElementaryAbelian_E_plus
    # call. The returned ea_rec.parent is the EPlusGroup(m) we'll use for
    # ALL subsequent subgroup constructions and chain maps.
    ea_rec := MaximalElementaryAbelian_E_plus(m);
    G := ea_rec.parent;

    # Enumerate max-EA / D_8 / Q_8 sections inside G. Strategy is
    # m-dependent (D-VAN m=5 OOM fix, issue #287):
    #   * m <= 3: ConjugacyClassesSubgroups(G) enumeration. At m=2
    #     that's ~50 subgroups, at m=3 ~700, still tractable.
    #   * m >= 4: direct construction via the helpers in
    #     quillen_detecting_subgroup.g. ConjugacyClassesSubgroups on
    #     E_+(5) (|G|=2048) OOMs at 32 GB.
    H_EA_list := _DETF_AllMaxEAsIn(G, m);
    H_D8 := _DETF_FindD8In(G, m);

    setup_G := SetupCohomology3(G);

    # Per-EA: build cohomology context and restriction matrix.
    ctx_EA_list := [];
    res_EA_list := [];
    for i in [1..Length(H_EA_list)] do
        Add(ctx_EA_list, SubgroupCohomologyContext(H_EA_list[i]));
        Add(res_EA_list, RestrictionMatrixViaHAP(
            setup_G,
            ctx_EA_list[i],
            SubgroupInclusion(H_EA_list[i], G)));
    od;

    # D_8 side.
    ctx_D8 := SubgroupCohomologyContext(H_D8);
    phi_D8 := SubgroupInclusion(H_D8, G);
    res_D8 := RestrictionMatrixViaHAP(setup_G, ctx_D8, phi_D8);

    # Q_8 side (optional — see _DETF_FindQ8In docstring for why).
    # When present, closes the integer-cohomology detection gap by
    # distinguishing 2·A(4)_gen from 0 via H^3(Q_8) = Z/8.
    H_Q8 := _DETF_FindQ8In(G, m);
    if H_Q8 = fail then
        ctx_Q8 := fail;
        res_Q8 := fail;
        Print("[BuildRestrictionMatrices] no Q_8 section found at m = ", m,
              "; Q_8 detection skipped (this leaves the integer-cohomology ",
              "gap at m=", m, " open per #153)\n");
    else
        ctx_Q8 := SubgroupCohomologyContext(H_Q8);
        phi_Q8 := SubgroupInclusion(H_Q8, G);
        res_Q8 := RestrictionMatrixViaHAP(setup_G, ctx_Q8, phi_Q8);
    fi;

    result := rec(
        m               := m,
        source          := source,

        # Full detecting family.
        H_EA_list       := H_EA_list,
        ctx_EA_list     := ctx_EA_list,
        res_EA_list     := res_EA_list,
        torsion_EA_list := List(ctx_EA_list, c -> c.torsion),
        exp_EA_list     := List(ctx_EA_list, c -> c.exponent),

        # D_8 section.
        H_D8            := H_D8,
        ctx_D8          := ctx_D8,
        res_D8          := res_D8,
        torsion_D8      := ctx_D8.torsion,
        exp_D8          := ctx_D8.exponent,

        # Q_8 section (optional). May be fail if G has no Q_8 subgroup.
        H_Q8            := H_Q8,
        ctx_Q8          := ctx_Q8,
        res_Q8          := res_Q8,
        torsion_Q8      := If_(ctx_Q8 = fail, fail, ctx_Q8.torsion),
        exp_Q8          := If_(ctx_Q8 = fail, fail, ctx_Q8.exponent),

        # G-side data.
        torsion_G       := setup_G.torsion,
        exp_G           := setup_G.exponent,
        setup_G         := setup_G,
        G               := G,

        # Backward-compat aliases pointing at the first EA in the list.
        # New code should iterate over H_EA_list/ctx_EA_list/res_EA_list.
        res_E           := res_EA_list[1],
        ctx_E           := ctx_EA_list[1],
        torsion_E       := ctx_EA_list[1].torsion,
        exp_E           := ctx_EA_list[1].exponent,
        H_E             := H_EA_list[1]
    );

    _DETF_CACHE.(key) := result;
    return result;
end;;

Print("Loaded detecting_family_restriction.g (D-VAN-2: BuildRestrictionMatrices).\n");
