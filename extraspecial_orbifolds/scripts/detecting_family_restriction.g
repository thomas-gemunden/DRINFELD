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
# CRITICAL DETAIL — coefficient ring (D-VAN-FIX, #151):
#
#   The autom case has exp_G = exp_H = exp, so the same exponent is
#   used for image reduction AND for hombasis-H slack. For subgroup
#   inclusion exp_G != exp_H (e.g., m=2: exp_G = 8, exp_E = 2). The
#   original D-VAN-2 code reduced image_vec mod exp_H, which KILLED
#   the Z/2 classes of H^3(G; Z/exp_G) that are represented by
#   entries divisible by exp_G/exp_H (= 4 mod 8 for the Z/2 part of
#   Z/8). Empirically 9 of 10 m=2 unit generators were lost this way.
#
#   Fix: work in Z/exp_G uniformly. The hombasis_H is given in
#   Z/exp_H representation (entries in [0..exp_H)). Rescale by
#   (exp_G/exp_H) so each entry x becomes x * (exp_G/exp_H) in
#   [0..exp_G); this is the Z/exp_G representation of the same
#   class. The augmented matrix's slack rows become exp_G * I.
#   After solving x * aug = image mod exp_G, the j-th coordinate
#   x[j] is in [0..exp_G) and reduces to the desired Z/torsion_H[j]
#   value by taking mod torsion_H[j].
#
#   This works because for our 2-group cases exp_H | exp_G always
#   (H is a subgroup of a 2-group), and H^3(H; Z) is all 2-torsion
#   so Hom(H_3(H; Z), Z/exp_G) ≅ Hom(H_3(H; Z), Z/exp_H) via the
#   natural inclusion Z/exp_H -> Z/exp_G (multiply by exp_G/exp_H).
RestrictionMatrixViaHAP := function(setup_G, ctx_H, phi_HG)
    local R_G, K_G, UCT_G, exp_G, k_G, hombasis_G,
          R_H, K_H, UCT_H, exp_H, k_H, torsion_H, hombasis_H, hb_len_H,
          chainmap, gcf, F, autmat, rescale, hombasis_H_rescaled,
          aug_matrix, i, image_vec, image_modG, sol, col_coeffs,
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

    if exp_G mod exp_H <> 0 then
        Error("RestrictionMatrixViaHAP: exp_H (", exp_H,
              ") must divide exp_G (", exp_G,
              "); rescale strategy assumes exp_H | exp_G.");
    fi;
    rescale := exp_G / exp_H;

    # Equivariant chain map R_H -> R_G above phi: H -> G, then Z-tensored.
    chainmap := TensorWithIntegers(EquivariantChainMap(R_H, R_G, phi_HG));
    gcf := GroupCohomologyFunctor(K_H, K_G, chainmap, 3);
    F := gcf!.matrix;
    autmat := TransposedMat(F);

    # Rescale hombasis_H to Z/exp_G representation: each entry in
    # [0..exp_H) -> entry * (exp_G/exp_H) in [0..exp_G). Then build
    # the augmented matrix with slack exp_G * I_{hb_len_H}.
    hombasis_H_rescaled := List(hombasis_H,
        h -> List(h, x -> x * rescale));
    aug_matrix := Concatenation(
        hombasis_H_rescaled,
        List([1..hb_len_H], r -> List([1..hb_len_H], c ->
            If_(r = c, exp_G, 0))));

    res_mat := NullMat(k_G, k_H);
    for i in [1..k_G] do
        # phi^*(hombasis_G[i]) as length-hb_len_H vector mod exp_G.
        image_vec := hombasis_G[i] * autmat;
        image_modG := List(image_vec, x -> x mod exp_G);
        sol := SolutionIntMat(aug_matrix, image_modG);
        if sol = fail then
            Error("RestrictionMatrixViaHAP: could not project image of ",
                  "hombasis_G[", i, "] onto hombasis_H_rescaled. ",
                  "Possible causes: phi is not actually a homomorphism, ",
                  "or hombasis_H doesn't span H^3(H; Z/exp_G) (would ",
                  "indicate exp_H | exp_G assumption violated for some ",
                  "torsion factor).");
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
_DETF_FindD8In := function(G, m)
    local maxsub, candidates;
    if m = 1 then return G; fi;
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

# Enumerate ALL conjugacy class representatives of maximal elementary
# abelians (rank m+1) inside G. Per Quillen 1971, the family of these
# conj-class reps is what detects H^*(G; F_2) mod nilpotents in low
# degrees. Using a SINGLE representative (the prior simplification)
# left a large kernel in the restriction map — D-VAN-FIX (#151).
#
# Implementation: ConjugacyClassesSubgroups + filter. At m=2 this gives
# 6 reps; m=3 gives 30. For m >= 5 enumeration may be slow; that's a
# future optimisation (Phase 2 / Quillen path uses isotropic-subspace
# enumeration analytically).
_DETF_AllMaxEAsIn := function(G, m)
    local expected_order, reps, candidates;
    expected_order := 2 ^ (m + 1);
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
# D-VAN-FIX (#151): uses the FULL detecting family — all conjugacy
# class representatives of maximal elementary abelians (rank m+1) plus
# the pinned D_8 section. A single max EA leaves a large kernel in
# the restriction map (verified empirically at m=2: 9/10 unit gens
# map to zero with just one EA).
#
# Returns rec(
#   m, source ("hap" | "quillen"),
#   H_EA_list       : list of GAP subgroups, one per conj class of max EA
#   ctx_EA_list     : parallel list of SubgroupCohomologyContext recs
#   res_EA_list     : parallel list of k_G x k_{E_i} restriction matrices
#   torsion_EA_list : parallel list of subgroup torsion vectors
#   exp_EA_list     : parallel list of subgroup exponents
#   H_D8, ctx_D8, res_D8, torsion_D8, exp_D8 : the pinned D_8 section
#   torsion_G, exp_G, setup_G, G  : G-side data
#   Backward-compat aliases (point at the FIRST EA, equal to the old
#   single-EA result at this index): res_E, ctx_E, torsion_E, exp_E, H_E.
# ). Cached at module level by (m, source) in _DETF_CACHE.
BuildRestrictionMatrices := function(m, source)
    local key, ea_rec, G, H_D8, setup_G, ctx_D8, phi_D8, res_D8,
          H_EA_list, ctx_EA_list, res_EA_list, i, result;

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

    # Enumerate all conjugacy class reps of max EAs inside G, AND the
    # pinned D_8 section. Both filters traverse ConjugacyClassesSubgroups(G)
    # — at m=2 that's ~50 subgroups, at m=3 ~700 subgroups, still tractable.
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
