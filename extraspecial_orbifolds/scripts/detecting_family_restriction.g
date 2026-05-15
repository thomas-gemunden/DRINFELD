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
#   * EquivariantChainMap(R_H, R_G, phi) builds a chain map R_H -> R_G
#     above phi.
#   * TensorWithIntegers(...) descends to a Z-chain map K_H -> K_G.
#   * GroupCohomologyFunctor(K_H, K_G, chainmap, 3) gives F such that
#     F acts on adapted Z_3 cycle coords. On hom-vectors (length |ZZ_H|),
#     the pullback phi^* acts via right-multiplication by TransposedMat(F),
#     producing an image in H^3(G; Z/exp_G).
#   * IMPORTANT: the source/target swap for the inclusion case is just
#     the choice of R_H as source and R_G as target. The cohomology
#     functor is contravariant, so phi^* maps cocycles on G to cocycles
#     on H (correct direction for our restriction).
#   * The projection onto hombasis_H uses exp_H (not exp_G) for the
#     slack since the target lives in H^3(H; Z/exp_H).
RestrictionMatrixViaHAP := function(setup_G, ctx_H, phi_HG)
    local R_G, K_G, UCT_G, exp_G, k_G, hombasis_G,
          R_H, K_H, UCT_H, exp_H, k_H, torsion_H, hombasis_H, hb_len_H,
          chainmap, gcf, F, autmat,
          aug_matrix, i, image_vec, image_modH, sol, col_coeffs,
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

    # Equivariant chain map R_H -> R_G above phi: H -> G, then Z-tensored.
    chainmap := TensorWithIntegers(EquivariantChainMap(R_H, R_G, phi_HG));

    # Matrix of phi on adapted Z_3 cycle coords. Same convention as in
    # H3MatrixOfAutomorphism (brw_h3_action.g): GroupCohomologyFunctor
    # returns F such that row-form cycle coords transform by right-
    # multiplication by F. On hom-vectors, the dual action is right-mult
    # by TransposedMat(F).
    gcf := GroupCohomologyFunctor(K_H, K_G, chainmap, 3);
    F := gcf!.matrix;
    autmat := TransposedMat(F);

    # Augmented matrix for projecting any phi^*(hombasis_G[i]) onto
    # hombasis_H mod exp_H. The first k_H rows are the H-side hom-basis;
    # the last hb_len_H rows are exp_H * I_{hb_len_H} (slack for
    # mod-exp_H equivalence). SolutionIntMat(aug, image) returns x with
    # x * aug = image; x{[1..k_H]} are the desired H-side coords.
    aug_matrix := Concatenation(
        hombasis_H,
        List([1..hb_len_H], r -> List([1..hb_len_H], c ->
            If_(r = c, exp_H, 0))));

    res_mat := NullMat(k_G, k_H);
    for i in [1..k_G] do
        # phi^*(hombasis_G[i]) as a length-hb_len_H vector mod exp_G.
        image_vec := List(hombasis_G[i] * autmat, x -> x mod exp_G);
        # Reduce mod exp_H since target is H^3(H; Z/exp_H).
        image_modH := List(image_vec, x -> x mod exp_H);
        sol := SolutionIntMat(aug_matrix, image_modH);
        if sol = fail then
            Error("RestrictionMatrixViaHAP: could not project image of ",
                  "hombasis_G[", i, "] onto hombasis_H. ",
                  "Possible cause: phi is not actually a homomorphism ",
                  "or aug_matrix span is incorrect for this exp_H.");
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

# Public entry point. Phase 1 supports source = "hap" for m in {2, 3, 5}.
# m = 7 + "hap" errors (would invoke ResolutionFiniteGroup(E_+(7), 4) which
# OOMs). source = "quillen" is Phase 2, gated on Q-int A2/A3 (#136), and
# currently errors.
#
# Returns rec(
#   m, source ("hap" | "quillen"),
#   res_E       : k_G x k_E integer matrix, entries in [0..torsion_E[j]-1]
#   res_D8      : k_G x k_D8 integer matrix, entries in [0..torsion_D8[j]-1]
#   torsion_G, torsion_E, torsion_D8,
#   exp_G,     exp_E,     exp_D8,
#   setup_G,                # SetupCohomology3(G) record (for omega lifting)
#   ctx_E, ctx_D8,          # SubgroupCohomologyContext recs
#   H_E, H_D8,              # the pinned GAP subgroups
#   G                       # the parent E_+(m), pinned across both H_E, H_D8
# ). Cached at module level by (m, source) in _DETF_CACHE.
BuildRestrictionMatrices := function(m, source)
    local key, ea_rec, G, H_E, H_D8, setup_G, ctx_E, ctx_D8,
          phi_E, phi_D8, res_E, res_D8, result;

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

    # Pin a single G instance (each EPlusGroup(m) call builds a fresh
    # group with non-overlapping element families; mixing instances breaks
    # GroupHomomorphismByImages).
    ea_rec := MaximalElementaryAbelian_E_plus(m);
    G := ea_rec.parent;
    H_E := ea_rec.subgroup;
    H_D8 := _DETF_FindD8In(G, m);

    setup_G := SetupCohomology3(G);
    ctx_E := SubgroupCohomologyContext(H_E);
    ctx_D8 := SubgroupCohomologyContext(H_D8);

    phi_E := SubgroupInclusion(H_E, G);
    phi_D8 := SubgroupInclusion(H_D8, G);

    res_E  := RestrictionMatrixViaHAP(setup_G, ctx_E, phi_E);
    res_D8 := RestrictionMatrixViaHAP(setup_G, ctx_D8, phi_D8);

    result := rec(
        m            := m,
        source       := source,
        res_E        := res_E,
        res_D8       := res_D8,
        torsion_G    := setup_G.torsion,
        torsion_E    := ctx_E.torsion,
        torsion_D8   := ctx_D8.torsion,
        exp_G        := setup_G.exponent,
        exp_E        := ctx_E.exponent,
        exp_D8       := ctx_D8.exponent,
        setup_G      := setup_G,
        ctx_E        := ctx_E,
        ctx_D8       := ctx_D8,
        H_E          := H_E,
        H_D8         := H_D8,
        G            := G
    );

    _DETF_CACHE.(key) := result;
    return result;
end;;

Print("Loaded detecting_family_restriction.g (D-VAN-2: BuildRestrictionMatrices).\n");
