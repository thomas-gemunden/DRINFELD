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
# LHSResolutionEPlus (PR #252, issue #238) is the m=7-feasible
# replacement for ResolutionFiniteGroup(E_+(m), 4); needed by the
# `"lhs"` source path (issue #322).
if not IsBoundGlobal("LHSResolutionEPlus") then
    Read("hap_lhs_resolution.g");
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

# --- LHS-resolution-based G-side setup (issue #322) -----------------
#
# Builds a setup_G-shaped record on top of an externally-provided HAP
# resolution `R`. Identical to SetupCohomology3(G) but bypasses the
# `ResolutionFiniteGroup(G, 4)` call that OOMs at m=7. The downstream
# RestrictionMatrixViaHAP only reads setup_G.R / .K / .UCT / .exponent
# / .num_generators / .torsion, so a hand-built record with those
# fields is a drop-in replacement.
#
# WHY THIS MATTERS FOR m=7: ResolutionFiniteGroup(E_+(7), 4) requires
# ~60 GB heap (issue #137). LHSResolutionEPlus(7, 5) (PR #252) builds
# the same resolution to degree 5 in ~14 min wall, ~500 MB heap — a
# >100x reduction. With the resolution in hand, TensorWithIntegers +
# UniversalCoefficientsTheorem cost a few seconds at m=7 (small linear
# algebra at degree 3) and yield the same setup_G shape.
#
# CRITICAL: `R!.group` must be the same GAP group instance used to
# construct subgroups H downstream — `EquivariantChainMap(R_H, R, phi)`
# fails when phi's range doesn't match R!.group elementwise. Callers
# must thread `LHSResolutionEPlusDetailed(m, 5).G` through to the
# subgroup enumerators.
_DETF_SetupG_FromResolution := function(G, R)
    local K, UCT;
    K := TensorWithIntegers(R);
    UCT := UniversalCoefficientsTheorem(K, 3);
    return rec(group := G, R := R, K := K, UCT := UCT,
               exponent := UCT.exponent,
               num_generators := Length(UCT.hombasis),
               torsion := UCT.torsion,
               num_h3_classes := Product(UCT.torsion));
end;;

# Build a setup_G via LHSResolutionEPlus(m, 5). Returns the same rec
# shape as SetupCohomology3 but uses the LHS-perturbed resolution as
# R, making the m=7 case feasible. Caches by m so the (expensive at
# m=7) LHS build runs at most once per session.
#
# Reuses LHSResolutionEPlus's own per-(m, max_n) cache for R_E, so
# repeated calls within a session are O(1) for the resolution; the
# only first-call cost is K := TensorWithIntegers(R) + UCT.
_DETF_LHS_SETUP_G_CACHE := rec();;
_DETF_BuildSetupG_LHS := function(m)
    local key, det, setup;
    key := Concatenation("m", String(m));
    if IsBound(_DETF_LHS_SETUP_G_CACHE.(key)) then
        return _DETF_LHS_SETUP_G_CACHE.(key);
    fi;
    det := LHSResolutionEPlusDetailed(m, 5);
    setup := _DETF_SetupG_FromResolution(det.G, det.R_E);
    _DETF_LHS_SETUP_G_CACHE.(key) := setup;
    return setup;
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

# --- Witt-decomposition Lagrangian enumerator (issue #299) ---
#
# Returns the FULL list of m-dim type-+ Lagrangians in (F_2^{2m}, Q)
# where Q(v) = sum_i v_{2i-1} v_{2i} is the standard type-+ quadratic
# form. Each Lagrangian is returned as a list of m row vectors in
# F_2^{2m}, forming a basis of the subspace in REDUCED ROW ECHELON form
# (RREF): pivot columns strictly increasing, leading-1 at the pivot,
# zeros at other pivots (in the same row) and below the pivot (in the
# pivot column).
#
# Math: at m, N_+(m, 2) = prod_{i=0..m-1}(2^i + 1) Lagrangians of type +.
# Closed-form counts: 2, 6, 30, 270, 4590, 151470, 9845550 at m = 1..7.
#
# Algorithm: pivot-set-driven enumeration. Each RREF basis is uniquely
# determined by a sorted m-subset of pivot columns P = (p_1 < ... < p_m)
# of [1..2m] together with the free entries c[k][j] for j > p_k, j not
# in P. The constraints that make the resulting span a type-+ Lagrangian
# are:
#   (i)  B-orthogonality B(w_k, w_l) = 0 for k != l -- LINEAR in c[k][.]
#        given c[l][.] for l < k.
#   (ii) Q-isotropy Q(w_k) = 0 for each row k -- QUADRATIC in c[k][.]
#        (row-local).
#
# We enumerate by recursing row-by-row: at row k, solve the linear
# B-orth constraints (giving an affine F_2-subspace of free-var
# assignments), then loop over that subspace and check Q-isotropy. Each
# successful row extends the recursion to row k+1; at row m+1 we yield
# the completed (w_1, ..., w_m) basis.
#
# Helpers below operate on integer-entry vectors and matrices reduced
# mod 2; the qforms_f2 helpers F2Mod / F2RREF / F2RightNullspace are
# reused for the linear-algebra primitive operations.

# Polarisation B(u, v) = sum_i (u_{2i-1} v_{2i} + u_{2i} v_{2i-1}) mod 2.
_DETF_BForm := function(u, v)
    local n, s, i;
    n := Length(u) / 2;
    s := 0;
    for i in [1..n] do
        s := s + u[2*i - 1] * v[2*i] + u[2*i] * v[2*i - 1];
    od;
    return s mod 2;
end;;

# Q(v) = sum_i v_{2i-1} v_{2i} mod 2.
_DETF_QForm := function(v)
    local n, s, i;
    n := Length(v) / 2;
    s := 0;
    for i in [1..n] do
        s := s + v[2*i - 1] * v[2*i];
    od;
    return s mod 2;
end;;

# Solve A * x = b over F_2 where A is a list of rows (each of length nVars).
# Returns rec(particular := x0, nullspace := basis_of_null) or fail if
# inconsistent. If A is empty, returns (zero vector, full standard basis).
_DETF_F2LinSolve := function(A, b, nVars)
    local m, augm, i, j, r, c, pivCols, freeCols, x0, basis, v, p, e;
    m := Length(A);
    if m = 0 then
        # No constraints: any x works; particular = 0.
        # Build standard basis of F_2^nVars manually (no dependency).
        basis := [];
        for i in [1..nVars] do
            e := List([1..nVars], j -> 0);
            e[i] := 1;
            Add(basis, e);
        od;
        return rec(particular := List([1..nVars], i -> 0),
                   nullspace := basis);
    fi;
    # Build augmented matrix [A | b] of size m x (nVars + 1), then RREF.
    augm := List([1..m], i -> Concatenation(List(A[i], x -> x mod 2),
                                            [b[i] mod 2]));
    r := 1;
    pivCols := [];
    for c in [1..nVars] do
        if r > m then break; fi;
        j := r;
        while j <= m and augm[j][c] = 0 do j := j + 1; od;
        if j > m then continue; fi;
        if j <> r then augm{[r, j]} := augm{[j, r]}; fi;
        for i in [1..m] do
            if i <> r and augm[i][c] = 1 then
                augm[i] := List([1..nVars + 1],
                                k -> (augm[i][k] + augm[r][k]) mod 2);
            fi;
        od;
        Add(pivCols, c);
        r := r + 1;
    od;
    # Inconsistent iff any row has all-zero left part but RHS = 1.
    for i in [r..m] do
        if augm[i][nVars + 1] <> 0 then
            return fail;
        fi;
    od;
    # Build particular solution: pivot var = augm[i][nVars+1], free = 0.
    x0 := List([1..nVars], i -> 0);
    for i in [1..Length(pivCols)] do
        x0[pivCols[i]] := augm[i][nVars + 1];
    od;
    # Build nullspace basis.
    freeCols := Filtered([1..nVars], c -> not (c in pivCols));
    basis := [];
    for c in freeCols do
        v := List([1..nVars], i -> 0);
        v[c] := 1;
        for i in [1..Length(pivCols)] do
            p := pivCols[i];
            v[p] := augm[i][c];
        od;
        Add(basis, v);
    od;
    return rec(particular := x0, nullspace := basis);
end;;

# Build row w_k for a given pivot set P and free-var assignment c_vec.
# c_vec is a list of length |F_k| giving the values c[k][F_k[j]] for j = 1..|F_k|.
# P is sorted, k is the row index (1-based), n = 2m.
_DETF_BuildRow := function(k, P, F_k, c_vec, n)
    local w, j;
    w := List([1..n], i -> 0);
    w[P[k]] := 1;
    for j in [1..Length(F_k)] do
        w[F_k[j]] := c_vec[j];
    od;
    return w;
end;;

# Free-variable positions for row k under pivot set P: positions > P[k]
# that are NOT in P. Returns a sorted list of column indices.
_DETF_FreeCols := function(k, P, n)
    return Filtered([(P[k] + 1)..n], j -> not (j in P));
end;;

# Build the B-orthogonality LINEAR constraints on c[k][.] given the
# already-chosen earlier rows W_prev (each a 1xn vector).
# Returns (A, b) where A is a list of rows of length |F_k| and b is
# the RHS such that A * c[k][.]^T = b enforces B(w_k, w_l) = 0 for all l.
#
# OPTIMIZATION (issue #299): for the standard symplectic form
# B(u, v) = sum_i (u_{2i-1} v_{2i} + u_{2i} v_{2i-1}),
# the bilinear pairing of e_j against w_l is just w_l[partner(j)] where
# partner(j) = j + 1 if j is odd, j - 1 if j is even. So we avoid
# materializing e_j entirely.
_DETF_BorthConstraints := function(k, P, F_k, W_prev, n)
    local rows, rhs, l, w_l, a_row, const, j, jj, partner_jj,
          pk, partner_pk;
    rows := [];
    rhs := [];
    pk := P[k];
    # partner_pk: column index "j" such that B(e_pk, e_j) = 1.
    # For pk odd: partner = pk + 1; for pk even: partner = pk - 1.
    if pk mod 2 = 1 then partner_pk := pk + 1;
    else partner_pk := pk - 1; fi;
    for l in [1..Length(W_prev)] do
        w_l := W_prev[l];
        a_row := [];
        for j in [1..Length(F_k)] do
            jj := F_k[j];
            if jj mod 2 = 1 then partner_jj := jj + 1;
            else partner_jj := jj - 1; fi;
            # B(e_jj, w_l) = w_l[partner_jj].
            Add(a_row, w_l[partner_jj]);
        od;
        # RHS = B(e_pk, w_l) = w_l[partner_pk].
        const := w_l[partner_pk];
        Add(rows, a_row);
        Add(rhs, const);
    od;
    return rec(A := rows, b := rhs);
end;;

# Enumerate type-+ Lagrangians of F_2^{2m} via the pivot-set + RREF
# algorithm. Returns a list of m-row matrices, each row a length-2m
# 0/1 integer vector.
#
# Memory-friendly variant: writes into `acc` (a record with .list field).
# Caller can swap to streaming if needed.
_DETF_LagrangiansViaWitt_inner := function(P, m, n, k, W_prev, acc)
    local F_k, borth, sol, null_dim, idx, c_part, c_free, c_vec, w_k,
          q_check, W_new, t;
    if k > m then
        Add(acc.list, ShallowCopy(W_prev));
        return;
    fi;
    F_k := _DETF_FreeCols(k, P, n);
    borth := _DETF_BorthConstraints(k, P, F_k, W_prev, n);
    sol := _DETF_F2LinSolve(borth.A, borth.b, Length(F_k));
    if sol = fail then return; fi;
    c_part := sol.particular;
    null_dim := Length(sol.nullspace);
    # Enumerate the 2^null_dim affine solutions.
    for idx in [0..(2^null_dim - 1)] do
        c_vec := ShallowCopy(c_part);
        for t in [1..null_dim] do
            if QuoInt(idx, 2^(t - 1)) mod 2 = 1 then
                c_vec := List([1..Length(c_vec)],
                              j -> (c_vec[j] + sol.nullspace[t][j]) mod 2);
            fi;
        od;
        w_k := _DETF_BuildRow(k, P, F_k, c_vec, n);
        q_check := _DETF_QForm(w_k);
        if q_check = 0 then
            W_new := Concatenation(W_prev, [w_k]);
            _DETF_LagrangiansViaWitt_inner(P, m, n, k + 1, W_new, acc);
        fi;
    od;
end;;

# Public: enumerate type-+ Lagrangians of F_2^{2m} via Witt decomposition
# (pivot-set RREF enumeration). Returns a list of m-row matrices.
#
# Cost: scales as N_+(m, 2) Lagrangians produced; per-Lagrangian work is
# O(m^2 * |F_k|) for the per-row linear-algebra. At m=7, expected wall is
# a few minutes (N_+(7, 2) = 9,845,550) on a 2026 laptop.
#
# Returns the full list; for m=7 the list occupies on the order of
# 9.8M * m * 2m * 4 bytes ~= 5 GB if stored as plain GAP lists (each F_2
# entry as a GAP integer). For more compact storage, callers can map to
# group elements eagerly (see _DETF_AllMaxEAsIn for that path).
_DETF_LagrangiansViaWitt := function(m)
    local n, P_iter, acc, P_list;
    n := 2 * m;
    acc := rec(list := []);
    # Enumerate all size-m subsets P of [1..n].
    for P_list in Combinations([1..n], m) do
        _DETF_LagrangiansViaWitt_inner(P_list, m, n, 1, [], acc);
    od;
    return acc.list;
end;;

# Streaming inner: recursion that calls consumer on each completed
# Lagrangian. Closes over m, n, consumer via the outer call. Mutual
# recursion through a closure-style global.
_DETF_LagrangiansViaWitt_streaming_inner := function(P, m, n, k, W_prev,
                                                     consumer, count_rec)
    local F_k, borth, sol, null_dim, idx, c_part, c_vec, w_k,
          q_check, t;
    if k > m then
        consumer(W_prev);
        count_rec.n := count_rec.n + 1;
        return;
    fi;
    F_k := _DETF_FreeCols(k, P, n);
    borth := _DETF_BorthConstraints(k, P, F_k, W_prev, n);
    sol := _DETF_F2LinSolve(borth.A, borth.b, Length(F_k));
    if sol = fail then return; fi;
    c_part := sol.particular;
    null_dim := Length(sol.nullspace);
    for idx in [0..(2^null_dim - 1)] do
        c_vec := ShallowCopy(c_part);
        for t in [1..null_dim] do
            if QuoInt(idx, 2^(t - 1)) mod 2 = 1 then
                c_vec := List([1..Length(c_vec)],
                              j -> (c_vec[j] + sol.nullspace[t][j])
                                    mod 2);
            fi;
        od;
        w_k := _DETF_BuildRow(k, P, F_k, c_vec, n);
        q_check := _DETF_QForm(w_k);
        if q_check = 0 then
            _DETF_LagrangiansViaWitt_streaming_inner(P, m, n, k + 1,
                Concatenation(W_prev, [w_k]),
                consumer, count_rec);
        fi;
    od;
end;;

# Streaming variant: applies `consumer(L)` to each Lagrangian L (an
# m-row 0/1 matrix) as it is produced, without accumulating the full
# list. Returns the count of Lagrangians produced.
#
# Use this when the caller can map each Lagrangian to a downstream
# representation (e.g. a GAP subgroup) and discard the F_2 basis
# immediately. Avoids the ~5 GB peak of _DETF_LagrangiansViaWitt at m=7.
_DETF_LagrangiansViaWitt_streaming := function(m, consumer)
    local n, P_list, count_rec;
    n := 2 * m;
    count_rec := rec(n := 0);
    for P_list in Combinations([1..n], m) do
        _DETF_LagrangiansViaWitt_streaming_inner(P_list, m, n, 1, [],
                                                  consumer, count_rec);
    od;
    return count_rec.n;
end;;

# Map a Lagrangian basis L (m row vectors in F_2^{2m}) to a GAP subgroup
# of G via the symplectic generator convention gens_G[1..2m]:
# w_k = (w_k[1], ..., w_k[2m]) -> prod_i gens_G[i]^{w_k[i]}.
# The subgroup is generated by z (centre) together with the m mapped
# basis elements; rank m+1 elementary abelian.
_DETF_LagrangianToSubgroup := function(L, gens_G, z, G)
    local m, n, basis, k, prod, i;
    m := Length(L);
    n := 2 * m;
    basis := [z];
    for k in [1..m] do
        prod := One(G);
        for i in [1..n] do
            if L[k][i] = 1 then
                prod := prod * gens_G[i];
            fi;
        od;
        Add(basis, prod);
    od;
    return Subgroup(G, basis);
end;;

# Map a Lagrangian basis L (m row vectors in F_2^{2m}) to a BASIS-TUPLE
# of group elements: [z, g_1, ..., g_m] where g_k = prod_i gens_G[i]^{w_k[i]}.
# Caller may wrap with `Subgroup(G, tuple)` if needed; storing tuples is
# ~5x more memory-efficient than Subgroup objects at scale (issue #299,
# m=7 budget).
#
# Optional `elem_cache` (a GAP record): if provided, used to memoize the
# group-element value of each F_2^{2m} vector (key = integer encoding of
# the bit vector). At m=7 with 9.8M Lagrangians, there are at most 2^14 -
# 1 = 16383 distinct nonzero F_2^14 row vectors used as basis elements,
# so caching dramatically reduces unique PC element churn.
_DETF_LagrangianToBasisTuple := function(L, gens_G, z, G, elem_cache,
                                          powers)
    local m, n, basis, k, prod, i, w_k_int;
    m := Length(L);
    n := 2 * m;
    basis := [z];
    for k in [1..m] do
        # Compute integer encoding of L[k] for cache key. Uses
        # precomputed powers[i] = 2^(i-1) to avoid repeated 2^i evals.
        w_k_int := 0;
        for i in [1..n] do
            if L[k][i] = 1 then
                w_k_int := w_k_int + powers[i];
            fi;
        od;
        if elem_cache <> fail and IsBound(elem_cache.(w_k_int)) then
            Add(basis, elem_cache.(w_k_int));
        else
            prod := One(G);
            for i in [1..n] do
                if L[k][i] = 1 then
                    prod := prod * gens_G[i];
                fi;
            od;
            if elem_cache <> fail then
                elem_cache.(w_k_int) := prod;
            fi;
            Add(basis, prod);
        fi;
    od;
    return basis;
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
#     elementary abelians (= 6, 30, 270, 4590, 151470, 9845550 at
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
#
# Dispatch by m (issue #287 m=5 fix, issue #299 m=7 Witt extension):
#
#   * m <= 3: full ConjugacyClassesSubgroups enumeration (bit-for-bit
#     compatibility with m=2/m=3 anchors). Returns GAP Subgroup objects.
#   * m = 4, 5: axis-aligned + diagonal-pair-swap (112 at m=5).
#     Empirically sufficient at m=5 (0/165 false trivials, issue #287);
#     preserved for backward compatibility. Returns GAP Subgroup objects.
#   * m >= 6: full Witt-decomposition systematic enumeration. Returns the
#     complete N_+(m, 2) = prod_{i=0..m-1}(2^i + 1) type-+ Lagrangians.
#     At m=6 this is 151470; at m=7 it is 9,845,550.
#
#     **API NOTE**: at m >= 6 we return a list of BASIS-TUPLES rather
#     than GAP Subgroup objects. Each tuple has the form
#     [z, g_1, ..., g_m] where the rank-(m+1) elementary abelian is
#     Subgroup(G, tuple). Rationale: at m=7, storing 9.8M GAP Subgroup
#     objects (~1.7 KB each incl. metadata) costs ~17 GB, vastly over
#     the 4 GB issue #299 budget. Basis-tuples cost ~400 bytes each
#     (m+1 PC element refs + list overhead), well within budget.
#     Callers that need a GAP Subgroup should call Subgroup(G, tuple)
#     per element. The m <= 5 path is unchanged (still returns
#     Subgroup objects) to preserve the existing API surface.
_DETF_AllMaxEAsIn := function(G, m)
    local expected_order, reps, candidates, H, Z_G, z, gens_G, n_pairs,
          sel_bits, sel, basis, i, ea, ea_list,
          a, b, other_pairs, other_sel_bits, oj, idx, consumer,
          first_check_sub, elem_cache, powers;
    expected_order := 2 ^ (m + 1);
    if m >= 6 then
        # Full Witt-decomposition enumeration (issue #299).
        # Returns BASIS-TUPLES (lists of m+1 group elements), not
        # Subgroup objects: ~5x smaller memory, fits in the 4 GB
        # budget at m=7. Callers wrap via Subgroup(G, tuple) on demand.
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
        # Group-element cache: keys are integer-encoded F_2^{2m} vectors,
        # values are the corresponding PC elements. At m=7 there are at
        # most 2^14 - 1 = 16383 distinct nonzero F_2^14 vectors that can
        # appear as basis-tuple entries, so the cache caps at 16K elements.
        # Memory saving: ~5-10x reduction in PC element churn vs creating
        # a fresh PC element per basis position per Lagrangian.
        elem_cache := rec();
        # Precomputed [2^0, 2^1, ..., 2^(2m-1)] for the integer encoding
        # in _DETF_LagrangianToBasisTuple — avoids re-evaluating 2^(i-1)
        # per row inside the per-Lagrangian hot loop.
        powers := List([1..2*m], i -> 2^(i - 1));
        consumer := function(L)
            Add(ea_list, _DETF_LagrangianToBasisTuple(L, gens_G, z, G,
                                                       elem_cache, powers));
        end;
        _DETF_LagrangiansViaWitt_streaming(m, consumer);
        if Length(ea_list) = 0 then
            Error("_DETF_AllMaxEAsIn: Witt enumeration at m = ", m,
                  " produced no Lagrangians. Witt enumerator bug?");
        fi;
        # Sanity-check the first basis-tuple (wrap, check Order +
        # ElementaryAbelian). PC-generator convention guard.
        first_check_sub := Subgroup(G, ea_list[1]);
        if Order(first_check_sub) <> expected_order
           or not IsElementaryAbelian(first_check_sub) then
            Error("_DETF_AllMaxEAsIn: Witt enumeration at m = ", m,
                  " produced a non-max-EA first basis-tuple ",
                  "(order ", Order(first_check_sub), ", expected ",
                  expected_order, "). PC-generator convention changed?");
        fi;
        return ea_list;
    fi;
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
#   m, source ("hap" | "lhs" | "quillen"),
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
    if not (source in ["hap", "lhs", "quillen"]) then
        Error("BuildRestrictionMatrices: source must be \"hap\", \"lhs\", ",
              "or \"quillen\"; got ", source);
    fi;

    # Phase 1 supports source = hap for m <= 5; m = 7 + hap is the trap we
    # explicitly want to prevent (would invoke ResolutionFiniteGroup(E_+(7), 4)).
    if source = "hap" and m > 5 then
        Error("BuildRestrictionMatrices: source=\"hap\" is not supported ",
              "for m > 5 because ResolutionFiniteGroup(E_+(", m, "), 4) ",
              "OOMs. Use source=\"lhs\" (issue #322), which builds the ",
              "same setup via LHSResolutionEPlus(m, 5) (PR #252). ",
              "At m = ", m, ".");
    fi;
    if source = "lhs" and m = 7 then
        # m=7 eager enumeration of all 9.8M max EAs would consume
        # ~17 GB. Defer to the streaming-greedy path in
        # _DETF_TrimmedFamily(7) instead of materialising via this
        # function. Users should call _DETF_TrimmedFamily(7) directly.
        Error("BuildRestrictionMatrices: source=\"lhs\" at m = 7 would ",
              "materialise 9 845 550 max-EA restriction matrices (out of ",
              "memory). Use _DETF_TrimmedFamily(7) which streams + samples ",
              "candidates instead. At m = ", m, ".");
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

    # G-side resolution: source-dependent.
    #
    #   "hap": ResolutionFiniteGroup(G, 4) — direct (m <= 5).
    #   "lhs": LHSResolutionEPlus(m, 5)    — LHS-perturbed (m <= 5 for
    #          cross-validation; m=7 path goes through
    #          _DETF_TrimmedFamily(7) instead since eager EA enumeration
    #          is infeasible).
    if source = "lhs" then
        # Pin G to the resolution's group instance — required for
        # EquivariantChainMap to find H's elements in R!.elts.
        setup_G := _DETF_BuildSetupG_LHS(m);
        G := setup_G.group;
    else
        # Pin a single G instance via the first MaximalElementaryAbelian_E_plus
        # call. The returned ea_rec.parent is the EPlusGroup(m) we'll use for
        # ALL subsequent subgroup constructions and chain maps.
        ea_rec := MaximalElementaryAbelian_E_plus(m);
        G := ea_rec.parent;
        setup_G := SetupCohomology3(G);
    fi;

    # Enumerate max-EA / D_8 / Q_8 sections inside G. Strategy is
    # m-dependent (D-VAN m=5 OOM fix, issue #287):
    #   * m <= 3: ConjugacyClassesSubgroups(G) enumeration. At m=2
    #     that's ~50 subgroups, at m=3 ~700, still tractable.
    #   * m >= 4: direct construction via the helpers in
    #     quillen_detecting_subgroup.g. ConjugacyClassesSubgroups on
    #     E_+(5) (|G|=2048) OOMs at 32 GB.
    H_EA_list := _DETF_AllMaxEAsIn(G, m);
    H_D8 := _DETF_FindD8In(G, m);

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


# =====================================================================
# Slack-trimming pass: minimal verified detecting family (issue #313).
#
# Helper `_DETF_KernelOrderSNF` is defined first so the parser sees it
# bound when `_DETF_TrimmedFamily` is read in (avoids the "unbound
# global" syntax warning even though GAP resolves globals at call
# time).

# SNF-based |ker(joint restriction)| for the given EA index subset +
# D_8 (always) + Q_8 (optional). Internal helper for _DETF_TrimmedFamily.
#
# Math: H^3(G; U(1)) = ⊕_i Z/torsion_G[i]; for a family
# F = {H_1, ..., H_k}, the joint restriction `R: H^3(G; U(1)) -> ⊕_j
# H^3(H_j; U(1))` is determined by stacking the per-H restriction
# matrices column-wise into a single k_G × N integer matrix M (where
# N = Σ_j k_{H_j}). The image of R inside the H-side ambient group
# A_H = ⊕_j Z/torsion_H_j has order |A_H| / |coker([M; D_H])| where
# D_H = diag(torsion_H). |ker(R)| = |H^3(G; U(1))| / |image(R)|.
_DETF_KernelOrderSNF := function(data, ea_indices, include_D8, include_Q8)
    local M_blocks, T_blocks, j, M, T_H, N, D_H, B, snf, factors,
          k, image_order, group_order;
    M_blocks := [];
    T_blocks := [];
    for j in ea_indices do
        Add(M_blocks, data.res_EA_list[j]);
        Append(T_blocks, data.torsion_EA_list[j]);
    od;
    if include_D8 then
        Add(M_blocks, data.res_D8);
        Append(T_blocks, data.torsion_D8);
    fi;
    if include_Q8 and data.res_Q8 <> fail then
        Add(M_blocks, data.res_Q8);
        Append(T_blocks, data.torsion_Q8);
    fi;
    # Concatenate column-wise: each block is k_G × k_{H_j}.
    M := TransposedMat(Concatenation(List(M_blocks, TransposedMat)));
    T_H := T_blocks;
    N := Length(T_H);
    if N = 0 then
        # Degenerate: no subgroups → image is trivial → |ker| = |H^3(G)|.
        return Product(data.torsion_G);
    fi;
    D_H := List([1..N], i -> List([1..N], j2 ->
                If_(i = j2, T_H[i], 0)));
    B := Concatenation(M, D_H);
    snf := SmithNormalFormIntegerMat(B);
    factors := [];
    for k in [1..Minimum(Length(snf), N)] do
        if snf[k][k] = 0 then
            Error("_DETF_KernelOrderSNF: SNF has a zero invariant ",
                  "factor (infinite cokernel). The D_H block in B ",
                  "should make the cokernel finite; this should never ",
                  "happen unless data.torsion_* is malformed.");
        fi;
        Add(factors, snf[k][k]);
    od;
    image_order := Product(T_H) / Product(factors);
    group_order := Product(data.torsion_G);
    return group_order / image_order;
end;;


# =====================================================================
# Public alias for the LHS-resolution-aware restriction-matrix builder
# (issue #322). Thin wrapper around BuildRestrictionMatrices(m, "lhs")
# that documents intent: build the same record as the HAP path but
# using LHSResolutionEPlus instead of ResolutionFiniteGroup, making
# the m=7 case feasible (within streaming + sampling at m=7; see
# _DETF_TrimmedFamily(7) for the m=7 driver).
#
# At m in {2, 3, 5}: returns the same shape as
# BuildRestrictionMatrices(m, "hap"), enabling cross-validation
# (kernel orders, image orders, trimmed-family invariants).
# At m=7: errors with a redirect to _DETF_TrimmedFamily(7), since
# eager enumeration of 9.8M EAs is infeasible.
_DETF_RestrictionMatricesViaLHS := function(m)
    return BuildRestrictionMatrices(m, "lhs");
end;;


# =====================================================================
# m=7 streaming + sampling driver for _DETF_TrimmedFamily (issue #322).
#
# Why this needs a custom driver: the m=7 Lagrangian count is
# 9 845 550, far too many to materialise eagerly. The strategy is:
#
#   1. Build the LHS G-side setup (LHSResolutionEPlus(7, 5) — ~14 min
#      wall, ~500 MB heap per PR #252's benchmarks).
#   2. Build the D_8 and Q_8 contexts + their restriction matrices.
#   3. Sample K candidates uniformly from the 9.8M Lagrangians using
#      reservoir sampling during the Witt-streaming pass (~10 min wall
#      per PR #307's m=6 → m=7 scaling). For each sampled candidate,
#      build the restriction matrix immediately (each takes ~seconds
#      against R_E_lhs at degree 3-4).
#   4. Greedy over the K sampled candidates + D_8 + Q_8.
#   5. Drop-one verification on the chosen family.
#
# The wall is dominated by step 1 (LHS resolution build) + step 3 (K
# restriction-matrix builds; at K=1000 with ~5 s per build, ~80 min).
#
# Memory bound: K restriction matrices × ~100 KB each (k_G × k_H,
# with k_G ~ 91 + few Z/4 generators at m=7 and k_H ~ a few hundred
# for a rank-8 elementary abelian) ≈ 100 MB. Plus 500 MB LHS
# resolution = ~600 MB peak, comfortably under the 4 GB target.
#
# Options:
#   opts.m           : m (default 7; can be overridden for unit-testing
#                       the streaming-greedy path at smaller m)
#   opts.sample_size : K = number of sampled candidates (default 1000)
#   opts.seed        : RNG seed for reservoir sampling (default `time-based`)
#   opts.verbose     : print progress (default true at m=7)
_DETF_TrimmedFamily_m7_streaming := function(opts)
    local m, sample_size, verbose, t0, t_end,
          setup_G, G, gens_G, Z_G, z, gens_G_non_central,
          H_D8, ctx_D8, phi_D8, res_D8,
          H_Q8, ctx_Q8, phi_Q8, res_Q8,
          include_Q8, n, powers, elem_cache,
          sample_basis_tuples, sample_consumer, count_so_far,
          n_target, K, candidates, ea_subs, ea_ctxs, ea_ress,
          i, H_i, ctx_i, phi_i, res_i, ea_list,
          data, n_EA, ea_chosen, greedy_log, curr_ker,
          best_j, best_ker, j, k_try, ea_sorted, drop_kers,
          sub_indices, ker_drop, locally_tight, result,
          seed, rs;

    # Allow opts.m override for testing the streaming path at smaller m.
    # Default = 7 (the production case).
    if IsBound(opts.m) then
        m := opts.m;
    else
        m := 7;
    fi;
    t0 := Runtime();

    # Resolve options.
    if IsBound(opts.sample_size) then
        sample_size := opts.sample_size;
    else
        sample_size := 1000;
    fi;
    if not (IsInt(sample_size) and sample_size >= 1) then
        Error("_DETF_TrimmedFamily_m7_streaming: opts.sample_size must ",
              "be a positive integer; got ", sample_size);
    fi;
    if IsBound(opts.verbose) then
        verbose := opts.verbose;
    else
        verbose := true;
    fi;
    if IsBound(opts.seed) then
        seed := opts.seed;
        rs := RandomSource(IsMersenneTwister, seed);
    else
        # Use the default GAP random source (state-shared with Random()).
        rs := GlobalMersenneTwister;
    fi;

    if verbose then
        Print("[_DETF_TrimmedFamily_m7] sample_size = ", sample_size, "\n");
    fi;

    # --- Step 1: LHS G-side setup. Slow at m=7 (~14 min cold).
    if verbose then
        Print("[_DETF_TrimmedFamily_m7] building LHS resolution + UCT ",
              "(~14 min cold) ...\n");
    fi;
    setup_G := _DETF_BuildSetupG_LHS(m);
    G := setup_G.group;

    # Sanity check on G: must be the LHS resolution's group instance.
    if verbose then
        Print("[_DETF_TrimmedFamily_m7] |G| = ", Order(G), ", ",
              "k_G (G-side H^3 generators) = ", setup_G.num_generators,
              ", torsion_G = ", setup_G.torsion, "\n");
    fi;

    # --- Step 2: D_8 + Q_8 sections.
    if verbose then
        Print("[_DETF_TrimmedFamily_m7] building D_8 + Q_8 contexts + ",
              "restriction matrices ...\n");
    fi;
    H_D8 := _DETF_FindD8In(G, m);
    ctx_D8 := SubgroupCohomologyContext(H_D8);
    phi_D8 := SubgroupInclusion(H_D8, G);
    res_D8 := RestrictionMatrixViaHAP(setup_G, ctx_D8, phi_D8);

    H_Q8 := _DETF_FindQ8In(G, m);
    if H_Q8 = fail then
        ctx_Q8 := fail;
        phi_Q8 := fail;
        res_Q8 := fail;
    else
        ctx_Q8 := SubgroupCohomologyContext(H_Q8);
        phi_Q8 := SubgroupInclusion(H_Q8, G);
        res_Q8 := RestrictionMatrixViaHAP(setup_G, ctx_Q8, phi_Q8);
    fi;
    include_Q8 := (res_Q8 <> fail);

    # --- Step 3: streaming reservoir sample of size K candidates.
    if verbose then
        Print("[_DETF_TrimmedFamily_m7] streaming Witt enumeration + ",
              "reservoir sampling K = ", sample_size, " out of 9 845 550 ",
              "Lagrangians ...\n");
    fi;
    n := 2 * m;
    powers := List([1..n], i -> 2^(i - 1));
    elem_cache := rec();
    Z_G := Centre(G);
    z := First(AsList(Z_G), x -> not IsOne(x));
    gens_G := GeneratorsOfGroup(G);
    gens_G_non_central := Filtered(gens_G, g -> not (g in Z_G));
    if Length(gens_G_non_central) < n then
        Error("_DETF_TrimmedFamily_m7_streaming: |GeneratorsOfGroup(G) \\ Z| < 2m");
    fi;
    gens_G_non_central := gens_G_non_central{[1..n]};

    sample_basis_tuples := [];
    count_so_far := rec(n := 0);
    K := sample_size;
    sample_consumer := function(L)
        local tuple, slot;
        count_so_far.n := count_so_far.n + 1;
        tuple := _DETF_LagrangianToBasisTuple(L, gens_G_non_central, z,
                                              G, elem_cache, powers);
        if Length(sample_basis_tuples) < K then
            # Reservoir not yet full: add unconditionally.
            Add(sample_basis_tuples, tuple);
        else
            # Reservoir full: replace position Random(rs, 1, count_so_far.n)
            # iff that index <= K.
            slot := Random(rs, 1, count_so_far.n);
            if slot <= K then
                sample_basis_tuples[slot] := tuple;
            fi;
        fi;
        if verbose and count_so_far.n mod 500000 = 0 then
            Print("[_DETF_TrimmedFamily_m7]   ", count_so_far.n,
                  " / 9845550 Lagrangians visited\n");
        fi;
    end;
    _DETF_LagrangiansViaWitt_streaming(m, sample_consumer);
    if verbose then
        Print("[_DETF_TrimmedFamily_m7]   sampling done: ",
              count_so_far.n, " visited, ",
              Length(sample_basis_tuples), " sampled.\n");
    fi;

    # --- Step 4: per-sample restriction matrices.
    if verbose then
        Print("[_DETF_TrimmedFamily_m7] building ",
              Length(sample_basis_tuples), " per-sample restriction matrices ",
              "(slow: ~seconds per build) ...\n");
    fi;
    ea_subs := [];
    ea_ctxs := [];
    ea_ress := [];
    for i in [1..Length(sample_basis_tuples)] do
        H_i := Subgroup(G, sample_basis_tuples[i]);
        ctx_i := SubgroupCohomologyContext(H_i);
        phi_i := SubgroupInclusion(H_i, G);
        res_i := RestrictionMatrixViaHAP(setup_G, ctx_i, phi_i);
        Add(ea_subs, H_i);
        Add(ea_ctxs, ctx_i);
        Add(ea_ress, res_i);
        if verbose and i mod 100 = 0 then
            Print("[_DETF_TrimmedFamily_m7]   built ", i, " / ",
                  Length(sample_basis_tuples),
                  " restriction matrices (wall = ",
                  Runtime() - t0, " ms)\n");
        fi;
    od;

    # Wrap into a data rec compatible with _DETF_KernelOrderSNF.
    data := rec(
        m               := m,
        source          := "lhs",
        H_EA_list       := ea_subs,
        ctx_EA_list     := ea_ctxs,
        res_EA_list     := ea_ress,
        torsion_EA_list := List(ea_ctxs, c -> c.torsion),
        exp_EA_list     := List(ea_ctxs, c -> c.exponent),
        H_D8            := H_D8,
        ctx_D8          := ctx_D8,
        res_D8          := res_D8,
        torsion_D8      := ctx_D8.torsion,
        exp_D8          := ctx_D8.exponent,
        H_Q8            := H_Q8,
        ctx_Q8          := ctx_Q8,
        res_Q8          := res_Q8,
        torsion_Q8      := If_(ctx_Q8 = fail, fail, ctx_Q8.torsion),
        exp_Q8          := If_(ctx_Q8 = fail, fail, ctx_Q8.exponent),
        torsion_G       := setup_G.torsion,
        exp_G           := setup_G.exponent,
        setup_G         := setup_G,
        G               := G,
        sampled         := true,
        sample_size     := sample_size,
        total_lagrangians := count_so_far.n
    );
    if Length(ea_subs) > 0 then
        # Backward-compat aliases (same convention as
        # BuildRestrictionMatrices).
        data.res_E := ea_ress[1];
        data.ctx_E := ea_ctxs[1];
        data.torsion_E := ea_ctxs[1].torsion;
        data.exp_E := ea_ctxs[1].exponent;
        data.H_E := ea_subs[1];
    fi;

    # --- Step 5: greedy growth over the sampled K candidates.
    n_EA := Length(ea_subs);
    if verbose then
        Print("[_DETF_TrimmedFamily_m7] greedy growth over ", n_EA,
              " sampled candidates ...\n");
    fi;
    ea_chosen := [];
    greedy_log := [];
    curr_ker := _DETF_KernelOrderSNF(data, [], true, include_Q8);
    if verbose then
        Print("[_DETF_TrimmedFamily_m7]   initial ker (just {D_8, Q_8}) = ",
              curr_ker, "\n");
    fi;
    while curr_ker > 1 do
        best_j := fail;
        best_ker := curr_ker;
        for j in [1..n_EA] do
            if j in ea_chosen then continue; fi;
            k_try := _DETF_KernelOrderSNF(data,
                                          Concatenation(ea_chosen, [j]),
                                          true, include_Q8);
            if k_try < best_ker then
                best_j := j;
                best_ker := k_try;
            fi;
        od;
        if best_j = fail then
            # Greedy stuck: no single sampled-EA addition reduces |ker|.
            # The sample is insufficient. Caller should rerun with a
            # larger sample_size.
            if verbose then
                Print("[_DETF_TrimmedFamily_m7]   greedy stuck at ker = ",
                      curr_ker, " (sample insufficient; ",
                      "try larger sample_size).\n");
            fi;
            break;
        fi;
        Add(ea_chosen, best_j);
        Add(greedy_log, rec(ea := best_j, ker := best_ker));
        curr_ker := best_ker;
        if verbose then
            Print("[_DETF_TrimmedFamily_m7]   step ", Length(ea_chosen),
                  ": added candidate ", best_j, ", ker = ", best_ker,
                  "\n");
        fi;
    od;

    ea_sorted := SortedList(ea_chosen);

    # --- Step 6: drop-one verification.
    drop_kers := [];
    locally_tight := true;
    if curr_ker = 1 then
        if verbose then
            Print("[_DETF_TrimmedFamily_m7] drop-one verification ...\n");
        fi;
        for i in [1..Length(ea_chosen)] do
            sub_indices := Concatenation(ea_chosen{[1..i - 1]},
                                          ea_chosen{[i + 1..Length(ea_chosen)]});
            ker_drop := _DETF_KernelOrderSNF(data, sub_indices,
                                              true, include_Q8);
            Add(drop_kers, ker_drop);
            if ker_drop = 1 then
                locally_tight := false;
            fi;
        od;
    fi;

    t_end := Runtime();

    result := rec(
        m                        := m,
        source                   := "lhs",
        ea_indices_chosen        := ea_chosen,
        ea_indices_chosen_sorted := ea_sorted,
        include_D8               := true,
        include_Q8               := include_Q8,
        final_ker                := curr_ker,
        ea_count                 := Length(ea_chosen),
        family_size              := Length(ea_chosen) + 1
                                    + If_(include_Q8, 1, 0),
        greedy_log               := greedy_log,
        locally_tight            := locally_tight,
        drop_one_kers            := drop_kers,
        walltime_ms              := t_end - t0,
        data                     := data,
        sample_size              := sample_size,
        total_lagrangians        := count_so_far.n
    );
    return result;
end;;


# Main public entry point.
#
# `_DETF_TrimmedFamily(m, [opts])` returns a verified-minimal detecting
# family for `res: H^3(E_+(m); U(1)) -> ⊕ H^3(H; U(1))`. The full
# production family from `BuildRestrictionMatrices(m, "hap")` has slack
# at every m ≥ 2 (refuted to be tight at m=2 and m=3 by PR #310): we
# shrink it via greedy growth, then verify local tightness.
#
# Algorithm (PR #310 §6.2):
#
#   1. Start with {D_8, Q_8} included (always required for the cyclic
#      A(4) summand per Harada-Kono 1.1; D_8 alone is insufficient at
#      m ≥ 3 and Q_8 alone is insufficient at m=2).
#   2. Iteratively add the EA index `j` (among those in
#      `data.H_EA_list`) whose joint restriction with the current
#      family reduces the SNF-computed kernel order the most. Ties
#      broken by smallest index (deterministic).
#   3. Stop when |ker| = 1.
#   4. Verify local tightness: drop each EA in the resulting family
#      and check that |ker| > 1 (i.e. no smaller subset of the chosen
#      EAs works with {D_8, Q_8}).
#
# At m=2 this reproduces PR #310's witness `{EA_2, EA_3, EA_5}`
# (matching one of the two minimum size-3 EA witnesses); at m=3 it
# reproduces `{EA_4, EA_6, EA_7, EA_11, EA_16, EA_22}`. At m=5 the
# greedy over the 112-EA production family (axis-aligned + pair-swap
# Lagrangians) converges to 9 EAs (sorted: [33, 48, 54, 57, 70, 76,
# 88, 89, 109]) in ~19 min wall (cold), well below the issue #313
# conjecture of 12-22 EAs.
#
# Cost model (reference walls, measured on a 2026 laptop with a cold
# BuildRestrictionMatrices cache; warm-cache walls drop ~5-10x):
#
#   * m=2: 6 EAs * 3 greedy steps = ~18 SNFs, each on a tiny matrix.
#     ~120 ms cold (most of which is BuildRestrictionMatrices).
#   * m=3: 30 EAs * 6 greedy steps = ~180 SNFs. ~5 s cold.
#   * m=5: 112 EAs * 9 greedy steps = ~1000 SNFs on growing matrices
#     (up to ~280x270 at the last greedy step). ~19 min wall cold,
#     almost all of which is the BuildRestrictionMatrices(5, "hap")
#     HAP resolution build + 114 EquivariantChainMaps; the greedy +
#     SNF + drop-one verification adds <1 min on top.
#   * m=7: SUPPORTED via source="lhs" (issue #322). Default at m=7.
#     Uses LHSResolutionEPlus(7, 5) (PR #252; ~14 min wall, ~500 MB
#     heap) instead of ResolutionFiniteGroup(E_+(7), 4) (OOMs at
#     ~60 GB, #137). The 9 845 550 Lagrangians are too many to
#     enumerate eagerly, so the greedy iterates over a UNIFORM
#     RANDOM SAMPLE of size opts.sample_size (default 1000) drawn
#     once via reservoir sampling during the Witt streaming pass.
#     Expected wall ~2-6 h; the wall is dominated by the per-EA
#     restriction-matrix builds against R_E_lhs.
#
# Returns rec(
#   m                       : m
#   ea_indices_chosen       : list of indices into data.H_EA_list,
#                             in greedy-pick order (sorted via
#                             `result.ea_indices_chosen_sorted`)
#   ea_indices_chosen_sorted: above, sorted ascending (matches PR
#                             #310's witness convention)
#   include_D8              : true
#   include_Q8              : true iff Q_8 found by _DETF_FindQ8In
#   final_ker               : 1 if injective, else >1 (stuck)
#   ea_count                : Length(ea_indices_chosen)
#   family_size             : ea_count + 1 (D_8) + (1 if Q_8 else 0)
#   greedy_log              : list of recs (ea := j, ker := k) per step
#   locally_tight           : true iff every drop-one subfamily fails
#   drop_one_kers           : per-position |ker| after dropping that EA
#                             from the chosen list
#   walltime_ms             : ms wall
#   data                    : the BuildRestrictionMatrices rec used
# ).
_DETF_TrimmedFamily := function(arg)
    local m, opts, source, t0, t_end, data, n_EA, include_Q8,
          ea_chosen, greedy_log, curr_ker, best_j, best_ker, j, k_try,
          ea_sorted, drop_kers, i, sub_indices, ker_drop, locally_tight,
          result;

    if Length(arg) = 0 then
        Error("_DETF_TrimmedFamily(m, [opts]): missing m.");
    fi;
    m := arg[1];
    # If_ eagerly evaluates both branches, so arg[2] would error when
    # only one argument was passed. Use a plain if-fi here.
    if Length(arg) >= 2 then
        opts := arg[2];
    else
        opts := rec();
    fi;

    if not (IsInt(m) and m >= 1) then
        Error("_DETF_TrimmedFamily: m must be a positive integer; got ", m);
    fi;

    if IsBound(opts.source) then
        source := opts.source;
    else
        # Default source selection by m:
        #   m <= 5: "hap" (preserves PR #320 anchors).
        #   m = 7:  "lhs" (#322; HAP path OOMs at m=7).
        if m = 7 then
            source := "lhs";
        else
            source := "hap";
        fi;
    fi;
    if not (source in ["hap", "lhs", "quillen"]) then
        Error("_DETF_TrimmedFamily: opts.source must be \"hap\", \"lhs\", ",
              "or \"quillen\"; got ", source);
    fi;
    if source = "hap" and m > 5 then
        Error("_DETF_TrimmedFamily: source=\"hap\" is not supported for ",
              "m = ", m, " (BuildRestrictionMatrices errors at m > 5). ",
              "Use source=\"lhs\" (issue #322; LHSResolutionEPlus(", m,
              ", 5) per PR #252). At m = ", m, ".");
    fi;
    if source = "quillen" then
        Error("_DETF_TrimmedFamily: source=\"quillen\" is gated on Q-int ",
              "A2/A3 (issue #136); not yet implemented. At m = ", m, ".");
    fi;

    # m=7 + LHS: dispatch to streaming-greedy path. Issue #322. The
    # eager BuildRestrictionMatrices(7, "lhs") would materialise 9.8M
    # max-EA restriction matrices (~17 GB), so m=7 needs a custom
    # streaming + sampling driver. m ∈ {2, 3, 5} with source="lhs" go
    # through the eager path (cross-validation against the HAP path).
    if source = "lhs" and m = 7 then
        return _DETF_TrimmedFamily_m7_streaming(opts);
    fi;

    t0 := Runtime();
    data := BuildRestrictionMatrices(m, source);
    n_EA := Length(data.H_EA_list);
    include_Q8 := (data.res_Q8 <> fail);

    # ---- Greedy growth ----
    ea_chosen := [];
    greedy_log := [];
    curr_ker := _DETF_KernelOrderSNF(data, [], true, include_Q8);
    while curr_ker > 1 do
        best_j := fail;
        best_ker := curr_ker;
        for j in [1..n_EA] do
            if j in ea_chosen then continue; fi;
            k_try := _DETF_KernelOrderSNF(data,
                                          Concatenation(ea_chosen, [j]),
                                          true, include_Q8);
            if k_try < best_ker then
                best_j := j;
                best_ker := k_try;
            fi;
        od;
        if best_j = fail then
            # Greedy stuck: no single-EA addition reduces |ker|.
            # Return the partial family with status flagged.
            break;
        fi;
        Add(ea_chosen, best_j);
        Add(greedy_log, rec(ea := best_j, ker := best_ker));
        curr_ker := best_ker;
    od;

    ea_sorted := SortedList(ea_chosen);

    # ---- Local tightness: drop-one test ----
    # For each chosen EA, remove it and recompute |ker|. If ANY drop
    # yields |ker| = 1, the chosen family is not locally tight (the
    # dropped index was redundant).
    drop_kers := [];
    locally_tight := true;
    if curr_ker = 1 then
        for i in [1..Length(ea_chosen)] do
            sub_indices := Concatenation(ea_chosen{[1..i - 1]},
                                          ea_chosen{[i + 1..Length(ea_chosen)]});
            ker_drop := _DETF_KernelOrderSNF(data, sub_indices,
                                              true, include_Q8);
            Add(drop_kers, ker_drop);
            if ker_drop = 1 then
                locally_tight := false;
            fi;
        od;
    fi;

    t_end := Runtime();

    result := rec(
        m                        := m,
        source                   := source,
        ea_indices_chosen        := ea_chosen,
        ea_indices_chosen_sorted := ea_sorted,
        include_D8               := true,
        include_Q8               := include_Q8,
        final_ker                := curr_ker,
        ea_count                 := Length(ea_chosen),
        family_size              := Length(ea_chosen) + 1
                                    + If_(include_Q8, 1, 0),
        greedy_log               := greedy_log,
        locally_tight            := locally_tight,
        drop_one_kers            := drop_kers,
        walltime_ms              := t_end - t0,
        data                     := data
    );
    return result;
end;;


Print("Loaded detecting_family_restriction.g (D-VAN-2: BuildRestrictionMatrices, _DETF_TrimmedFamily).\n");
