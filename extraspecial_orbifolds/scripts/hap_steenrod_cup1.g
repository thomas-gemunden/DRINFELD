# hap_steenrod_cup1.g — Steenrod cup-1 product on HAP's compact resolution.
#
# Issue #170 (Q-int B3-1). Spec:
# docs/superpowers/specs/2026-05-16-path3-hap-resolution-redesign.md
#
# # Status: SCAFFOLD — not yet a working implementation.
#
# This file lays out the public API, the algorithmic plan, and the HAP
# building blocks. The actual chain-level implementation is left as the
# remaining body of #170.
#
# # Why on HAP's resolution.
#
# The bar-resolution Steenrod ∪₁ (#160, file `steenrod_cup1.g`) works
# byte-for-byte at m=1 (D_8: 0 violations on 32,768 G^4 tuples in the
# (3, 2) Pontryagin-shape identity). It does NOT scale to m ≥ 3 because
# the bar resolution has |G^n| cells at degree n. HAP's
# `ResolutionFiniteGroup(G, n)` builds a free ZG-resolution with cells
# of count `R!.dimension(d)` ≈ `O(|G| × poly(d))` — orders of magnitude
# smaller, with the same H^*. This file's job is to reimplement
# `SteenrodCup1` on HAP's chain modules.
#
# # Mathematical setup.
#
# Let R be a HAP free ZG-resolution of Z. A cochain in degree d is a
# function on the d-th module's basis, encoded as a list of length
# `R!.dimension(d)`. The bar coboundary maps to HAP's resolution
# coboundary, induced by `R!.boundary(d, k)`.
#
# For the cup product on a HAP resolution, HAP exposes
# `IntegralCupProduct(R, vec1, n1, vec2, n2)` which returns the cup
# product cocycle vector. Under the hood this uses a diagonal
# approximation Δ : R → R ⊗ R, chosen consistently with the chain map
# `HAP_PHI(G, N)` from `lib/CohomologyOperations/mycupi.gi`.
#
# For the cup-i product (i ≥ 1), the construction is the next term in
# the chain homotopy comparing Δ with its twist τΔ. Specifically:
#
#   d(h_1) = Δ - τΔ
#
# where h_1: R_n → (R ⊗ R)_{n+1} is the level-1 cup-1 homotopy. The
# cup-1 product of cochains α (degree p) and β (degree q) is the
# composition (α ⊗ β) ∘ h_1, giving a cochain of degree p+q-1.
#
# HAP's `HAP_PHI(G, N)` provides exactly this homotopy structure
# (parameterised on C_2 × G to encode the Z/2 action that swaps tensor
# factors). The level-i slices of `HAP_PHI` are the cup-i products.
# Specifically, `phi(n, (s, g), k)` with s ∈ C_2 evaluated at the
# generator of C_2 gives the relevant chain homotopy for cup-1.
#
# # Implementation plan for the full body of this issue.
#
# 1. Build the diagonal Δ at the chain level using `HAP_PHI(G, n+1)`
#    where n is the max degree we'll ever need (probably 5 for our
#    use case).
# 2. Extract the level-1 homotopy h_1 from HAP_PHI by evaluating phi
#    on the generator of C_2 (= the "twist" element of C_2).
# 3. For α a p-cochain, β a q-cochain on R, compute
#    `(α ⊗ β) ∘ h_1`. Output is a (p+q-1)-cochain on R.
# 4. Acceptance test: cup-1 coboundary identity on D_8 mirrors #160's
#    test. Compare against bar-resolution `SteenrodCup1` at the level
#    of evaluations on chain elements identified via the bar→HAP
#    chain map (`EquivariantChainMap(BarResolution(G), HAP_R)` if
#    available — otherwise via element-by-element correspondence).
#
# # HAP API surface used.
#
# - `R!.dimension(d)` — number of free generators in degree d.
# - `R!.boundary(d, k)` — boundary of the k-th generator (encoded as
#   a list of [j, g] pairs: j-th generator of degree d-1, with g ∈ G
#   coefficient).
# - `R!.elts` — list of elements of G (used to look up coefficient
#   group elements by index).
# - `IntegralCupProduct(R, vec1, n1, vec2, n2)` — cup product (the
#   level-0 piece of the cup-i tower).
# - `HAP_PHI(G, N)` — chain map C_2 × G → G × G that encodes the
#   diagonal approximation and its higher-level homotopies. Returns
#   [phi, RC2G, RGG] where phi(n, a, i) gives the image of the i-th
#   generator of RC2G in degree n.
# - `ResolutionFiniteDirectProduct(R, R)` — used internally to build
#   R ⊗ R.

if not IsPackageMarkedForLoading("hap", "") then
    LoadPackage("hap");
fi;

# ------------------------------------------------------------------
# Public API (scaffolded).
# ------------------------------------------------------------------

# HAP_SteenrodCup1(R, alpha_vec, p, beta_vec, q)
#
# R         : a HAP free ZG-resolution (e.g. ResolutionFiniteGroup(G, 5)).
# alpha_vec : cocycle vector of degree p over R (length R!.dimension(p)).
# beta_vec  : cocycle vector of degree q over R.
# Returns   : cocycle vector of degree p+q-1 over R representing
#             α ∪₁ β.
#
# Over F_2 (when alpha_vec, beta_vec are F_2-valued), the signs in
# the cup-i formula drop. Over Z (used inside Pontryagin square at
# #171), signs matter.
#
# IMPLEMENTATION STATUS: first attempt — symmetric F_2 case via
# HAP_PHI. The HAP `cupgen` in lib/CohomologyOperations/mycupi.gi gives
# us the per-coordinate cup-i product for two F_2 classes of the SAME
# degree. We replicate that pattern and extend to integer-valued cup-1.
#
# Limitations to address in follow-up work:
#   - Symmetric only (p = q). For Pontryagin square (P(α) = α̃ ∪ α̃ +
#     δα̃ ∪₁ α̃) we need ∪₁ on (degree-3, degree-2) cochains — i.e.
#     ASYMMETRIC. Extension requires a different RC2G encoding.
#   - F_2-coefficient. Integer cup-1 needs signed coefficient sums from
#     HAP_PHI's output, not the mod-2 count.
#
# Caching: HAP_PHI is expensive (~minutes for E_+(3)). Cache by group
# identity to avoid rebuilding across multiple cochain-level calls.

_HAP_PHI_cache := [];;

_HAP_GetPhi := function(G, N)
    local entry, phi_data;
    for entry in _HAP_PHI_cache do
        if IsIdenticalObj(entry.G, G) and entry.N >= N then return entry; fi;
    od;
    phi_data := HAP_PHI(G, N);
    # HAP_PHI returns [phi, RC2G, RGG, RG] (last from arg[3] dispatch).
    # Some HAP versions return [phi, RC2G, RGG] only.
    entry := rec(
        G    := G,
        N    := N,
        phi  := phi_data[1],
        RC2G := phi_data[2],
        RGG  := phi_data[3]
    );
    if IsBound(phi_data[4]) then entry.RG := phi_data[4]; fi;
    Add(_HAP_PHI_cache, entry);
    return entry;
end;;

# HAP_SteenrodCup1Symmetric(R, alpha_vec, beta_vec, n)
#
# Symmetric F_2 cup-1: α ∪₁ β for α, β both in H^n(R; F_2). Output is
# a (2n-1)-cocycle on R. Built from HAP_PHI on R!.group.
#
# Returns a length-`R!.dimension(2n-1)` vector over F_2.
HAP_SteenrodCup1Symmetric := function(R, alpha_vec, beta_vec, n)
    local G, phi_data, phi, RC2G, RGG, one, result, m, v, j, k, a, x, w,
          alpha_pos, beta_pos;
    G := R!.group;
    phi_data := _HAP_GetPhi(G, 2 * n);
    phi  := phi_data.phi;
    RC2G := phi_data.RC2G;
    RGG  := phi_data.RGG;
    one  := Identity(RC2G!.group);

    result := ListWithIdenticalEntries(R!.dimension(2 * n - 1), 0 * Z(2));
    # Determine non-zero coordinates of α, β.
    alpha_pos := Filtered([1..Length(alpha_vec)], i -> not IsZero(alpha_vec[i]));
    beta_pos  := Filtered([1..Length(beta_vec)],  i -> not IsZero(beta_vec[i]));

    for m in [1..R!.dimension(2 * n - 1)] do
        # cupgen-style: encode (1, 2n-1, 1, m) — meaning C_2 factor at
        # degree 1 (for cup-1), G factor at degree 2n-1, generator 1 of
        # C_2 (the order-2 generator), and m-th generator of G in degree 2n-1.
        v := RC2G!.Vector2Int(1, 2 * n - 1, 1, m);
        v := phi(2 * n, one, v);
        a := 0 * Z(2);
        # Sum coefficients of v matching (n, n-1, j, k) for non-zero (j, k).
        # Wait — for cup-1 at symmetric n, the encoding of the output
        # has the C_2 factor at "level 1" and the two G generators of
        # degrees n and n-1. Actually for OUR cup-1 with output degree
        # 2n-1, the tensor factors are (degree p in α, degree q in β)
        # = (n, n) with shift of 1 from the homotopy — making the
        # right tensor have degree n-1.
        # NOTE: this is the formula's BEST guess; verify in tests.
        # RGG-encode the target tensor position: both factors at degree n.
        # cup-i of two degree-n cochains has output degree 2n-i; the
        # RC2G→RGG chain map phi already shifts the C_2 contribution out.
        for j in alpha_pos do
            for k in beta_pos do
                w := RGG!.Vector2Int(n, n, j, k);
                for x in v do
                    if AbsInt(x[1]) = w then
                        a := a + alpha_vec[j] * beta_vec[k];
                    fi;
                od;
            od;
        od;
        result[m] := a;
    od;
    return result;
end;;

# Public entry point. Currently only the symmetric F_2 case is wired.
HAP_SteenrodCup1 := function(R, alpha_vec, p, beta_vec, q)
    if p <> q then
        Error("HAP_SteenrodCup1: asymmetric (p, q) = (", p, ", ", q,
              ") not yet implemented. Symmetric case p=q only. ",
              "Asymmetric is the Pontryagin-square-shape use case ",
              "and is the next step in #170.");
    fi;
    return HAP_SteenrodCup1Symmetric(R, alpha_vec, beta_vec, p);
end;;

# HAP_BarCup(R, alpha_vec, p, beta_vec, q)
#
# Ordinary cup product on HAP's resolution. Provided as a thin wrapper
# around HAP's `IntegralCupProduct` for API uniformity inside the B3
# pipeline.
HAP_BarCup := function(R, alpha_vec, p, beta_vec, q)
    return IntegralCupProduct(R, alpha_vec, p, beta_vec, q);
end;;

# HAP_BarCoboundary(R, alpha_vec, p)
#
# Returns the (p+1)-cochain δα on R given a p-cochain α. Computed from
# `R!.boundary(p+1, k)`.
HAP_BarCoboundary := function(R, alpha_vec, p)
    local d, k, j, entry, total, b;
    d := ListWithIdenticalEntries(R!.dimension(p + 1), 0);
    for k in [1..R!.dimension(p + 1)] do
        b := R!.boundary(p + 1, k);
        total := 0;
        for entry in b do
            # entry = [j, g_index] where j is signed generator index.
            j := AbsoluteValue(entry[1]);
            total := total + SignInt(entry[1]) * alpha_vec[j];
        od;
        d[k] := total;
    od;
    return d;
end;;

Print("Loaded hap_steenrod_cup1.g (Q-int B3-1 scaffold; ",
      "HAP_SteenrodCup1 not yet implemented).\n");
