# hap_pontryagin_square.g — Pontryagin square on HAP's compact resolution.
#
# Issue #171 (Q-int B3-2). Builds on B3-1 (#170, merged in PR #174).
# Spec: docs/superpowers/specs/2026-05-16-path3-hap-resolution-redesign.md
#
# # Formula (Brumfiel-Morgan 1973 Lemma 3.5(b)).
#
#     P(α) = α̃ ∪ α̃ + δα̃ ∪₁ α̃   mod 4
#
# where α is an F_2 n-cocycle on R, α̃ its integer set-theoretic lift
# (values in {0, 1} ⊂ Z), and ∪, ∪₁ are the cup and Steenrod cup-1
# products.
#
# # 2-divisibility trick (avoids integer cup-1).
#
# Since α is an F_2 cocycle, δα̃ has all entries divisible by 2. Write
# δα̃ = 2β with β an integer (n+1)-cochain. Then:
#
#     δα̃ ∪₁ α̃ = 2·(β ∪₁ α̃)
#
# Mod 4, this equals 2·((β mod 2) ∪₁ (α̃ mod 2)) = 2·(β_F2 ∪₁ α_F2),
# where β_F2 = β mod 2 is just an F_2 cochain. So we never need an
# integer cup-1 — F_2 cup-1 (which HAP_PHI computes) suffices.
#
# # Resolution choice.
#
# HAP_PHI(G, N) builds its own resolution `RG := ResolutionPrimePowerGroup(G, N)`
# internally. Cochains for cup / cup-1 must be on this RG, not on
# user-supplied `ResolutionFiniteGroup` resolutions (their dimensions
# differ: D_8 gives [1,2,3,5,8,12] vs [1,2,3,4,5,6] resp.). Therefore
# HAP_PontryaginSquare takes the *group* G as input and exposes the
# internal RG to callers (B3-3 integration will use the same RG).

if not IsBoundGlobal("HAP_SteenrodCup1_Int") then
    Read("hap_steenrod_cup1.g");
fi;

# Local ternary helper.
If_loc_zero_one := function(c, a, b)
    if c then return a; else return b; fi;
end;;

# ------------------------------------------------------------------
# HAP_PontryaginGetResolution(G, deg_max)
#
# Returns the resolution RG = ResolutionPrimePowerGroup(G, deg_max + 1)
# that HAP_PHI uses internally. Callers should anchor all subsequent
# cochain / cocycle work on this RG so indexing stays consistent.
# ------------------------------------------------------------------

HAP_PontryaginGetResolution := function(G, deg_max)
    local phi_data;
    phi_data := _HAP_GetPhi(G, deg_max);
    return phi_data.RG;
end;;

# ------------------------------------------------------------------
# HAP_ChainCupProduct_Int(R, alpha_vec, p, beta_vec, q)
#
# Integer chain-level cup product. Mirrors HAP's IntegralCupProduct
# (lib/Rings/cupProduct.gi) but skips the cocycle-class round-trip so
# it works on non-cocycle integer cochains (α̃ a {0,1}-lift of an F_2
# cocycle is NOT a Z-cocycle in general).
#
# Output: integer (p+q)-cochain on R, length R!.dimension(p+q).
# ------------------------------------------------------------------

HAP_ChainCupProduct_Int := function(R, alpha_vec, p, beta_vec, q)
    local uChainMap, IDEN, EltsG, i, w, x, sw, uvCochain;
    EltsG := R!.elts;
    IDEN := Position(EltsG, Identity(R!.group));
    if IDEN = fail then
        Add(EltsG, Identity(R!.group));
        IDEN := Length(EltsG);
    fi;
    uChainMap := CR_ChainMapFromCocycle(R, alpha_vec, p, q);
    uvCochain := ListWithIdenticalEntries(R!.dimension(p + q), 0);
    for i in [1..R!.dimension(p + q)] do
        w := uChainMap([[i, IDEN]]);
        sw := 0;
        for x in w do
            sw := sw + SignInt(x[1]) * beta_vec[AbsoluteValue(x[1])];
        od;
        uvCochain[i] := sw;
    od;
    return uvCochain;
end;;

# ------------------------------------------------------------------
# HAP_PontryaginSquare(G, alpha_F2_vec, n)
#
# Pontryagin square Z/4-valued 2n-cocycle, given an F_2 n-cocycle
# alpha_F2_vec on the internal HAP_PHI resolution RG of G.
#
# Returns a list of length RG!.dimension(2n) with entries in {0,1,2,3}.
# Companion `HAP_PontryaginGetResolution(G, 2n+1)` returns RG so the
# caller can size the input cochain correctly.
# ------------------------------------------------------------------

HAP_PontryaginSquare := function(G, alpha_F2_vec, n)
    local phi_data, R, alpha_int, d_alpha_int, beta_int, beta_F2,
          cup_aa, cup1_b_a_F2, cup1_b_a_int, result, i;

    if not (IsInt(n) and n >= 1) then
        Error("HAP_PontryaginSquare: n must be a positive integer, got ", n);
    fi;

    # Internal resolution = RG from HAP_PHI(G, 2n+1).
    phi_data := _HAP_GetPhi(G, 2 * n + 1);
    R := phi_data.RG;

    if Length(alpha_F2_vec) <> R!.dimension(n) then
        Error("HAP_PontryaginSquare: alpha_F2_vec has length ",
              Length(alpha_F2_vec), " but R!.dimension(", n, ") = ",
              R!.dimension(n), " — use HAP_PontryaginGetResolution to ",
              "size the input.");
    fi;

    # Integer lift α̃: F_2 {0,1} → Z {0,1}.
    alpha_int := List(alpha_F2_vec,
                      x -> If_loc_zero_one(IsZero(x), 0, 1));

    # δα̃: integer (n+1)-cochain. Must be 2-divisible (α is an F_2 cocycle).
    d_alpha_int := HAP_BarCoboundary(R, alpha_int, n);
    if not ForAll(d_alpha_int, x -> x mod 2 = 0) then
        Error("HAP_PontryaginSquare: input alpha is not an F_2 ",
              "cocycle on the internal RG resolution.");
    fi;
    beta_int := List(d_alpha_int, x -> x / 2);
    beta_F2  := List(beta_int, x -> (x mod 2) * Z(2)^0);

    # α̃ ∪ α̃: integer 2n-cochain (chain-level cup; no cocycle required).
    cup_aa := HAP_ChainCupProduct_Int(R, alpha_int, n, alpha_int, n);

    # β_F2 ∪₁ α_F2: F_2 2n-cochain. Lifted to {0,1} integers, then ×2.
    cup1_b_a_F2 := HAP_SteenrodCup1_F2(R, beta_F2, n + 1, alpha_F2_vec, n);
    cup1_b_a_int := List(cup1_b_a_F2,
                         x -> If_loc_zero_one(IsZero(x), 0, 1));

    # P(α) = (α̃ ∪ α̃) + 2·(β_F2 ∪₁ α_F2) mod 4.
    result := ListWithIdenticalEntries(R!.dimension(2 * n), 0);
    for i in [1..R!.dimension(2 * n)] do
        result[i] := (cup_aa[i] + 2 * cup1_b_a_int[i]) mod 4;
    od;
    return result;
end;;

# ------------------------------------------------------------------
# HAP_VerifyZ4CocycleMod4(R, f, n)
#
# Verify a Z/4 2n-cochain f on R satisfies the bar (2n+1)-cocycle
# equation mod 4. Returns rec(violations, total).
# ------------------------------------------------------------------

HAP_VerifyZ4CocycleMod4 := function(R, f, n)
    local d_f, violations, total, x;
    d_f := HAP_BarCoboundary(R, f, 2 * n);
    violations := 0;
    total := Length(d_f);
    for x in d_f do
        if x mod 4 <> 0 then violations := violations + 1; fi;
    od;
    return rec(violations := violations, total := total);
end;;

Print("Loaded hap_pontryagin_square.g ",
      "(HAP_PontryaginSquare, HAP_PontryaginGetResolution, ",
      "HAP_ChainCupProduct_Int, HAP_VerifyZ4CocycleMod4).\n");
