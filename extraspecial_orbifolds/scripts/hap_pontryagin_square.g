# hap_pontryagin_square.g — Pontryagin square on HAP's compact resolution.
#
# Issue #171 (Q-int B3-2). Builds on B3-1 (#170, merged in PR #174) and
# the diagonal/cup-1 chain-level construction from `hap_diagonal.g` and
# `hap_cup1_homotopy.g` (issue #171 follow-up spec
# 2026-05-16-pontryagin-diagonal-chain-map-spec.md).
#
# # Formula (Brumfiel-Morgan 1973 Lemma 3.5(b)).
#
#     P(α) = α̃ ∪ α̃ + δα̃ ∪₁ α̃   mod 4
#
# where α is an F_2 n-cocycle on R, α̃ its integer set-theoretic lift
# (values in {0, 1} ⊂ Z), and ∪, ∪₁ are the cup and Steenrod cup-1
# products. Both must be Z-bilinear chain operations satisfying the
# Hirsch-Steenrod identities (Leibniz for ∪ and the cup-1 coboundary
# identity) over Z, NOT just on cocycle classes.
#
# # Implementation note: chain-level integer cup/cup-1.
#
# Prior B3-2 scaffolds used HAP's `CR_ChainMapFromCocycle` for the cup
# product. That function builds a chain map under the assumption that
# the input is a Z-cocycle — bilinear, but not Leibniz on non-cocycles.
# For the integer lift α̃ of an F_2 cocycle, α̃ is NOT a Z-cocycle
# (δα̃ ∈ 2Z, not 0), so the prior cup product violated Leibniz and
# P(α) was not a Z/4 cocycle.
#
# The fix: build a true chain-level diagonal Δ: R → R⊗R using
# `HAP_BuildDiagonal` (from `hap_diagonal.g`) and the level-1 cup-1
# homotopy h_1: R → (R⊗R)[+1] via `HAP_BuildCup1Homotopy` (from
# `hap_cup1_homotopy.g`). These are constructed inductively from
# `R!.boundary` + `R!.homotopy` and satisfy the chain identities over Z.
#
# # Resolution choice.
#
# Must use `ResolutionFiniteGroup` (a free ZG-resolution of Z, with
# characteristic 0). `ResolutionPrimePowerGroup` has characteristic 2,
# so ∂² is non-zero in 2Z over Z and the BM formula's chain-level
# identity `d(P(α)) ≡ 0 mod 4` cannot hold — there's an irreducible
# error term from δ²α̃ ∈ 2Z. The Δ and h_1 inductive constructions also
# rely on ∂² = 0 over Z to produce a well-defined integer chain map.
#
# `HAP_PontryaginGetResolution(G, deg_max)` returns
# `ResolutionFiniteGroup(G, deg_max + 1)`. The internal R⊗R is the
# 7-tuple representation defined in `hap_diagonal.g`.

if not IsBoundGlobal("HAP_SteenrodCup1_Int") then
    Read("hap_steenrod_cup1.g");
fi;
if not IsBoundGlobal("HAP_BuildDiagonal") then
    Read("hap_diagonal.g");
fi;
if not IsBoundGlobal("HAP_BuildCup1Homotopy") then
    Read("hap_cup1_homotopy.g");
fi;

# Local ternary helper.
If_loc_zero_one := function(c, a, b)
    if c then return a; else return b; fi;
end;;

# ------------------------------------------------------------------
# Resolution caching.
#
# We need both R = ResolutionFiniteGroup and its Δ, h_1 caches. To
# avoid rebuilding across calls, we keep a per-group cache.
# ------------------------------------------------------------------

_HAP_Pontryagin_cache := [];;

# Cache lookup keyed by group identity. Note: HAP's ResolutionFiniteGroup
# creates a NEW group object from the input's generators (so
# `IsIdenticalObj(R!.group, original_G)` is false). We accept both the
# input G and the internal R!.group as keys.
_HAP_Pontryagin_GetCache := function(G, deg_max)
    local entry, R, Diag_data, Cup1_data, N;
    for entry in _HAP_Pontryagin_cache do
        if (IsIdenticalObj(entry.G, G)
            or IsIdenticalObj(entry.R!.group, G))
           and entry.deg_max >= deg_max then
            return entry;
        fi;
    od;
    N := deg_max + 1;  # R built to degree N = deg_max + 1
    R := ResolutionFiniteGroup(G, N);
    Diag_data := HAP_BuildDiagonal(R, deg_max);
    Cup1_data := HAP_BuildCup1Homotopy(R, Diag_data, deg_max);
    entry := rec(G        := G,
                 deg_max  := deg_max,
                 R        := R,
                 DiagMap  := Diag_data,
                 Cup1Hty  := Cup1_data);
    Add(_HAP_Pontryagin_cache, entry);
    return entry;
end;;

# _HAP_Pontryagin_GetCacheForR(R, deg_max)
#
# Like _HAP_Pontryagin_GetCache but takes a resolution R (not a group)
# and returns a cache entry whose `R` field is identical to the input
# R. If no such cache exists, builds Δ and h_1 ON THE SUPPLIED R (does
# not call ResolutionFiniteGroup again).
#
# Used by `HAP_ChainCupProduct_Int` and `HAP_SteenrodCup1_Int` which
# accept user-supplied R rather than always going through
# `HAP_PontryaginGetResolution`.
_HAP_Pontryagin_GetCacheForR := function(R, deg_max)
    local entry, Diag_data, Cup1_data;
    for entry in _HAP_Pontryagin_cache do
        if IsIdenticalObj(entry.R, R) and entry.deg_max >= deg_max then
            return entry;
        fi;
    od;
    Diag_data := HAP_BuildDiagonal(R, deg_max);
    Cup1_data := HAP_BuildCup1Homotopy(R, Diag_data, deg_max);
    entry := rec(G        := R!.group,
                 deg_max  := deg_max,
                 R        := R,
                 DiagMap  := Diag_data,
                 Cup1Hty  := Cup1_data);
    Add(_HAP_Pontryagin_cache, entry);
    return entry;
end;;

# ------------------------------------------------------------------
# HAP_PontryaginGetResolution(G, deg_max)
#
# Returns the resolution R = ResolutionFiniteGroup(G, deg_max + 1)
# used by HAP_PontryaginSquare. Callers should anchor all subsequent
# cochain / cocycle work on this R so indexing stays consistent.
#
# Note: this CHANGED in the diagonal-chain-map fix (#171 follow-up).
# Previous versions returned the HAP_PHI-internal
# `ResolutionPrimePowerGroup`. The new version returns
# `ResolutionFiniteGroup` because integer chain-level cup / cup-1
# require a Z-resolution (∂² = 0 over Z).
# ------------------------------------------------------------------

HAP_PontryaginGetResolution := function(G, deg_max)
    return _HAP_Pontryagin_GetCache(G, deg_max).R;
end;;

# ------------------------------------------------------------------
# HAP_ChainCupProduct_Int(R, alpha_vec, p, beta_vec, q)
#
# Integer chain-level cup product computed via the diagonal Δ from
# `HAP_BuildDiagonal`. Leibniz-correct on ANY integer cochain (not just
# cocycles), so usable inside the Pontryagin square's BM formula.
#
# Output: integer (p+q)-cochain on R, length R!.dimension(p+q).
#
# Note: requires R to be the cached ResolutionFiniteGroup from
# `HAP_PontryaginGetResolution`. We look up the Δ cache by R!.group.
# ------------------------------------------------------------------

HAP_ChainCupProduct_Int := function(R, alpha_vec, p, beta_vec, q)
    local cache, dim_pq, result, i, val, r;
    cache := _HAP_Pontryagin_GetCacheForR(R, p + q);
    dim_pq := R!.dimension(p + q);
    result := ListWithIdenticalEntries(dim_pq, 0);
    for i in [1..dim_pq] do
        val := 0;
        for r in cache.DiagMap[p+q+1][i] do
            if r.p = p and r.q = q then
                val := val + r.sgn * alpha_vec[r.jp] * beta_vec[r.jq];
            fi;
        od;
        result[i] := val;
    od;
    return result;
end;;

# ------------------------------------------------------------------
# HAP_PontryaginSquare(G, alpha_F2_vec, n)
#
# Pontryagin square Z/4-valued 2n-cocycle, given an F_2 n-cocycle
# alpha_F2_vec on the cached resolution R for G.
#
# Returns a list of length R!.dimension(2n) with entries in {0,1,2,3}.
# Companion `HAP_PontryaginGetResolution(G, 2n+1)` returns R so the
# caller can size the input cochain correctly.
# ------------------------------------------------------------------

HAP_PontryaginSquare := function(G, alpha_F2_vec, n)
    local cache, R, alpha_int, d_alpha_int, cup_aa, cup1_da_a, result, i;

    if not (IsInt(n) and n >= 1) then
        Error("HAP_PontryaginSquare: n must be a positive integer, got ", n);
    fi;

    cache := _HAP_Pontryagin_GetCache(G, 2 * n + 1);
    R := cache.R;

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
              "cocycle on the cached resolution.");
    fi;

    # α̃ ∪ α̃: integer 2n-cochain via chain-level Δ.
    cup_aa := HAP_ChainCupProduct_Int(R, alpha_int, n, alpha_int, n);

    # δα̃ ∪₁ α̃: integer 2n-cochain via chain-level h_1.
    cup1_da_a := HAP_SteenrodCup1_Int(R, d_alpha_int, n + 1, alpha_int, n);

    # P(α) = (α̃ ∪ α̃) + (δα̃ ∪₁ α̃) mod 4.
    result := ListWithIdenticalEntries(R!.dimension(2 * n), 0);
    for i in [1..R!.dimension(2 * n)] do
        result[i] := (cup_aa[i] + cup1_da_a[i]) mod 4;
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
