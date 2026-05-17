# hap_h3_z4_generator.g — extract ω_4, a Z/4 cocycle representative of
# the order-4 generator of H^3(G; Z/4) on HAP's compact resolution R.
#
# Issue #164 (Q-int B2-4 m=3 anchor). Helper for `test_b2_4_m3_anchor.g`
# but factored out so other m anchors (#165, #166) can reuse.
#
# # What it does.
#
# Given a finite 2-group G with `H^3(G; Z) = ⊕_i Z/d_i` whose exponent
# is `m` (so `H^3(G; Z/m) = ⊕_i Z/d_i` too, by UCT), this builds:
#
#   - R     := HAP_PontryaginGetResolution(G, deg_max) (cached).
#   - K     := TensorWithIntegers(R).
#   - UCT   := UniversalCoefficientsTheorem(K, 3) (from src/modular_data.g).
#   - omega : a Z/m-valued 3-cocycle vector on R (length R!.dimension(3))
#             representing the i-th generator of H^3(G; Z/m), for the
#             user-selected index i. The default i = Length(UCT.torsion)
#             picks the LAST generator, which for E_+(m) is the Z/4 (m>=3)
#             or Z/8 (m=2) summand.
#
# # The Z/4 generator at E_+(3).
#
# At G = E_+(3), `UCT.torsion = [2, 2, ..., 2, 4]` (34 copies of 2 + one 4),
# `UCT.exponent = 4`. So `UCT.cocyclebasis[35]` is a length-R!.dimension(3)
# integer vector with entries in {0, 1, 2, 3} representing the Z/4
# generator as a Z/4 3-cocycle on R.
#
# Cross-check: at this generator, `m / torsion[35] = 4 / 4 = 1`, so the
# hom-basis encoding `homlist[35]` sends the corresponding cycle class
# to value 1 in Z/4 (i.e., the Z/4 unit). For the other 34 generators
# (torsion 2), `m / torsion[i] = 4 / 2 = 2`, so those cocycles take
# values in {0, 2} ⊂ Z/4 only.
#
# # Verification.
#
# After construction we sanity-check `HAP_BarCoboundary(R, omega, 3)` is
# 0 mod m (i.e., omega is a Z/m cocycle on R). This is automatic from
# UCT's construction; we re-check defensively.
#
# # Why not a freshly-built R from `ResolutionFiniteGroup(G, 4)`?
#
# The `transgression_kernel.g::SetupCohomology3` path uses
# `ResolutionFiniteGroup(G, 4)`, but the integration pipeline
# (`HAP_PontryaginGetResolution`) uses `ResolutionFiniteGroup(G, 6)`.
# Two SEPARATE `ResolutionFiniteGroup` calls produce DIFFERENT R objects,
# and the cocyclebasis vectors are indexed against R!.dimension(d)
# generators in a specific (presentation-dependent) order. To compare
# `f` (from integration on R_integration) and `omega` (from UCT on
# R_setup), we MUST use the SAME R object — hence this helper builds
# UCT on the cached HAP R.

if not IsBoundGlobal("HAP_PontryaginGetResolution") then
    Read("hap_pontryagin_square.g");
fi;
if not IsBoundGlobal("UniversalCoefficientsTheorem") then
    Read("../../src/modular_data.g");
fi;
if not IsBoundGlobal("HAP_BarCoboundary") then
    Read("hap_steenrod_cup1.g");
fi;

# Cache to avoid rebuilding K + UCT on the same R.
_HAP_H3Z4Gen_cache := [];;

# HAP_Z4Generator(G[, idx])
#
# Returns a record:
#   .R           : HAP resolution (= HAP_PontryaginGetResolution(G, 5))
#   .K           : TensorWithIntegers(R)
#   .UCT         : UniversalCoefficientsTheorem(K, 3)
#   .exponent    : UCT.exponent (= lcm of torsion entries)
#   .torsion     : UCT.torsion
#   .idx         : selected generator index (default last)
#   .order       : torsion[idx]
#   .vec         : the cocycle vector (length R!.dimension(3))
#   .is_cocycle  : true iff HAP_BarCoboundary(R, vec, 3) ≡ 0 mod exponent
#
# The default `idx = Length(UCT.torsion)` selects the LAST generator.
# For 2-groups whose torsion is sorted (which it should be by
# ComplementIntMatWithTransforms' Smith-normal-form convention), this
# is the highest-order (cyclic) summand. At E_+(3) that's Z/4 ⊂ Z/4.
#
# Optional `idx` lets callers pick a different generator (e.g., one of
# the order-2 generators) for analogous tests at m ∈ {5, 7}.

HAP_Z4Generator := function(arg)
    local G, idx, deg_max, entry, R, K, UCT, vec, exponent, torsion,
          order_at_idx, db, violations, total, x, found_cache;

    G       := arg[1];
    if Length(arg) >= 2 then idx := arg[2]; else idx := fail; fi;
    deg_max := 5;  # we need R up to degree 5 anyway for B3 pipeline.

    # Lookup cache by group identity. Same convention as
    # _HAP_Pontryagin_GetCache: accept both G and R!.group as keys.
    found_cache := fail;
    for entry in _HAP_H3Z4Gen_cache do
        if (IsIdenticalObj(entry.G, G)
            or IsIdenticalObj(entry.R!.group, G))
           and entry.deg_max >= deg_max then
            found_cache := entry;
            break;
        fi;
    od;
    if found_cache <> fail then
        R := found_cache.R;
        K := found_cache.K;
        UCT := found_cache.UCT;
        exponent := UCT.exponent;
        torsion  := UCT.torsion;
        if idx = fail then idx := Length(torsion); fi;
        if idx < 1 or idx > Length(torsion) then
            Error("HAP_Z4Generator: idx ", idx, " out of range [1..",
                  Length(torsion), "]");
        fi;
        vec := UCT.cocyclebasis[idx];
        # Re-verify cocycle property for THIS idx.
        db := HAP_BarCoboundary(R, vec, 3);
        violations := 0;
        for x in db do
            if x mod exponent <> 0 then violations := violations + 1; fi;
        od;
        return rec(
            G          := G,
            R          := R,
            K          := K,
            UCT        := UCT,
            exponent   := exponent,
            torsion    := torsion,
            idx        := idx,
            order      := torsion[idx],
            vec        := vec,
            is_cocycle := violations = 0
        );
    fi;

    Print("  HAP_Z4Generator: building K = TensorWithIntegers(R) ",
          "and UCT for ", StructureDescription(G), "...\n");
    R := HAP_PontryaginGetResolution(G, deg_max);
    K := TensorWithIntegers(R);
    UCT := UniversalCoefficientsTheorem(K, 3);
    exponent := UCT.exponent;
    torsion  := UCT.torsion;

    Print("  HAP_Z4Generator: UCT.torsion = ", torsion, "\n");
    Print("  HAP_Z4Generator: UCT.exponent = ", exponent, "\n");
    Print("  HAP_Z4Generator: # generators = ", Length(torsion), "\n");

    # Default idx: last generator (highest order in the Smith normal form).
    if idx = fail then
        idx := Length(torsion);
    fi;

    if idx < 1 or idx > Length(torsion) then
        Error("HAP_Z4Generator: idx ", idx, " out of range [1..",
              Length(torsion), "]");
    fi;

    order_at_idx := torsion[idx];
    vec := UCT.cocyclebasis[idx];

    Print("  HAP_Z4Generator: selected idx = ", idx,
          ", order = ", order_at_idx, "\n");
    Print("  HAP_Z4Generator: |vec| = ", Length(vec),
          " (= R!.dimension(3))\n");

    # Sanity-check: vec is a Z/exponent cocycle on R.
    db := HAP_BarCoboundary(R, vec, 3);
    violations := 0;
    total := Length(db);
    for x in db do
        if x mod exponent <> 0 then violations := violations + 1; fi;
    od;
    Print("  HAP_Z4Generator: δ(vec) mod ", exponent, " violations: ",
          violations, " / ", total, "\n");

    # Cache the (R, K, UCT) triple keyed by group identity. Per-idx
    # cocycle properties are recomputed on cache-hit (cheap on R).
    Add(_HAP_H3Z4Gen_cache, rec(
        G          := G,
        deg_max    := deg_max,
        R          := R,
        K          := K,
        UCT        := UCT
    ));

    return rec(
        G          := G,
        R          := R,
        K          := K,
        UCT        := UCT,
        exponent   := exponent,
        torsion    := torsion,
        idx        := idx,
        order      := order_at_idx,
        vec        := vec,
        is_cocycle := violations = 0
    );
end;;

Print("Loaded hap_h3_z4_generator.g (HAP_Z4Generator).\n");
