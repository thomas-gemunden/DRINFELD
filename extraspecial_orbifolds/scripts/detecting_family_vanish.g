# detecting_family_vanish.g — D-VAN-3 (issue #144).
#
# Core vanishing test: decides whether [omega] = 0 in H^3(E_+(m); U(1))
# by checking omega|_E = 0 and omega|_{D_8} = 0 on the AM04 detecting
# family F = {E, D_8}. Injectivity of res : H^3(G; U(1)) -> H^3(E) ⊕ H^3(D_8)
# is given by AM04 IV.7 + Quillen 1971 (essential ideal starts in degree
# 2m, clear of degree 3 for m >= 2).
#
# Spec: docs/superpowers/specs/2026-05-15-detecting-family-vanishing-test-design.md
# Plan: docs/superpowers/plans/2026-05-15-detecting-family-vanishing-phase1.md
# Closes #144.

if not IsBoundGlobal("BuildRestrictionMatrices") then
    Read("detecting_family_restriction.g");
fi;
if not IsBoundGlobal("FSI_LiftIfHom") then
    Read("fsi_wrapper.g");
fi;
if not IsBoundGlobal("StandardCocycleOf") then
    Read("transgression_kernel.g");
fi;

If_ := function(c, a, b) if c then return a; else return b; fi; end;;

# Normalise omega_vec to hom-basis coordinates of length k_G.
#
# Phase-1 scope: accepts hom-basis coord vectors only (length
# k_G = Length(UCT_G.hombasis)). Cocycle-form input (length
# K_G!.dimension(3)) is recognised and rejected with a clear error
# rather than mis-projected.
#
# Why cocycle input is deferred: the planned augmented-matrix
# projection (used in RestrictionMatrixViaHAP) operates on length-
# Length(UCT.hombasis[1]) hom-vectors, NOT on length-K_G!.dimension(3)
# K^3-cocycles. The two live in different chain levels:
#   - cocyclebasis[i] is a K^3 vector (length K!.dimension(3))
#   - hombasis[i] is a functional on Z_3 (length |cyclebasis|)
# Translating a raw K^3 cocycle to its H^3 class coords needs an
# extra pairing step against UCT.cyclebasis that we haven't wired
# in yet. No current caller uses the cocycle form — all upstream
# code paths (A-3a, A-5b, K-* drivers) work in hom-basis coords —
# so the deferral is API-only.
NormaliseOmegaToHomBasis := function(rec_m, omega_vec)
    local setup_G, k_G, k3_dim, torsion_G;

    setup_G := rec_m.setup_G;
    k_G := setup_G.num_generators;
    torsion_G := setup_G.torsion;
    k3_dim := setup_G.K!.dimension(3);

    if Length(omega_vec) = k_G then
        return List([1..k_G], i -> omega_vec[i] mod torsion_G[i]);
    fi;
    if Length(omega_vec) = k3_dim then
        Error("NormaliseOmegaToHomBasis: cocycle-form input (length ",
              k3_dim, ") not yet implemented in D-VAN-3. Pass a hom-basis ",
              "vector of length ", k_G, " instead (e.g. coordinates ",
              "against UCT.hombasis). The cocycle-form path needs a ",
              "pairing against UCT.cyclebasis before the hombasis ",
              "projection and is tracked as a follow-up.");
    fi;
    Error("NormaliseOmegaToHomBasis: vec has length ", Length(omega_vec),
          "; expected ", k_G, " (hom-basis).");
end;;

# Build a callable bar 3-cocycle f : H^3 -> Z/exp_H from a hom-basis
# coordinate vector on H. Same idiom as StandardCocycleOf
# (transgression_kernel.g) but parameterised by ctx_H so we don't have
# to import the whole setup-G context.
_DVAN_BuildHCocycleFromHomVec := function(ctx_H, hom_vec)
    local v, i;
    v := ListWithIdenticalEntries(ctx_H.K!.dimension(3), 0);
    for i in [1..Length(hom_vec)] do
        v := v + hom_vec[i] * ctx_H.UCT.cocyclebasis[i];
    od;
    return StandardCocycle(ctx_H.R, v, 3, ctx_H.exponent);
end;;

# Decide which source to use for a given m. Phase 1 supports m in
# {2, 3, 5} via HAP. Phase 2 will add "quillen" for m = 7
# (gated on Q-int A2/A3, issue #136).
_DVAN_SelectSource := function(m)
    if m <= 5 then return "hap"; fi;
    return "quillen";
end;;

# Public entry point.
#
# Returns rec(
#   trivial    : bool        — [omega] = 0 in H^3(E_+(m); U(1))?
#   res_E_vec  : coord vector of omega|_E  in H^3(E;   U(1)) mod torsion_E
#   res_D8_vec : coord vector of omega|_D8 in H^3(D_8; U(1)) mod torsion_D8
#   f_E        : callable cocycle E^3   -> Z/exp_E
#   f_D8       : callable cocycle D_8^3 -> Z/exp_D8
#   source     : "hap" | "quillen"
# ).
ResIsTrivialOnDetectingFamily := function(m, omega_vec)
    local rec_m, hom_omega, res_E_vec_int, res_D8_vec_int,
          res_E_vec, res_D8_vec, trivial, f_E, f_D8, source;

    if not (IsInt(m) and m >= 1) then
        Error("ResIsTrivialOnDetectingFamily: m must be a positive ",
              "integer; got ", m);
    fi;

    source := _DVAN_SelectSource(m);
    rec_m := BuildRestrictionMatrices(m, source);
    hom_omega := NormaliseOmegaToHomBasis(rec_m, omega_vec);

    # Apply restriction matrices. Convention: res_E[i][j] = j-th coord
    # of the image of hombasis_G[i]. So a hom_omega in (Z/torsion_G[i])^k_G
    # maps via:
    #   res_E_vec[j] = sum_i hom_omega[i] * res_E[i][j]  mod torsion_E[j].
    res_E_vec_int := List([1..Length(rec_m.torsion_E)], j ->
        Sum([1..Length(hom_omega)], i ->
            hom_omega[i] * rec_m.res_E[i][j]));
    res_D8_vec_int := List([1..Length(rec_m.torsion_D8)], j ->
        Sum([1..Length(hom_omega)], i ->
            hom_omega[i] * rec_m.res_D8[i][j]));

    res_E_vec := List([1..Length(res_E_vec_int)], j ->
        res_E_vec_int[j] mod rec_m.torsion_E[j]);
    res_D8_vec := List([1..Length(res_D8_vec_int)], j ->
        res_D8_vec_int[j] mod rec_m.torsion_D8[j]);

    trivial := ForAll(res_E_vec, x -> x = 0)
               and ForAll(res_D8_vec, x -> x = 0);

    # Build callable cocycles on E and D_8 from the coordinate vectors
    # via each subgroup's UCT.cocyclebasis (the V-4a-fixed lift idiom).
    f_E  := _DVAN_BuildHCocycleFromHomVec(rec_m.ctx_E,  res_E_vec);
    f_D8 := _DVAN_BuildHCocycleFromHomVec(rec_m.ctx_D8, res_D8_vec);

    return rec(
        trivial     := trivial,
        res_E_vec   := res_E_vec,
        res_D8_vec  := res_D8_vec,
        f_E         := f_E,
        f_D8        := f_D8,
        source      := source
    );
end;;

Print("Loaded detecting_family_vanish.g (D-VAN-3).\n");
