# detecting_family_vanish.g — D-VAN-3 (issue #144).
#
# Core vanishing test: decides whether [omega] = 0 in H^3(E_+(m); U(1))
# by checking omega|_E = 0 and omega|_{D_8} = 0 on the AM04 detecting
# family F = {E, D_8}. Injectivity of res : H^3(G; U(1)) -> H^3(E) ⊕ H^3(D_8)
# is given by AM04 §IV.4-§IV.5 (specifically Thm 4.3 + Thm 5.6) +
# Quillen 1971 (essential ideal starts in degree 2m, clear of degree 3
# for m >= 2). The citation chain in detail: Adem-Milgram framework
# (§IV.4-§IV.5) -> Quillen 1971 Thm 5.10 (explicit H*(E_+(m); F_2)) ->
# Harada-Kono 1987 Thm 1.1 (integer A(k) summand) -> UCT for U(1)
# coefficients. See R-1
# (docs/superpowers/research/2026-05-17-detecting-family-literature.md)
# for the full synthesis.
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
# Iterative D-VAN-FIX (#151 → #154 → #153 closed): applies the FULL
# detecting family — restrict ω to (a) every conjugacy class rep of
# max elementary abelians, (b) the pinned D_8 section, and (c) the
# pinned Q_8 section (when present; absent only at m=1). [omega] = 0
# iff every restriction vanishes.
#
# Q_8 inclusion closes the m≥3 detection gap (#153) by catching the
# cyclic A(4) summand of H^3(E_+(m); U(1)); Q_8's H^3 = Z/8 natively
# distinguishes 2·A(4)_gen from 0, which D_8 sections cannot at m≥3.
# See docs/superpowers/research/2026-05-15-integer-cohomology-extraspecial-2-groups.md
# for the Harada-Kono structure-theoretic explanation.
#
# Returns rec(
#   trivial          : bool — [omega] = 0 in H^3(E_+(m); U(1))?
#   res_EA_vec_list  : list of coord vectors (one per max-EA conj class),
#                      each mod its EA's torsion
#   res_D8_vec       : coord vector of omega|_D_8 mod torsion_D8
#   res_Q8_vec       : coord vector of omega|_Q_8 mod torsion_Q8
#                      (`fail` when G has no Q_8 — m=1 only)
#   f_EA_list        : list of callable cocycles, one per EA in H_EA_list
#   f_D8             : callable cocycle D_8^3 -> Z/exp_D8
#   f_Q8             : callable cocycle Q_8^3 -> Z/exp_Q8 (or `fail`)
#   source           : "hap" | "quillen"
#   Backward-compat aliases res_E_vec and f_E point at the FIRST EA.
# ).
ResIsTrivialOnDetectingFamily := function(m, omega_vec)
    local rec_m, hom_omega, source, res_EA_vec_list, f_EA_list, i,
          torsion_EA_i, res_EA_i, vec_int, vec_modH,
          res_D8_vec_int, res_D8_vec, f_D8,
          res_Q8_vec_int, res_Q8_vec, f_Q8, all_Q8_zero,
          all_EA_zero, trivial;

    if not (IsInt(m) and m >= 1) then
        Error("ResIsTrivialOnDetectingFamily: m must be a positive ",
              "integer; got ", m);
    fi;

    source := _DVAN_SelectSource(m);
    rec_m := BuildRestrictionMatrices(m, source);
    hom_omega := NormaliseOmegaToHomBasis(rec_m, omega_vec);

    # Per-EA restriction: res_EA_list[i] applied to hom_omega gives the
    # i-th EA's image in coords mod torsion_EA_list[i].
    #
    # A-DVAN-1 (PR #402 audit): the previous shape
    #   vec_int := List([1..Length(torsion_EA_i)], j ->
    #       Sum([1..Length(hom_omega)], k ->
    #           hom_omega[k] * res_EA_i[k][j]));
    # was the P9 anti-pattern (Sum-of-List per entry, interpreted GAP
    # loops). Replaced by compiled `hom_omega * res_EA_i` (vector-times-
    # matrix) which dispatches to PROD_VEC_MAT_INT. The res_EA_i
    # matrices are already int-cast + IsMatrixRep-tagged by
    # RestrictionMatrixViaHAP (PR #381 + #382), so the compiled matvec
    # path engages immediately. Same fix applied to the D_8 and Q_8
    # branches below. The trailing per-column mod loop is left
    # untouched because moduli vary per column.
    res_EA_vec_list := [];
    f_EA_list := [];
    for i in [1..Length(rec_m.res_EA_list)] do
        torsion_EA_i := rec_m.torsion_EA_list[i];
        res_EA_i := rec_m.res_EA_list[i];
        vec_int := hom_omega * res_EA_i;
        vec_modH := List([1..Length(vec_int)], j ->
            vec_int[j] mod torsion_EA_i[j]);
        Add(res_EA_vec_list, vec_modH);
        Add(f_EA_list,
            _DVAN_BuildHCocycleFromHomVec(rec_m.ctx_EA_list[i], vec_modH));
    od;

    # D_8 restriction.
    res_D8_vec_int := hom_omega * rec_m.res_D8;
    res_D8_vec := List([1..Length(res_D8_vec_int)], j ->
        res_D8_vec_int[j] mod rec_m.torsion_D8[j]);
    f_D8 := _DVAN_BuildHCocycleFromHomVec(rec_m.ctx_D8, res_D8_vec);

    # Q_8 restriction (closes the m≥3 integer-cohomology gap; #154).
    # rec_m.res_Q8 = fail when G has no Q_8 subgroup (m=1 only). In that
    # degenerate case the Q_8 contribution to trivial-detection is
    # vacuously satisfied.
    if rec_m.res_Q8 = fail then
        res_Q8_vec := fail;
        f_Q8 := fail;
        all_Q8_zero := true;
    else
        res_Q8_vec_int := hom_omega * rec_m.res_Q8;
        res_Q8_vec := List([1..Length(res_Q8_vec_int)], j ->
            res_Q8_vec_int[j] mod rec_m.torsion_Q8[j]);
        f_Q8 := _DVAN_BuildHCocycleFromHomVec(rec_m.ctx_Q8, res_Q8_vec);
        all_Q8_zero := ForAll(res_Q8_vec, x -> x = 0);
    fi;

    # [omega] = 0 iff ALL restrictions vanish.
    all_EA_zero := ForAll(res_EA_vec_list, v -> ForAll(v, x -> x = 0));
    trivial := all_EA_zero
               and ForAll(res_D8_vec, x -> x = 0)
               and all_Q8_zero;

    return rec(
        trivial          := trivial,
        res_EA_vec_list  := res_EA_vec_list,
        res_D8_vec       := res_D8_vec,
        res_Q8_vec       := res_Q8_vec,
        f_EA_list        := f_EA_list,
        f_D8             := f_D8,
        f_Q8             := f_Q8,
        source           := source,

        # Backward-compat aliases.
        res_E_vec        := res_EA_vec_list[1],
        f_E              := f_EA_list[1]
    );
end;;

Print("Loaded detecting_family_vanish.g (D-VAN-3).\n");
