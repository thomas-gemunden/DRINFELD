# hap_diagonal.g — chain-level diagonal Δ: R → R⊗R on HAP's compact
# resolution. Issue #171 follow-up.
#
# Spec: docs/superpowers/specs/2026-05-16-pontryagin-diagonal-chain-map-spec.md
#
# # Math.
#
# Given a free ZG-resolution R of Z, we want Δ: R → R⊗R such that:
#   - Δ is a ZG-chain map (G acts diagonally on R⊗R).
#   - At degree 0, Δ(e_0^1) = e_0^1 ⊗ e_0^1.
#   - ∂_RR ∘ Δ = Δ ∘ ∂_R.
#
# The standard inductive construction: assume Δ is defined on R_{<n}. For
# each generator e_n^i, the chain Δ(∂_R e_n^i) ∈ (R⊗R)_{n-1} is a cycle
# (since Δ commutes with ∂ on lower degrees and ∂² = 0). Use a Z-module
# contracting homotopy s on R⊗R to lift it:
#
#   Δ(e_n^i) := s(Δ(∂_R e_n^i)).
#
# Then ∂_RR(Δ(e_n^i)) = Δ(∂_R e_n^i) automatically (by ∂s + s∂ = id - aug,
# applied to a cycle in degree ≥ 1).
#
# # Data structure for R⊗R chains.
#
# A chain in (R⊗R)_n is a list of records:
#   rec(sgn := ±1, p, q, jp, jq, gl, gr)
# Interpretation:
#   sgn · (gl · e_p^{jp}) ⊗ (gr · e_q^{jq})
# where p + q = n, jp ∈ [1..R!.dimension(p)], jq ∈ [1..R!.dimension(q)],
# and gl, gr ∈ R!.elts (encoded as positions in that list).
#
# Note: the spec describes a 6-tuple with a single diagonal `g`. We use
# 7-fields because the boundary on R⊗R produces non-diagonal terms (the
# action of g on the first factor of ∂ ⊗ id propagates only through that
# factor). The diagonal G-action `g · _` shifts both `gl` and `gr` by g
# simultaneously.
#
# Like terms are combined by summing `sgn`s over matching
# (p, q, jp, jq, gl, gr) keys; zero-coefficient terms are dropped.
#
# # Resolution choice.
#
# Must use a Z-resolution (`ResolutionFiniteGroup`), NOT
# `ResolutionPrimePowerGroup` (the latter has characteristic 2, so
# ∂² ≠ 0 over Z and the inductive Δ has no consistent integer lift).
# `HAP_PontryaginGetResolution` (defined in `hap_pontryagin_square.g`)
# returns `ResolutionFiniteGroup(G, deg_max + 1)` for this reason.

if not IsPackageMarkedForLoading("hap", "") then
    LoadPackage("hap");
fi;

# ------------------------------------------------------------------
# Data-structure helpers.
# ------------------------------------------------------------------

# _HAP_Diag_RMult(R, p_pos, q_pos): position of R!.elts[p_pos] * R!.elts[q_pos]
# in R!.elts. Grows R!.elts if the product is absent.
_HAP_Diag_RMult := function(R, p_pos, q_pos)
    local gp, r;
    gp := R!.elts[p_pos] * R!.elts[q_pos];
    r := Position(R!.elts, gp);
    if r = fail then
        Add(R!.elts, gp);
        r := Length(R!.elts);
    fi;
    return r;
end;;

# _HAP_Diag_IdenPos(R): position of Identity(R!.group) in R!.elts.
_HAP_Diag_IdenPos := function(R)
    local p;
    p := Position(R!.elts, Identity(R!.group));
    if p = fail then
        Add(R!.elts, Identity(R!.group));
        p := Length(R!.elts);
    fi;
    return p;
end;;

# _HAP_RR_Reduce(chain): combine like terms in an R⊗R chain. Sum signs
# over identical (p, q, jp, jq, gl, gr) keys; drop zero-coefficient.
_HAP_RR_Reduce := function(chain)
    local d, k, key, result, r;
    d := rec();
    for r in chain do
        if r.sgn = 0 then continue; fi;
        key := Concatenation("k", String(r.p), "_", String(r.q), "_",
                             String(r.jp), "_", String(r.jq), "_",
                             String(r.gl), "_", String(r.gr));
        if IsBound(d.(key)) then
            d.(key).sgn := d.(key).sgn + r.sgn;
        else
            d.(key) := rec(sgn := r.sgn, p := r.p, q := r.q,
                           jp := r.jp, jq := r.jq,
                           gl := r.gl, gr := r.gr);
        fi;
    od;
    result := [];
    for key in RecNames(d) do
        if d.(key).sgn <> 0 then
            Add(result, d.(key));
        fi;
    od;
    return result;
end;;

# _HAP_RR_Scale(chain, k): multiply every sgn by k. Returns a new chain
# (does not reduce).
_HAP_RR_Scale := function(chain, k)
    local result, r;
    if k = 1 then return chain; fi;
    result := [];
    for r in chain do
        Add(result, rec(sgn := k * r.sgn, p := r.p, q := r.q,
                        jp := r.jp, jq := r.jq, gl := r.gl, gr := r.gr));
    od;
    return result;
end;;

# _HAP_RR_DiagAction(R, g_pos, chain): apply (g, g) diagonal action to a
# chain. Shifts gl and gr both by left-multiplication by g.
_HAP_RR_DiagAction := function(R, g_pos, chain)
    local r, result, iden;
    iden := _HAP_Diag_IdenPos(R);
    if g_pos = iden then return chain; fi;
    result := [];
    for r in chain do
        Add(result, rec(sgn := r.sgn, p := r.p, q := r.q,
                        jp := r.jp, jq := r.jq,
                        gl := _HAP_Diag_RMult(R, g_pos, r.gl),
                        gr := _HAP_Diag_RMult(R, g_pos, r.gr)));
    od;
    return result;
end;;

# ------------------------------------------------------------------
# R⊗R boundary and homotopy.
# ------------------------------------------------------------------

# _HAP_RR_Boundary(R, chain): boundary of an (R⊗R)_n chain. Returns an
# (R⊗R)_{n-1} chain (reduced).
#
# Formula (Z-linearly extended from basis elements):
#   ∂((gl · e_p^jp) ⊗ (gr · e_q^jq))
#     = (gl · ∂_R e_p^jp) ⊗ (gr · e_q^jq)
#     + (-1)^p (gl · e_p^jp) ⊗ (gr · ∂_R e_q^jq)
# Each term gl · ∂_R(e_p^jp) = sum_i sgn_i · (gl * g_i) · e_{p-1}^{j_i}.
_HAP_RR_Boundary := function(R, chain)
    local result, r, bdr, b, sgn_b, j_b, g_b, p_sgn;
    result := [];
    for r in chain do
        # term1 (∂ on first factor), active for p ≥ 1
        if r.p >= 1 then
            bdr := R!.boundary(r.p, r.jp);
            for b in bdr do
                sgn_b := SignInt(b[1]);
                j_b := AbsInt(b[1]);
                g_b := b[2];
                Add(result, rec(sgn := r.sgn * sgn_b,
                                p := r.p - 1, q := r.q,
                                jp := j_b, jq := r.jq,
                                gl := _HAP_Diag_RMult(R, r.gl, g_b),
                                gr := r.gr));
            od;
        fi;
        # term2 (∂ on second factor), active for q ≥ 1, with sign (-1)^p
        if r.q >= 1 then
            bdr := R!.boundary(r.q, r.jq);
            if IsOddInt(r.p) then p_sgn := -1; else p_sgn := 1; fi;
            for b in bdr do
                sgn_b := SignInt(b[1]);
                j_b := AbsInt(b[1]);
                g_b := b[2];
                Add(result, rec(sgn := r.sgn * p_sgn * sgn_b,
                                p := r.p, q := r.q - 1,
                                jp := r.jp, jq := j_b,
                                gl := r.gl,
                                gr := _HAP_Diag_RMult(R, r.gr, g_b)));
            od;
        fi;
    od;
    return _HAP_RR_Reduce(result);
end;;

# _HAP_RR_Homotopy(R, chain): Z-module contracting homotopy on R⊗R.
# Satisfies ∂s + s∂ = id - aug ⊗ aug.
#
# Formula: s = h_R ⊗ 1 + (η_R ε_R) ⊗ h_R
# - h_R ⊗ 1: applied for all p (h_R is the Z-module homotopy on R,
#   exposed by R!.homotopy(p, [j, g])).
# - (η_R ε_R) ⊗ h_R: applied only when p = 0, since ε_R(e_p^j · g) = 0
#   for p ≥ 1. For p = 0, ε(e_0^1 · gl) = 1, so the (ηε) factor becomes
#   e_0^1 · 1_G.
_HAP_RR_Homotopy := function(R, chain)
    local result, r, hty, h, sgn_h, j_h, g_h, iden;
    iden := _HAP_Diag_IdenPos(R);
    result := [];
    for r in chain do
        # term1: h ⊗ 1, active for all p ≥ 0.
        hty := R!.homotopy(r.p, [r.jp, r.gl]);
        for h in hty do
            sgn_h := SignInt(h[1]);
            j_h := AbsInt(h[1]);
            g_h := h[2];
            Add(result, rec(sgn := r.sgn * sgn_h,
                            p := r.p + 1, q := r.q,
                            jp := j_h, jq := r.jq,
                            gl := g_h, gr := r.gr));
        od;
        # term2: ηε ⊗ h, active for p = 0 only.
        if r.p = 0 then
            hty := R!.homotopy(r.q, [r.jq, r.gr]);
            for h in hty do
                sgn_h := SignInt(h[1]);
                j_h := AbsInt(h[1]);
                g_h := h[2];
                Add(result, rec(sgn := r.sgn * sgn_h,
                                p := 0, q := r.q + 1,
                                jp := 1, jq := j_h,
                                gl := iden, gr := g_h));
            od;
        fi;
    od;
    return _HAP_RR_Reduce(result);
end;;

# ------------------------------------------------------------------
# HAP_BuildDiagonal — main entry point.
# ------------------------------------------------------------------

# HAP_BuildDiagonal(R, n_max)
#
# Builds and returns the diagonal cache Δ_data for R = a HAP free
# ZG-resolution, up to degree n_max.
#
# Returns a list Δ_data such that Δ_data[n+1][i] is the (R⊗R)_n chain
# representing Δ(e_n^i) for i ∈ [1..R!.dimension(n)]. The chain is in
# the record form described at the top of this file.
HAP_BuildDiagonal := function(R, n_max)
    local DiagMap, n, i, iden, c, entry, sgn, j, g_pos, shifted;
    iden := _HAP_Diag_IdenPos(R);
    DiagMap := [];
    DiagMap[1] := [[rec(sgn := 1, p := 0, q := 0, jp := 1, jq := 1,
                        gl := iden, gr := iden)]];
    for n in [1..n_max] do
        DiagMap[n+1] := [];
        for i in [1..R!.dimension(n)] do
            # c = Δ(∂_R(e_n^i)) = sum_a sgn_a · (g_a, g_a) · Δ[n-1][j_a]
            c := [];
            for entry in R!.boundary(n, i) do
                sgn := SignInt(entry[1]);
                j := AbsInt(entry[1]);
                g_pos := entry[2];
                shifted := _HAP_RR_DiagAction(R, g_pos, DiagMap[n][j]);
                Append(c, _HAP_RR_Scale(shifted, sgn));
            od;
            c := _HAP_RR_Reduce(c);
            # Δ(e_n^i) := homotopy lift of c.
            DiagMap[n+1][i] := _HAP_RR_Homotopy(R, c);
        od;
    od;
    return DiagMap;
end;;

# ------------------------------------------------------------------
# Verification helper.
# ------------------------------------------------------------------

# HAP_VerifyDiagonalChainMap(R, Δ_data, n_max)
#
# Verifies that ∂_RR(Δ_data[n+1][i]) = Δ(∂_R(e_n^i)) for all (n, i)
# with n ∈ [1..n_max], i ∈ [1..R!.dimension(n)].
#
# Returns rec(violations, total, details).
HAP_VerifyDiagonalChainMap := function(R, DiagMap, n_max)
    local violations, total, details, n, i, lhs, rhs, entry, sgn, j,
          g_pos, shifted, diff;
    violations := 0;
    total := 0;
    details := [];
    for n in [1..n_max] do
        for i in [1..R!.dimension(n)] do
            total := total + 1;
            lhs := _HAP_RR_Boundary(R, DiagMap[n+1][i]);
            rhs := [];
            for entry in R!.boundary(n, i) do
                sgn := SignInt(entry[1]);
                j := AbsInt(entry[1]);
                g_pos := entry[2];
                shifted := _HAP_RR_DiagAction(R, g_pos, DiagMap[n][j]);
                Append(rhs, _HAP_RR_Scale(shifted, sgn));
            od;
            rhs := _HAP_RR_Reduce(rhs);
            diff := _HAP_RR_Reduce(Concatenation(lhs, _HAP_RR_Scale(rhs, -1)));
            if Length(diff) <> 0 then
                violations := violations + 1;
                Add(details, rec(n := n, i := i, diff_len := Length(diff)));
            fi;
        od;
    od;
    return rec(violations := violations, total := total, details := details);
end;;

Print("Loaded hap_diagonal.g ",
      "(HAP_BuildDiagonal, HAP_VerifyDiagonalChainMap, ",
      "_HAP_RR_Boundary, _HAP_RR_Homotopy).\n");
