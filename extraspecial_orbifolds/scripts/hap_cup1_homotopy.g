# hap_cup1_homotopy.g — level-1 cup-1 homotopy h_1: R → (R⊗R)[+1].
#
# Issue #171 follow-up.
# Spec: docs/superpowers/specs/2026-05-16-pontryagin-diagonal-chain-map-spec.md
#
# # Math.
#
# Given Δ: R → R⊗R (the chain-level diagonal from hap_diagonal.g) and
# the twist map τ: R⊗R → R⊗R that swaps factors with Koszul sign, the
# composite τΔ - Δ: R → R⊗R is a chain map (since Δ and τΔ are). It is
# null-homotopic (because both Δ and τΔ are homotopic at the cohomology
# level by the cup product's graded-commutativity up to homotopy). Define
# h_1: R → (R⊗R)[+1] so that
#
#   ∂_RR ∘ h_1 + h_1 ∘ ∂_R = τΔ - Δ.
#
# Constructed inductively: at e_n^i, set
#   h_1(e_n^i) := s(τΔ(e_n^i) - Δ(e_n^i) - h_1(∂_R e_n^i))
# where s is the Z-module contracting homotopy on R⊗R from
# `_HAP_RR_Homotopy` in `hap_diagonal.g`. The "lift target"
# τΔ(e_n^i) - Δ(e_n^i) - h_1(∂_R e_n^i) is a cycle by induction, so the
# lift is well-defined.
#
# At degree 0, both Δ and τΔ agree, so h_1(e_0^1) = 0.
#
# # τ swap.
#
# (sgn, p, q, jp, jq, gl, gr)  →  (sgn · (-1)^{pq}, q, p, jq, jp, gr, gl).

if not IsBoundGlobal("HAP_BuildDiagonal") then
    Read("hap_diagonal.g");
fi;

# ------------------------------------------------------------------
# τ swap with Koszul sign.
# ------------------------------------------------------------------

_HAP_RR_Swap := function(chain)
    local result, r, ksign;
    result := [];
    for r in chain do
        if IsEvenInt(r.p * r.q) then ksign := 1; else ksign := -1; fi;
        Add(result, rec(sgn := r.sgn * ksign,
                        p := r.q, q := r.p,
                        jp := r.jq, jq := r.jp,
                        gl := r.gr, gr := r.gl));
    od;
    return result;
end;;

# ------------------------------------------------------------------
# HAP_BuildCup1Homotopy(R, Δ_data, n_max)
#
# Builds and returns the cup-1 homotopy cache h_1_data such that
# h_1_data[n+1][i] is the (R⊗R)_{n+1} chain representing h_1(e_n^i) for
# i ∈ [1..R!.dimension(n)].
#
# Δ_data should be a Δ cache covering at least degrees [0..n_max]
# (from `HAP_BuildDiagonal`).
# ------------------------------------------------------------------

HAP_BuildCup1Homotopy := function(R, DiagMap, n_max)
    local Cup1Hty, n, i, c, entry, sgn, j, g_pos, shifted, tau_d, neg_d;
    Cup1Hty := [];
    Cup1Hty[1] := [[]];  # h_1(e_0^1) = 0
    for n in [1..n_max] do
        Cup1Hty[n+1] := [];
        for i in [1..R!.dimension(n)] do
            # rhs := τΔ(e_n^i) - Δ(e_n^i) - h_1(∂_R e_n^i)
            tau_d := _HAP_RR_Swap(DiagMap[n+1][i]);
            neg_d := _HAP_RR_Scale(DiagMap[n+1][i], -1);
            c := Concatenation(tau_d, neg_d);
            for entry in R!.boundary(n, i) do
                sgn := SignInt(entry[1]);
                j := AbsInt(entry[1]);
                g_pos := entry[2];
                shifted := _HAP_RR_DiagAction(R, g_pos, Cup1Hty[n][j]);
                Append(c, _HAP_RR_Scale(shifted, -sgn));
            od;
            c := _HAP_RR_Reduce(c);
            # Lift: h_1(e_n^i) := homotopy of c.
            Cup1Hty[n+1][i] := _HAP_RR_Homotopy(R, c);
        od;
    od;
    return Cup1Hty;
end;;

# ------------------------------------------------------------------
# Verification helper.
# ------------------------------------------------------------------

# HAP_VerifyCup1Homotopy(R, Δ_data, h_1_data, n_max)
#
# Verifies ∂_RR(h_1_data[n+1][i]) = (τΔ - Δ)(e_n^i) - h_1(∂_R e_n^i)
# for all (n, i) with n ∈ [1..n_max], i ∈ [1..R!.dimension(n)].
HAP_VerifyCup1Homotopy := function(R, DiagMap, Cup1Hty, n_max)
    local violations, total, details, n, i, lhs, rhs, entry, sgn, j,
          g_pos, shifted, diff;
    violations := 0;
    total := 0;
    details := [];
    for n in [1..n_max] do
        for i in [1..R!.dimension(n)] do
            total := total + 1;
            lhs := _HAP_RR_Boundary(R, Cup1Hty[n+1][i]);
            rhs := Concatenation(_HAP_RR_Swap(DiagMap[n+1][i]),
                                 _HAP_RR_Scale(DiagMap[n+1][i], -1));
            for entry in R!.boundary(n, i) do
                sgn := SignInt(entry[1]);
                j := AbsInt(entry[1]);
                g_pos := entry[2];
                shifted := _HAP_RR_DiagAction(R, g_pos, Cup1Hty[n][j]);
                Append(rhs, _HAP_RR_Scale(shifted, -sgn));
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

Print("Loaded hap_cup1_homotopy.g ",
      "(HAP_BuildCup1Homotopy, HAP_VerifyCup1Homotopy, _HAP_RR_Swap).\n");
