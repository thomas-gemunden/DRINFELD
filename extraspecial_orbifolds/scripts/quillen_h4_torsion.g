# quillen_h4_torsion.g — Q-int A2 (issue #136).
#
# Derives the torsion vector of H^4(E_+(m); Z) ≅ H^3(E_+(m); U(1)) for
# m ≥ 3, using:
#
#   1. Harada-Kono 1987 Theorem 1.1: for h(Q) ≥ 2,
#         H^k(V^-; Z) = A(k) ⊕ (elementary abelian 2-group),
#      with A(k) cyclic of order 2^{a(k,Q)} when k ≡ 0 (mod 4) and 0
#      otherwise. For k = 4 and h(Q) = m ≥ 3 (i.e. n(4) = 2 ≤ h-1),
#      a(4, Q) = n(4) = 2, so A(4) = Z/4. This gives the cyclic-summand
#      contribution a priori.
#
#   2. The Bockstein β : H^4(G; F_2) → H^5(G; F_2). Standard:
#         2-rank of H^4(G; Z)  =  dim_{F_2} ker β_4.
#      For m ≥ 3 we have deg(w) = 2^m ≥ 8, so w does not appear in any
#      monomial of degree ≤ 5 in the canonical Quillen presentation.
#      Hence β is fully determined by β(x_i) = x_i² (Q-int A1) and the
#      Leibniz rule — no `fail` from `BocksteinOnMonomial`.
#
# With the cyclic A(4) = Z/4 contributing one cyclic summand to the
# 2-rank, the rest of the 2-rank comes from the (Z/2)^r summand:
#
#       r + 1  =  dim_{F_2} ker β_4
#       r      =  dim_{F_2} H^4(G; F_2)  -  rank_{F_2}(β bar)  -  1
#
# The torsion vector is therefore [2, 2, ..., 2, 4] with r twos.
#
# Implementation note. The Q-2a canonical presentation is a regular
# sequence but NOT a Gröbner basis under graded-lex (verified by
# checking that the S-polynomial of Q and B(x, x²)_1 at m = 3 produces
# x_1 x_2 x_5 + x_1 x_3 x_6 + x_1 x_4², whose leading monomial
# x_1 x_2 x_5 is not divisible by any relation's leading monomial).
# Consequently `BocksteinOnElement`'s leading-term-only reduction
# leaves some terms outside `BasisInDegree(R, 5)`. We work around this
# by computing β at the FULL monomial level (V_4 → V_5) and reducing
# modulo I_5 via the same ideal-span matrix that `BasisInDegree`
# constructs internally — i.e. RREF over F_2.
#
# Reference: docs/superpowers/research/2026-05-15-integer-cohomology-extraspecial-2-groups.md

if not IsBoundGlobal("QuillenCanonicalPresentation") then
    Read("quillen_canonical_presentation.g");
fi;
if not IsBoundGlobal("BocksteinOnMonomial") then
    Read("quillen_bockstein.g");
fi;
if not IsBoundGlobal("QuillenAllMonomialsOfDegree") then
    Read("quillen_algebra.g");
fi;

# Build the F_2 matrix of β acting on the FULL monomial space V_d in
# degree d: rows index all_mons_d, columns index all_mons_{d+1}.
_QH4_BuildBetaMatrix := function(R, all_d, idx_dp1, n_dp1)
    local mat, i, mu, beta_mu, mon, k;
    mat := List([1..Length(all_d)],
                r -> ListWithIdenticalEntries(n_dp1, 0));
    for i in [1..Length(all_d)] do
        mu := all_d[i];
        beta_mu := BocksteinOnMonomial(R, mu);
        if beta_mu = fail then
            Error("_QH4_BuildBetaMatrix: BocksteinOnMonomial returned ",
                  "fail at monomial index ", i,
                  " (sym=", mu.sym, "). β(w) is the only unknown; ",
                  "either m < 3 (use hardcoded path) or the monomial ",
                  "table is malformed.");
        fi;
        for mon in beta_mu do
            k := LookupDictionary(idx_dp1, mon);
            if k <> fail then
                mat[i][k] := (mat[i][k] + 1) mod 2;
            fi;
        od;
    od;
    return mat;
end;;

# Build the matrix whose rows span I_d in V_d: one row per (relation r,
# η ∈ all_mons_{d - deg(r)}) pair.
_QH4_BuildIdealMatrix := function(R, target_deg, all_d, idx_d, n_d)
    local rows, r, deg_r, mu_deg, eta, scaled, row, mon, k;
    rows := [];
    for r in R.relations do
        deg_r := QuillenMonomialDegree(R, r[1]);
        mu_deg := target_deg - deg_r;
        if mu_deg < 0 then continue; fi;
        for eta in QuillenAllMonomialsOfDegree(R, mu_deg) do
            scaled := QuillenScaleByMonomial(R, r, eta);
            if Length(scaled) = 0 then continue; fi;
            row := ListWithIdenticalEntries(n_d, 0);
            for mon in scaled do
                k := LookupDictionary(idx_d, mon);
                row[k] := 1;
            od;
            Add(rows, row);
        od;
    od;
    return rows;
end;;

# Compute the F_2 dimension of H^d(E_+(m); F_2) for any d using the
# same ideal-span-then-RREF logic that BasisInDegree uses internally,
# but as a flat dim count.
_QH4_DimF2 := function(R, d, all_d, idx_d, n_d)
    local I, F2;
    I := _QH4_BuildIdealMatrix(R, d, all_d, idx_d, n_d);
    if Length(I) = 0 then return n_d; fi;
    F2 := Z(2) ^ 0;
    return n_d - RankMat(I * F2);
end;;

# Main exported function. Returns rec(matrix=β bar matrix in B_4 × B_5
# coords, dim_h4, dim_h5, ker_dim, rank_betabar, raw).
QuillenH4BocksteinMatrix := function(m)
    local R, all4, all5, idx4, idx5, n4, n5, i, j,
          beta_full, I5_rows, I4_rows, F2, beta_F2, I5_F2, I4_F2,
          rank_I5, rank_I4, dim_h4, dim_h5,
          combined, rank_combined, rank_betabar, ker_dim;

    if m < 3 then
        Error("QuillenH4BocksteinMatrix: requires m >= 3 ",
              "(at m=2, deg(w)=4 enters H^4 and β(w) is not yet ",
              "tabulated in quillen_bockstein.g)");
    fi;

    R := QuillenCanonicalPresentation(m);
    all4 := QuillenAllMonomialsOfDegree(R, 4);
    all5 := QuillenAllMonomialsOfDegree(R, 5);
    n4 := Length(all4);
    n5 := Length(all5);

    idx4 := NewDictionary(all4[1], true, all4);
    idx5 := NewDictionary(all5[1], true, all5);
    for i in [1..n4] do AddDictionary(idx4, all4[i], i); od;
    for j in [1..n5] do AddDictionary(idx5, all5[j], j); od;

    beta_full := _QH4_BuildBetaMatrix(R, all4, idx5, n5);
    I4_rows   := _QH4_BuildIdealMatrix(R, 4, all4, idx4, n4);
    I5_rows   := _QH4_BuildIdealMatrix(R, 5, all5, idx5, n5);

    F2 := Z(2) ^ 0;
    beta_F2 := beta_full * F2;
    if Length(I4_rows) > 0 then
        I4_F2 := I4_rows * F2;
        rank_I4 := RankMat(I4_F2);
    else
        rank_I4 := 0;
    fi;
    if Length(I5_rows) > 0 then
        I5_F2 := I5_rows * F2;
        rank_I5 := RankMat(I5_F2);
    else
        rank_I5 := 0;
    fi;
    dim_h4 := n4 - rank_I4;
    dim_h5 := n5 - rank_I5;

    # rank of β bar (the induced map on H^4 → H^5):
    #   rank β bar = rank([β; I_5]) - rank(I_5).
    if rank_I5 = 0 then
        combined := beta_F2;
    else
        combined := Concatenation(beta_F2, I5_F2);
    fi;
    rank_combined := RankMat(combined);
    rank_betabar := rank_combined - rank_I5;
    ker_dim := dim_h4 - rank_betabar;

    return rec(
        m            := m,
        dim_h4       := dim_h4,
        dim_h5       := dim_h5,
        rank_betabar := rank_betabar,
        ker_dim      := ker_dim,
        n4           := n4,
        n5           := n5,
        rank_I4      := rank_I4,
        rank_I5      := rank_I5
    );
end;;

# Derive the torsion vector of H^4(E_+(m); Z) for m >= 3.
QuillenH4TorsionFromBockstein := function(m)
    local rec_b, r;
    rec_b := QuillenH4BocksteinMatrix(m);
    r := rec_b.ker_dim - 1;
    if r < 0 then
        Error("QuillenH4TorsionFromBockstein: derived r = ", r,
              " < 0 at m = ", m,
              ". This contradicts Harada-Kono's A(4) = Z/4 prediction ",
              "(which forces 2-rank >= 1). dim H^4 = ", rec_b.dim_h4,
              ", rank β bar = ", rec_b.rank_betabar,
              ", ker dim = ", rec_b.ker_dim, ".");
    fi;
    return Concatenation(ListWithIdenticalEntries(r, 2), [4]);
end;;

Print("Loaded quillen_h4_torsion.g ",
      "(QuillenH4BocksteinMatrix, QuillenH4TorsionFromBockstein; m>=3).\n");
