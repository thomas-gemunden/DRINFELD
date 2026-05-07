# Port of section 3 of the Magma supplement (Keller-Roberts-Roberts,
# arXiv:2411.13646): the Barnes-Wall lattice BW(m), its Gram matrix,
# and the "half-Gram" matrix H used to define the lift u_g.
#
# We follow appendix A.1 of the paper. Basis vectors are indexed by
# i in {0, 1, ..., 2^m - 1} interpreted in m-bit binary. Define
#
#     parity p(i) = (number of zero bits of i, mod 2)
#                 = ((m - bits(i)) mod 2)
#
# and the basis of BW(m) is, schematically,
#
#     w_i = sqrt(2)^{p(i) - ceil(m/2)} u_{i[m-1]} ⊗ ... ⊗ u_{i[0]}
#
# with u_0 = (sqrt(2), 0), u_1 = (1, 1). The Gram matrix has entries
# (Lemma A.1.2 of the paper)
#
#     (G_m)_{ij} = 2^{(p(i) + p(j) - 2*ceil(m/2)
#                    + sum_l (2 i[l] j[l] - i[l] - j[l] + 2)) / 2}
#
# i.e. the exponent is HALF the integer
#
#     E(i,j) = p(i) + p(j) - 2*ceil(m/2) + sum_l (2 i[l] j[l] - i[l] - j[l] + 2)
#
# A short check shows E(i,j) is always even, so the entry is integer.

# Helpers.
BitsOf := function(i, m)
    return List([0..m-1], k -> (i mod 2^(k+1) - i mod 2^k) / 2^k);
end;;
NumOnes := function(i, m)
    return Sum(BitsOf(i, m));
end;;
Parity := function(i, m)
    return (m - NumOnes(i, m)) mod 2;
end;;

# Gram matrix (G_m)_{ij} computed via (A.1.2).
BWGram := function(m)
    local n, G, i, j, bi, bj, exponent, l;
    n := 2^m;
    G := List([1..n], i -> List([1..n], j -> 0));
    for i in [0..n-1] do
        for j in [0..n-1] do
            bi := BitsOf(i, m);
            bj := BitsOf(j, m);
            exponent := Parity(i, m) + Parity(j, m) - 2 * Int((m + 1)/2);
            for l in [1..m] do
                exponent := exponent + 2 * bi[l] * bj[l] - bi[l] - bj[l] + 2;
            od;
            # exponent must be even and ≥ 0 (positive-definite lattice)
            G[i+1][j+1] := 2^(exponent / 2);
        od;
    od;
    return G;
end;;

# Half-Gram matrix H from section 2.2 of the paper:
#    H_{ij} = G_{ij} for i > j, G_{ii}/2 for i = j, 0 for i < j.
HalfGram := function(m)
    local G, n, H, i, j;
    G := BWGram(m);
    n := Length(G);
    H := List([1..n], i -> List([1..n], j -> 0));
    for i in [1..n] do
        for j in [1..n] do
            if i > j then H[i][j] := G[i][j];
            elif i = j then H[i][i] := G[i][i] / 2;
            fi;
        od;
    od;
    return H;
end;;

# Basic checks of the Gram matrix (used by test_bw_lattice.g, not run on Read).
VerifyBW := function(m)
    local G, n, det;
    Print("\n=== BW(", m, ") Gram matrix ===\n");
    G := BWGram(m);
    n := Length(G);
    Print("Dimension: ", n, " x ", n, "\n");
    Print("Symmetric:  ", G = TransposedMat(G), "\n");
    Print("All integer: ", ForAll(Concatenation(G), IsInt), "\n");
    Print("Even on diagonal (lattice is even): ",
          ForAll([1..n], i -> G[i][i] mod 2 = 0), "\n");
    if m >= 3 and IsOddInt(m) then
        det := DeterminantMat(G);
        Print("Determinant: ", det, " (predicted 1 for odd m >= 3)\n");
    elif m >= 4 and IsEvenInt(m) then
        det := DeterminantMat(G);
        Print("Determinant: ", det,
              " (predicted 2^{2^{m-1}} = 2^", 2^(m-1), ")\n");
    fi;
    Print("Min diagonal entry: ", Minimum(List([1..n], i -> G[i][i])),
          " (predicted 2^{floor(m/2)} = ", 2^(Int(m/2)), ")\n");
end;;
