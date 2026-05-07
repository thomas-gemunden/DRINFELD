# Port of Keller-Roberts-Roberts (arXiv:2411.13646) intertwiner check for m=3.
#
# We implement the explicit intertwiner matrices from equations
# (4.4.3)-(4.4.8) of the paper, which act on Omega_0 spanned by basis
# vectors e_c indexed by c = (c1, c2, c3, c4) in (F_2)^4 (so dim 16).
# We then verify that for the lifted z = -1 sector, the projective
# representation of the centralizer C_{E(3)}(-1) = E(3) on Omega_0 has
# trivial 2-cocycle by checking
#
#     T_ar^2  = 1                            (eq. 4.4.1)
#     T_ar T_bs = T_bs T_ar                  (eq. 4.4.2)
#
# for a in {1, 2, 3}, r in {1, 2}.  These are NOT just projective; the
# paper observes (after appropriate normalization) that they hold
# exactly, so the cocycle of the intertwining representation of
# E(3)/<z> = (Z/2)^6 on Omega_0 vanishes.

# Index the basis vectors of Omega_0 by integers 1..16 corresponding to
# (c1, c2, c3, c4) in {0,1}^4 with c1 = bit0, c2 = bit1, etc.
EncodeC := function(c)
    return 1 + c[1] + 2*c[2] + 4*c[3] + 8*c[4];
end;;
DecodeC := function(idx)
    local i, bits;
    i := idx - 1;
    bits := [];
    bits[1] := i mod 2; i := QuoInt(i, 2);
    bits[2] := i mod 2; i := QuoInt(i, 2);
    bits[3] := i mod 2; i := QuoInt(i, 2);
    bits[4] := i mod 2;
    return bits;
end;;

# Build a 16x16 matrix from a function f : (c1,c2,c3,c4) -> coeff_basis_pairs.
# f returns a list of [coeff, c'_vector] pairs giving T(e_c) = sum coeff * e_{c'}.
BuildT := function(f)
    local M, idx, c, terms, term, jdx;
    M := List([1..16], i -> List([1..16], j -> 0));
    for idx in [1..16] do
        c := DecodeC(idx);
        terms := f(c);
        for term in terms do
            jdx := EncodeC(term[2]);
            M[jdx][idx] := M[jdx][idx] + term[1];
        od;
    od;
    return M;
end;;

# Equations (4.4.3)-(4.4.8). Here c1, c2, c3, c4 are entries of c (4-tuple in F_2).
T11_f := function(c) return [[1, [c[1], c[2], c[3], (c[4]+c[2]+c[3]) mod 2]]]; end;;
T12_f := function(c)
    local sgn;
    sgn := (-1)^(c[1]*(c[2]+c[3]));
    return [[sgn, [c[1], (c[2]+c[1]) mod 2, (c[3]+c[1]) mod 2, c[4]]]];
end;;
T21_f := function(c) return [[1, [c[1], c[3], c[2], c[4]]]]; end;;
T22_f := function(c) return [[1, [c[1], c[2], c[3], (c[4]+c[1]) mod 2]]]; end;;
T31_f := function(c)
    local s1, s2;
    s1 := 1/2;
    s2 := (-1)^(c[2]+c[3]) / 2;
    # 1/2 ( e_{c1,c2,c3,c4} + e_{c1,c2,c3,c4+1}) + 1/2 (-1)^{c2+c3} ( e_{c1,c2+1,c3+1,c4} - e_{c1,c2+1,c3+1,c4+1} )
    return [
        [s1, [c[1], c[2], c[3], c[4]]],
        [s1, [c[1], c[2], c[3], (c[4]+1) mod 2]],
        [s2, [c[1], (c[2]+1) mod 2, (c[3]+1) mod 2, c[4]]],
        [-s2, [c[1], (c[2]+1) mod 2, (c[3]+1) mod 2, (c[4]+1) mod 2]]
    ];
end;;
T32_f := function(c)
    local sgn;
    sgn := (-1)^(c[1]*(c[2]+c[3]));
    return [[sgn, [c[1], c[2], c[3], c[4]]]];
end;;

T11 := BuildT(T11_f);;
T12 := BuildT(T12_f);;
T21 := BuildT(T21_f);;
T22 := BuildT(T22_f);;
T31 := BuildT(T31_f);;
T32 := BuildT(T32_f);;

Print("=== Intertwiner matrices for m=3 (Keller-Roberts-Roberts (4.4.3)-(4.4.8)) ===\n");
Print("dim Omega_0 = 16 = 2^{2m-2} for m=3\n");

# ---- Verify (4.4.1): T_ar^2 = identity ----
gens := [["T11", T11], ["T12", T12], ["T21", T21], ["T22", T22], ["T31", T31], ["T32", T32]];;
Id16 := IdentityMat(16);;

Print("\n--- (4.4.1) T_ar^2 = identity? ---\n");
for pair in gens do
    sq := pair[2] * pair[2];
    Print("  ", pair[1], "^2 = identity: ", sq = Id16, "\n");
od;

Print("\n--- (4.4.2) T_ar T_bs = T_bs T_ar (commutativity)? ---\n");
for i in [1..Length(gens)] do
    for j in [i+1..Length(gens)] do
        Aname := gens[i][1]; A := gens[i][2];
        Bname := gens[j][1]; B := gens[j][2];
        Print("  [", Aname, ", ", Bname, "] = 0: ", A*B = B*A, "\n");
    od;
od;

# Diagnostic: print the actual T11 matrix
Print("\n--- Sanity: T11 acts on basis as e_{c1,c2,c3,c4} -> e_{c1,c2,c3,c4 XOR c2 XOR c3} ---\n");
Print("Is T11 a permutation matrix? ", ForAll(Concatenation(T11), x -> x = 0 or x = 1), " (entries 0/1)\n");
Print("Each row of T11 sums to 1? ", ForAll(T11, row -> Sum(row) = 1), "\n");
Print("Each col of T11 sums to 1? ", ForAll(TransposedMat(T11), col -> Sum(col) = 1), "\n");
Print("Order of T11: ", Order(T11), "\n");

QUIT;
