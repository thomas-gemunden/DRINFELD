# Construction of the Bolt-Room-Wall (BRW) group BRW(m), the normaliser
# of the extraspecial 2-group E_+(m) = 2_+^{2m+1} inside the orthogonal
# group on 2^m-dimensional space. The quotient BRW(m)/E_+(m) is the
# outer-automorphism group of E_+(m) acting orthogonally, which for
# plus-type extraspecial groups is O^+(2m, F_2).
#
# Construction (KRR-style, arXiv:2411.13646 section 2): take the Pauli
# generators σ_{a,r} (slot a in {1..m}, r in {1, 2}) and z = -I from
# em_construction.g, then adjoin the *real* Clifford generators that
# normalise the orthogonal form:
#
#     H = (1/√2) · [[1, 1], [1, -1]]   (Hadamard, 2x2; det = -1)
#     CZ = diag(1, 1, 1, -1)            (controlled-Z on slots (a, b))
#
# embedded by tensor product into slot a (for H) or slots (a, b) (for
# CZ). The Hadamard requires √2, so the matrix entries live in
# Q[√2] = Z[√2] inside the 8th cyclotomic field Q[ζ_8] (we use
# √2 = ζ_8 + ζ_8^{-1}). The phase gate D = diag(1, i) is intentionally
# NOT included: it generates the full Sp(2m, F_2) on the symplectic
# quotient instead of the orthogonal O^+(2m, F_2).
#
# Empirical results (m=2):
#   |BRW(2)|         = 2304 = 2 · |Aut(E_+(2))|.
#   The kernel of BRW(2) → Aut(E_+(2)) is the centre {±I}, order 2.
#   BRW(2)/E_+(2)    ≅ O^+(4, F_2) = (S_3 x S_3) : C_2, order 72.
#
# The "factor of 2" between |BRW(m)| and |Aut(E_+(m))| is the centre
# {±I_{2^m}} ⊂ BRW(m), which acts trivially on E_+(m) by conjugation.
#
# Reference: em_construction.g for E_+(m) generators (Sigma_ar, ZGen).

if not IsBound(Sigma_ar) then
    Read("em_construction.g");
fi;

# 8th root of unity: ζ_8 = exp(2πi/8) = (1 + i)/√2. We use
# √2 = ζ_8 + ζ_8^{-1} so that 1/√2 = (ζ_8 + ζ_8^{-1})/2 lives in
# Q[ζ_8] (in fact in the real subfield Q[√2] ⊂ Q[ζ_8]).
ZETA8 := E(8);;
SQRT2 := E(8) + E(8)^(-1);;       # = √2
INV_SQRT2 := SQRT2 / 2;;           # = 1/√2 = (ζ_8 + ζ_8^{-1})/2
IMAG := E(4);;                     # i (= ζ_4 = ζ_8^2)

# ---------------------------------------------------------------------
# Local 2x2 real-Clifford generators.
# ---------------------------------------------------------------------

# H = (1/√2) [[1, 1], [1, -1]]: real orthogonal (over Q[√2]), det = -1.
# Conjugation by H swaps σ_1 (X) with σ_2 (Z) and fixes σ_3 (Y) up to
# a sign — i.e. it induces the outer-aut swap of the two Pauli families.
HadamardGate := INV_SQRT2 * [[1, 1], [1, -1]];;

# CZ = diag(1, 1, 1, -1): real orthogonal on slots (a, b), det = -1.
# Conjugation by CZ adds the slot-b Pauli σ_2 onto the slot-a Pauli σ_1
# (and symmetrically), entangling the two slots in F_2^{2m}.
ControlledZRaw := [[1, 0, 0, 0],
                   [0, 1, 0, 0],
                   [0, 0, 1, 0],
                   [0, 0, 0, -1]];;

# Phase gate D = diag(1, i): complex, det = i. NOT used in BRW because
# it generates the full Sp(2m, F_2) (Clifford-mod-Pauli) rather than
# the orthogonal subgroup O^+(2m, F_2). Kept here only for reference.
PhaseGate := [[1, 0], [0, IMAG]];;

# ---------------------------------------------------------------------
# Embed a single-slot 2x2 gate G into slot a of an m-qubit system:
#     I_2 ⊗ ... ⊗ G ⊗ ... ⊗ I_2  (G in slot a, slots indexed 1..m from
#     the LEFT in the Kronecker product, matching Sigma_ar).
# ---------------------------------------------------------------------

EmbedGate := function(m, a, G)
    local factors, i;
    Assert(0, 1 <= a and a <= m, "a must be in 1..m");
    factors := [];
    for i in [1..m] do
        if i = a then
            Add(factors, G);
        else
            Add(factors, [[1, 0], [0, 1]]);
        fi;
    od;
    return TensorList(factors);
end;;

# ---------------------------------------------------------------------
# Embed a two-slot 4x4 gate G into slots (a, b) of an m-qubit system,
# with 1 <= a < b <= m. Basis vectors are indexed 0..2^m-1, with bit-
# string (i_1, ..., i_m) (i_1 most-significant; matches the Kronecker
# convention of EmbedGate/Sigma_ar).
#
# The gate G acts on the 4x4 block indexed by (i_a, i_b) and leaves
# the other m-2 slots untouched.
# ---------------------------------------------------------------------

EmbedTwoSlotGate := function(m, a, b, G)
    local n, M, x, y, ia, ib, ya, yb, i, j, x_bits, y_bits, c;
    Assert(0, 1 <= a and a < b and b <= m, "need 1 <= a < b <= m");
    Assert(0, Length(G) = 4 and Length(G[1]) = 4, "G must be 4x4");
    n := 2^m;
    M := NullMat(n, n);
    for x in [0..n-1] do
        x_bits := List([1..m], k -> (QuoInt(x, 2^(m - k))) mod 2);
        ia := x_bits[a]; ib := x_bits[b];
        i := 2*ia + ib + 1;
        for c in [0..3] do
            ya := QuoInt(c, 2); yb := c mod 2;
            j := c + 1;
            if G[j][i] <> 0 then
                y_bits := ShallowCopy(x_bits);
                y_bits[a] := ya; y_bits[b] := yb;
                y := Sum([1..m], k -> y_bits[k] * 2^(m - k));
                M[y+1][x+1] := M[y+1][x+1] + G[j][i];
            fi;
        od;
    od;
    return M;
end;;

# ---------------------------------------------------------------------
# BRW(m): generated by
#     - E_+(m) generators z = -I, σ_{a, r}            (from em_construction.g)
#     - Hadamard H in each slot a ∈ [1..m]
#     - CZ on each pair (a, b) with 1 <= a < b <= m
#
# Empirically verified at m=2:
#     |BRW(2)|              = 2304
#     [BRW(2) : E_+(2)]     = 72  = |O^+(4, F_2)|
#     Centralizer of E_+(2) = {±I}  (scalars; criterion 4)
#     BRW(2)/E_+(2)         = (S_3 x S_3) : C_2  (matches GO(1, 4, 2))
# ---------------------------------------------------------------------

BRW := function(m)
    local gens, a, b;
    Assert(0, m >= 1, "m must be a positive integer");
    gens := ShallowCopy(GeneratorsOfGroup(EmGroup(m)));
    # Hadamard in each slot.
    for a in [1..m] do
        Add(gens, EmbedGate(m, a, HadamardGate));
    od;
    # CZ on each (a, b) pair, a < b.
    for a in [1..m] do
        for b in [a+1..m] do
            Add(gens, EmbedTwoSlotGate(m, a, b, ControlledZRaw));
        od;
    od;
    return Group(gens);
end;;

# Convenience wrapper: given an extraspecial 2-group G of plus type with
# |G| = 2^{2m+1}, return BRW(m).
BrwGroup := function(G)
    local n, m;
    n := Order(G);
    Assert(0, IsInt(n) and n > 0 and (n mod 2) = 0,
           "Order of G must be a positive even integer.");
    m := LogInt(n, 2);
    Assert(0, m >= 3 and (m mod 2) = 1,
           "|G| = 2^{2m+1} requires odd exponent >= 3.");
    return BRW((m - 1) / 2);
end;;
