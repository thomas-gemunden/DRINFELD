# Port of section 6 of the Magma supplement (Keller-Roberts-Roberts,
# arXiv:2411.13646): the defect representation for g = -I (the central
# element z of E(m)), and the brute-force Schur-averaging routine
# `InterTwineref` (Magma line 912) used to compute matrix entries of the
# intertwiners T_h on Omega_0.
#
# This is a *pure library* file (no QUIT). The m=3 verification driver
# is `test_defect_rep_m3.g`.
#
# What this file ports (Magma line numbers in parentheses):
#
#   1.  Symplectic basis for N = L/2L         (BasisForN, lines 476-485)
#   2.  Two-cocycle P of rho on N             (TwoCocycleForN, line 487)
#   3.  Cocycle delta_h := P_h - P            (DeltaHHalf, line 504)
#   4.  Auxiliary BigPi, Kernef, MhHalfef     (lines 721-778)
#   5.  Brute-force Schur sum InterTwineref   (line 912)
#   6.  Driver BuildIntertwinerAR that assembles the 2^k x 2^k matrix
#       T_h for h in {Sigma_{a,r}}, used in the m=3 verification.
#
# We do NOT port the optimisation pipeline (Finder, FinderNext,
# HardCodeFinder, HardCodeShortComputeInterTwineref, the efCoeff* helpers
# of section 5/6 used to evaluate entries without summation). Those will
# be ported separately and are only needed for m >= 5 efficiency.
#
# Conventions: F_2 stuff is held as plain Integer matrices and reduced
# mod 2 explicitly. Function names in CamelCase mirror the Magma ones
# closely; helpers prefixed with F2_ are extra GAP-only utilities.
#
# Basis-of-N caveat: Magma's `BasisForN` calls `WittDecomposition` on a
# symplectic space defined over GF(2). Magma's specific Witt
# decomposition is not documented in detail and we do not attempt to
# replicate it bit-for-bit. Our `SymplecticBasisF2` produces a
# *different* but equally valid symplectic basis. Because the
# intertwiners T_h depend on the choice of symplectic basis, our
# computed matrices will not match the paper's explicit formulas
# (4.4.3)-(4.4.8) element-wise — but they encode the same projective
# representation up to a basis change of Omega_0 induced by the
# basis-of-N choice. The substantive paper claim for m=3 (eqs (4.4.1)
# and (4.4.2): T_ar^2 = scalar*I and pairwise commutativity, hence
# trivial 2-cocycle) is reproduced exactly. See `test_defect_rep_m3.g`
# for the verification.

# Dependencies (the test driver Reads these first):
#   bw_lattice.g            -> BWGram, HalfGram
#   em_construction.g       -> Sigma_ar, ZGen
#   twisted_group_algebra.g -> UnimodSigma, UnimodZ
#   qforms_f2.g             -> F2Mod, F2RREF, F2RowAdd, F2LeftNullspace,
#                              F2ModVec, F2RowSpanBasis
#
# All functions below assume those globals are loaded.


# ============================================================
# F_2 linear-algebra helpers (extra to qforms_f2.g)
# ============================================================

# Solve x * M = b over F_2, where M is a list of m row vectors (each of
# length n) and b has length n. Returns either a length-m vector x with
# x * M = b (mod 2), or `fail` if no solution.
F2_SolveRowEq := function(M, b)
    local mLen, n, A, i, j, c, r, x, pivCols, k;
    mLen := Length(M);
    if mLen = 0 then
        if ForAll(b, e -> e mod 2 = 0) then return []; fi;
        return fail;
    fi;
    n := Length(M[1]);
    # Solve x*M = b: equivalent to M^T * x^T = b^T. Build augmented
    # n x (m+1) matrix [M^T | b^T] and row-reduce over F_2.
    A := List([1..n], i -> Concatenation(List([1..mLen], j -> M[j][i] mod 2),
                                         [b[i] mod 2]));
    r := 1;
    pivCols := [];
    for c in [1..mLen] do
        if r > n then break; fi;
        i := r;
        while i <= n and A[i][c] = 0 do i := i + 1; od;
        if i > n then continue; fi;
        if i <> r then A{[r, i]} := A{[i, r]}; fi;
        for j in [1..n] do
            if j <> r and A[j][c] = 1 then
                A[j] := List([1..mLen+1], k -> (A[j][k] + A[r][k]) mod 2);
            fi;
        od;
        Add(pivCols, c);
        r := r + 1;
    od;
    # Inconsistency check: any row with all-zero on M^T side but a 1 in b?
    for i in [r..n] do
        if A[i][mLen+1] = 1 then return fail; fi;
    od;
    # Back-substitute. Free variables get 0.
    x := List([1..mLen], i -> 0);
    for i in [1..Length(pivCols)] do
        x[pivCols[i]] := A[i][mLen+1];
    od;
    return x;
end;;

# Inverse of an n x n F_2 matrix M; `fail` if singular over F_2.
F2_Inverse := function(M)
    local n, A, c, r, i, j, k, inv, eye;
    n := Length(M);
    if n = 0 then return []; fi;
    eye := IdentityMat(n);
    A := List([1..n], i ->
        Concatenation(List([1..n], j -> M[i][j] mod 2), eye[i]));
    r := 1;
    for c in [1..n] do
        if r > n then break; fi;
        i := r;
        while i <= n and A[i][c] = 0 do i := i + 1; od;
        if i > n then return fail; fi;
        if i <> r then A{[r, i]} := A{[i, r]}; fi;
        for j in [1..n] do
            if j <> r and A[j][c] = 1 then
                A[j] := List([1..2*n], k -> (A[j][k] + A[r][k]) mod 2);
            fi;
        od;
        r := r + 1;
    od;
    if r <> n + 1 then return fail; fi;
    inv := List([1..n], i -> A[i]{[n+1..2*n]});
    return inv;
end;;

# Multiply two F_2 matrices (lists of integer rows), reducing mod 2.
F2_Mul := function(A, B)
    local mLen, n, p, C, i, j, k, s;
    mLen := Length(A);
    if mLen = 0 then return []; fi;
    n := Length(A[1]);
    p := Length(B[1]);
    C := List([1..mLen], i -> List([1..p], j -> 0));
    for i in [1..mLen] do
        for j in [1..p] do
            s := 0;
            for k in [1..n] do
                s := s + A[i][k] * B[k][j];
            od;
            C[i][j] := s mod 2;
        od;
    od;
    return C;
end;;

# F_2 matrix-vector product: M (mLen x n) times row vector v (length n),
# treating both as F_2 and reducing.  Returns row of length mLen via
# v -> M * v interpreted as v[i] = sum_j M[i][j] * (something), i.e.
# this is **column** mult.  Use the row-vector convention helpers below.

# Row-vector times matrix: returns v * M  (length cols of M).
F2_VMul := function(v, M)
    local n, p, out, j, k, s;
    if Length(M) = 0 then return []; fi;
    n := Length(v);
    p := Length(M[1]);
    out := List([1..p], j -> 0);
    for j in [1..p] do
        s := 0;
        for k in [1..n] do s := s + v[k] * M[k][j]; od;
        out[j] := s mod 2;
    od;
    return out;
end;;

# Matrix times column-vector: returns M * v^T as a row of length rows(M).
F2_MVec := function(M, v)
    local mLen, n, out, i, j, s;
    if Length(M) = 0 then return []; fi;
    mLen := Length(M);
    n := Length(v);
    out := List([1..mLen], i -> 0);
    for i in [1..mLen] do
        s := 0;
        for j in [1..n] do s := s + M[i][j] * v[j]; od;
        out[i] := s mod 2;
    od;
    return out;
end;;

# F_2 transpose.
F2_Trans := function(M)
    local mLen, n, R, i, j;
    mLen := Length(M);
    if mLen = 0 then return []; fi;
    n := Length(M[1]);
    R := List([1..n], i -> List([1..mLen], j -> 0));
    for i in [1..mLen] do
        for j in [1..n] do R[j][i] := M[i][j] mod 2; od;
    od;
    return R;
end;;

# Add two F_2 matrices.
F2_Add := function(A, B)
    return List([1..Length(A)], i ->
        List([1..Length(A[1])], j -> (A[i][j] + B[i][j]) mod 2));
end;;

# Identity n x n over F_2.
F2_Identity := function(n)
    return IdentityMat(n);
end;;

# Zero-row vector of length n (Integer entries).
F2_ZeroVec := function(n)
    return List([1..n], i -> 0);
end;;

# Bit decomposition: integer i (0 <= i < 2^d) -> length-d F_2 row vector,
# bit 0 in position 1, etc.
F2_BitsOfLen := function(i, d)
    local k;
    return List([1..d], k -> QuoInt(i, 2^(k-1)) mod 2);
end;;

# Inner product (F_2 scalar) of two same-length row vectors.
F2_Dot := function(u, v)
    local s, i;
    s := 0;
    for i in [1..Length(u)] do s := s + u[i] * v[i]; od;
    return s mod 2;
end;;

# u * Q * v^T  (F_2 scalar) for square F_2 matrix Q.
F2_QuadDot := function(u, Q, v)
    local n, s, i, j;
    n := Length(u);
    s := 0;
    for i in [1..n] do
        for j in [1..n] do s := s + u[i] * Q[i][j] * v[j]; od;
    od;
    return s mod 2;
end;;


# ============================================================
# Symplectic basis of (N, C) over F_2
# ============================================================

# Given an alternating bilinear form on F_2^{2k} represented by a 2k x 2k
# matrix C (with zero diagonal), produce a 2k x 2k matrix B over F_2
# whose rows are alpha_1, ..., alpha_k, beta_1, ..., beta_k, satisfying
#       B * C * B^T  =  [ 0  I_k ]
#                       [ I_k  0 ]
# (i.e. C(alpha_i, beta_j) = delta_{ij}, others zero).
#
# Algorithm: Witt-decomposition style. We maintain a list of standard
# basis vectors that span the current orthogonal complement of the
# already-extracted hyperbolic planes. At each step we pick the
# lexicographically smallest pair (e_i, e_j) (with i < j) inside the
# complement that pairs to 1; if no such pair of pure standard vectors
# exists we fall back to a hyperbolic pair within the abstract complement.
# The algorithm is designed to mimic Magma's `WittDecomposition` output
# as closely as possible (Magma picks standard basis vectors when it
# can).
SymplecticBasisF2 := function(C)
    local n, k, alphas, betas, i, j, v, w, x, c1, c2, e, ee,
          pairs, otherStd, otherCombo, found, idxV, idxW;
    n := Length(C);
    if n = 0 then return []; fi;
    if n mod 2 <> 0 then
        Error("SymplecticBasisF2: matrix must have even size");
    fi;
    k := n / 2;
    pairs := [];
    # otherStd: list of "clean" standard basis vectors still in the
    # current orthogonal complement (kept untouched as long as they pair
    # trivially with all already-extracted v's and w's).
    # otherCombo: list of "messy" linear combinations introduced by the
    # orthogonalization step. We try to find pairs from otherStd first,
    # otherwise we have to pair a vector from otherCombo (or split
    # otherStd against otherCombo).
    otherStd := List([1..n], i -> F2_BitsOfLen(2^(i-1), n));
    otherCombo := [];
    while Length(otherStd) + Length(otherCombo) >= 2 do
        v := fail;
        w := fail;
        # 1) Look for a pair entirely in otherStd.
        for i in [1..Length(otherStd)] do
            for j in [i+1..Length(otherStd)] do
                if F2_QuadDot(otherStd[i], C, otherStd[j]) = 1 then
                    v := otherStd[i]; w := otherStd[j];
                    idxV := i; idxW := j;
                    break;
                fi;
            od;
            if v <> fail then break; fi;
        od;
        # 2) If not found, look for a pair in otherStd x otherCombo.
        if v = fail then
            for i in [1..Length(otherStd)] do
                for j in [1..Length(otherCombo)] do
                    if F2_QuadDot(otherStd[i], C, otherCombo[j]) = 1 then
                        v := otherStd[i]; w := otherCombo[j];
                        idxV := i; idxW := -j;     # negative => combo
                        break;
                    fi;
                od;
                if v <> fail then break; fi;
            od;
        fi;
        # 3) If still nothing, look entirely in otherCombo.
        if v = fail then
            for i in [1..Length(otherCombo)] do
                for j in [i+1..Length(otherCombo)] do
                    if F2_QuadDot(otherCombo[i], C, otherCombo[j]) = 1 then
                        v := otherCombo[i]; w := otherCombo[j];
                        idxV := -i; idxW := -j;
                        break;
                    fi;
                od;
                if v <> fail then break; fi;
            od;
        fi;
        if v = fail then
            Error("SymplecticBasisF2: form became degenerate");
        fi;
        Add(pairs, [v, w]);
        # Remove v, w from their lists.
        if idxV > 0 then Remove(otherStd, idxV); fi;
        if idxW > 0 then
            # idxW was the index in otherStd; after we removed idxV it shifted.
            if idxV > 0 and idxW > idxV then idxW := idxW - 1; fi;
            Remove(otherStd, idxW);
        elif idxW < 0 then
            Remove(otherCombo, -idxW);
        fi;
        if idxV < 0 then
            Remove(otherCombo, -idxV);
        fi;
        # Orthogonalize remaining vectors against {v, w}: x' = x + C(x,w)*v
        # + C(x,v)*w. Apply to both lists; standards that get modified
        # move to otherCombo.
        i := 1;
        while i <= Length(otherStd) do
            x := otherStd[i];
            c1 := F2_QuadDot(x, C, v);
            c2 := F2_QuadDot(x, C, w);
            if c1 = 0 and c2 = 0 then
                i := i + 1;
            else
                e := List([1..n], idxV -> (x[idxV] + c2*v[idxV] + c1*w[idxV]) mod 2);
                Remove(otherStd, i);
                if not ForAll(e, ee -> ee = 0) then
                    Add(otherCombo, e);
                fi;
            fi;
        od;
        i := 1;
        while i <= Length(otherCombo) do
            x := otherCombo[i];
            c1 := F2_QuadDot(x, C, v);
            c2 := F2_QuadDot(x, C, w);
            if c1 = 0 and c2 = 0 then
                i := i + 1;
            else
                e := List([1..n], idxV -> (x[idxV] + c2*v[idxV] + c1*w[idxV]) mod 2);
                otherCombo[i] := e;
                if ForAll(e, ee -> ee = 0) then
                    Remove(otherCombo, i);
                else
                    i := i + 1;
                fi;
            fi;
        od;
    od;
    alphas := List(pairs, p -> p[1]);
    betas  := List(pairs, p -> p[2]);
    if Length(alphas) <> k or Length(betas) <> k then
        Error("SymplecticBasisF2: rank mismatch ", Length(alphas), " vs ", k);
    fi;
    return Concatenation(alphas, betas);
end;;


# ============================================================
# Section 4 of Magma: BasisForN and TwoCocycleForN
# ============================================================

# Cache for BasisForN(m) so we don't recompute for every InterTwineref
# call. Indexed by m.
_BasisForN_cache := [];;
_TwoCocycleForN_cache := [];;

# Symplectic basis of N = L/2L for g = -I.
BasisForN := function(m)
    local n, G, C, i, j, B;
    if IsBound(_BasisForN_cache[m]) then
        return _BasisForN_cache[m];
    fi;
    n := 2^m;
    G := BWGram(m);
    C := List([1..n], i -> List([1..n], j -> G[i][j] mod 2));
    for i in [1..n] do C[i][i] := 0; od;
    B := SymplecticBasisF2(C);
    _BasisForN_cache[m] := B;
    return B;
end;;

# Cocycle P for the defect representation rho on N.
# In the symplectic basis it is the upper-triangular part of the
# alternating form, i.e. R = [[0, I_k], [0, 0]] (R_{1/2} of paper eq 4.2.3).
TwoCocycleForN := function(m)
    local n, k, B, G, R, i, j;
    if IsBound(_TwoCocycleForN_cache[m]) then
        return _TwoCocycleForN_cache[m];
    fi;
    n := 2^m;
    k := 2^(m-1);
    B := BasisForN(m);
    G := BWGram(m);
    R := F2_Mul(F2_Mul(B, F2Mod(G)), F2_Trans(B));
    for i in [1..k] do
        for j in [1..k] do R[k + i][j] := 0; od;
    od;
    for i in [1..n] do R[i][i] := 0; od;
    _TwoCocycleForN_cache[m] := R;
    return R;
end;;


# ============================================================
# h-dependent matrices: H, BigPi, Kernef, DeltaHHalf, MhHalfef
# ============================================================

# Action of h on N in the symplectic basis: H = B * h * B^{-1} (F_2).
HinSympBasis := function(h, m)
    local B, hF2, Binv;
    B := BasisForN(m);
    hF2 := F2Mod(h);
    Binv := F2_Inverse(B);
    if Binv = fail then
        Error("BasisForN(", m, ") is not invertible over F_2");
    fi;
    return F2_Mul(F2_Mul(B, hF2), Binv);
end;;

# RightHalf of an (rows x cols) F_2 matrix M: take columns (cols/2)+1..cols.
F2_RightHalf := function(M)
    local cols, k;
    if Length(M) = 0 then return []; fi;
    cols := Length(M[1]);
    k := cols / 2;
    return List(M, row -> row{[k + 1 .. cols]});
end;;

# proj2(I_n) in Magma's convention: returns an n x k F_2 matrix with the
# top half zero and the bottom half I_k  (k = n/2).
F2_Proj2NK := function(n)
    local k, P, i;
    k := n / 2;
    P := List([1..n], i -> List([1..k], j -> 0));
    for i in [1..k] do P[k + i][i] := 1; od;
    return P;
end;;

# BigPi(h, m): the n x n F_2 matrix [RightHalf(H) | Proj2NK(I_n)].
# A row vector y in N has image (y * RightHalf(H), bottom-half(y)).
BigPi := function(h, m)
    local n, H, RH, P2, i;
    n := 2^m;
    H := HinSympBasis(h, m);
    RH := F2_RightHalf(H);
    P2 := F2_Proj2NK(n);
    return List([1..n], i -> Concatenation(RH[i], P2[i]));
end;;

# Basis of {y : y * BigPi(h) = 0} (left nullspace).
Kernef := function(h, m)
    return F2LeftNullspace(BigPi(h, m));
end;;

# Strictly upper-triangular part of an F_2 matrix.
F2_UpperStrict := function(M)
    local n, R, i, j;
    n := Length(M);
    R := List([1..n], i -> List([1..n], j -> 0));
    for i in [1..n] do
        for j in [i+1..n] do R[i][j] := M[i][j] mod 2; od;
    od;
    return R;
end;;

# DeltaHHalf(h, m): in Magma this is
#   Transpose(LowerTriangularize(TwoCocycleForN(m) + TwoCocycleForNOfa(h))).
# Magma's LowerTriangularize zeroes entries with i <= j, leaving entries
# with i > j alone. Its transpose puts those entries strictly above the
# diagonal. Equivalently: take the strictly upper-triangular part of
#       TwoCocycleForN(m) + (B*h*B^-1) * R * (B*h*B^-1)^T.
DeltaHHalfMatrix := function(h, m)
    local R, H, Bhalf, sum;
    R := TwoCocycleForN(m);
    H := HinSympBasis(h, m);
    Bhalf := F2_Mul(F2_Mul(H, R), F2_Trans(H));
    sum := F2_Add(R, Bhalf);
    return F2_UpperStrict(sum);
end;;

# RhHalfef(h) = H * R * H^T  (Magma RhHalfef).
RhHalfef := function(h, m)
    local R, H;
    R := TwoCocycleForN(m);
    H := HinSympBasis(h, m);
    return F2_Mul(F2_Mul(H, R), F2_Trans(H));
end;;

# MhHalfef(h, m) = DeltaHHalf(h) + RhHalfef(h)  (Magma MhHalfef).
MhHalfefMat := function(h, m)
    return F2_Add(DeltaHHalfMatrix(h, m), RhHalfef(h, m));
end;;


# ============================================================
# Brute-force Schur sum: InterTwineref
# ============================================================

# Magma's Insertc: vector c of length k -> length-2k vector (0, c).
F2_Insertc := function(c)
    local k;
    k := Length(c);
    return Concatenation(F2_ZeroVec(k), c);
end;;

# Compute the (c, d) entry of the sh-modified intertwiner T_h^{e, f} on
# Omega_0, by brute-force summation over the kernel of BigPi(h).
# Mirrors Magma `InterTwineref` (line 912).
#
# Inputs:
#   h : integer matrix, the unimodular generator (UnimodSigma / UnimodZ)
#   c, d, e, f : F_2 vectors of length k = 2^{m-1}
#   sh : F_2 vector of length 2^m (the shift in B_h)
#   m : the rank parameter (so n = 2^m, k = 2^{m-1})
#
# Returns an integer (sum of +/- 1; equals (Schur sum) without the
# 1/sqrt(|N|) normalization -- we compare to the paper up to a global
# scalar per generator).
InterTwineref := function(h, c, d, e, f, sh, m)
    local n, k, R, H, Mhh, Pi, target, x, A, KerLen, total,
          a_quad, b_lin, g_const, rRow, q, i, j, l,
          MhhSym, vc, vf, vsh, w_extra, contrib, x_in, x_in_mat;
    n := 2^m;
    k := n / 2;
    R := TwoCocycleForN(m);
    H := HinSympBasis(h, m);
    Mhh := MhHalfefMat(h, m);
    Pi := BigPi(h, m);
    # target = (c+e, d+f), length n.
    target := Concatenation(
        List([1..k], i -> (c[i] + e[i]) mod 2),
        List([1..k], i -> (d[i] + f[i]) mod 2));
    # Particular x with x * Pi = target, or 0 if inconsistent.
    x := F2_SolveRowEq(Pi, target);
    if x = fail then return 0; fi;
    A := Kernef(h, m);
    KerLen := Length(A);
    # Compute g_const = x*Mhh*x^T + x*H*R*Insertc(c)^T + x*R*Insertc(f)^T
    #                 + x*sh^T  (over F_2)
    g_const := F2_QuadDot(x, Mhh, x);
    g_const := (g_const + F2_Dot(F2_VMul(F2_VMul(x, H), R),
                                 F2_Insertc(c))) mod 2;
    g_const := (g_const + F2_Dot(F2_VMul(x, R), F2_Insertc(f))) mod 2;
    g_const := (g_const + F2_Dot(x, sh)) mod 2;
    if KerLen = 0 then
        if g_const = 0 then return 1; else return -1; fi;
    fi;
    # a_quad = A * Mhh * A^T  (KerLen x KerLen, F_2).
    a_quad := F2_Mul(F2_Mul(A, F2Mod(Mhh)), F2_Trans(A));
    # b_lin (length KerLen) = x*(Mhh+Mhh^T)*A^T + Insertc(c)*R^T*H^T*A^T
    #                        + Insertc(f)*R^T*A^T + sh*A^T
    # First, x*(Mhh+Mhh^T) over F_2:
    MhhSym := List([1..n], i ->
        List([1..n], j -> (Mhh[i][j] + Mhh[j][i]) mod 2));
    b_lin := F2_VMul(F2_VMul(x, MhhSym), F2_Trans(A));
    # Add (Insertc(c)*R^T*H^T) * A^T:
    vc := F2_VMul(F2_Insertc(c), F2_Trans(R));
    vc := F2_VMul(vc, F2_Trans(H));
    contrib := F2_VMul(vc, F2_Trans(A));
    b_lin := List([1..KerLen], i -> (b_lin[i] + contrib[i]) mod 2);
    # Add (Insertc(f)*R^T) * A^T:
    vf := F2_VMul(F2_Insertc(f), F2_Trans(R));
    contrib := F2_VMul(vf, F2_Trans(A));
    b_lin := List([1..KerLen], i -> (b_lin[i] + contrib[i]) mod 2);
    # Add sh * A^T:
    vsh := List([1..n], i -> sh[i] mod 2);
    contrib := F2_VMul(vsh, F2_Trans(A));
    b_lin := List([1..KerLen], i -> (b_lin[i] + contrib[i]) mod 2);
    # Sum (-1)^Q over r in F_2^{KerLen}.
    total := 0;
    for i in [0..2^KerLen - 1] do
        rRow := F2_BitsOfLen(i, KerLen);
        q := g_const;
        # Quadratic part: r * a_quad * r^T
        q := q + F2_QuadDot(rRow, a_quad, rRow);
        # Linear part: b_lin . r
        q := q + F2_Dot(b_lin, rRow);
        if q mod 2 = 0 then
            total := total + 1;
        else
            total := total - 1;
        fi;
    od;
    return total;
end;;


# ============================================================
# Build the full intertwiner matrix for h on Omega_0
# ============================================================

# Encoding convention chosen to match m3_intertwiners_explicit.g:
#   index = 1 + c[1] + 2 c[2] + 4 c[3] + ... + 2^{k-1} c[k]
# i.e. low bit first.
EncodeBitVec := function(v)
    local idx, i;
    idx := 1;
    for i in [1..Length(v)] do
        idx := idx + v[i] * 2^(i-1);
    od;
    return idx;
end;;

DecodeBitVec := function(idx, k)
    local v, num, i;
    num := idx - 1;
    v := List([1..k], i -> 0);
    for i in [1..k] do
        v[i] := num mod 2;
        num := QuoInt(num, 2);
    od;
    return v;
end;;

# Build the 2^k x 2^k intertwiner matrix for h with elementary index
# (e, f) and shift sh. With e = f = 0, sh = 0 we should reproduce the
# paper's formulas (4.4.3)-(4.4.8) up to a per-generator scalar.
BuildIntertwiner := function(h, e, f, sh, m)
    local k, dim, M, ci, di, c, d, val;
    k := 2^(m-1);
    dim := 2^k;
    M := List([1..dim], i -> List([1..dim], j -> 0));
    for ci in [1..dim] do
        c := DecodeBitVec(ci, k);
        for di in [1..dim] do
            d := DecodeBitVec(di, k);
            val := InterTwineref(h, c, d, e, f, sh, m);
            M[di][ci] := val;
        od;
    od;
    return M;
end;;

# Convenience: build T_{a,r} with default e = f = 0, sh = 0.
BuildIntertwinerAR := function(m, a, r)
    local h, k, e, f, sh;
    h := UnimodSigma(m, a, r);
    k := 2^(m-1);
    e := F2_ZeroVec(k);
    f := F2_ZeroVec(k);
    sh := F2_ZeroVec(2^m);
    return BuildIntertwiner(h, e, f, sh, m);
end;;
