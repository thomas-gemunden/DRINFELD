# Port of section 6 (post-`InterTwineref`) of the Magma supplement
# (Keller-Roberts-Roberts, arXiv:2411.13646, BWOrbifoldsMagma.txt lines
# ~770-1320): the optimisation pipeline for the defect representation
# of g = -I.
#
# This is a *pure library* file (no QUIT). The verification driver is
# `test_defect_rep_optim.g`.
#
# What this file ports (Magma function names in parentheses):
#
#   1. EfCoeff1(h, m), EfCoeff2(h, e, f, c, d, m), EfCoeff3(h, e, f, c, d, m)
#      (Magma efCoeff1, efCoeff2, efCoeff3, lines 780-823): quadratic,
#      linear, and constant coefficients of the F_2 quadratic form
#      whose Schur sum gives an entry of T_h^{e,f}.
#   2. EfCoeff1New, EfCoeff2nNew, EfCoeff2d2New, EfCoeff2d1New,
#      EfCoeff3New, EfNew (Magma efCoeff1New ... efNew, lines 825-880):
#      change-of-basis versions that put the quadratic form alpha^h in
#      standard form via QuadStandardFormChar2*.
#   3. Xefcd(h, e, f, c, d, m) (Magma Xefcd, line 785): a particular
#      solution of x * BigPi(h) = (c+e, f+d).
#   4. RealB(h, m) (Magma RealB, line 935; same as BPiInverse).
#   5. Finder, FinderNext, FinalFinder, HardCodeFinder, HardCodeFinderNext,
#      HardCodeFinalFinder (lines 943-1030): linear-system solver that
#      finds e, f, c, d making the (c, d) entry of T_h^{e,f} non-zero.
#   6. ShortComputeInterTwineref, HardCodeShortComputeInterTwineref,
#      HardCodeShortComputeInterTwinerefWithX (lines 1032-1082, 1263-1267):
#      the closed-form Gauss sum.
#   7. ProductFinder, ProductFinderNext, ProductFinderNextAlt,
#      HardCodeProductFinder, HardCodeProductFinderNext (lines 1085-1217):
#      linear-system solver that picks intermediate b's making
#      T_{h1}^{e1,f1}_{c, b} * T_{h2}^{e2,f2}_{b, d} non-zero.
#   8. HardCodeShortComputeProductCoordinateef and
#      ShortComputeProductCoordinateef (lines 1283-1318): wrapper that
#      evaluates one entry of the product T_{h1} T_{h2}.
#
# Dependencies (already loaded by the test driver):
#   bw_lattice.g, em_construction.g, twisted_group_algebra.g,
#   qforms_f2.g, defect_rep_minus_id.g.

# ============================================================
# Small extra F_2 helpers
# ============================================================

# Override F2_Mul, F2_VMul, F2_Trans, F2_Add from defect_rep_minus_id.g
# with faster GAP-builtin-based versions.  GAP's IntegerMatrix * is
# orders of magnitude faster than the manual loops in defect_rep_minus_id.g
# for n=64 and above; we then reduce mod 2.
F2_Mul := function(A, B)
    local p;
    if Length(A) = 0 then return []; fi;
    if Length(B) = 0 or Length(B[1]) = 0 then
        return List(A, r -> []);
    fi;
    p := A * B;   # GAP integer matrix multiplication
    return List(p, row -> List(row, x -> x mod 2));
end;;

F2_VMul := function(v, M)
    local p;
    if Length(M) = 0 then return []; fi;
    p := v * M;   # row vector times matrix
    return List(p, x -> x mod 2);
end;;

F2_Trans := function(M)
    if Length(M) = 0 then return []; fi;
    return List(TransposedMat(M), row -> List(row, x -> x mod 2));
end;;

F2_Add := function(A, B)
    if Length(A) = 0 then return []; fi;
    return List([1..Length(A)], i ->
        List([1..Length(A[1])], j -> (A[i][j] + B[i][j]) mod 2));
end;;

# Override MatOfBilForm with a closed-form O(n^2) version: the bilinear
# form B associated to Q is simply (q + q^T) (mod 2).  The original
# implementation in qforms_f2.g loops over all (i, j) and evaluates
# QFormEval three times per pair, giving O(n^4) cost.  At n = 64 (= dim K
# for m = 7) that becomes the dominant cost in the section-6 pipeline,
# so we replace it with the direct formula.
MatOfBilForm := function(q)
    local n, M, i, j;
    n := Length(q);
    if n = 0 then return []; fi;
    M := List([1..n], i -> List([1..n], j -> 0));
    for i in [1..n] do
        for j in [1..n] do
            M[i][j] := (q[i][j] + q[j][i]) mod 2;
        od;
        M[i][i] := 0;   # B(e_i, e_i) = 0 (alternating; over F_2 this is 2 q[i][i] = 0)
    od;
    return M;
end;;

# LeftHalf of a single row (length-2k vector): first k coords.
F2_LeftHalfVec := function(v)
    local k;
    k := Length(v) / 2;
    return v{[1..k]};
end;;

# RightHalf of a single row.
F2_RightHalfVec := function(v)
    local k;
    k := Length(v) / 2;
    return v{[k+1..2*k]};
end;;

# LeftHalf of an F_2 matrix M (rows x cols): take columns 1..cols/2.
F2_LeftHalf := function(M)
    local cols, k;
    if Length(M) = 0 then return []; fi;
    cols := Length(M[1]);
    k := cols / 2;
    return List(M, row -> row{[1..k]});
end;;

# Solve a system of linear equations  X * M = b  over F_2 (X has length
# rows(M) per row of b).  Here `b` is a list-of-rows.  Returns a record
# with .particular (one solution per row of b) and .nullspace (basis of
# {x : x * M = 0}).  If any row of b is inconsistent, .particular is
# `fail`.
F2_SolveRowEqAll := function(M, bRows)
    local mLen, n, A, i, j, c, r, k, pivCols, freeCols, sols, kerBasis,
          rhsCol, x, p, sol, inconsistent, b, eye;
    mLen := Length(M);
    if mLen = 0 then
        # X is the empty vector. Solution iff every row of b is zero.
        for b in bRows do
            if not ForAll(b, e -> e mod 2 = 0) then
                return rec(particular := fail, nullspace := []);
            fi;
        od;
        return rec(particular := List(bRows, b -> []), nullspace := []);
    fi;
    n := Length(M[1]);
    # Augment M^T with identity on the right and one column per row of b
    # on the very right.  We row-reduce on M^T.
    A := List([1..n], i -> Concatenation(
            List([1..mLen], j -> M[j][i] mod 2),
            List(bRows, b -> b[i] mod 2)));
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
                A[j] := List([1..mLen + Length(bRows)],
                              k -> (A[j][k] + A[r][k]) mod 2);
            fi;
        od;
        Add(pivCols, c);
        r := r + 1;
    od;
    # Inconsistency: any zero row of M^T-side with non-zero in any RHS.
    inconsistent := false;
    sols := List(bRows, b -> List([1..mLen], k -> 0));
    for i in [r..n] do
        for k in [1..Length(bRows)] do
            if A[i][mLen + k] = 1 then
                inconsistent := true;
            fi;
        od;
    od;
    if inconsistent then
        return rec(particular := fail, nullspace := []);
    fi;
    for i in [1..Length(pivCols)] do
        for k in [1..Length(bRows)] do
            sols[k][pivCols[i]] := A[i][mLen + k];
        od;
    od;
    # Nullspace basis: free columns.
    freeCols := Filtered([1..mLen], c -> not (c in pivCols));
    kerBasis := [];
    for c in freeCols do
        x := List([1..mLen], i -> 0);
        x[c] := 1;
        for i in [1..Length(pivCols)] do
            x[pivCols[i]] := A[i][c];
        od;
        Add(kerBasis, x);
    od;
    return rec(particular := sols, nullspace := kerBasis);
end;;

# Single-row convenience: solve x * M = b, return one particular x or
# `fail`.  (Mirrors F2_SolveRowEq but reuses the augmented-form solver.)
F2_SolveOneRow := function(M, b)
    local res;
    res := F2_SolveRowEqAll(M, [b]);
    if res.particular = fail then return fail; fi;
    return res.particular[1];
end;;

# Magma's `Insertc`: vector c of length k -> length-2k vector (0_k, c).
# (Already in defect_rep_minus_id.g as F2_Insertc; we mirror the name.)
EfInsertc := F2_Insertc;;


# ============================================================
# Section 6 helpers: RealB, Xefcd, EfCoeffs
# ============================================================

# RealB / BPiInverse: a basis matrix of a complement of Kernel(BigPi(h))
# inside F_2^{2^m}.  In Magma this uses the symplectic basis-of-N as the
# ambient space, but since BasisForN is invertible the ambient is just
# F_2^{2^m}.
RealB := function(h, m)
    local n, K, comp, ambient;
    n := 2^m;
    K := Kernef(h, m);
    ambient := F2StdBasis(n);
    comp := F2ComplementInBasis(ambient, K);
    return comp;
end;;

# Particular solution x of x * BigPi(h) = (c+e, f+d), or `fail`.
Xefcd := function(h, e, f, c, d, m)
    local n, k, target, Pi, x, i;
    n := 2^m;
    k := n / 2;
    Pi := BigPi(h, m);
    # Issue #381+#382 audit-followup (P3): closure-free vector add+mod.
    target := Concatenation((c + e) mod 2, (d + f) mod 2);
    x := F2_SolveOneRow(Pi, target);
    return x;
end;;

# EfCoeff1(h, m) = A * Mhh * A^T  (the matrix of the quadratic part of
# the Schur exponent in the kernel basis).
EfCoeff1 := function(h, m)
    local A, Mhh;
    A := Kernef(h, m);
    Mhh := MhHalfefMat(h, m);
    return F2_Mul(F2_Mul(A, F2Mod(Mhh)), F2_Trans(A));
end;;

# EfCoeff2(h, e, f, c, d, m): linear coefficient of the Schur exponent,
# *without* the shift sh contribution.
#   = x*(Mhh+Mhh^T)*A^T + Insertc(c)*R^T*H^T*A^T + Insertc(f)*R^T*A^T
EfCoeff2 := function(h, e, f, c, d, m)
    local n, A, R, Mhh, MhhSym, H, x, term1, term2, term3, ic, ifv,
          AT, RT;
    n := 2^m;
    A := Kernef(h, m);
    R := TwoCocycleForN(m);
    Mhh := MhHalfefMat(h, m);
    H := HinSympBasis(h, m);
    x := Xefcd(h, e, f, c, d, m);
    if x = fail then return fail; fi;
    # Issue #381+#382 audit-followup (P3): O(n^2) closure replaced by
    # one matrix add + mod via TransposedMat.
    MhhSym := (Mhh + TransposedMat(Mhh)) mod 2;
    AT := F2_Trans(A);
    RT := F2_Trans(R);
    term1 := F2_VMul(F2_VMul(x, MhhSym), AT);
    ic := EfInsertc(c);
    ifv := EfInsertc(f);
    term2 := F2_VMul(F2_VMul(F2_VMul(ic, RT), F2_Trans(H)), AT);
    term3 := F2_VMul(F2_VMul(ifv, RT), AT);
    # Issue #381+#382 audit-followup (P3): closure-free vector sum+mod.
    return (term1 + term2 + term3) mod 2;
end;;

# EfCoeff3(h, e, f, c, d, m): constant coefficient (Magma's efCoeff3,
# excluding the sh contribution).
#   = x*Mhh*x^T + x*H*R*Insertc(c)^T + x*R*Insertc(f)^T
EfCoeff3 := function(h, e, f, c, d, m)
    local n, R, Mhh, H, x, ic, ifv, q1, q2, q3;
    n := 2^m;
    R := TwoCocycleForN(m);
    Mhh := MhHalfefMat(h, m);
    H := HinSympBasis(h, m);
    x := Xefcd(h, e, f, c, d, m);
    if x = fail then return fail; fi;
    ic := EfInsertc(c);
    ifv := EfInsertc(f);
    q1 := F2_QuadDot(x, Mhh, x);
    q2 := F2_Dot(F2_VMul(F2_VMul(x, H), R), ic);
    q3 := F2_Dot(F2_VMul(x, R), ifv);
    return (q1 + q2 + q3) mod 2;
end;;


# ============================================================
# Standard-form versions: EfCoeff1New ... EfNew
# ============================================================

# Quadratic form alpha^h written in standard form (Magma efCoeff1New).
EfCoeff1New := function(h, m)
    return QuadStandardFormChar2CompleteForm(EfCoeff1(h, m));
end;;

# Coordinates of efCoeff2 in the basis where alpha^h's bilinear form is
# non-degenerate (the "n" piece).  Returns a row of length 0 if there is
# no non-degenerate part.
EfCoeff2nNew := function(h, e, f, c, d, m)
    local rst, r, b2;
    rst := QuadStandardFormChar2CompleteBasesSeparate(EfCoeff1(h, m));
    r := rst[1];
    if Length(r) = 0 then return []; fi;
    b2 := EfCoeff2(h, e, f, c, d, m);
    if b2 = fail then return fail; fi;
    return F2_VMul(b2, F2_Trans(r));
end;;

# Coordinates of efCoeff2 on the totally-isotropic part of the radical
# (Magma efCoeff2d2New, "the d2 piece"; q is identically 0 there).
EfCoeff2d2New := function(h, e, f, c, d, m)
    local rs, sp, b2;
    rs := SplitDegeneratePart(EfCoeff1(h, m));
    sp := rs[2];
    if Length(sp) = 0 then return []; fi;
    b2 := EfCoeff2(h, e, f, c, d, m);
    if b2 = fail then return fail; fi;
    return F2_VMul(b2, F2_Trans(sp));
end;;

# Coordinates of efCoeff2 on the anisotropic part of the radical
# (Magma efCoeff2d1New, "the d1 piece"; q == 1 there).
EfCoeff2d1New := function(h, e, f, c, d, m)
    local rs, an, b2;
    rs := SplitDegeneratePart(EfCoeff1(h, m));
    an := rs[1];
    if Length(an) = 0 then return []; fi;
    b2 := EfCoeff2(h, e, f, c, d, m);
    if b2 = fail then return fail; fi;
    return F2_VMul(b2, F2_Trans(an));
end;;

# Constant coefficient (same as EfCoeff3); kept for naming symmetry with
# the Magma original.
EfCoeff3New := function(h, e, f, c, d, m)
    return EfCoeff3(h, e, f, c, d, m);
end;;

# Returns the full quintuple (A, Bn, Bd1, Bd2, C) of the standard-form
# data; or `fail` if the system is inconsistent.
EfNew := function(h, e, f, c, d, m)
    local A, Bn, Bd1, Bd2, C, x;
    x := Xefcd(h, e, f, c, d, m);
    if x = fail then return fail; fi;
    A := EfCoeff1New(h, m);
    Bn := EfCoeff2nNew(h, e, f, c, d, m);
    Bd1 := EfCoeff2d1New(h, e, f, c, d, m);
    Bd2 := EfCoeff2d2New(h, e, f, c, d, m);
    C := EfCoeff3New(h, e, f, c, d, m);
    return rec(A := A, Bn := Bn, Bd1 := Bd1, Bd2 := Bd2, C := C);
end;;


# ============================================================
# Finder / FinderNext / FinalFinder
# ============================================================

# Concatenate a list of rows (column-stacked, i.e. VerticalJoin).
F2_VJoinRows := function(rowsList)
    return Concatenation(rowsList);
end;;

# HardCodeFinder(h, s, mhh, A, B, m): build the 4 building blocks of the
# linear system in (z, c, f) whose solution gives e, f, c, d making
# (T_h^{e,f})_{c,d} non-zero.
#   x1 = D * (mhh + mhh^T) * A^T * Sh^T            (rows |D|)
#   x2 = R^T * H^T * A^T * Sh^T                    (rows 2^m)
#   x3 = R^T * A^T * Sh^T                          (rows 2^m)
#   x4 = s * A^T * Sh^T                            (rows 1)
# where H = B*h*B^{-1} = HinSympBasis(h, m), D = RealB(h, m),
# Sh = VerticalJoin(b, a), and (a, b) = SplitDegeneratePart(efCoeff1(h)).
HardCodeFinder := function(h, s, mhh, A, B, m)
    local n, R, sd, an, sp, Sh, D, mhhSym, AT, ShT, x1, x2, x3, x4,
          H, RT, HT;
    n := 2^m;
    R := TwoCocycleForN(m);
    sd := SplitDegeneratePart(EfCoeff1(h, m));
    an := sd[1];   # anisotropic radical (q=1)
    sp := sd[2];   # isotropic radical (q=0)
    Sh := Concatenation(sp, an);    # b first, then a (Magma order)
    D := RealB(h, m);
    # Issue #381+#382 audit-followup (P3): O(n^2) closure replaced by
    # one matrix add + mod via TransposedMat.
    mhhSym := (mhh + TransposedMat(mhh)) mod 2;
    AT := F2_Trans(A);
    ShT := F2_Trans(Sh);
    x1 := F2_Mul(F2_Mul(F2_Mul(D, mhhSym), AT), ShT);
    H := HinSympBasis(h, m);
    RT := F2_Trans(R);
    HT := F2_Trans(H);
    x2 := F2_Mul(F2_Mul(F2_Mul(RT, HT), AT), ShT);
    x3 := F2_Mul(F2_Mul(RT, AT), ShT);
    x4 := F2_VMul(F2_VMul(s, AT), ShT);
    return rec(x1 := x1, x2 := x2, x3 := x3, x4 := x4);
end;;

# Convenience wrapper: like HardCodeFinder but recovers mhh, A from h.
Finder := function(h, s, m)
    local mhh, A, B;
    mhh := MhHalfefMat(h, m);
    A := Kernef(h, m);
    B := BasisForN(m);
    return HardCodeFinder(h, s, mhh, A, B, m);
end;;

# Build the target row t for the Finder system: zero on b followed by
# a 1 on a (when |a| = 1).  Returns the row t.
_FinderTargetRow := function(h, m)
    local sd, an, sp, t, i;
    sd := SplitDegeneratePart(EfCoeff1(h, m));
    an := sd[1];
    sp := sd[2];
    if Length(an) = 0 then
        return List([1..Length(sp)], i -> 0);
    elif Length(an) = 1 then
        t := List([1..Length(sp) + 1], i -> 0);
        t[Length(sp) + 1] := 1;
        return t;
    else
        Error("Finder: anisotropic radical has dim ", Length(an),
              " >= 2; this case is not handled by the Magma Finder.");
    fi;
end;;

# HardCodeFinderNext: solve the system for (z, c, f).  Returns a record
# with .z, .c, .f and .nullspace (so the caller can enumerate other
# solutions if needed).  If no solution exists returns `fail`.
HardCodeFinderNext := function(h, s, mhh, A, B, m)
    local fb, x1, x2, x3, x4, M, t, rhs, sol, nrz, nrc, nrf, ncols, k,
          n, k1, idx, sParticular;
    fb := HardCodeFinder(h, s, mhh, A, B, m);
    x1 := fb.x1; x2 := fb.x2; x3 := fb.x3; x4 := fb.x4;
    nrz := Length(x1);
    nrc := Length(x2);
    nrf := Length(x3);
    M := Concatenation(x1, x2, x3);
    t := _FinderTargetRow(h, m);
    if Length(M) = 0 then
        # No unknowns: only solvable if t = x4.
        if Length(x4) = 0 then return rec(z := [], c := [], f := []); fi;
        if List([1..Length(t)], i -> (t[i] - x4[i]) mod 2)
           = List([1..Length(t)], i -> 0) then
            return rec(z := [], c := [], f := []);
        fi;
        return fail;
    fi;
    rhs := List([1..Length(t)], i -> (t[i] - x4[i]) mod 2);
    sParticular := F2_SolveOneRow(M, rhs);
    if sParticular = fail then return fail; fi;
    return rec(z := sParticular{[1..nrz]},
               c := sParticular{[nrz + 1 .. nrz + nrc]},
               f := sParticular{[nrz + nrc + 1 .. nrz + nrc + nrf]});
end;;

# FinderNext: like HardCodeFinderNext but only takes h and s.
FinderNext := function(h, s, m)
    local mhh, A, B;
    mhh := MhHalfefMat(h, m);
    A := Kernef(h, m);
    B := BasisForN(m);
    return HardCodeFinderNext(h, s, mhh, A, B, m);
end;;

# HardCodeFinalFinder: convert the (z, c, f) returned by FinderNext back
# to (e, f, c, d) suitable for use as elementary-matrix indices.
#   x = z * RealB(h) * BigPi(h)
#   sum = x + c + f
#   e = LeftHalf(sum), d = RightHalf(sum), and we return RightHalf of
#   the inputs c, f as well to match the Magma signature.
# Returns rec(e, f, c, d) all as length-k row vectors.
HardCodeFinalFinder := function(h, s, mhh, A, B, m)
    local fn, n, k, D, Pi, x, sum, e, d, fOut, cOut, i;
    fn := HardCodeFinderNext(h, s, mhh, A, B, m);
    if fn = fail then return fail; fi;
    n := 2^m;
    k := n / 2;
    D := RealB(h, m);
    Pi := BigPi(h, m);
    if Length(fn.z) > 0 then
        x := F2_VMul(F2_VMul(fn.z, D), Pi);
    else
        x := List([1..n], i -> 0);
    fi;
    # c and f from the system are length 2^m; we take RightHalf to land
    # in F_2^k as elementary-matrix indices (matching Magma's
    # FinalFinder, which also takes RightHalf).
    # Issue #381+#382 audit-followup (P3): vectorise.
    sum := (x + fn.c + fn.f) mod 2;
    e := F2_LeftHalfVec(sum);
    d := F2_RightHalfVec(sum);
    fOut := F2_RightHalfVec(fn.f);
    cOut := F2_RightHalfVec(fn.c);
    return rec(e := e, f := fOut, c := cOut, d := d);
end;;

FinalFinder := function(h, s, m)
    local mhh, A, B;
    mhh := MhHalfefMat(h, m);
    A := Kernef(h, m);
    B := BasisForN(m);
    return HardCodeFinalFinder(h, s, mhh, A, B, m);
end;;


# ============================================================
# Closed-form Schur sum: HardCodeShortComputeInterTwineref
# ============================================================
#
# Closed-form evaluation of (T_h^{e, f})_{c, d}.  Following appendix C
# of arXiv:2411.13646, once we change basis of the kernel using
# Sh from QuadStandardFormChar2CompleteBasesTogether(EfCoeff1(h)), the
# F_2 quadratic form decomposes into
#   (a) r non-degenerate hyperbolic pairs                -> r=0 in our
#       Barnes-Wall cases (verified empirically; for any case where
#       r > 0 we Error rather than silently produce wrong output),
#   (b) s anisotropic 1-d blocks  Q(v) = 1 (s in {0, 1}),
#   (c) k - 2r - s isotropic blocks                      Q(v) = 0.
# Letting beta = efCoeff2 + s*A^T (the linear coefficient projected
# onto the kernel) and writing beta_tilde = beta * Sh^T, the sum
#   sum_y (-1)^{Q(y) + beta_tilde y + gamma}
# evaluates to 0 unless beta_tilde matches  (1, ..., 1, 0, ..., 0)
# (s ones then k-s-2r zeros) on the degenerate part.  When it does
# match, the result is  2^{k - 2r} * (-1)^{gamma + Sum beta_tilde
# pair-products}, which (with r = 0) simplifies to 2^k * (-1)^gamma.

# Cache for per-h data needed by the product code AND the closed-form
# single-entry code: bigPi, H, D, S (= ChangeBasesTogether), an, sp,
# nondeg.  Memoised by h identity/equality.
_efPerH_keys := [];;
_efPerH_vals := [];;

_efPerHData := function(h, m)
    local j, qf, sep, an, sp, nondeg, S, D, BPi, H, n, p1;
    for j in [1..Length(_efPerH_keys)] do
        if IsIdenticalObj(_efPerH_keys[j], h)
           or _efPerH_keys[j] = h then
            return _efPerH_vals[j];
        fi;
    od;
    n := 2^m;
    qf := EfCoeff1(h, m);
    # sep returns [nondeg, an, sp]; this single call replaces both
    # SplitDegeneratePart(qf) and QuadStandardFormChar2CompleteBasesTogether(qf).
    sep := QuadStandardFormChar2CompleteBasesSeparate(qf);
    nondeg := sep[1];
    an := sep[2];
    sp := sep[3];
    # S = nondeg + an + sp  (the matrix from QuadStandardFormChar2CompleteBasesTogether).
    S := Concatenation(nondeg, an, sp);
    D := RealB(h, m);
    BPi := BigPi(h, m);
    H := HinSympBasis(h, m);
    p1 := F2_Mul(D, BPi);
    Add(_efPerH_keys, h);
    Add(_efPerH_vals, rec(qf := qf, an := an, sp := sp, nondeg := nondeg,
                          S := S, ST := F2_Trans(S),
                          D := D, BPi := BPi, H := H, p1 := p1,
                          HT := F2_Trans(H), nrD := Length(D)));
    return _efPerH_vals[Length(_efPerH_vals)];
end;;

# Cache for _efShAndTarget: parallel lists `_efShAndTarget_keys`
# (matrix h's) and `_efShAndTarget_vals` (corresponding records).  We
# look up by IsIdenticalObj first (fast); fall back to equality (`=`).
_efShAndTarget_keys := [];;
_efShAndTarget_vals := [];;

# Given h and m, return rec(Sh, ShT, t, nDimAn, nDimSp, nDimND) where Sh
# is the change-of-basis matrix (rows: anisotropic radical first,
# isotropic radical next, non-degenerate pairs last) used to standardise
# alpha^h, t is the target row beta_bar projected onto Sh (rows |an|
# ones followed by zeros).  Memoised by h.  The same record is also
# stored on the corresponding _efPerHData record so that the per-h
# preprocessing (SplitDegeneratePart + QuadStandardFormChar2CompleteBasesSeparate)
# is shared between _efShAndTarget and _efPerHData.
_efShAndTarget := function(h, m)
    local sd, an, sp, sep, nondeg, kerLen, Sh, t, i, qf, result, ShT, j,
          hd;
    for j in [1..Length(_efShAndTarget_keys)] do
        if IsIdenticalObj(_efShAndTarget_keys[j], h)
           or _efShAndTarget_keys[j] = h then
            return _efShAndTarget_vals[j];
        fi;
    od;
    hd := _efPerHData(h, m);
    an := hd.an; sp := hd.sp;
    nondeg := hd.nondeg;
    kerLen := Length(an) + Length(sp) + Length(nondeg);
    Sh := Concatenation(an, sp, nondeg);
    t := List([1..kerLen], i -> 0);
    for i in [1..Length(an)] do t[i] := 1; od;
    ShT := F2_Trans(Sh);
    result := rec(Sh := Sh, ShT := ShT, t := t,
               nDimAn := Length(an),
               nDimSp := Length(sp),
               nDimND := Length(nondeg));
    Add(_efShAndTarget_keys, h);
    Add(_efShAndTarget_vals, result);
    return result;
end;;

# Closed-form (c, d) entry of T_h^{e, f} with shift sh.  Returns 0 if
# either (a) the system  x*BigPi = (c+e, f+d)  is inconsistent or
# (b) the linear coefficient beta_tilde does not match beta_bar on the
# radical part.  Otherwise returns
#     2^{dim K - 2r} * (-1)^{gamma + Sum_{i} beta_tilde_{2i-1}^h
#                                              beta_tilde_{2i}^h}.
HardCodeShortComputeInterTwineref := function(h, e, f, c, d, s, mhh, A, B, R, m)
    local x, H, ic, ifv, gammaConst, kerLen, sht, beta, betaTilde, betaPair,
          i, signExp, dimND, dimAn, dimSp, n, betaSum, hpairProduct,
          AT, sAT;
    x := Xefcd(h, e, f, c, d, m);
    if x = fail then return 0; fi;
    H := HinSympBasis(h, m);
    n := 2^m;
    kerLen := Length(A);
    ic := EfInsertc(c);
    ifv := EfInsertc(f);
    gammaConst := F2_QuadDot(x, mhh, x);
    gammaConst := (gammaConst
                   + F2_Dot(F2_VMul(F2_VMul(x, H), R), ic)) mod 2;
    gammaConst := (gammaConst + F2_Dot(F2_VMul(x, R), ifv)) mod 2;
    gammaConst := (gammaConst + F2_Dot(x, s)) mod 2;
    if kerLen = 0 then
        if gammaConst = 0 then return 1; else return -1; fi;
    fi;
    # Linear coefficient on the kernel:  beta = efCoeff2 + s * A^T.
    AT := F2_Trans(A);
    beta := EfCoeff2(h, e, f, c, d, m);
    sAT := F2_VMul(s, AT);
    # Issue #381+#382 audit-followup (P3): vectorise.
    beta := (beta + sAT) mod 2;
    # Bring to standard basis: beta_tilde = beta * Sh^T.
    sht := _efShAndTarget(h, m);
    betaTilde := F2_VMul(beta, sht.ShT);
    dimAn := sht.nDimAn;
    dimSp := sht.nDimSp;
    dimND := sht.nDimND;
    for i in [1..dimAn + dimSp] do
        if betaTilde[i] <> sht.t[i] then return 0; fi;
    od;
    hpairProduct := 0;
    for i in [1..dimND / 2] do
        hpairProduct := (hpairProduct
            + betaTilde[dimAn + dimSp + 2*i - 1]
              * betaTilde[dimAn + dimSp + 2*i]) mod 2;
    od;
    signExp := (gammaConst + hpairProduct) mod 2;
    if signExp = 0 then return 2^(kerLen - dimND); fi;
    return -(2^(kerLen - dimND));
end;;

# Variant without pre-computed mhh, A, B, R.
ShortComputeInterTwineref := function(h, e, f, c, d, s, m)
    return HardCodeShortComputeInterTwineref(h, e, f, c, d, s,
        MhHalfefMat(h, m), Kernef(h, m), BasisForN(m),
        TwoCocycleForN(m), m);
end;;

# Variant with pre-computed x = Xefcd(h, e, f, c, d, m) (used by the
# product code, which must reuse the x of the y enumeration).
HardCodeShortComputeInterTwinerefWithX := function(h, H, e, f, c, d, s, mhh,
                                                    A, B, R, x, m)
    local ic, ifv, gammaConst, kerLen, sht, beta, betaTilde, dimND, dimAn,
          dimSp, i, signExp, hpairProduct, n, mhhSym, AT, j, k1,
          xMhhSym, icRT, icRTHT, ifvRT, sAT, term1, term2, term3, term4;
    kerLen := Length(A);
    n := Length(mhh);
    ic := EfInsertc(c);
    ifv := EfInsertc(f);
    # gamma = x*Mhh*x^T + x*H*R*Insertc(c)^T + x*R*Insertc(f)^T + x*s^T
    gammaConst := F2_QuadDot(x, mhh, x);
    gammaConst := (gammaConst
                   + F2_Dot(F2_VMul(F2_VMul(x, H), R), ic)) mod 2;
    gammaConst := (gammaConst + F2_Dot(F2_VMul(x, R), ifv)) mod 2;
    gammaConst := (gammaConst + F2_Dot(x, s)) mod 2;
    if kerLen = 0 then
        if gammaConst = 0 then return 1; else return -1; fi;
    fi;
    # beta = x*(Mhh+Mhh^T)*A^T + Insertc(c)*R^T*H^T*A^T
    #        + Insertc(f)*R^T*A^T + s*A^T
    AT := F2_Trans(A);
    # Issue #381+#382 audit-followup (P3): vectorise.
    mhhSym := (mhh + TransposedMat(mhh)) mod 2;
    xMhhSym := F2_VMul(x, mhhSym);
    term1 := F2_VMul(xMhhSym, AT);
    icRT := F2_VMul(ic, F2_Trans(R));
    icRTHT := F2_VMul(icRT, F2_Trans(H));
    term2 := F2_VMul(icRTHT, AT);
    ifvRT := F2_VMul(ifv, F2_Trans(R));
    term3 := F2_VMul(ifvRT, AT);
    term4 := F2_VMul(s, AT);
    # Issue #381+#382 audit-followup (P3): vectorise.
    beta := (term1 + term2 + term3 + term4) mod 2;
    sht := _efShAndTarget(h, m);
    betaTilde := F2_VMul(beta, sht.ShT);
    dimAn := sht.nDimAn;
    dimSp := sht.nDimSp;
    dimND := sht.nDimND;
    for i in [1..dimAn + dimSp] do
        if betaTilde[i] <> sht.t[i] then return 0; fi;
    od;
    hpairProduct := 0;
    for i in [1..dimND / 2] do
        hpairProduct := (hpairProduct
            + betaTilde[dimAn + dimSp + 2*i - 1]
              * betaTilde[dimAn + dimSp + 2*i]) mod 2;
    od;
    signExp := (gammaConst + hpairProduct) mod 2;
    if signExp = 0 then return 2^(kerLen - dimND); fi;
    return -(2^(kerLen - dimND));
end;;


# ============================================================
# ProductFinder / HardCodeProductFinder
# ============================================================

# Helper: given an n x n F_2 matrix M, replace each row r by Insertc(LeftHalf(r))
# (so first half becomes 0 and second half becomes the original first
# half).  Mirrors the loop in Magma's ProductFinder building P from D2*BigPi(h2).
_PProjLeft := function(M)
    local n, k, P, i, j;
    n := Length(M);
    if n = 0 then return []; fi;
    k := Length(M[1]) / 2;
    P := List([1..n], i -> List([1..2 * k], j -> 0));
    for i in [1..n] do
        for j in [1..k] do
            P[i][k + j] := M[i][j] mod 2;
        od;
    od;
    return P;
end;;

# (Per-h cache is defined earlier, before _efShAndTarget; both share it.)

# HardCodeProductFinder: build the building blocks of the linear system
# whose solutions z parametrise all b's for which
# (T_{h1}^{e1, f1})_{c1, b} * (T_{h2}^{e2, f2})_{b, d2} is non-zero.
#
# Returns a record with .T1..T5 (the column blocks) and the metadata
# .nrD1, .nrD2 needed by ProductFinderNext.
HardCodeProductFinder := function(h1, e1, f1, c1, s1, mhh1, A1, B1,
                                   h2, e2, f2, d2, s2, mhh2, A2, B2, m)
    local n, k, R, S1, S2, D1, D2, b1, P, b2, ZL, ZR,
          T1, T2, T3, T4, T5, mhh1Sym, mhh2Sym, p1, p2, an1, sp1,
          an2, sp2, RT, H1, H2, BPi1, BPi2, ncolsS1, ncolsS2,
          nrD1, nrD2, ne, A1T, A2T, p1H, p2H, hd1, hd2, i, j;
    n := 2^m;
    k := n / 2;
    R := TwoCocycleForN(m);
    RT := F2_Trans(R);
    hd1 := _efPerHData(h1, m);
    hd2 := _efPerHData(h2, m);
    an1 := hd1.an; sp1 := hd1.sp; S1 := hd1.S; D1 := hd1.D;
    BPi1 := hd1.BPi; H1 := hd1.H; p1 := hd1.p1; nrD1 := hd1.nrD;
    an2 := hd2.an; sp2 := hd2.sp; S2 := hd2.S; D2 := hd2.D;
    BPi2 := hd2.BPi; H2 := hd2.H; p2 := hd2.p1; nrD2 := hd2.nrD;
    A1T := F2_Trans(A1);
    A2T := F2_Trans(A2);
    # Issue #381+#382 audit-followup (P3): vectorise.
    mhh1Sym := (mhh1 + TransposedMat(mhh1)) mod 2;
    mhh2Sym := (mhh2 + TransposedMat(mhh2)) mod 2;
    # b1 = D1 * Mh1 * A1^T   (rows nrD1, cols Nrows(A1))
    b1 := F2_Mul(F2_Mul(D1, mhh1Sym), A1T);
    # P = D2*BigPi(h2) (rows nrD2, cols n) but with each row replaced by
    # Insertc(LeftHalf(row)).
    P := _PProjLeft(p2);
    # b2 = D2*Mh2*A2^T + P * R^T * H2^T * A2^T
    b2 := F2_Mul(F2_Mul(D2, mhh2Sym), A2T);
    b2 := F2_Add(b2, F2_Mul(F2_Mul(F2_Mul(P, RT), hd2.HT), A2T));
    ncolsS1 := Length(S1);
    ncolsS2 := Length(S2);
    ZL := List([1..nrD2], i -> List([1..ncolsS1], j -> 0));
    ZR := List([1..nrD1], i -> List([1..ncolsS2], j -> 0));
    T1 := Concatenation(F2_Mul(b1, hd1.ST), ZL);
    T2 := Concatenation(ZR, F2_Mul(b2, hd2.ST));
    T3 := Concatenation(F2_RightHalf(p1), F2_LeftHalf(p2));
    ne := k;
    T4 := Concatenation(F2_LeftHalf(p1),
                        List([1..nrD2], i -> List([1..ne], j -> 0)));
    T5 := Concatenation(List([1..nrD1], i -> List([1..ne], j -> 0)),
                        F2_RightHalf(p2));
    return rec(T1 := T1, T2 := T2, T3 := T3, T4 := T4, T5 := T5,
               nrD1 := nrD1, nrD2 := nrD2,
               an1 := an1, sp1 := sp1, an2 := an2, sp2 := sp2,
               S1 := S1, S2 := S2,
               BPi1 := BPi1, BPi2 := BPi2,
               H1 := H1, H2 := H2,
               D1 := D1, D2 := D2);
end;;

# Convenience: like HardCodeProductFinder but recovers mhh and A from h.
ProductFinder := function(h1, e1, f1, c1, s1, h2, e2, f2, d2, s2, m)
    local mhh1, A1, B1, mhh2, A2, B2;
    mhh1 := MhHalfefMat(h1, m); A1 := Kernef(h1, m); B1 := BasisForN(m);
    mhh2 := MhHalfefMat(h2, m); A2 := Kernef(h2, m); B2 := BasisForN(m);
    return HardCodeProductFinder(h1, e1, f1, c1, s1, mhh1, A1, B1,
                                  h2, e2, f2, d2, s2, mhh2, A2, B2, m);
end;;

# Build the right-hand-side row V for the product system.  V is the
# concatenation V1, V2, V3, V4, V5 where
#   V1 = t1 + Insertc(c1)*R^T*H1^T*A1^T*Sh1^T + Insertc(f1)*R^T*A1^T*Sh1^T
#         + s1*A1^T*Sh1^T
#   V2 = t2 + Insertc(e2)*R^T*H2^T*A2^T*Sh2^T + Insertc(f2)*R^T*A2^T*Sh2^T
#         + s2*A2^T*Sh2^T
#   V3 = f1 + e2
#   V4 = c1 + e1
#   V5 = d2 + f2
# where Sh1 = VerticalJoin(an1, sp1), Sh2 = analogous, and t1 = (1, 0, ..., 0)
# if |an1| = 1 else zeros (similar for t2).
_ProductRhs := function(pf, e1, f1, c1, s1, A1, e2, f2, d2, s2, A2, m)
    local R, RT, Sh1, t1, Sh2, t2, ic1, if1, ic2, if2,
          v1, v2, v3, v4, v5, ATSh1T, ATSh2T, AT1, AT2, n, i;
    R := TwoCocycleForN(m);
    RT := F2_Trans(R);
    n := 2^m;
    if Length(pf.an1) = 0 then
        Sh1 := pf.sp1;
        t1 := List([1..Length(pf.sp1)], i -> 0);
    else
        Sh1 := Concatenation(pf.an1, pf.sp1);
        t1 := List([1..Length(pf.an1) + Length(pf.sp1)], i -> 0);
        t1[1] := 1;
    fi;
    if Length(pf.an2) = 0 then
        Sh2 := pf.sp2;
        t2 := List([1..Length(pf.sp2)], i -> 0);
    else
        Sh2 := Concatenation(pf.an2, pf.sp2);
        t2 := List([1..Length(pf.an2) + Length(pf.sp2)], i -> 0);
        t2[1] := 1;
    fi;
    ic1 := EfInsertc(c1);
    if1 := EfInsertc(f1);
    AT1 := F2_Trans(A1);
    ATSh1T := F2_Mul(AT1, F2_Trans(Sh1));
    v1 := List(t1, x -> x);
    v1 := List([1..Length(v1)], i ->
        (v1[i] + F2_VMul(F2_VMul(F2_VMul(ic1, RT), F2_Trans(pf.H1)),
                         ATSh1T)[i]) mod 2);
    v1 := List([1..Length(v1)], i ->
        (v1[i] + F2_VMul(F2_VMul(if1, RT), ATSh1T)[i]) mod 2);
    v1 := List([1..Length(v1)], i ->
        (v1[i] + F2_VMul(s1, ATSh1T)[i]) mod 2);
    ic2 := EfInsertc(e2);
    if2 := EfInsertc(f2);
    AT2 := F2_Trans(A2);
    ATSh2T := F2_Mul(AT2, F2_Trans(Sh2));
    v2 := List(t2, x -> x);
    v2 := List([1..Length(v2)], i ->
        (v2[i] + F2_VMul(F2_VMul(F2_VMul(ic2, RT), F2_Trans(pf.H2)),
                         ATSh2T)[i]) mod 2);
    v2 := List([1..Length(v2)], i ->
        (v2[i] + F2_VMul(F2_VMul(if2, RT), ATSh2T)[i]) mod 2);
    v2 := List([1..Length(v2)], i ->
        (v2[i] + F2_VMul(s2, ATSh2T)[i]) mod 2);
    v3 := List([1..Length(f1)], i -> (f1[i] + e2[i]) mod 2);
    v4 := List([1..Length(c1)], i -> (c1[i] + e1[i]) mod 2);
    v5 := List([1..Length(d2)], i -> (d2[i] + f2[i]) mod 2);
    return Concatenation(v1, v2, v3, v4, v5);
end;;

# HardCodeProductFinderNext: solve the system, returning a record with
# .particular = one solution z, .nullspace = basis of the kernel, or
# `fail` if no solution.
HardCodeProductFinderNext := function(h1, e1, f1, c1, s1, mhh1, A1, B1,
                                       h2, e2, f2, d2, s2, mhh2, A2, B2, m)
    local pf, T, V, res;
    pf := HardCodeProductFinder(h1, e1, f1, c1, s1, mhh1, A1, B1,
                                 h2, e2, f2, d2, s2, mhh2, A2, B2, m);
    T := List([1..pf.nrD1 + pf.nrD2], i ->
              Concatenation(pf.T1[i], pf.T2[i], pf.T3[i], pf.T4[i],
                            pf.T5[i]));
    V := _ProductRhs(pf, e1, f1, c1, s1, A1, e2, f2, d2, s2, A2, m);
    res := F2_SolveRowEqAll(T, [V]);
    if res.particular = fail then return fail; fi;
    return rec(particular := res.particular[1],
               nullspace := res.nullspace,
               pf := pf);
end;;

ProductFinderNext := function(h1, e1, f1, c1, s1, h2, e2, f2, d2, s2, m)
    local mhh1, A1, B1, mhh2, A2, B2;
    mhh1 := MhHalfefMat(h1, m); A1 := Kernef(h1, m); B1 := BasisForN(m);
    mhh2 := MhHalfefMat(h2, m); A2 := Kernef(h2, m); B2 := BasisForN(m);
    return HardCodeProductFinderNext(h1, e1, f1, c1, s1, mhh1, A1, B1,
                                      h2, e2, f2, d2, s2, mhh2, A2, B2, m);
end;;

ProductFinderNextAlt := ProductFinderNext;;


# ============================================================
# Closed-form for entries of the product T_{h1} T_{h2}
# ============================================================

# HardCodeShortComputeProductCoordinateef: compute one entry (c1, d2) of
# the product T_{h1}^{e1, f1} * T_{h2}^{e2, f2}.  Sums over the small
# set of intermediate b's parametrised by ProductFinderNext.
HardCodeShortComputeProductCoordinateef := function(a1, A1Mat, e1, f1, c1, s1,
                                                     mh1, k1, B1, a2, A2Mat,
                                                     e2, f2, d2, s2, mh2, k2,
                                                     B2, m)
    local pfRes, R, n, kHalf, total, ss, P, ker, all, p, y, y1, y2,
          BPi1, BPi2, D1, D2, p1, p2, brl, mhalf, halfDom, mEntry,
          nEntry, x1, x2, bk, seen, key, kerSize, idx, iter, cVec;
    pfRes := HardCodeProductFinderNext(a1, e1, f1, c1, s1, mh1, k1, B1,
                                        a2, e2, f2, d2, s2, mh2, k2, B2, m);
    if pfRes = fail then return 0; fi;
    n := 2^m;
    kHalf := n / 2;
    R := TwoCocycleForN(m);
    BPi1 := pfRes.pf.BPi1;
    BPi2 := pfRes.pf.BPi2;
    D1 := pfRes.pf.D1;
    D2 := pfRes.pf.D2;
    p1 := F2_Mul(D1, BPi1);
    total := 0;
    ss := pfRes.particular;
    ker := pfRes.nullspace;
    kerSize := 2^Length(ker);
    seen := [];
    for idx in [0..kerSize - 1] do
        # Build the kernel combination
        cVec := List([1..Length(ss)], iter -> ss[iter]);
        for iter in [1..Length(ker)] do
            if QuoInt(idx, 2^(iter - 1)) mod 2 = 1 then
                cVec := List([1..Length(cVec)], y ->
                    (cVec[y] + ker[iter][y]) mod 2);
            fi;
        od;
        # Split into y1 (length nrD1) and y2 (length nrD2).
        y1 := cVec{[1..pfRes.pf.nrD1]};
        y2 := cVec{[pfRes.pf.nrD1 + 1 .. pfRes.pf.nrD1 + pfRes.pf.nrD2]};
        # bk = f1 + RightHalf(y1 * D1 * BigPi(h1))
        x1 := F2_VMul(y1, p1);
        bk := List([1..kHalf], iter ->
            (f1[iter] + x1[kHalf + iter]) mod 2);
        # Skip duplicates of bk to avoid overcounting (Magma uses
        # SequenceToSet).  Use bk as the dedup key.
        key := ShallowCopy(bk);
        if key in seen then continue; fi;
        Add(seen, key);
        # Recompute the actual x_h1 and x_h2 to feed
        # HardCodeShortComputeInterTwinerefWithX.  In the Magma:
        #   x_h1 = y1 * D1            (length n)
        #   x_h2 = y2 * D2            (length n)
        x1 := F2_VMul(y1, D1);
        x2 := F2_VMul(y2, D2);
        mEntry := HardCodeShortComputeInterTwinerefWithX(
                      a1, pfRes.pf.H1, e1, f1, c1, bk, s1,
                      mh1, k1, B1, R, x1, m);
        nEntry := HardCodeShortComputeInterTwinerefWithX(
                      a2, pfRes.pf.H2, e2, f2, bk, d2, s2,
                      mh2, k2, B2, R, x2, m);
        total := total + mEntry * nEntry;
    od;
    return total;
end;;

# ShortComputeProductCoordinateef: convenience wrapper that recovers
# mh, A from h.  Mirrors the Magma function of the same name.
ShortComputeProductCoordinateef := function(a1, e1, f1, c1, s1,
                                             a2, e2, f2, d2, s2, m)
    local mh1, A1, B1, mh2, A2, B2;
    mh1 := MhHalfefMat(a1, m); A1 := Kernef(a1, m); B1 := BasisForN(m);
    mh2 := MhHalfefMat(a2, m); A2 := Kernef(a2, m); B2 := BasisForN(m);
    return HardCodeShortComputeProductCoordinateef(
               a1, A1, e1, f1, c1, s1, mh1, A1, B1,
               a2, A2, e2, f2, d2, s2, mh2, A2, B2, m);
end;;

ShortComputeProductCoordinateefAlt := ShortComputeProductCoordinateef;;
