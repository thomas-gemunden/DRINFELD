# Port of section 5 of the Magma supplement (Keller-Roberts-Roberts,
# arXiv:2411.13646, BWOrbifoldsMagma.txt lines 540-710): standardisation
# of quadratic forms over F_2.
#
# A "quadratic form on F_2^n" is represented by an n x n matrix q (with
# integer entries 0/1, all arithmetic mod 2) via
#   Q(v) = v * q * v^T   (mod 2).
# The associated bilinear form is
#   B(v, w) = Q(v + w) - Q(v) - Q(w)        (mod 2).
#
# The Magma original uses GF(2)/FiniteField(2) directly. Per the project
# conventions we keep matrices as plain integer matrices and reduce mod 2
# explicitly. F_2 linear-algebra helpers (RREF, nullspace, complement
# basis) are written here from scratch using GAP built-ins on integer
# matrices, so we don't rely on the GF(2) machinery or external packages.

# ---- F_2 linear algebra helpers (not in the Magma original) ----

# Reduce an integer matrix mod 2.
F2Mod := function(M)
    local i, R;
    R := [];
    for i in [1..Length(M)] do
        Add(R, List(M[i], x -> x mod 2));
    od;
    return R;
end;;

# Reduce an integer vector mod 2.
F2ModVec := function(v)
    return List(v, x -> x mod 2);
end;;

# F_2 row addition: r1 := r1 + r2  (mod 2), in place style returning the row.
F2RowAdd := function(r1, r2)
    return List([1..Length(r1)], i -> (r1[i] + r2[i]) mod 2);
end;;

# Reduced row echelon form of an integer matrix M, viewed over F_2.
# Returns a record with fields .rref (RREF rows), .pivots (1-based pivot
# column for each nonzero RREF row), .rank.
F2RREF := function(M)
    local A, m, n, pivots, r, c, i, k;
    A := F2Mod(M);
    m := Length(A);
    if m = 0 then
        return rec(rref := [], pivots := [], rank := 0);
    fi;
    n := Length(A[1]);
    pivots := [];
    r := 1;
    for c in [1..n] do
        if r > m then break; fi;
        i := r;
        while i <= m and A[i][c] = 0 do i := i + 1; od;
        if i > m then continue; fi;
        if i <> r then
            A{[r, i]} := A{[i, r]};
        fi;
        for k in [1..m] do
            if k <> r and A[k][c] = 1 then
                A[k] := F2RowAdd(A[k], A[r]);
            fi;
        od;
        Add(pivots, c);
        r := r + 1;
    od;
    return rec(rref := A, pivots := pivots, rank := Length(pivots));
end;;

# Basis (list of rows) of the F_2 row span of the integer matrix M.
F2RowSpanBasis := function(M)
    local rr;
    rr := F2RREF(M);
    return rr.rref{[1..rr.rank]};
end;;

# Basis (list of column-vectors-as-rows) of {x in F_2^n : M * x = 0}.
# The RIGHT null space of M (as a list of vectors of length n_cols).
F2RightNullspace := function(M)
    local m, n, A, r, c, pivCols, freeCols, basis, j, v, i, p;
    m := Length(M);
    if m = 0 then return []; fi;
    n := Length(M[1]);
    A := F2Mod(M);
    A := List(A, ShallowCopy);
    r := 1;
    pivCols := [];
    for c in [1..n] do
        if r > m then break; fi;
        j := r;
        while j <= m and A[j][c] = 0 do j := j + 1; od;
        if j > m then continue; fi;
        if j <> r then A{[r, j]} := A{[j, r]}; fi;
        for i in [1..m] do
            if i <> r and A[i][c] = 1 then
                A[i] := F2RowAdd(A[i], A[r]);
            fi;
        od;
        Add(pivCols, c);
        r := r + 1;
    od;
    freeCols := Filtered([1..n], c -> not (c in pivCols));
    basis := [];
    for c in freeCols do
        v := List([1..n], i -> 0);
        v[c] := 1;
        for i in [1..Length(pivCols)] do
            p := pivCols[i];
            v[p] := A[i][c];
        od;
        Add(basis, v);
    od;
    return basis;
end;;

# Basis (list of rows) of {v in F_2^n : v * M = 0}.
# That is, the LEFT null space of M, matching Magma's `Kernel(M)`.
F2LeftNullspace := function(M)
    local m, n, A, r, c, pivCols, freeCols, basis, j, v, i, p;
    m := Length(M);
    if m = 0 then return []; fi;
    n := Length(M[1]);
    # We compute left nullspace of M as the right nullspace of M^T:
    # find vectors x in F_2^m with M^T * x = 0  (treating x as a column).
    # Equivalently row-reduce M^T and read off the kernel.
    A := List([1..n], i -> List([1..m], j -> M[j][i] mod 2));
    # row-reduce A in place
    r := 1;
    pivCols := [];
    for c in [1..m] do
        if r > n then break; fi;
        j := r;
        while j <= n and A[j][c] = 0 do j := j + 1; od;
        if j > n then continue; fi;
        if j <> r then A{[r, j]} := A{[j, r]}; fi;
        for i in [1..n] do
            if i <> r and A[i][c] = 1 then
                A[i] := F2RowAdd(A[i], A[r]);
            fi;
        od;
        Add(pivCols, c);
        r := r + 1;
    od;
    freeCols := Filtered([1..m], c -> not c in pivCols);
    basis := [];
    for c in freeCols do
        v := List([1..m], i -> 0);
        v[c] := 1;
        # back-substitute: for each pivot row, x[pivCols[i]] = sum over
        # the free variables of A[i][freeCol] * x[freeCol].
        for i in [1..Length(pivCols)] do
            p := pivCols[i];
            v[p] := A[i][c];      # only this free col is set to 1
        od;
        Add(basis, v);
    od;
    return basis;
end;;

# Standard basis vectors of F_2^n as a list of integer rows.
F2StdBasis := function(n)
    local i, e, B;
    B := [];
    for i in [1..n] do
        e := List([1..n], j -> 0);
        e[i] := 1;
        Add(B, e);
    od;
    return B;
end;;

# Given a list `subBasis` of independent rows in F_2^n, return a list of
# n - d standard basis vectors e_{i_1}, ..., e_{i_{n-d}} that together
# with `subBasis` form a basis of F_2^n.  This realises Magma's
# Complement(V, W) where V = F_2^n and W = <subBasis>.
F2ComplementStandardBasis := function(subBasis, n)
    local rr, pivots, missing, basis, i, e;
    if Length(subBasis) = 0 then
        return F2StdBasis(n);
    fi;
    # Find pivot columns of subBasis under RREF.  A standard basis
    # vector e_i is independent of subBasis iff i is NOT a pivot column.
    rr := F2RREF(subBasis);
    pivots := rr.pivots;
    missing := Filtered([1..n], c -> not (c in pivots));
    basis := [];
    for i in missing do
        e := List([1..n], j -> 0);
        e[i] := 1;
        Add(basis, e);
    od;
    return basis;
end;;

# Helper: given a basis B of a subspace U <= F_2^n and a list of
# coordinate-vectors `coeffs` (each of length |B|), return the lifted
# vectors in F_2^n (i.e. coeffs[i] * B).
F2LiftThroughBasis := function(B, coeffs)
    local i, j, n, lifted, v, k;
    if Length(coeffs) = 0 then return []; fi;
    if Length(B) = 0 then return []; fi;
    n := Length(B[1]);
    lifted := [];
    for i in [1..Length(coeffs)] do
        v := List([1..n], k -> 0);
        for j in [1..Length(B)] do
            if coeffs[i][j] = 1 then
                v := F2RowAdd(v, B[j]);
            fi;
        od;
        Add(lifted, v);
    od;
    return lifted;
end;;

# Given a subspace U with basis `ambientBasis` of F_2^n and a subspace
# W (basis `subBasis`) contained in <ambientBasis>, return a basis of a
# complement of W inside U.  This realises Magma's
# Complement(VectorSpaceWithBasis(ambientBasis), W).
F2ComplementInBasis := function(ambientBasis, subBasis)
    local n, all, rr, pivots, dimSub, comp, i, picked, j;
    if Length(ambientBasis) = 0 then return []; fi;
    n := Length(ambientBasis[1]);
    # Strategy: the subBasis lives in <ambientBasis>; greedily pick
    # ambientBasis vectors that are independent of subBasis until the
    # union spans U.
    rr := F2RREF(subBasis);
    dimSub := rr.rank;
    comp := [];
    picked := List(subBasis, ShallowCopy);
    for i in [1..Length(ambientBasis)] do
        # Test independence by stacking and re-RREF.
        rr := F2RREF(Concatenation(picked, [ambientBasis[i]]));
        if rr.rank > Length(picked) then
            Add(picked, ambientBasis[i]);
            Add(comp, ambientBasis[i]);
        fi;
    od;
    return comp;
end;;

# Helper for SplitDegeneratePart: given basis B of a subspace U and a
# list `coeffsK` of B-coordinate vectors describing a sub-subspace W,
# return a basis of a complement of W in U as vectors in F_2^n.
F2ComplementInBasisLifted := function(B, coeffsK)
    local liftedK, comp;
    liftedK := F2LiftThroughBasis(B, coeffsK);
    comp := F2ComplementInBasis(B, liftedK);
    return comp;
end;;

# ---- Section 5 functions ----

# Apply the quadratic form q (as a matrix) to vector v: Q(v) = v q v^T.
# Mirrors Magma `qForm`.
QFormEval := function(q, v)
    local s, n, i, j;
    n := Length(v);
    s := 0;
    for i in [1..n] do
        for j in [1..n] do
            s := s + v[i] * q[i][j] * v[j];
        od;
    od;
    return s mod 2;
end;;

# Mirrors Magma `BilForm`: B_q(v,w) = Q(v+w) - Q(v) - Q(w)  (mod 2).
BilForm := function(q, v, w)
    local vw;
    vw := List([1..Length(v)], i -> (v[i] + w[i]) mod 2);
    return (QFormEval(q, vw) - QFormEval(q, v) - QFormEval(q, w)) mod 2;
end;;

# Mirrors Magma `MatOfBilForm`: matrix of B_q on the standard basis.
MatOfBilForm := function(q)
    local n, M, e, i, j;
    n := Length(q);
    M := List([1..n], i -> List([1..n], j -> 0));
    e := F2StdBasis(n);
    for i in [1..n] do
        for j in [1..n] do
            M[i][j] := BilForm(q, e[i], e[j]);
        od;
    od;
    return M;
end;;

# Mirrors Magma `StandardizeQForm`: zero out balanced off-diagonal pairs.
# In Magma: q + L + L^T where L is the lower triangle of q (with diag).
# Over F_2 this leaves the diagonal alone (since q[i][i] + 2 q[i][i] = 0
# mod 2 keeps the diagonal, actually L includes the diagonal so q[i][i]
# becomes q[i][i] + 2*q[i][i] = q[i][i] mod 2; q[i][j] for i>j becomes
# q[i][j] + q[i][j] + q[j][i] = q[j][i] mod 2; and q[i][j] for i<j
# becomes q[i][j] + q[j][i] + q[j][i] = q[i][j] mod 2).  The net effect:
# entries above the diagonal of q are kept; entries below the diagonal
# of q are replaced by the corresponding above-diagonal entry mirrored.
StandardizeQForm := function(q)
    local n, L, i, j, R;
    n := Length(q);
    L := List([1..n], i -> List([1..n], j -> 0));
    for i in [1..n] do
        for j in [1..i] do
            L[i][j] := q[i][j] mod 2;
        od;
    od;
    R := List([1..n], i ->
        List([1..n], j ->
            (q[i][j] + L[i][j] + L[j][i]) mod 2));
    return R;
end;;

# Mirrors Magma `QuadStandardFormStart`: returns a pair [bd, bn] where
# bd is a basis of the radical of q (= left null space of MatOfBilForm)
# and bn is a basis of a complement.
QuadStandardFormStart := function(q)
    local n, B, bd, bn;
    n := Length(q);
    B := MatOfBilForm(q);
    bd := F2LeftNullspace(B);
    bn := F2ComplementStandardBasis(bd, n);
    return [bd, bn];
end;;

# Mirrors Magma `SplitDegeneratePart`: further split the radical into a
# part where Q is 1 and a totally singular part.  Returns [bAniso, bZero].
SplitDegeneratePart := function(q)
    local pair, bd, n, i, diagVals, colMat, K, comp;
    pair := QuadStandardFormStart(q);
    bd := pair[1];
    n := Length(bd);
    if n = 0 then return [[], []]; fi;
    # Build the diagonal of (bd) q (bd)^T over F_2:
    diagVals := List(bd, v -> QFormEval(q, v));
    # K = vectors c in F_2^n with sum c_i diagVals[i] = 0 -- the kernel of
    # the n x 1 column matrix [Diagonal(Bd)].  In matrix form: c*colMat=0.
    colMat := List(diagVals, x -> [x]);          # n x 1 matrix
    K := F2LeftNullspace(colMat);                # list of length-n rows
    # The "zero part" basis (in the original space) is K combined with
    # bd; the "anisotropic part" is a complement of K inside <bd>.
    # We return both as lists of vectors in F_2^n.
    comp := F2ComplementInBasisLifted(bd, K);
    return [comp, F2LiftThroughBasis(bd, K)];
end;;


# Mirrors Magma `FindHyperBolicPair`: given quadratic form q and a basis
# B of a subspace, find a hyperbolic pair u, v in <B>.  Returns a list
# [u, v] with Q(u)=0, Q(v+Q(v)*u) = 0 and B(u, v+Q(v)*u) = 1, OR `fail`
# if none exists / the space has dimension < 2.
FindHyperBolicPair := function(q, B)
    local d, n, vecs, i, k, x, y, qy, ynew, coeff;
    d := Length(B);
    if d < 2 then return fail; fi;
    n := Length(B[1]);
    # Enumerate all 2^d vectors in <B>.
    vecs := [];
    for i in [0..2^d - 1] do
        coeff := List([0..d-1], k -> QuoInt(i, 2^k) mod 2);
        Add(vecs, F2LiftThroughBasis(B, [coeff])[1]);
    od;
    for x in vecs do
        if QFormEval(q, x) = 0 then
            for y in vecs do
                if BilForm(q, x, y) = 1 then
                    qy := QFormEval(q, y);
                    if qy = 1 then
                        ynew := List([1..n], k -> (y[k] + x[k]) mod 2);
                    else
                        ynew := y;
                    fi;
                    return [x, ynew];
                fi;
            od;
        fi;
    od;
    return fail;
end;;

# Mirrors Magma `OrthogonalizeWrtuv`: orthogonalize a basis of <B> with
# respect to the bilinear form B_q against the hyperbolic pair (u, v).
# Returns a basis of the orthogonal complement of <u, v> in <B>.
OrthogonalizeWrtuv := function(q, u, v, B)
    local S, n, b, i, si, t1, t2, w;
    n := Length(u);
    S := F2ComplementInBasis(B, [u, v]);
    b := [];
    for i in [1..Length(S)] do
        si := S[i];
        t1 := BilForm(q, si, u);
        t2 := BilForm(q, si, v);
        # b_i = si - t1*v - t2*u   (mod 2)
        w := ShallowCopy(si);
        if t1 = 1 then w := F2RowAdd(w, v); fi;
        if t2 = 1 then w := F2RowAdd(w, u); fi;
        Add(b, w);
    od;
    return b;
end;;

# Mirrors Magma `QuadStandardFormChar2`: the recursive worker that, given
# a basis Bd of the radical, a basis Bn of its complement and an
# accumulator Bn1, returns the new basis on the non-degenerate part in
# standard form, plus a "defect type" integer.  Returns either the
# string "Totally isotropic" (for the empty case) or a pair [Bn1, type].
QuadStandardFormChar2 := function(q, Bd, Bn, Bn1)
    local n, d, V, hp, foundBn1, x, y, vecs, i, k, w;
    if Length(Bn) = 0 then return "Totally isotropic"; fi;
    d := Length(Bn);
    n := Length(Bn[1]);
    if d = 1 then
        Add(Bn1, Bn[1]);
        if QFormEval(q, Bn[1]) = 0 then
            return [Bn1, 3];
        else
            return [Bn1, 4];
        fi;
    elif d = 2 then
        hp := FindHyperBolicPair(q, Bn);
        if hp = fail then
            # Enumerate the 4 vectors of <Bn>
            vecs := [];
            for i in [0..3] do
                w := List([1..n], k -> 0);
                if i mod 2 = 1 then w := F2RowAdd(w, Bn[1]); fi;
                if QuoInt(i, 2) mod 2 = 1 then w := F2RowAdd(w, Bn[2]); fi;
                Add(vecs, w);
            od;
            for x in vecs do
                for y in vecs do
                    if BilForm(q, y, x) = 1 then
                        Add(Bn1, x);
                        Add(Bn1, y);
                        return [Bn1, 2];
                    fi;
                od;
            od;
            return [Bn1, 2];   # should not happen
        else
            Add(Bn1, hp[2]);
            Add(Bn1, hp[1]);
            return [Bn1, 0];
        fi;
    else
        hp := FindHyperBolicPair(q, Bn);
        x := hp[2]; y := hp[1];
        Bn := OrthogonalizeWrtuv(q, y, x, Bn);
        Add(Bn1, x);
        Add(Bn1, y);
        return QuadStandardFormChar2(q, Bd, Bn, Bn1);
    fi;
end;;

# Mirrors Magma `QuadStandardFormChar2CompleteBasesTogether`: returns a
# single matrix whose rows put q in standard form, ordered as
# [non-degenerate part; anisotropic part of radical; isotropic part of
# radical].  Also returns the defect type (or fail if no nondegenerate
# part).  Returns [matrix, defectType]; defectType = fail if no nondeg.
QuadStandardFormChar2CompleteBasesTogether := function(q)
    local pair, b1, b2, sd, b3, b4, ab, p, joined, n;
    pair := QuadStandardFormStart(q);
    b1 := pair[1]; b2 := pair[2];
    if Length(b2) = 0 then
        sd := SplitDegeneratePart(q);
        return [Concatenation(sd[1], sd[2]), fail];
    fi;
    sd := SplitDegeneratePart(q);
    b3 := sd[1]; b4 := sd[2];
    ab := QuadStandardFormChar2(q, b1, b2, []);
    p := ab[1];
    joined := Concatenation(p, b3, b4);
    return [joined, ab[2]];
end;;

# Mirrors Magma `QuadStandardFormChar2CompleteBasesSeparate`: same as
# above but returns the three pieces separately.  Returns
# [nondegPart, anisoRadPart, isoRadPart].
QuadStandardFormChar2CompleteBasesSeparate := function(q)
    local pair, b1, b2, sd, ab;
    pair := QuadStandardFormStart(q);
    b1 := pair[1]; b2 := pair[2];
    if Length(b2) = 0 then
        sd := SplitDegeneratePart(q);
        return [[], sd[1], sd[2]];
    fi;
    ab := QuadStandardFormChar2(q, b1, b2, []);
    sd := SplitDegeneratePart(q);
    return [ab[1], sd[1], sd[2]];
end;;

# Mirrors Magma `QuadStandardFormChar2CompleteForm`: returns the
# standardised matrix of q in its standard basis (so the output is of
# the form J = sum of x_i y_i blocks, plus optional x^2 blocks for the
# anisotropic part).
QuadStandardFormChar2CompleteForm := function(q)
    local pair, b1, b2, sd, t, tMat, qMat, prod, abm, a;
    pair := QuadStandardFormStart(q);
    b1 := pair[1]; b2 := pair[2];
    sd := SplitDegeneratePart(q);
    if Length(b2) = 0 then
        t := Concatenation(sd[1], sd[2]);
        tMat := F2Mod(t);
        prod := tMat * F2Mod(q) * TransposedMat(tMat);
        return StandardizeQForm(F2Mod(prod));
    else
        abm := QuadStandardFormChar2CompleteBasesTogether(q);
        a := abm[1];
        prod := F2Mod(a) * F2Mod(q) * TransposedMat(F2Mod(a));
        return StandardizeQForm(F2Mod(prod));
    fi;
end;;

# Mirrors Magma `QSymp`: evaluates the standard symplectic-derived
# quadratic form Q(v) = sum_{i=1}^{m} v_{2i-1} v_{2i} on a length-2m
# vector v.
QSymp := function(v)
    local n, s, i;
    n := Length(v) / 2;
    s := 0;
    for i in [1..n] do
        s := s + v[2*i - 1] * v[2*i];
    od;
    return s mod 2;
end;;

# Mirrors Magma `g`: auxiliary defect-handling function.
GDefect := function(n, b1, b2)
    if n = 0 then return 0; fi;
    if n = 1 then return (b1 + b2 + 1) mod 2; fi;
    return fail;
end;;
