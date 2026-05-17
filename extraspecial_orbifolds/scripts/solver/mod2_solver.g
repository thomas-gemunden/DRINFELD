# mod2_solver.g — GF(2) coboundary test.
#
# IsCoboundary2Mod2(H, c'_g) — given a finite group H and a function
#   c'_g : H × H -> Z/2 (or returning integers; we mod 2 internally),
# decide whether there exists beta : H -> Z/2 with
#   c'_g(h, k) = beta(h) - beta(hk) + beta(k)  (mod 2).
#
# Builds the boundary system A·beta = b over GF(2) and runs SolutionMat.
# Spike-confirmed at 1 ms / 10 ms for |H| = 64 / 128.

# BoundaryMatrixGF2(H) — n^2 x n GF(2) matrix A where row (i, j) (linearised
# as (i-1)*n+j) encodes the constraint
#   β(elts[i]) + β(elts[i]*elts[j]) + β(elts[j]) = c(elts[i], elts[j])  (mod 2).
# Equivalently, column k of A is δ(1_{elts[k]}) viewed as a length-n² vector,
# so the column space of A is B²(H; F_2) ⊆ C²(H; F_2). Used by both
# IsCoboundary2Mod2 (solving A·β = b) and IsCoboundary2Mod2WithLift (where
# the row space of TransposedMat(A) is the boundary subspace we add to im(β)
# for cohomology-level membership testing).
# Module-level cache for BoundaryMatrixGF2. The matrix depends only on
# the group H, not on the cocycle c_g being tested. The transgression-
# kernel driver calls this function with a small number of distinct H
# values (one per BRW orbit representative — 4 at m=5) but invokes it
# 165 × 1025 ≈ 170,000 times during the enumeration sweep. Building the
# n²×n GF(2) matrix from scratch each call at n=2048 dominates wall time
# (estimated weeks for A-5b without this cache). With IsIdenticalObj
# lookup against the BRW orbit representative centralizers we get O(1)
# cache hits after the first 4 builds.
_BoundaryMatrixGF2_cache := [];;

_BoundaryMatrixGF2_raw := function(H)
    local elts, n, idx, A, i, j, ij, row, zero, one;
    elts := AsList(H);
    n := Length(elts);
    idx := function(h) return Position(elts, h); end;
    zero := Zero(GF(2));
    one  := One(GF(2));

    A := List([1..n*n], i -> List([1..n], j -> zero));
    for i in [1..n] do
        for j in [1..n] do
            row := (i - 1) * n + j;
            ij := idx(elts[i] * elts[j]);
            A[row][i]  := A[row][i]  + one;
            A[row][j]  := A[row][j]  + one;
            A[row][ij] := A[row][ij] + one;
        od;
    od;
    ConvertToMatrixRep(A, GF(2));
    return A;
end;;

BoundaryMatrixGF2 := function(H)
    local entry, A;
    for entry in _BoundaryMatrixGF2_cache do
        if IsIdenticalObj(entry.H, H) then return entry.A; fi;
    od;
    A := _BoundaryMatrixGF2_raw(H);
    Add(_BoundaryMatrixGF2_cache, rec(H := H, A := A));
    return A;
end;;

# Module-level cache for SemiEchelonMatTransformation(TransposedMat(A)).
# A-5b's enumeration sweep at m=5 calls IsCoboundary2Mod2 ~170,000 times
# with at most 4 distinct centralizer matrices A (one per BRW orbit).
# The dominant per-call cost is GAP's internal Gaussian elimination
# (O(rank^2 · cols) per call), which we hoist into a one-time factorisation
# per A. Subsequent solves reuse the cached `sem` record for fast
# subspace-membership testing.
_IsCoboundary2Mod2_SemCache := [];;

_GetCachedSemForAT := function(A)
    local entry, sem, nonzero_heads;
    for entry in _IsCoboundary2Mod2_SemCache do
        if IsIdenticalObj(entry.A, A) then return entry; fi;
    od;
    # Build sem for TransposedMat(A) once and cache.
    sem := SemiEchelonMatTransformation(TransposedMat(A));
    # R2-2 (#177): the back-substitution loop iterates [1..Length(b)] which
    # is n² (up to 4M at n=2048). Most of those indices have sem.heads[i] = 0
    # (rank is bounded by n = |C|, so at most n of the n² heads are non-zero
    # — i.e. ≥ 99.9% of the iterations are pure-skip noise costing 4
    # interpreter ops each: EvalElmList + ExecAssLVar + EvalNe + ExecIf).
    # Sample of A-5b live during gen ~13 showed these 4 primitives at 67.6 %
    # combined of total CPU. Precompute the non-zero-head index list once
    # per cached sem and iterate that instead.
    nonzero_heads := Filtered([1..Length(sem.heads)], i -> sem.heads[i] <> 0);
    Add(_IsCoboundary2Mod2_SemCache,
        rec(A := A, sem := sem, nonzero_heads := nonzero_heads));
    return _IsCoboundary2Mod2_SemCache[Length(_IsCoboundary2Mod2_SemCache)];
end;;

IsCoboundary2Mod2 := function(H, c)
    local elts, n, b, i, j, one;
    # Slow-path adapter for callers that supply a function `c(h, k)`.
    # Internally we route through IsCoboundary2Mod2Vec, which is the
    # vectorised path the A-5b sweep actually uses. Each c(elts[i], elts[j])
    # call is ~10us of GAP-interpreter + 2 dict lookups; at n=1024 the n^2
    # function-call loop is the dominant per-call cost.
    elts := AsList(H);
    n := Length(elts);
    one := One(GF(2));
    b := List([1..n*n], i -> 0);
    for i in [1..n] do
        for j in [1..n] do
            b[(i - 1) * n + j] := c(elts[i], elts[j]);
        od;
    od;
    return IsCoboundary2Mod2Vec(H, b);
end;;

# IsCoboundary2Mod2Vec(H, c_g_vec) — fast vectorised path.
#
# `c_g_vec` is a length-n² integer (or GF(2)) vector encoding the cocycle
# values c(elts[i], elts[j]) at index (i-1)*n + j, with elts := AsList(H)
# (callers that build c_g_vec from a basis-table dot-product already use
# this indexing — see BuildPerClassCocycleBasis).
#
# Identical to IsCoboundary2Mod2 mathematically; replaces the n² function-
# call loop with a single List(..., x -> (x mod 2) * one) over the
# precomputed vector. At n=1024 this drops the per-call cost from ~5s to
# under 100 ms.
IsCoboundary2Mod2Vec := function(H, c_g_vec)
    local n, A, entry, sem, nonzero_heads, b, i, one, z, sol_dim, sol, vno, x;
    n := Length(AsList(H));
    one := One(GF(2));
    z := Zero(GF(2));

    A := BoundaryMatrixGF2(H);                  # cached
    entry := _GetCachedSemForAT(A);             # cached factorisation + heads
    sem := entry.sem;
    nonzero_heads := entry.nonzero_heads;

    b := List(c_g_vec, x -> (x mod 2) * one);
    ConvertToVectorRep(b, GF(2));

    if Length(sem.coeffs) = 0 then
        return IsZero(b);
    fi;
    sol_dim := Length(sem.coeffs[1]);
    sol := ListWithIdenticalEntries(sol_dim, z);
    ConvertToVectorRep(sol, GF(2));
    b := ShallowCopy(b);
    # R2-2 (#177): iterate only the non-zero-head indices (the rank-many
    # pivot rows of sem) instead of every i in [1..Length(b)]. The skipped
    # iterations had vno = 0 and contributed nothing to b or sol.
    for i in nonzero_heads do
        vno := sem.heads[i];
        x := b[i];
        if x <> z then
            AddRowVector(b, sem.vectors[vno], -x);
            AddRowVector(sol, sem.coeffs[vno], x);
        fi;
    od;
    return IsZero(b);
end;;

# BocksteinH1ToH2(C) — image of the connecting homomorphism
#   β : H^1(C; F_2) -> H^2(C; F_2)
# from the SES 0 -> F_2 -·²-> F_4 -> F_2 -> 0 (equivalently Sq^1).
#
# H^1(C; F_2) = Hom(C, F_2) = Hom(C^ab ⊗ F_2, F_2). For α in this Hom space,
# β(α) is the cup-square at degree 1 in F_2: β(α)(h, k) = α(h) · α(k).
#
# Returns a reduced F_2-basis of the image as a list of length-n² vectors,
# indexed compatibly with IsCoboundary2Mod2: vec[(i-1)*n + j] = α(elts[i])·α(elts[j])
# where elts := AsList(C). The basis is produced by BaseMat over GF(2).
#
# Construction of the F_2-functionals α: take phi := MaximalAbelianQuotient(C),
# pick independent abelian generators of Image(phi); for each generator whose
# order is even, the corresponding coordinate of IndependentGeneratorExponents,
# reduced mod 2, gives one α. Generators of odd order contribute no F_2
# functional (the mod-2 reduction kills them). So |hom_basis| equals the
# number of even-order elementary divisors of C^ab — i.e. the F_2-rank of
# C^ab / 2·C^ab = H^1(C; F_2).
BocksteinH1ToH2 := function(C)
    local elts, n, phi, GA, abgens, ab_orders, hom_basis, alpha_vals,
          k, ord, vecs, i, j, v, zero, one;
    elts := AsList(C);
    n := Length(elts);
    zero := Zero(GF(2));
    one  := One(GF(2));

    phi := MaximalAbelianQuotient(C);
    GA := Image(phi);
    abgens := IndependentGeneratorsOfAbelianGroup(GA);
    ab_orders := List(abgens, Order);

    # For each even-order independent generator, build α : C -> F_2 as a
    # length-n list of GF(2) values: α(elts[i]) = (k-th IGE coord of phi(elts[i])) mod 2.
    hom_basis := [];
    for k in [1..Length(abgens)] do
        ord := ab_orders[k];
        if ord mod 2 = 0 then
            alpha_vals := List(elts, g ->
                (IndependentGeneratorExponents(GA, Image(phi, g))[k] mod 2) * one);
            Add(hom_basis, alpha_vals);
        fi;
    od;

    # For each α, build β(α) as a length-n² vector with β(α)(i, j) = α(i)·α(j).
    vecs := [];
    for alpha_vals in hom_basis do
        v := List([1..n*n], i -> zero);
        for i in [1..n] do
            for j in [1..n] do
                v[(i - 1) * n + j] := alpha_vals[i] * alpha_vals[j];
            od;
        od;
        Add(vecs, v);
    od;

    if IsEmpty(vecs) then
        return [];
    fi;
    ConvertToMatrixRep(vecs, GF(2));
    return BaseMat(vecs);
end;;

# IsCoboundary2Mod2WithLift(C, c'_g) — does [c'_g] in H^2(C; F_2) lie in image(β)?
#
# Equivalent (per the SES LES 0 -> F_2 -·²-> Z/4 -> F_2 -> 0) to: does the
# cocycle c_g = (exp/2) · c'_g lift to a Z/exp coboundary on C? Returns true if
# yes — covering both [c'_g] = 0 (early-returned via IsCoboundary2Mod2) and
# [c'_g] ≠ 0 but in image(β).
#
# Algorithm: build vec ∈ F_2^{n²} from c. Then [vec] ∈ im(β) ⊆ H^2(C; F_2) iff
#   vec ∈ span(BocksteinH1ToH2(C)) + B²(C; F_2)
# at the cochain level. Stack the image basis and the boundary subspace
# (rows of TransposedMat(BoundaryMatrixGF2(C))) into one matrix M and run
# SolutionMat against vec. The boundary subspace is necessary because the
# rows of BocksteinH1ToH2 only span im(β) modulo B² — concretely, on
# Z/2 × Z/2 with α := α₁+α₂, β(α) differs from β(α₁)+β(α₂) by the
# coboundary α₁∪α₂ + α₂∪α₁, so a row-span-only check would falsely reject
# β(α).
IsCoboundary2Mod2WithLift := function(C, c)
    local elts, n, b, i, j;
    # Slow-path adapter: build c_g_vec from the function and call the Vec API.
    elts := AsList(C);
    n := Length(elts);
    b := List([1..n*n], i -> 0);
    for i in [1..n] do
        for j in [1..n] do
            b[(i - 1) * n + j] := c(elts[i], elts[j]);
        od;
    od;
    return IsCoboundary2Mod2WithLiftVec(C, b);
end;;

# Module-level cache for the Bockstein-stacked solver matrix M = [img; B]
# and its SemiEchelonMatTransformation factorisation. Keyed on C.
# A-5b at m=5 calls IsCoboundary2Mod2WithLiftVec on at most 4 distinct
# centralisers (one per BRW orbit). Building M = [BocksteinH1ToH2(C); B]
# and factorising it once amortises across all subsequent solves.
_LiftSemCache := [];;

_GetLiftSemForC := function(C)
    local entry, img, B, M, sem, nonzero_heads;
    for entry in _LiftSemCache do
        if IsIdenticalObj(entry.C, C) then return entry; fi;
    od;
    img := BocksteinH1ToH2(C);
    B := TransposedMat(BoundaryMatrixGF2(C));
    if img = [] then
        M := B;
    else
        M := Concatenation(img, B);
        ConvertToMatrixRep(M, GF(2));
    fi;
    sem := SemiEchelonMatTransformation(M);
    # R2-2 (#177): same head-skip optimisation as _GetCachedSemForAT.
    nonzero_heads := Filtered([1..Length(sem.heads)], i -> sem.heads[i] <> 0);
    Add(_LiftSemCache, rec(C := C, sem := sem, nonzero_heads := nonzero_heads));
    return _LiftSemCache[Length(_LiftSemCache)];
end;;

# IsCoboundary2Mod2WithLiftVec(C, c_g_vec) — fast vectorised path. Identical
# to IsCoboundary2Mod2WithLift but takes a precomputed length-n² vector
# instead of a function c(h, k). Used by the A-5b sweep.
IsCoboundary2Mod2WithLiftVec := function(C, c_g_vec)
    local b, one, z, entry, sem, nonzero_heads, sol, sol_dim, i, vno, x;
    if IsCoboundary2Mod2Vec(C, c_g_vec) then return true; fi;

    one := One(GF(2));
    z := Zero(GF(2));
    b := List(c_g_vec, x -> (x mod 2) * one);
    ConvertToVectorRep(b, GF(2));

    entry := _GetLiftSemForC(C);
    sem := entry.sem;
    nonzero_heads := entry.nonzero_heads;
    if Length(sem.coeffs) = 0 then
        return IsZero(b);
    fi;
    sol_dim := Length(sem.coeffs[1]);
    sol := ListWithIdenticalEntries(sol_dim, z);
    ConvertToVectorRep(sol, GF(2));
    b := ShallowCopy(b);
    for i in nonzero_heads do
        vno := sem.heads[i];
        x := b[i];
        if x <> z then
            AddRowVector(b, sem.vectors[vno], -x);
            AddRowVector(sol, sem.coeffs[vno], x);
        fi;
    od;
    return IsZero(b);
end;;
