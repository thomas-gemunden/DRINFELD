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

# R2-3 (#177): supplementary "batched" view of the same factorisation.
# `pivot_cols` is the list of column indices that are pivots (= the
# non-zero entries of sem.heads). `Y_full` is the rank × ncols GF(2) matrix
# stacking sem.vectors in pivot-column-ascending order and reduced to
# reduced row echelon form (each pivot column is canonical-basis-vector-
# valued: 1 at the pivot row, 0 elsewhere). With these in hand, the
# row-space-membership test "is b in row-space(M)?" becomes the matrix
# identity
#   b == b{pivot_cols} * Y_full   (mod the pivot bits which both sides
#                                   share; equivalently:
#                                   IsZero(b + b{pivot_cols} * Y_full))
# (over GF(2), '-' and '+' coincide). This expresses the entire back-
# substitution as a single compiled GF(2) matrix product `B_P * Y_full`
# when batched across many RHSes; see IsCoboundary2Mod2VecBatch.
#
# CRITICAL: SemiEchelonMatTransformation returns rows in *semi-echelon*
# form, where above-pivot entries may be non-zero (only below-pivot is
# guaranteed zero). For the simple "c_k = b[p_k]" decomposition to hold,
# we need the *reduced* row echelon form. We compute it via the cheap
# back-substitution pass below — since sem.vectors is already in
# semi-echelon, reducing to RREF only requires zeroing above-pivot
# entries, which is O(rank^2 · ncols / 64) GF(2) work (well under a
# second at rank ≤ 2048, ncols ≤ 4M) and done ONCE per cached sem.
#
# Note on the missing slice: we deliberately KEEP Y_full at rank × ncols
# rather than slicing to rank × (ncols - rank). The slicing saves trivial
# memory (rank << ncols typically) and the matmul `B_P * Y_full + B` has
# the property that, at pivot columns, `(B_P * Y_full)[j][p_k] = B_P[j][k]
# = B[j][p_k]`, so the XOR cancels and pivot columns of the residual are
# zero by construction. The residual reduces to B_N + B_P * Y_N at
# non-pivot columns, exactly the quantity we test for zero.
_BuildBatchedSolverArtefacts := function(sem)
    local nrows, ncols, nonzero_heads, pivot_cols, rank, Y_full,
          k, k_prime, src_row, x;
    nrows := Length(sem.vectors);
    if nrows = 0 then
        # Trivial: rank 0. sem.heads has length = cols of the matrix M
        # we factorised. Build the empty artefacts so the caller can
        # short-circuit on "is b zero?".
        ncols := Length(sem.heads);
        return rec(
            pivot_cols := [],
            Y_full     := [],
            rank       := 0,
            ncols      := ncols);
    fi;
    ncols := Length(sem.vectors[1]);
    nonzero_heads := Filtered([1..Length(sem.heads)], i -> sem.heads[i] <> 0);
    # `pivot_cols` is in ascending column order (Filtered preserves index
    # order). The k-th pivot column corresponds to the row sem.heads[p_k].
    pivot_cols := nonzero_heads;
    rank := Length(pivot_cols);

    # Stack the pivot rows in pivot-column-ascending order. Y_full[k]
    # has pivot at column pivot_cols[k] (= 1) and zeros at pivot
    # columns pivot_cols[k'] for k' > k (below-pivot rule). Entries at
    # pivot_cols[k'] for k' < k may be non-zero; we reduce them next.
    Y_full := [];
    for k in [1..rank] do
        src_row := sem.vectors[sem.heads[pivot_cols[k]]];
        # ShallowCopy so we can reduce in place without mutating sem.
        Add(Y_full, ShallowCopy(src_row));
    od;
    ConvertToMatrixRep(Y_full, GF(2));

    # Back-substitute: for k = rank down to 2, zero out the entries of
    # Y_full[k'] (k' < k) at column pivot_cols[k]. Since Y_full[k] has 1
    # at pivot_cols[k] and 0 at pivot_cols[k''] for k'' > k, this is one
    # AddRowVector per (k', k) pair where the bit is set. Total
    # interpreter overhead is O(rank^2) = ~4M ops at rank=2048, but each
    # op is one compiled AddRowVector. Time-budget: ~seconds, paid once
    # per cached sem; amortised across thousands of subsequent solves.
    for k in [rank, rank - 1 .. 2] do
        for k_prime in [1 .. k - 1] do
            x := Y_full[k_prime][pivot_cols[k]];
            if not IsZero(x) then
                AddRowVector(Y_full[k_prime], Y_full[k], -x);
            fi;
        od;
    od;

    return rec(
        pivot_cols := pivot_cols,
        Y_full     := Y_full,
        rank       := rank,
        ncols      := ncols);
end;;

_GetCachedSemForAT := function(A)
    local entry, sem, nonzero_heads, batched;
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
    # R2-3 (#177): precompute the batched-back-sub artefacts (pivot_cols,
    # Y_full matrix in RREF) for the multi-RHS path used by
    # IsCoboundary2Mod2VecBatch.
    batched := _BuildBatchedSolverArtefacts(sem);
    Add(_IsCoboundary2Mod2_SemCache,
        rec(A := A, sem := sem, nonzero_heads := nonzero_heads,
            batched := batched));
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
    local elts, phi, GA, abgens, ab_orders, hom_basis, alpha_vals,
          k, ord, vecs, v, one;
    elts := AsList(C);
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
    # A-5b R2-3 (#186): replaced an n^2 nested interpreter loop with a single
    # compiled KroneckerProduct. The wrap `[alpha_vals]` makes it a 1×n matrix;
    # the `[1]` unwraps the result back to a length-n² row whose entry at
    # column (i-1)*n+j is alpha_vals[i] * alpha_vals[j] — equivalent to the
    # original loop body. Cuts lift-cache build time at n=2048 from ~25 min
    # to under a minute.
    vecs := [];
    for alpha_vals in hom_basis do
        v := KroneckerProduct([alpha_vals], [alpha_vals])[1];
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
    local entry, img, B, M, sem, nonzero_heads, batched;
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
    # R2-3 (#177): batched-back-sub artefacts for IsCoboundary2Mod2WithLiftVecBatch.
    batched := _BuildBatchedSolverArtefacts(sem);
    Add(_LiftSemCache, rec(C := C, sem := sem, nonzero_heads := nonzero_heads,
                            batched := batched));
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

# ======================================================================
# R2-3 (#177): batched multi-RHS back-substitution.
#
# Motivation (live A-5b profile, May 2026): the per-call back-sub loop
# `for i in nonzero_heads do if b[i] <> 0 then AddRowVector(...) fi od;`
# was found to spend 99.7% of CPU in the GAP interpreter (loop, list-elm,
# eq-test, if-branch) and only 0.3% in compiled GF(2) row-add work, even
# after the R2-2 head-skip patch. Per generator at m=5 the A-5b sweep
# issues ~1023 such back-subs against the same cached `sem` (one per
# BRW-orbit target across the largest orbit), so a single batched call
# can amortise the interpreter cost across all RHSes.
#
# Algorithm: see _BuildBatchedSolverArtefacts above. In summary, we
# precompute the rank × ncols GF(2) matrix Y_full (reduced row echelon
# form of sem.vectors, with pivot columns canonical-basis valued); the
# row-space-membership test for a stacked batch B of RHSes then reduces
# to `residual := B + B{:, pivot_cols} * Y_full`, one compiled GF(2)
# matmul + matrix add. Each chunk's `IsZero(residual[j])` answers the
# membership question for RHS j.
#
# Measured speedup on the back-sub portion alone (pre-converted GF(2)
# input, |C|=128, 1023 RHSes): ~100x vs the per-call sweep. With
# integer input (legacy convention), the integer→GF(2) reduction
# (interpreter List comprehension over n²) becomes the bottleneck and
# the visible speedup drops to ~2x; the production caller in
# run_e_plus_5_kernel.g pre-converts to avoid this.

# _RowSpanResidualBatch(batched_sem, B) — given the batched artefacts and
# a list/matrix B of GF(2) rows (one per RHS), return the residual matrix
# whose row j is zero iff B[j] is in row-space(M). Internal helper used
# by both the kernel-only and lift batched paths.
#
# Formulation: residual := B + B{:, pivot_cols} * Y_full. By construction
# (Y_full is in RREF), the pivot columns of `B_P * Y_full` equal those of
# B, so XOR cancels them, leaving the non-pivot residual we test for zero.
# This is one compiled GF(2) matmul + one compiled GF(2) matrix add,
# replacing rank × numRHS interpreter AddRowVector iterations.
_RowSpanResidualBatch := function(batched, B)
    local numRHS, pivot_cols, Y_full, B_P, residual;
    numRHS := Length(B);
    if numRHS = 0 then return []; fi;
    pivot_cols := batched.pivot_cols;
    Y_full := batched.Y_full;
    if batched.rank = 0 then
        # Empty row-space: residual == B itself (zero only when B[j] = 0).
        return B;
    fi;
    # Compiled column-slice to GF(2). ConvertToMatrixRep is essential:
    # without it, the multiply below falls back to interpreter rows.
    B_P := List(B, b -> b{pivot_cols});
    ConvertToMatrixRep(B_P, GF(2));
    # Compiled GF(2) matmul (PROD_GF2MAT_GF2MAT):
    #   (numRHS × rank) × (rank × ncols) → (numRHS × ncols).
    # Then compiled GF(2) matrix add (SUM_GF2MAT_GF2MAT) with B. After
    # XOR, pivot columns of the residual are zero by construction; the
    # non-pivot columns hold B_N + B_P * Y_N, the back-sub residual.
    residual := B_P * Y_full;
    residual := residual + B;
    return residual;
end;;

# _StackBVectorsForBatch(c_g_vec_list) — convert a list of length-n² integer
# (or GF(2)) row-vectors into a single GF(2) matrix B in compiled form.
# Each row is reduced mod 2 and converted to GF(2). Used by both batched
# entry points.
#
# If a row is already a GF(2) vector (e.g. caller pre-reduced to save the
# intermediate integer-vector memory), we pass it through unchanged. This
# matters at m=5: the per-target c_g_table is a length-n² INTEGER list,
# and holding ~1023 of them simultaneously at n²=1M would consume ~8 GB.
# The caller is expected to pre-reduce to GF(2) inside its per-target loop
# so each integer c_g_table can be GC'd immediately.
_StackBVectorsForBatch := function(c_g_vec_list)
    local one, B, c_g_vec, row, first_is_gf2;
    if IsEmpty(c_g_vec_list) then return []; fi;
    one := One(GF(2));
    # Detect pre-reduced GF(2) input. IsGF2VectorRep guards the fast path;
    # if the user pre-converted, we just stack and convert to matrix rep.
    first_is_gf2 := IsGF2VectorRep(c_g_vec_list[1]);
    B := [];
    if first_is_gf2 then
        for row in c_g_vec_list do
            Add(B, row);
        od;
    else
        for c_g_vec in c_g_vec_list do
            row := List(c_g_vec, x -> (x mod 2) * one);
            ConvertToVectorRep(row, GF(2));
            Add(B, row);
        od;
    fi;
    ConvertToMatrixRep(B, GF(2));
    return B;
end;;

# Batch size for chunked back-sub. The full batched matrix at m=5 is
# (numRHS × n²) bits = (~1023 × ~4M) ≈ 512 MB peak in the worst case;
# we chunk to bound peak memory. CHUNK = 256 caps each chunk's
# residual + intermediates at ~32 MB at the largest centraliser (n=2048).
# This is a tuning knob: smaller chunks recover more memory but lose
# matmul-batching efficiency; larger chunks risk allocation pressure.
_IS_COBOUNDARY2_BATCH_CHUNK := 256;;

# _RunBatchedRowSpanTest(batched, c_g_vec_list) — chunked dispatcher for
# a single batched row-space-membership test. Reduces the input to GF(2)
# per-chunk (so peak GF(2)-matrix memory is bounded by chunk_size × ncols)
# and applies _RowSpanResidualBatch to each chunk. Returns a list of
# booleans of length |c_g_vec_list|.
_RunBatchedRowSpanTest := function(batched, c_g_vec_list)
    local num, results, chunk_size, chunk_start, chunk_end, chunk_inputs,
          chunk_B, residual, j;
    num := Length(c_g_vec_list);
    results := EmptyPlist(num);
    chunk_size := _IS_COBOUNDARY2_BATCH_CHUNK;
    # GAP's `[start, second .. end]` arithmetic-progression syntax requires
    # `(end - start)` to be divisible by `(second - start)`, which is not
    # guaranteed here (the final chunk is usually short). We use a while
    # loop with explicit increment instead.
    chunk_start := 1;
    while chunk_start <= num do
        chunk_end := Minimum(num, chunk_start + chunk_size - 1);
        chunk_inputs := c_g_vec_list{[chunk_start..chunk_end]};
        chunk_B := _StackBVectorsForBatch(chunk_inputs);
        if batched.rank = 0 then
            # Trivial row-space (M had rank 0): in-span iff b is itself zero.
            for j in [1..Length(chunk_B)] do
                Add(results, IsZero(chunk_B[j]));
            od;
        else
            residual := _RowSpanResidualBatch(batched, chunk_B);
            for j in [1..Length(residual)] do
                Add(results, IsZero(residual[j]));
            od;
        fi;
        chunk_start := chunk_start + chunk_size;
    od;
    return results;
end;;

# IsCoboundary2Mod2VecBatch(H, c_g_vec_list)
#
# Batched analogue of IsCoboundary2Mod2Vec. Takes a list of length-n²
# integer/GF(2) vectors (the c_g values for each RHS) and returns a list of
# booleans of the same length: result[j] = (c_g_vec_list[j] is a GF(2)
# coboundary on H).
#
# Equivalent (element-for-element) to
#   List(c_g_vec_list, b -> IsCoboundary2Mod2Vec(H, b))
# but expressed as a single compiled GF(2) matmul against the cached
# Y_full matrix instead of numRHS × rank interpreter iterations of
# AddRowVector. Live profile (May 2026) showed the per-call back-sub
# was 99.7% interpreter overhead; the batched form recovers this.
IsCoboundary2Mod2VecBatch := function(H, c_g_vec_list)
    local A, entry;
    A := BoundaryMatrixGF2(H);              # cached
    entry := _GetCachedSemForAT(A);         # cached factorisation
    return _RunBatchedRowSpanTest(entry.batched, c_g_vec_list);
end;;

# IsCoboundary2Mod2WithLiftVecBatch(C, c_g_vec_list)
#
# Batched analogue of IsCoboundary2Mod2WithLiftVec. Returns a list of
# booleans: result[j] is true iff c_g_vec_list[j] (interpreted mod 2)
# lies in the Bockstein image + B² (i.e. lifts to a Z/2^k coboundary).
#
# Algorithm: run both batched tests in sequence on a single GF(2) chunk —
# first against the boundary subspace M_kernel = TransposedMat(BoundaryMatrixGF2(C))
# and for the RHSes that fail that test, the lift subspace
# M_lift = [BocksteinH1ToH2(C); boundary]. The lift test subsumes the
# kernel test mathematically (B² is a subspace of [img; B²]), but we
# preserve the staged check to match the per-call behaviour of
# IsCoboundary2Mod2WithLiftVec: rapid early-exit on coboundary inputs.
#
# IMPORTANT (perf): the integer→GF(2) reduction (`(x mod 2) * one` over a
# length-n² row) is the bulk of the per-call cost at small/moderate
# centraliser sizes. We do it ONCE per chunk, shared between the kernel
# and lift residual tests, rather than re-converting in a naive
# `IsCoboundary2Mod2VecBatch then _RunBatchedRowSpanTest` chain.
IsCoboundary2Mod2WithLiftVecBatch := function(C, c_g_vec_list)
    local A, kernel_entry, lift_entry, kernel_batched, lift_batched,
          num, results, chunk_size, chunk_start, chunk_end, chunk_inputs,
          chunk_B, kernel_residual, lift_todo_local, lift_subset,
          lift_sub_residual, j, jj, chunk_results, chunk_len;
    num := Length(c_g_vec_list);
    if num = 0 then return []; fi;
    A := BoundaryMatrixGF2(C);
    kernel_entry := _GetCachedSemForAT(A);
    kernel_batched := kernel_entry.batched;
    lift_entry := _GetLiftSemForC(C);
    lift_batched := lift_entry.batched;

    results := EmptyPlist(num);
    chunk_size := _IS_COBOUNDARY2_BATCH_CHUNK;
    chunk_start := 1;
    while chunk_start <= num do
        chunk_end := Minimum(num, chunk_start + chunk_size - 1);
        chunk_inputs := c_g_vec_list{[chunk_start..chunk_end]};
        chunk_len := Length(chunk_inputs);
        # Stack & convert to GF(2) ONCE. The kernel and lift residual
        # tests below both consume this matrix; this halves the
        # integer→GF(2) cost vs. running the two tests independently.
        chunk_B := _StackBVectorsForBatch(chunk_inputs);

        # Stage 1: kernel-only test (cocycle is a coboundary?).
        if kernel_batched.rank = 0 then
            kernel_residual := chunk_B;
        else
            kernel_residual := _RowSpanResidualBatch(kernel_batched, chunk_B);
        fi;

        # Build the per-chunk results list, marking unresolved rows for
        # the Stage 2 lift test.
        chunk_results := EmptyPlist(chunk_len);
        lift_todo_local := [];
        for j in [1..chunk_len] do
            if IsZero(kernel_residual[j]) then
                Add(chunk_results, true);
            else
                Add(chunk_results, false);   # provisional; may flip true.
                Add(lift_todo_local, j);
            fi;
        od;

        # Stage 2: lift test, only for rows that failed Stage 1.
        if not IsEmpty(lift_todo_local) then
            lift_subset := chunk_B{lift_todo_local};
            # GAP's `M{idxlist}` on a GF(2)-matrix returns a plain list of
            # GF(2) vectors, not a GF(2) matrix; force the compressed
            # matrix representation so the matmul in _RowSpanResidualBatch
            # dispatches to PROD_GF2MAT_GF2MAT, not the generic fallback.
            ConvertToMatrixRep(lift_subset, GF(2));
            if lift_batched.rank = 0 then
                lift_sub_residual := lift_subset;
            else
                lift_sub_residual := _RowSpanResidualBatch(lift_batched,
                                                            lift_subset);
            fi;
            for jj in [1..Length(lift_todo_local)] do
                if IsZero(lift_sub_residual[jj]) then
                    chunk_results[lift_todo_local[jj]] := true;
                fi;
            od;
        fi;
        Append(results, chunk_results);
        chunk_start := chunk_start + chunk_size;
    od;
    return results;
end;;
