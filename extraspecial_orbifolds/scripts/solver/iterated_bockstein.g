# iterated_bockstein.g — fast coboundary test for Z/2^k cochains.
#
# Replaces the slow Z/exp baseline (IsCoboundary2Zexp) for the canonical
# extraspecial-orbifold setting where the dispatcher's Path Z must decide
# whether a 2-cochain c : C × C -> Z/2^k is a coboundary.
#
# Algorithm. We iterate the SES
#     0 -> Z/2^(k-1)  -·²->  Z/2^k  -mod 2->  F_2  -> 0
# at each level. The associated long exact sequence in cohomology is
#     H¹(F_2) -β-> H²(Z/2^(k-1)) -·²-> H²(Z/2^k) -mod 2-> H²(F_2) -β-> H³(Z/2^(k-1))
# so [c] = 0 in H²(Z/2^k) iff
#   (a) [c mod 2] = 0 in H²(F_2), AND
#   (b) the lift [d_1] = [(c - δβ̃_0)/2] (with β_0 any F_2 witness for c mod 2)
#       is in im(β: H¹(F_2) -> H²(Z/2^(k-1))).
#
# Condition (b) at level 2 (Z/4) reduces, by another application of the LES,
# to "exists α ∈ Z¹(F_2) such that [d_1 - α∪α] = 0 in H²(Z/4)" — which by
# the chain-level identity δα̃/2 = α∪α (Bockstein cochain representative)
# is exactly the recursive question at level k-1.
#
# At the bottom (k = 2) we need the F_2-Bockstein-image test: this is
# exactly what IsCoboundary2Mod2WithLift implements.
#
# Why the simple "strict-coboundary at every level" iteration is wrong.
#
# A common but BUGGY shortcut tests [d_i mod 2] = 0 in H²(F_2) strictly at
# each level i. The diagnostic spike `spike_iterated_bockstein_correctness.g`
# (despite its name) actually shows this only achieves 37/75 agreement
# against the augmented-Z baseline on E_+(2) with a Path-Z-routable vec.
#
# The reason: at the second iteration (L = k-1 < k) the cocycle d_1 may
# represent a NON-zero class in H²(Z/2^(k-1)) that nevertheless lies in
# im(β: H¹(F_2) -> H²(Z/2^(k-1))). The strict mod-2 test rejects such
# cases, returning false even though [c] = 0 in H²(Z/2^k). The fix is to
# allow Bockstein-image freedom at every intermediate level above the
# F_2 base case — which we do by recursive enumeration of α at the
# WithLift correction step.
#
# Performance. Each IsCob call at level L > 1 does one strict F_2 solve
# plus 2^r recursive calls at level L-1 (r := F_2-rank of C^ab/2C^ab).
# At the bottom (L = 2) we delegate to IsCoboundary2Mod2WithLift, which
# itself enumerates 2^r α candidates internally. Total cost:
#    O((2^r)^(L-1) · F_2-solve(|C|))
# For E_+(2) (r ≤ 5, L = 3), this is at most 2^10 ≈ 1024 F_2 solves
# per Path Z call — easily sub-second. For E_+(3) (r ≤ 6, L = 4) it
# scales as 2^18 ≈ 256K solves; still tractable.
#
# Read-path note: this file is intended to be Read either directly from
# solver/ or from solver/tests/. We locate mod2_solver.g (companion file)
# by walking up from CWD until we find iterated_bockstein.g — same shim
# pattern as iscoboundary2_split.g.
itb_orig_dir := DirectoryCurrent();;
itb_target := fail;;
for itb_try in [".", "..", "../.."] do
    if IsExistingFile(Concatenation(itb_try, "/iterated_bockstein.g")) then
        itb_target := itb_try;
        break;
    fi;
od;;
if itb_target = fail then
    Error("iterated_bockstein.g: cannot locate companion files from CWD ",
          Filename(itb_orig_dir, ""));
fi;
ChangeDirectoryCurrent(itb_target);;
Read("mod2_solver.g");
ChangeDirectoryCurrent(Filename(itb_orig_dir, ""));;

# If_ helper: same convention as transgression_kernel.g and z4_fallback.g.
# Defined unconditionally (callers may have set it from a prior Read;
# redefinition is safe).
If_ := function(cond, a, b) if cond then return a; else return b; fi; end;;

# Module-level cache for A_F2_T := TransposedMat(BoundaryMatrixGF2(C)).
#
# A-5b R2-5 (#258): the per-call rebuild of A_F2_T inside IsCoboundary2Z2k
# was the dominant remaining bottleneck after the R2-3/R2-4 batched solver
# landed. Live profile (May 2026, PID 44998 post-PR-233) attributed ~2.5 %
# of total CPU to FuncTRANSPOSED_GF2MAT and the surrounding rebuild
# accounted for the majority of the remaining ~95 % interpreter overhead
# in ExecFor3/ExecAssList/EvalFunccall4args inside the Z2k Path-Z calls.
#
# At m=5 with |C|=1024 the boundary matrix is n^2 x n = 1M x 1024 = ~125 MB
# (compressed GF(2)), and TransposedMat moves ~1 GB of bits each call. The
# m=5 sweep issues thousands of Z2k calls per generator on a small number
# (~4) of distinct centralisers (one per BRW orbit), so caching by
# IsIdenticalObj(C) recovers nearly all of that cost.
#
# We mirror the pattern of _BoundaryMatrixGF2_cache in mod2_solver.g:
# the BoundaryMatrixGF2(C) call returns an IsIdenticalObj-stable matrix
# (also cached by C), so we key by C and hold the precomputed transpose.
_ItBock_AF2T_CACHE := [];;

_GetCachedAF2T := function(C)
    local entry, A_F2_T;
    for entry in _ItBock_AF2T_CACHE do
        if IsIdenticalObj(entry.C, C) then return entry.A_F2_T; fi;
    od;
    A_F2_T := TransposedMat(BoundaryMatrixGF2(C));
    Add(_ItBock_AF2T_CACHE, rec(C := C, A_F2_T := A_F2_T));
    return A_F2_T;
end;;

# Module-level cache for the multiplication table mult[i][j] := idx(elts[i] * elts[j]).
#
# A-5b R2-6 (#258 follow-up): IB_DeltaBeta does
#   ij := idx(elts[i] * elts[j])
# inside a nested n×n loop, where idx is `Position(elts, h)` — an O(n)
# linear scan over the centraliser. That makes IB_DeltaBeta O(n³).
# At m=5 with n = |C| = 1024, that's ~10⁹ ops per IB_DeltaBeta call,
# and IB_RecCob calls it per recursion level × 2^num_basis enumerated α.
#
# Precomputing mult_table once per C reduces IB_DeltaBeta to a pure
# O(n²) integer-arithmetic loop with O(1) compiled list lookups, and
# allows IB_AlphaCupAlpha-style operations to be done with vectorised
# indexing instead of element-by-element function calls.
_ItBock_MULT_CACHE := [];;

_GetCachedMultTable := function(C)
    local entry, elts, n, idx_dict, mult, i, j, prod_ij;
    for entry in _ItBock_MULT_CACHE do
        if IsIdenticalObj(entry.C, C) then return entry; fi;
    od;
    elts := AsList(C);
    n := Length(elts);
    idx_dict := NewDictionary(elts[1], true, elts);
    for i in [1..n] do AddDictionary(idx_dict, elts[i], i); od;
    mult := List([1..n], i -> List([1..n], j -> 0));
    for i in [1..n] do
        for j in [1..n] do
            prod_ij := elts[i] * elts[j];
            mult[i][j] := LookupDictionary(idx_dict, prod_ij);
        od;
    od;
    entry := rec(C := C, elts := elts, n := n,
                 idx_dict := idx_dict, mult := mult);
    Add(_ItBock_MULT_CACHE, entry);
    return entry;
end;;

# IsCoboundary2Mod2WithLiftWitness(C, c) — witness-returning variant of
# IsCoboundary2Mod2WithLift.
#
# Returns rec(is_coboundary, beta_F2, alpha_F2):
#   .is_coboundary : bool — whether [c mod 2] in im(β) + B²(C; F_2).
#   .beta_F2       : F_2 length-n list (β as a 1-cochain) such that
#                    c mod 2 = δβ + α∪α as F_2 2-cochains. Only meaningful
#                    when .is_coboundary = true.
#   .alpha_F2      : F_2 length-n list (α as a 1-cocycle, possibly zero)
#                    that picks up the Bockstein image part. Always a
#                    valid Z¹(C; F_2) cocycle; is the zero cochain when
#                    c mod 2 is already a strict coboundary.
#
# Algorithm: enumerate the at-most-2^|hom_basis| candidate α's (where
# hom_basis is the F_2 functional basis from BocksteinH1ToH2). For each
# α, compute α∪α as a length-n² F_2 vector, subtract from c mod 2, and
# test whether the residual is a strict F_2 coboundary; if so, return
# the matching α and the witness β. If no α works (including α = 0),
# return is_coboundary = false.
#
# For E_+(2) centralizers |hom_basis| ≤ 5, so at most 32 candidate α's.
# Each candidate is a single F_2 SolutionMat — fast.
IsCoboundary2Mod2WithLiftWitness := function(C, c)
    local elts, n, c_F2, A_F2_T, phi, GA, abgens, ab_orders, hom_basis,
          alpha_vals, k, ord, num_basis, mask, alpha, alpha_cup_alpha,
          residual, sol, beta_F2, i, j, zero, one;
    elts := AsList(C);
    n := Length(elts);
    zero := Zero(GF(2));
    one  := One(GF(2));

    # Build c mod 2 as an F_2 cochain on C×C, linearised as a length-n²
    # vector (row-major: index (i, j) -> (i-1)*n + j).
    c_F2 := List([1..n*n], i -> zero);
    for i in [1..n] do
        for j in [1..n] do
            c_F2[(i-1)*n + j] := (c(elts[i], elts[j]) mod 2) * one;
        od;
    od;
    ConvertToVectorRep(c_F2, GF(2));

    # A-5b R2-5 (#258): cached per-C (see _GetCachedAF2T below). This entry
    # point is far cooler than IsCoboundary2Z2k but the same cache covers it
    # for free.
    A_F2_T := _GetCachedAF2T(C);

    # Build the F_2-functional basis for H¹(C; F_2) (mirrors
    # BocksteinH1ToH2's construction but keeps the alpha-as-1-cochain).
    phi := MaximalAbelianQuotient(C);
    GA := Image(phi);
    abgens := IndependentGeneratorsOfAbelianGroup(GA);
    ab_orders := List(abgens, Order);
    hom_basis := [];
    for k in [1..Length(abgens)] do
        ord := ab_orders[k];
        if ord mod 2 = 0 then
            alpha_vals := List(elts, g ->
                (IndependentGeneratorExponents(GA, Image(phi, g))[k] mod 2) * one);
            Add(hom_basis, alpha_vals);
        fi;
    od;
    num_basis := Length(hom_basis);

    # Enumerate the 2^num_basis candidate α's. Mask = 0 means α = 0
    # (the strict-coboundary case); other masks pick subsets of the basis.
    for mask in [0..(2^num_basis - 1)] do
        # Build α as a length-n F_2 list = bitwise sum of selected basis
        # functionals.
        alpha := List([1..n], i -> zero);
        for k in [1..num_basis] do
            if (mask mod (2^k)) >= 2^(k-1) then
                alpha := alpha + hom_basis[k];
            fi;
        od;

        # Build α∪α as a length-n² F_2 vector.
        # A-5b R2-3 sibling (refs #186, #221): replaced an n^2 nested
        # interpreter loop with a single compiled KroneckerProduct. The wrap
        # `[alpha]` makes it a 1×n matrix; the `[1]` unwraps the result back
        # to a length-n² row whose entry at column (i-1)*n+j is
        # alpha[i] * alpha[j] — equivalent to the original loop body.
        # Mirrors the BocksteinH1ToH2 fix in mod2_solver.g.
        alpha_cup_alpha := KroneckerProduct([alpha], [alpha])[1];
        ConvertToVectorRep(alpha_cup_alpha, GF(2));

        # Test whether c_F2 - α∪α is a strict F_2 coboundary.
        residual := c_F2 - alpha_cup_alpha;
        sol := SolutionMat(A_F2_T, residual);
        if sol <> fail then
            beta_F2 := sol;
            return rec(is_coboundary := true,
                       beta_F2  := beta_F2,
                       alpha_F2 := alpha);
        fi;
    od;

    return rec(is_coboundary := false,
               beta_F2  := fail,
               alpha_F2 := fail);
end;;

# IB_F2HomBasis(C) — F_2 functional basis for H¹(C; F_2) as length-n
# integer (0/1) lists. Same construction as the F_2-version inside
# BocksteinH1ToH2, but keeping the α as a length-n list of integers
# rather than F_2 elements (so we can take {0,1}-lifts and form α∪α
# as an integer cochain).
IB_F2HomBasis := function(C)
    local elts, n, phi, GA, abgens, ab_orders, hom_basis, alpha_vals,
          k, ord;
    elts := AsList(C);
    n := Length(elts);
    phi := MaximalAbelianQuotient(C);
    GA := Image(phi);
    abgens := IndependentGeneratorsOfAbelianGroup(GA);
    ab_orders := List(abgens, Order);
    hom_basis := [];
    for k in [1..Length(abgens)] do
        ord := ab_orders[k];
        if ord mod 2 = 0 then
            alpha_vals := List(elts, g ->
                IndependentGeneratorExponents(GA, Image(phi, g))[k] mod 2);
            Add(hom_basis, alpha_vals);
        fi;
    od;
    return hom_basis;
end;;

# IB_AlphaFromMask(hom_basis, mask) — assemble α as a length-n list of
# 0/1 integers from the F_2 hom basis and a bitmask.
IB_AlphaFromMask := function(hom_basis, mask)
    local n, alpha, k, num_basis;
    num_basis := Length(hom_basis);
    if num_basis = 0 then return []; fi;
    n := Length(hom_basis[1]);
    alpha := List([1..n], i -> 0);
    for k in [1..num_basis] do
        if (mask mod (2^k)) >= 2^(k-1) then
            alpha := List([1..n], i -> (alpha[i] + hom_basis[k][i]) mod 2);
        fi;
    od;
    return alpha;
end;;

# IB_AlphaCupAlpha(alpha, n) — the cup-square (α∪α)(h, k) := α(h)·α(k)
# as a length-n² integer (0/1) cochain. Used to subtract Bockstein image
# corrections from a Z/2^L cochain table at any level.
#
# A-5b R2-9 (#258 follow-up): replace nested for-loop with compiled
# KroneckerProduct, matching the pattern landed in PR #221 / #225 for
# BocksteinH1ToH2 and IsCoboundary2Mod2WithLiftWitness. KroneckerProduct
# is called per α (up to 2^num_basis ≈ 2K-16K α candidates per Path Z
# class at m=5), so the per-call O(n²) interpreted loop dominated Path
# Z wall after the R2-5/R2-6/R2-7/R2-8 audit series eliminated the
# Path A bottlenecks.
IB_AlphaCupAlpha := function(alpha, n)
    if Length(alpha) = 0 then
        return List([1..n*n], i -> 0);
    fi;
    # GAP's KroneckerProduct on two 1xn matrices [alpha], [alpha] returns
    # a 1x(n*n) matrix whose only row is the outer product alpha ⊗ alpha,
    # laid out as v[(i-1)*n + j] = alpha[i] * alpha[j] — exactly the
    # cup-square. Returning [1] extracts the row.
    return KroneckerProduct([alpha], [alpha])[1];
end;;

# IsCob_aux(C, c_table, modulus, hom_basis, A_F2_T, elts, n, idx) —
# core recursive solver. c_table is the integer cochain table at the
# CURRENT modulus; modulus = 2^L.
#
# At L = 1 (modulus = 2): fall back to IsCoboundary2Mod2 by reading the
# table directly into an F_2 vector.
#
# At L ≥ 2: do the strict F_2 mod-2 coboundary test (yielding β_0); compute
# d_1 = (c_table - δβ̃_0)/2 at modulus 2^(L-1); enumerate α and recurse on
# (d_1 - α∪α) at modulus 2^(L-1). At L = 2 the inner test is exactly
# IsCoboundary2Mod2WithLift, which we delegate to as a fast path.
IB_DeltaBeta := function(beta_int, elts, n, idx, modulus)
    local delta_beta, i, j, ij;
    delta_beta := List([1..n*n], i -> 0);
    for i in [1..n] do
        for j in [1..n] do
            ij := idx(elts[i] * elts[j]);
            delta_beta[(i-1)*n + j] := (beta_int[i] + beta_int[j] - beta_int[ij]) mod modulus;
        od;
    od;
    return delta_beta;
end;;

# A-5b R2-6 (#258 follow-up): mult-cached variant. mult[i][j] is the
# 1-based index of elts[i] * elts[j] in elts, precomputed once per C.
# Pure O(n²) integer arithmetic; no Position lookups.
IB_DeltaBetaMult := function(beta_int, n, mult, modulus)
    local delta_beta, i, j, mult_i, beta_i, b;
    delta_beta := List([1..n*n], i -> 0);
    for i in [1..n] do
        mult_i := mult[i];
        beta_i := beta_int[i];
        for j in [1..n] do
            b := beta_i + beta_int[j] - beta_int[mult_i[j]];
            # `mod` is positive in GAP; for negative b we adjust:
            delta_beta[(i-1)*n + j] := b mod modulus;
        od;
    od;
    return delta_beta;
end;;

# Strict F_2 coboundary test on a c_table (modulus 2^L); returns the
# F_2 witness (as a list of 0/1 integers) or fail.
#
# Issue #367: previously called `SolutionMat(A_F2_T, b_F2)` directly,
# which does a fresh Gaussian elimination on a n × n^2 matrix per call.
# At m=5 (n up to 2048) this dominates the fail-column wall — each
# RREF is O(n^3 / 64) word ops, called ~1024 times per IB_RecCob, and
# the cached `_GetCachedSemForAT(C)` factorisation in mod2_solver.g
# was being bypassed. Routing through IsCoboundary2Mod2VecWithWitness
# reuses the cached factorisation; per-call cost drops to back-sub only.
IB_StrictF2Witness := function(C, c_table, n)
    local result;
    result := IsCoboundary2Mod2VecWithWitness(C,
                  List([1..n*n], i -> c_table[i] mod 2));
    if not result.yes then return fail; fi;
    return List(result.witness, x -> If_(IsZero(x), 0, 1));
end;;

# IB_TableMod2WithLift(C, c_table, n) — WithLift test operating
# directly on a length-n^2 integer table (avoids re-evaluating the
# cochain function).
#
# Issue #367: the original implementation enumerated all
# `2^num_basis` masks over IB_F2HomBasis(C) and, per mask, called
# `SolutionMat(A_F2_T, b - alpha cup alpha)`. On F_2 the cup-square
# `beta(alpha) = alpha cup alpha` is additive (mixed cross terms
# `alpha cup alpha' + alpha' cup alpha` are coboundaries), so the
# set {beta(alpha) : alpha in Hom(C, F_2)} modulo B^2 equals
# `span(BocksteinH1ToH2(C)) + B^2`. The mask enumeration was therefore
# computing exactly the same kernel-membership test that
# `IsCoboundary2Mod2WithLiftVec(C, c)` answers in a single back-
# substitution against the cached `_GetLiftSemForC(C)` factorisation.
# Replacing the loop with that single call cuts the per-IB_RecCob
# cost by `2^num_basis * <speedup from cached RREF>` — about 10^4x
# at m=5.
IB_TableMod2WithLift := function(C, c_table, n)
    return IsCoboundary2Mod2WithLiftVec(C,
               List([1..n*n], i -> c_table[i] mod 2));
end;;

# IB_DivBy2 — utility: subtract subtrahend (length-n² integers) from
# c_table (length-n² integers in [0..2*modulus)), assert divisibility
# by 2, divide, reduce mod modulus.
IB_DivBy2 := function(c_table, subtrahend, modulus)
    local n_eq, result, i, diff;
    n_eq := Length(c_table);
    result := List([1..n_eq], i -> 0);
    for i in [1..n_eq] do
        diff := (c_table[i] - subtrahend[i]) mod (2 * modulus);
        result[i] := (diff / 2) mod modulus;
    od;
    return result;
end;;

# IB_RecCob — the core recursion. Tests "[c_table] = 0 in H²(C; Z/modulus)"
# where modulus = 2^L. Uses precomputed centraliser data.
#
# A-5b R2-6 (#258 follow-up): the `mult` argument is the precomputed
# multiplication-index table from _GetCachedMultTable(C); when present,
# IB_DeltaBeta is dispatched to IB_DeltaBetaMult (pure O(n²) integer
# arithmetic) instead of the O(n³) Position-based path. `elts` and
# `idx` are kept in the signature for compatibility with the legacy
# fallback but are unused on the mult path.
IB_RecCob := function(C, c_table, modulus, elts, n, idx, A_F2_T, hom_basis, mult)
    local L, beta_int, delta_beta, c_table_next, mask, alpha,
          alpha_cup_alpha, c_table_shifted, num_basis;
    if modulus = 2 then
        # Base case: strict F_2 coboundary test.
        return IB_StrictF2Witness(C, c_table, n) <> fail;
    fi;

    # Strict mod-2 test on c_table (gives β_0).
    beta_int := IB_StrictF2Witness(C, c_table, n);
    if beta_int = fail then return false; fi;

    # Compute d_1 at modulus / 2.
    if mult <> fail then
        delta_beta := IB_DeltaBetaMult(beta_int, n, mult, modulus);
    else
        delta_beta := IB_DeltaBeta(beta_int, elts, n, idx, modulus);
    fi;
    c_table_next := IB_DivBy2(c_table, delta_beta, modulus / 2);

    # Now test [c_table_next] in im(β: H¹(F_2) -> H²(Z/(modulus/2)))
    # + B²(Z/(modulus/2)). Equivalently: ∃α ∈ Z¹(F_2) s.t.
    # [c_table_next - α∪α] = 0 in H²(Z/(modulus/2)).
    if modulus = 4 then
        # Inner level is modulus = 2 (F_2). The "[d - α∪α] = 0 in H²(F_2)
        # for some α" test is exactly IsCoboundary2Mod2WithLift on d.
        return IB_TableMod2WithLift(C, c_table_next, n);
    fi;

    # Inner level is modulus / 2 ≥ 4. Enumerate α and recurse.
    # Note: this path is not exercised at m=5 (where modulus = 4 takes
    # the IB_TableMod2WithLift fast path above) but remains for k >= 3.
    num_basis := Length(hom_basis);
    for mask in [0..(2^num_basis - 1)] do
        alpha := IB_AlphaFromMask(hom_basis, mask);
        if Length(alpha) = 0 then
            alpha_cup_alpha := List([1..n*n], i -> 0);
        else
            alpha_cup_alpha := IB_AlphaCupAlpha(alpha, n);
        fi;
        c_table_shifted := List([1..n*n], i ->
            (c_table_next[i] - alpha_cup_alpha[i]) mod (modulus / 2));
        if IB_RecCob(C, c_table_shifted, modulus / 2, elts, n, idx,
                     A_F2_T, hom_basis, mult) then
            return true;
        fi;
    od;
    return false;
end;;

# IsCoboundary2Z2k(C, c, k) — public entry point.
# Tests whether [c] = 0 in H²(C; Z/2^k). c is a 2-cochain function
# (h, k) -> Z (values reduced mod 2^k internally). k >= 1.
IsCoboundary2Z2k := function(C, c, k)
    local mult_rec, elts, n, idx, c_table, modulus, A_F2_T, hom_basis, i, j;
    if k < 1 then
        Error("IsCoboundary2Z2k: k must be >= 1");
    fi;
    if k = 1 then
        return IsCoboundary2Mod2(C, c);
    fi;

    # A-5b R2-6 (#258 follow-up): use cached mult table so IB_DeltaBeta
    # is O(n²) instead of O(n³). The cached record also holds elts so we
    # don't re-AsList.
    mult_rec := _GetCachedMultTable(C);
    elts := mult_rec.elts;
    n := mult_rec.n;
    idx := function(h) return LookupDictionary(mult_rec.idx_dict, h); end;

    modulus := 2^k;
    c_table := List([1..n*n], i -> 0);
    for i in [1..n] do
        for j in [1..n] do
            c_table[(i-1)*n + j] := c(elts[i], elts[j]) mod modulus;
        od;
    od;

    # A-5b R2-5 (#258): A_F2_T is built once per C and cached. Previously
    # this was rebuilt every IsCoboundary2Z2k call — at m=5 with |C|=1024
    # each rebuild moves ~1 GB of bits through TransposedMat, and the sweep
    # issues thousands of calls. The transpose dominates remaining wall.
    A_F2_T := _GetCachedAF2T(C);
    hom_basis := IB_F2HomBasis(C);

    return IB_RecCob(C, c_table, modulus, elts, n, idx, A_F2_T, hom_basis,
                     mult_rec.mult);
end;;
