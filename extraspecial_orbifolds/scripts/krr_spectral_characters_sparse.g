# K-4a-T4c sparse / trace-only variant of `krr_spectral_characters.g`.
#
# Issue #220 (follow-up to #208/#218): the dense `BuildKRRSpectralCharacters`
# materialises the full 2^k x 2^k intertwiner matrix T_h for each
# centraliser generator h. At m=5 that is ~4.3 billion entries x 27 ms
# ~= 3.7 years per matrix -- infeasible. At m=7 it is impossible at any
# realistic compute budget.
#
# This file replaces matrix construction + joint-eigendecomposition with
# a TRACE-ONLY formulation built on top of the existing closed-form
# entries in `defect_rep_minus_id_optim.g`:
#
# 1. Compute Tr(T_h) = sum_{c in F_2^k} (T_h)_{c, c} directly. Each trace
#    touches only 2^k diagonal entries (one per basis vector of W_a):
#       m = 3: 2^4 = 16 entries
#       m = 5: 2^16 = 65 536 entries
#       m = 7: 2^64 -- still infeasible naively, but see (3) below.
#
# 2. By character orthogonality of the centraliser C_G(a) = E(m), the
#    multiplicity of each irrep chi of C_G(a) in W_a is
#       mult_chi = (1 / |C_G(a)|)
#                  * sum_{h in C_G(a)} Tr(hat{T}_h) * chi(h^-1).
#    Since Tr(hat{T}_h) is a CLASS FUNCTION on C_G(a) (true for any
#    representation), the sum reduces to one trace per conjugacy class.
#    E(m) has 2 + 2^{2m} - 1 = 2^{2m} + 1 classes (two centralised
#    singletons {1}, {z} plus 2^{2m} - 1 size-2 classes {h, zh}).
#    At m=5 that is 1025 traces; at m=7 it is 16 385.
#
# 3. For the dim Tr to be tractable at m=7, we'd need to exploit that
#    the integrand (T_h)_{c, c} is a quadratic-Gauss-sum function of c.
#    The diagonal is zero outside a linear subspace L_h \subset F_2^k
#    (feasibility), and on L_h the value is +/- 2^{kerLen - dimND}
#    with sign determined by a quadratic F_2 form Q(c). The full sum
#    is therefore a standard F_2-Gauss sum, computable in poly(k) time.
#    This file implements the m=3, m=5 cases via naive c-enumeration
#    (vectorised over rows of `Cmat` in GAP); m=7 is left as a stub --
#    see `TraceOnOmega0Gauss` below.
#
# 4. The m=5 dominant cost is per-c arithmetic, not the linear solve.
#    Two further optimisations are in play:
#    - `_BuildTraceCtx(h, m)` precomputes the row reduction of BigPi(h)
#      once per h, plus all the other per-h matrices (H, R, Mhh,
#      MhhSym, AT, RT, HT, Sh).
#    - `TraceOnOmega0Batch(h, m)` vectorises the per-c inner loop:
#      builds dim x k matrix Cmat once, then computes targetMat, Xmat,
#      icMat, betaMat, betaTilde via GAP's native integer matrix
#      multiplication, reducing mod 2 only after each batch product.
#
# Interface matches the dense version `BuildKRRSpectralCharacters` in
# krr_spectral_characters.g exactly, so downstream callers can switch
# implementations without changes.
#
# DEPENDENCIES (loaded by the test driver, in this order):
#   bw_lattice.g, em_construction.g, twisted_group_algebra.g,
#   qforms_f2.g, defect_rep_minus_id.g, defect_rep_minus_id_optim.g,
#   untwisted_modular_data.g, krr_spectral_characters.g
#     (we reuse EmUnimodGroup, NormaliseIntertwiner from the dense version).


# ============================================================
# Sparse cache for per-h decomposition + trace computation.
# ============================================================

# Cache: list of (h, rec) pairs where rec contains the trace
# `Tr(T_h)` (NOT normalised) and `Tr_norm` (= Tr / 2^k).
_sparseTraceKeys := [];;
_sparseTraceVals := [];;

# Reset cache (used by tests).  Clears the trace cache only; the per-h
# `_traceHKeys` and (later-defined) `_gaussCtxKeys` caches are independent
# and reset via `ResetTraceHCache` / `ResetGaussCtxCache` respectively.
ResetSparseTraceCache := function()
    _sparseTraceKeys := [];
    _sparseTraceVals := [];
end;;


# ============================================================
# Per-h precomputation for fast trace evaluation.
#
# The dense closed-form `HardCodeShortComputeInterTwineref` recomputes
# `BigPi(h), H, A, R, Mhh, MhhSym, AT, F2_Trans(R), F2_Trans(H)`,
# row-reduces BigPi from scratch, and re-evaluates linear functionals
# on each c.  In the trace loop (one call per c in F_2^k) this
# duplication dominates the cost.  We precompute everything once.
# ============================================================

_traceHKeys := [];;
_traceHVals := [];;

ResetTraceHCache := function()
    _traceHKeys := [];
    _traceHVals := [];
end;;

# Build the per-h trace context.  Returns a record with all the
# matrices / row-reduction data needed for the per-c inner loop.
#
# Row-reduces BigPi(h) -- an n x n F_2 matrix -- once, storing pivot
# columns + a "back-substitution" map that turns any target row of
# length n into a particular solution x (length n) in O(n^2) time
# (vs O(n^3) via F2_SolveOneRow each call).
_BuildTraceCtx := function(h, m)
    local j, ctx, n, k, BPi, H, R, Mhh, A, AT, MhhSym, sht, RT, HT,
          hd, BPiT, augRows, r, c, i, A2, pivCols, pivRows, fullSol,
          rowOfRREF, freeMask, sumLen, mhhSym, B;
    # Identity-based cache lookup: we always pass the same matrix
    # object on repeat calls within a build, so IsIdenticalObj is
    # sufficient and avoids the O(n^2) matrix-equality fallback.
    for j in [1..Length(_traceHKeys)] do
        if IsIdenticalObj(_traceHKeys[j], h) then
            return _traceHVals[j];
        fi;
    od;
    n := 2^m;
    k := n / 2;
    hd := _efPerHData(h, m);
    sht := _efShAndTarget(h, m);
    B := BasisForN(m);
    R := TwoCocycleForN(m);
    Mhh := MhHalfefMat(h, m);
    A := Kernef(h, m);
    H := hd.H;
    BPi := hd.BPi;
    AT := F2_Trans(A);
    RT := F2_Trans(R);
    HT := F2_Trans(H);
    MhhSym := List([1..n], i ->
        List([1..n], j -> (Mhh[i][j] + Mhh[j][i]) mod 2));
    # Row-reduce BPi.  We solve x * BPi = target by reducing the
    # augmented matrix [BPi^T | target^T]; pre-reduce the BPi^T side.
    # A2 starts as BPi^T augmented with identity for back-substitution.
    BPiT := F2_Trans(BPi);  # n x n
    A2 := List([1..n], i -> Concatenation(BPiT[i], IdentityMat(n)[i]));
    r := 1;
    pivCols := [];
    pivRows := [];
    for c in [1..n] do
        if r > n then break; fi;
        i := r;
        while i <= n and A2[i][c] = 0 do i := i + 1; od;
        if i > n then continue; fi;
        if i <> r then A2{[r, i]} := A2{[i, r]}; fi;
        for j in [1..n] do
            if j <> r and A2[j][c] = 1 then
                A2[j] := List([1..2 * n],
                              i -> (A2[j][i] + A2[r][i]) mod 2);
            fi;
        od;
        Add(pivCols, c);
        Add(pivRows, r);
        r := r + 1;
    od;
    # After RREF:
    #   * For each pivot row p (column c = pivCols[p]):
    #       A2[p][1..n] has 1 at column c and 0 elsewhere among pivCols.
    #     A2[p][n+1..2n] is the row of P (n x n) such that
    #     P * BPi^T appears in row p as e_c.
    #   * For rows r..n (no pivots), A2[i][n+1..2n] gives a linear
    #     functional that must be 0 for feasibility.
    # Feasibility: target^T * P = (target . P_row) per row.
    # Construct as separate matrices to keep things fast:
    #   feasMat (rows n - rank, n) : if (feasMat * target^T) = 0 then
    #     target ∈ Im(BPi).
    #   solveMap (rank, n) : x in F_2^n s.t. (x[pivCols[i]]) = (solveMap[i] . target^T)
    #     for i in 1..rank.  Other x[c] = 0.
    ctx := rec(
        h := h, m := m, n := n, k := k,
        BPi := BPi, H := H, HT := HT, R := R, RT := RT,
        Mhh := Mhh, MhhSym := MhhSym,
        A := A, AT := AT, kerLen := Length(A),
        sht := sht,
        rank := Length(pivCols),
        pivCols := pivCols,
        # solveMap[i] (length n): x[pivCols[i]] = solveMap[i] . target.
        solveMap := List([1..Length(pivCols)], i -> A2[i]{[n+1..2*n]}),
        # feasMat (rows n - rank): rows are linear functionals on target;
        # target feasible iff all evaluate to 0.
        feasMat := List([Length(pivCols) + 1 .. n],
                        i -> A2[i]{[n+1..2*n]})
    );
    Add(_traceHKeys, h);
    Add(_traceHVals, ctx);
    return ctx;
end;;


# Solve x * BPi(h) = target using the precomputed pivot structure.
# Returns x as a length-n vector, or `fail` if infeasible.
_FastSolveX := function(ctx, target)
    local n, x, i, dot, fmat, k, smap, pcols;
    n := ctx.n;
    fmat := ctx.feasMat;
    # Feasibility check: feasMat * target should be 0.
    for i in [1..Length(fmat)] do
        dot := 0;
        for k in [1..n] do
            dot := dot + fmat[i][k] * target[k];
        od;
        if dot mod 2 <> 0 then return fail; fi;
    od;
    # Particular solution: x[pivCols[i]] = solveMap[i] . target; else 0.
    x := List([1..n], i -> 0);
    smap := ctx.solveMap;
    pcols := ctx.pivCols;
    for i in [1..Length(pcols)] do
        dot := 0;
        for k in [1..n] do
            dot := dot + smap[i][k] * target[k];
        od;
        x[pcols[i]] := dot mod 2;
    od;
    return x;
end;;


# Fast per-c entry computation for the trace: (T_h)_{c, c} with
# e = f = 0, sh = 0.  Equivalent to
# HardCodeShortComputeInterTwineref(h, 0, 0, c, c, 0, ...) but
# reuses ctx for all per-h matrices.
#
# Returns 0 (entry vanishes), or ±2^{kerLen - dimND} otherwise.
_TraceEntry := function(ctx, c)
    local target, x, n, k, kerLen, dimND, dimAn, dimSp, R, RT, H, HT,
          AT, Mhh, MhhSym, ic, gammaConst, beta, betaTilde, signExp,
          hpairProduct, i, term1, term2, term3, val, t1, t2, t3;
    n := ctx.n;
    k := ctx.k;
    # target = (c, c) as length-n vector.
    target := Concatenation(c, c);
    x := _FastSolveX(ctx, target);
    if x = fail then return 0; fi;
    R := ctx.R;
    H := ctx.H;
    HT := ctx.HT;
    RT := ctx.RT;
    AT := ctx.AT;
    Mhh := ctx.Mhh;
    MhhSym := ctx.MhhSym;
    kerLen := ctx.kerLen;
    # ic = Insertc(c) = length-n vector (0_k, c) with k = ctx.k.
    # ifv = Insertc(f) with f = 0, so ifv = (0_k, 0_k) = zero.
    # Since f = 0 and shift s = 0, the gamma and beta computations
    # simplify: term3 and the sAT term vanish.
    ic := Concatenation(List([1..k], i -> 0), c);
    # gammaConst = x*Mhh*x^T + x*H*R*ic^T  (f = 0, s = 0)
    gammaConst := F2_QuadDot(x, Mhh, x);
    t1 := F2_VMul(F2_VMul(x, H), R);
    gammaConst := (gammaConst + F2_Dot(t1, ic)) mod 2;
    # No f = 0 term, no shift term.
    if kerLen = 0 then
        if gammaConst = 0 then return 1; else return -1; fi;
    fi;
    # beta = x*(Mhh+Mhh^T)*A^T + Insertc(c)*R^T*H^T*A^T
    #         + Insertc(f)*R^T*A^T + s*A^T
    # With f = 0 and s = 0: beta = x*MhhSym*A^T + ic*RT*HT*AT.
    term1 := F2_VMul(F2_VMul(x, MhhSym), AT);
    t2 := F2_VMul(F2_VMul(F2_VMul(ic, RT), HT), AT);
    beta := List([1..kerLen], i -> (term1[i] + t2[i]) mod 2);
    betaTilde := F2_VMul(beta, ctx.sht.ShT);
    dimAn := ctx.sht.nDimAn;
    dimSp := ctx.sht.nDimSp;
    dimND := ctx.sht.nDimND;
    for i in [1..dimAn + dimSp] do
        if betaTilde[i] <> ctx.sht.t[i] then return 0; fi;
    od;
    hpairProduct := 0;
    for i in [1..dimND / 2] do
        hpairProduct := (hpairProduct
            + betaTilde[dimAn + dimSp + 2 * i - 1]
              * betaTilde[dimAn + dimSp + 2 * i]) mod 2;
    od;
    signExp := (gammaConst + hpairProduct) mod 2;
    if signExp = 0 then return 2^(kerLen - dimND); fi;
    return -(2^(kerLen - dimND));
end;;


# ============================================================
# TraceOnOmega0Naive(h, m): compute Tr(T_h) by summing diagonal
# entries directly, but using the optimised inner loop via
# _BuildTraceCtx + _TraceEntry.  Returns the UNNORMALISED trace.
# ============================================================
#
# Cost: 2^k calls to `_TraceEntry`, each O(n^2) (no row reductions).
# At m=3: 16 entries x O(64) ~ 1k ops.
# At m=5: 65k entries x O(1024) ~ 67M ops.  Estimated at ~1-2 seconds
# per trace in GAP if list ops are well-vectorised.
TraceOnOmega0Naive := function(h, m)
    local k, dim, c, ci, total, val, ctx;
    k := 2^(m - 1);
    dim := 2^k;
    ctx := _BuildTraceCtx(h, m);
    total := 0;
    for ci in [1..dim] do
        c := DecodeBitVec(ci, k);
        val := _TraceEntry(ctx, c);
        total := total + val;
    od;
    return total;
end;;


# ============================================================
# TraceOnOmega0Batch(h, m): compute Tr(T_h) by vectorising the
# per-c inner loop over GAP's native integer matrix multiplication.
# ============================================================
#
# Build a 2^k x k matrix Cmat of all c-vectors, then compute the
# per-c quantities (target, x, ic, gamma, beta_tilde) as 2^k-row
# matrices in single GAP `*` calls, finishing with a reduce-mod-2.
# This typically dominates the per-call GAP list-iteration overhead
# by ~10x at m=5.
_cmatCache := [];;

# Cmat for given m: 2^k x k matrix where row ci = DecodeBitVec(ci, k).
# Cached because it only depends on m and is used in every trace.
_GetCmat := function(m)
    local k, dim;
    k := 2^(m - 1);
    if not IsBound(_cmatCache[m]) then
        dim := 2^k;
        _cmatCache[m] := List([1..dim], ci -> DecodeBitVec(ci, k));
    fi;
    return _cmatCache[m];
end;;

TraceOnOmega0Batch := function(h, m)
    local k, n, dim, ctx, Cmat, i, j, c, ci,
          targetMat, # dim x n
          Xmat,      # dim x n
          icMat,     # dim x n
          gammaQuad, # dim, quadratic part x*Mhh*x^T (mod 2)
          gammaCross,# dim, x*H*R*ic^T (mod 2)
          gammaConst,# dim, total
          betaMat,   # dim x kerLen
          term1,     # dim x kerLen  : Xmat * MhhSym * AT
          term2,     # dim x kerLen  : icMat * RT * HT * AT
          betaTilde, # dim x kerLen
          dimAn, dimSp, dimND, kerLen, total, sign,
          feasMat, fmat_diag, infeasMask, matchTarget, mismatchMask,
          radical_len, sumXMhhX, XH, XHR, XHRiT, XMhhSym, icRT, icRTHT,
          icRTHTAT, hpair, hp_part, halfND, base_val, signExp;
    n := 2^m;
    k := n / 2;
    dim := 2^k;
    ctx := _BuildTraceCtx(h, m);
    kerLen := ctx.kerLen;
    dimAn := ctx.sht.nDimAn;
    dimSp := ctx.sht.nDimSp;
    dimND := ctx.sht.nDimND;
    radical_len := dimAn + dimSp;
    halfND := dimND / 2;
    # Build all c's as rows of a dim x k matrix (cached per m).
    Cmat := _GetCmat(m);
    # target(c) = (c, c) is dim x n.
    targetMat := List(Cmat, c -> Concatenation(c, c));
    # Feasibility: for each c, feasMat * target^T = 0 (mod 2).
    # feasMat is (n - rank) x n; we want infeasibility = nonzero entry.
    feasMat := ctx.feasMat;
    if Length(feasMat) > 0 then
        # feas_mat_apply: dim x #feas rows. Entry (i, j) = feasMat[j] . targetMat[i].
        # In GAP: targetMat * F2_Trans(feasMat) (integer mat-mat product), mod 2.
        # Anti-pattern P3+P6 fix (PR #402 A-K4-3): use compiled
        # matrix-mod-int `(M * V) mod 2` instead of double-closure
        # `List(M * V, row -> List(row, x -> x mod 2))`.
        fmat_diag := (targetMat * TransposedMat(feasMat)) mod 2;
        infeasMask := List(fmat_diag, row -> ForAny(row, e -> e <> 0));
    else
        infeasMask := List([1..dim], i -> false);
    fi;
    # x(c) = (solveMap rows) . target  ; put zero elsewhere.
    # Build dim x n Xmat.
    Xmat := List([1..dim], i -> List([1..n], j -> 0));
    if Length(ctx.solveMap) > 0 then
        # ctx.solveMap is rank x n; map[i] gives x[pivCols[i]] = map[i] . target.
        # Xmat[i][pivCols[j]] = solveMap[j] . target[i].
        # Compute dim x rank by  targetMat * F2_Trans(solveMap)  reduced mod 2.
        # Then scatter into x's pivot positions.
        i := targetMat * TransposedMat(ctx.solveMap);
        for j in [1..Length(ctx.pivCols)] do
            for ci in [1..dim] do
                Xmat[ci][ctx.pivCols[j]] := i[ci][j] mod 2;
            od;
        od;
    fi;
    # ic = (0_k, c) is dim x n.
    icMat := List(Cmat, c -> Concatenation(List([1..k], j -> 0), c));
    # gammaQuad = x*Mhh*x^T for each row: dim values.
    # XMhh = Xmat * Mhh : dim x n.
    # gammaQuad[ci] = Sum_j XMhh[ci][j] * Xmat[ci][j] (mod 2).
    sumXMhhX := Xmat * ctx.Mhh;
    gammaQuad := List([1..dim], ci ->
        Sum([1..n], j -> sumXMhhX[ci][j] * Xmat[ci][j]) mod 2);
    # gammaCross = x*H*R . ic for each row.
    # XH = Xmat * H : dim x n.  XHR = XH * R : dim x n.  Then dot with ic.
    XH := Xmat * ctx.H;
    # PR #402 A-K4-3: compiled `(M * V) mod 2` (was double-closure P3+P6).
    XHR := (XH * ctx.R) mod 2;
    gammaCross := List([1..dim], ci ->
        Sum([1..n], j -> XHR[ci][j] * icMat[ci][j]) mod 2);
    gammaConst := List([1..dim], ci ->
        (gammaQuad[ci] + gammaCross[ci]) mod 2);
    if kerLen = 0 then
        # Entries are ±1 depending on gammaConst (when feasible).
        total := 0;
        for ci in [1..dim] do
            if not infeasMask[ci] then
                if gammaConst[ci] = 0 then
                    total := total + 1;
                else
                    total := total - 1;
                fi;
            fi;
        od;
        return total;
    fi;
    # beta = x*MhhSym*AT + ic*RT*HT*AT : dim x kerLen.
    XMhhSym := Xmat * ctx.MhhSym;
    # PR #402 A-K4-3: compiled `(M * V) mod 2` (was double-closure P3+P6).
    term1 := (XMhhSym * ctx.AT) mod 2;
    icRT := icMat * ctx.RT;
    icRTHT := (icRT * ctx.HT) mod 2;
    icRTHTAT := (icRTHT * ctx.AT) mod 2;
    betaMat := List([1..dim], ci ->
        List([1..kerLen], j -> (term1[ci][j] + icRTHTAT[ci][j]) mod 2));
    # betaTilde = beta * ShT : dim x kerLen.
    # PR #402 A-K4-3: compiled `(M * V) mod 2` (was double-closure P3+P6).
    betaTilde := (betaMat * ctx.sht.ShT) mod 2;
    # Radical-match check: betaTilde[ci][1..radical_len] must equal sht.t[1..radical_len].
    matchTarget := ctx.sht.t{[1..radical_len]};
    mismatchMask := List([1..dim], ci ->
        ForAny([1..radical_len],
               i -> betaTilde[ci][i] <> matchTarget[i]));
    # hpair = sum_{i=1..halfND} betaTilde[radical_len + 2i - 1] * betaTilde[radical_len + 2i] (mod 2)
    hpair := List([1..dim], ci ->
        Sum([1..halfND], i ->
            betaTilde[ci][radical_len + 2 * i - 1]
            * betaTilde[ci][radical_len + 2 * i]) mod 2);
    base_val := 2^(kerLen - dimND);
    total := 0;
    for ci in [1..dim] do
        if infeasMask[ci] then continue; fi;
        if mismatchMask[ci] then continue; fi;
        signExp := (gammaConst[ci] + hpair[ci]) mod 2;
        if signExp = 0 then
            total := total + base_val;
        else
            total := total - base_val;
        fi;
    od;
    return total;
end;;


# ============================================================
# TraceOnOmega0Gauss(h, m): closed-form Gauss-sum evaluation of Tr(T_h).
# Issue #236 (parent #220, sibling of #234).
# ============================================================
#
# The diagonal entry (T_h)_{c, c} for c ∈ F_2^k is computed by the optim
# closed form `HardCodeShortComputeInterTwineref(h, 0, 0, c, c, 0, ...)`
# (see defect_rep_minus_id_optim.g). Tracing through it with e = f = 0,
# d = c, s = 0 we discover that, on the affine subspace
#
#     M_h = { c : feasMat * (c, c)^T = 0 AND BT_radmat * c^T = t_rad },
#
# the entry equals
#
#     (-1)^{phi(c)} * base_val,    base_val = 2^{kerLen - dimND}
#
# where phi(c) := gammaConst(c) + hpair(c) is a PURELY QUADRATIC F_2 form
# in c (no linear part, no constant — verified by inspection of each term
# at c = 0).  Off M_h the entry is 0.
#
# So Tr(T_h | Omega_0) = base_val * sum_{c ∈ M_h} (-1)^{phi(c)}.
#
# Reduction:
#   1. Compute affine subspace M_h: solve the joint linear system
#        [F_mat; BT_radmat] * c^T = [0; t_rad]^T
#      where F_mat = feasMat applied to c -> (c, c), and BT_radmat is
#      the radical-match-row block.  Returns c_0 + W_h (or empty).
#   2. Build the k x k F_2 matrix Q of phi: Q = Q1 + Q2 + Q3 with
#        Q1 = X_mat * Mhh * X_mat^T            (gamma quadratic part)
#        Q2 = X_mat * H * R * ic_mat^T         (gamma cross part)
#        Q3 = sum_i BT_odd[i] BT_even[i]^T     (hpair on non-deg part)
#      where X_mat is c -> x(c) (the lifted particular solution) and
#      ic_mat is c -> (0, c).
#   3. Pull phi back to W_h-coordinates: phi(c_0 + y * B_W) decomposes
#      as phi(c_0) + y * Q_psi * y^T + (linear-in-y) with the linear
#      part absorbed into Q_psi's diagonal over F_2.
#   4. Witt-decompose Q_psi (via `_F2_QuadGaussSum`):
#        a. Compute the alternating bilinear form B_psi = Q_psi + Q_psi^T
#           with zero diagonal.
#        b. Find radical Rad = ker(B_psi) and check Q_psi vanishes on
#           Rad's basis (else the Gauss sum is 0 because Q_psi restricted
#           to Rad has a non-trivial linear part).
#        c. Pick a standard-basis complement Bn of Rad with B_psi|<Bn>
#           non-degenerate alternating.  Compute a symplectic basis
#           {(alpha_i, beta_i)} for <Bn> via `_F2_FastSymplecticBasis`
#           (poly-time, O(d^3)).
#        d. Arf invariant = sum_i Q_psi(alpha_i) * Q_psi(beta_i) (mod 2).
#        e. G(Q_psi) = (-1)^{Arf} * 2^{|Rad| + |Bn|/2}.
#   5. Return base_val * (-1)^{phi(c_0)} * G(Q_psi).
#
# Cost analysis at m = 7 (k = 64):
#   * One k x k F_2 row reduction for the affine solve: O(k^3) = 250K ops.
#   * Building Q: a couple of k x n * n x k mat-muls: O(k^2 * n) = 500K ops.
#   * `_F2_QuadGaussSum`: O(k^3) = 250K ops (fast symplectic-basis algo,
#     no 2^d enumeration).
# Per-trace cost: dominated by `_BuildTraceCtx`'s n x n F_2 row reduction
# (n = 128 at m=7), O(n^3) ~= 2M ops.  Total for 16K classes: a minute or
# two.

# Solve x * A = b over F_2 for x of length nRows(A), and produce a basis
# of the kernel { x : x * A = 0 } as well.  Here we want a SOLVING-FROM-
# THE-RIGHT solve: A is rows x cols, c (length cols) satisfies A * c^T =
# b^T.  Equivalent to solving b = A * c^T = (A_transposed)^T * c^T, which
# is the same as solving b * I = c * A^T  on the left.
#
# Returns rec(particular := length-cols vector (or fail), kerBasis :=
# list of length-cols vectors) so that the full affine solution set is
#   { particular + sum_i e_i * kerBasis[i] : e_i in F_2 }.
_F2_AffineSolveCols := function(A, b)
    local rows, cols, M, r, c, i, j, k, pivCols, freeCols, x, kerBasis, v;
    rows := Length(A);
    if rows = 0 then
        # No constraints — any c is a solution, kernel is all of F_2^cols.
        # We don't know cols here; caller must handle this case.
        return rec(particular := [], kerBasis := []);
    fi;
    cols := Length(A[1]);
    # Augment A with b as the last column; row-reduce.
    M := List([1..rows], i ->
        Concatenation(List([1..cols], j -> A[i][j] mod 2), [b[i] mod 2]));
    r := 1;
    pivCols := [];
    for c in [1..cols] do
        if r > rows then break; fi;
        i := r;
        while i <= rows and M[i][c] = 0 do i := i + 1; od;
        if i > rows then continue; fi;
        if i <> r then M{[r, i]} := M{[i, r]}; fi;
        for j in [1..rows] do
            if j <> r and M[j][c] = 1 then
                M[j] := List([1..cols + 1],
                              k -> (M[j][k] + M[r][k]) mod 2);
            fi;
        od;
        Add(pivCols, c);
        r := r + 1;
    od;
    # Inconsistent if any row [0, 0, ..., 0 | 1] survives.
    for i in [r..rows] do
        if M[i][cols + 1] = 1 then
            return rec(particular := fail, kerBasis := []);
        fi;
    od;
    # Particular solution: pivot cols get the RHS, free cols get 0.
    x := List([1..cols], i -> 0);
    for i in [1..Length(pivCols)] do
        x[pivCols[i]] := M[i][cols + 1];
    od;
    # Kernel basis: one vector per free column.
    freeCols := Filtered([1..cols], c -> not (c in pivCols));
    kerBasis := [];
    for c in freeCols do
        v := List([1..cols], j -> 0);
        v[c] := 1;
        for i in [1..Length(pivCols)] do
            v[pivCols[i]] := M[i][c];
        od;
        Add(kerBasis, v);
    od;
    return rec(particular := x, kerBasis := kerBasis);
end;;


# Per-h ctx for the Gauss-sum trace formula.  Includes Q (the k x k F_2
# quadratic-form matrix of phi(c)), the radical-match constraint
# [BT_radmat | t_rad], and the feasibility constraint F_mat.  Cached by h.
_gaussCtxKeys := [];;
_gaussCtxVals := [];;

ResetGaussCtxCache := function()
    _gaussCtxKeys := [];
    _gaussCtxVals := [];
end;;

# Build the per-h Gauss-sum context.  Reuses `_BuildTraceCtx(h, m)` for the
# row-reduction of BigPi (gives feasMat and solveMap).
_BuildGaussCtx := function(h, m)
    local j, ctx, base, n, k, X_mat, ic_mat, feasMat, F_mat,
          solveMap, pivCols, Q1, Q2, Q3, L_mat, BT_mat, BT_radmat,
          BT_npod, BT_npev, radLen, dimND, halfND, sht,
          R, H, RT, HT, Mhh, MhhSym, AT, A, kerLen, t_rad,
          row, col, i, t1, t2;
    for j in [1..Length(_gaussCtxKeys)] do
        if IsIdenticalObj(_gaussCtxKeys[j], h) then
            return _gaussCtxVals[j];
        fi;
    od;
    base := _BuildTraceCtx(h, m);
    n := base.n;
    k := base.k;
    R := base.R; RT := base.RT;
    H := base.H; HT := base.HT;
    Mhh := base.Mhh; MhhSym := base.MhhSym;
    A := base.A; AT := base.AT;
    kerLen := base.kerLen;
    sht := base.sht;
    feasMat := base.feasMat;
    solveMap := base.solveMap;
    pivCols := base.pivCols;
    dimND := sht.nDimND;
    radLen := sht.nDimAn + sht.nDimSp;
    halfND := dimND / 2;
    # ---- Build X_mat (k x n): x(c) = c * X_mat ----
    # x(c)[p_j] = solveMap[j] . (c, c) = c · (left+right halves of solveMap[j]).
    # x(c)[non-pivot col] = 0.
    X_mat := List([1..k], i -> List([1..n], j -> 0));
    for j in [1..Length(pivCols)] do
        col := pivCols[j];
        for i in [1..k] do
            X_mat[i][col] := (solveMap[j][i] + solveMap[j][k + i]) mod 2;
        od;
    od;
    # ---- ic_mat (k x n): ic(c) = c * ic_mat = (0_k, c) ----
    ic_mat := List([1..k], i -> List([1..n], j -> 0));
    for i in [1..k] do
        ic_mat[i][k + i] := 1;
    od;
    # ---- F_mat (#feas x k): feasibility constraint F_mat * c^T = 0 ----
    # feasMat[r] . (c, c) = sum_i feasMat[r][i] * c[i] + feasMat[r][k+i] * c[i]
    #                   = sum_i (feasMat[r][i] + feasMat[r][k+i]) * c[i].
    F_mat := List([1..Length(feasMat)], i ->
        List([1..k], j -> (feasMat[i][j] + feasMat[i][k + j]) mod 2));
    # ---- Q1 = X_mat * Mhh * X_mat^T (k x k) ----
    Q1 := F2_Mul(F2_Mul(X_mat, Mhh), F2_Trans(X_mat));
    # ---- Q2 = X_mat * H * R * ic_mat^T (k x k) ----
    Q2 := F2_Mul(F2_Mul(F2_Mul(X_mat, H), R), F2_Trans(ic_mat));
    # ---- L_mat (k x kerLen): beta(c) = c * L_mat ----
    # L_mat = X_mat * MhhSym * A^T + ic_mat * R^T * H^T * A^T.
    if kerLen > 0 then
        t1 := F2_Mul(F2_Mul(X_mat, MhhSym), AT);
        t2 := F2_Mul(F2_Mul(F2_Mul(ic_mat, RT), HT), AT);
        L_mat := List([1..k], i ->
            List([1..kerLen], j -> (t1[i][j] + t2[i][j]) mod 2));
        # ---- BT_mat = L_mat * Sh^T (k x kerLen) ----
        BT_mat := F2_Mul(L_mat, sht.ShT);
        # Radical-match constraint: BT_radmat * c^T = t_rad where
        # BT_radmat[r] = BT_mat[*, r] for r in [1..radLen].
        BT_radmat := List([1..radLen], r -> List([1..k], i -> BT_mat[i][r]));
        t_rad := sht.t{[1..radLen]};
        # hpair(c) sum: build Q3 = sum_i BT_odd[i] * BT_even[i]^T.
        Q3 := List([1..k], i -> List([1..k], j -> 0));
        for i in [1..halfND] do
            BT_npod := List([1..k], j -> BT_mat[j][radLen + 2 * i - 1]);
            BT_npev := List([1..k], j -> BT_mat[j][radLen + 2 * i]);
            for row in [1..k] do
                for col in [1..k] do
                    Q3[row][col] := (Q3[row][col]
                        + BT_npod[row] * BT_npev[col]) mod 2;
                od;
            od;
        od;
    else
        L_mat := [];
        BT_mat := [];
        BT_radmat := [];
        t_rad := [];
        Q3 := List([1..k], i -> List([1..k], j -> 0));
    fi;
    # ---- Q = Q1 + Q2 + Q3 (k x k) ----
    ctx := rec(
        h := h, m := m, n := n, k := k,
        kerLen := kerLen,
        dimND := dimND,
        radLen := radLen,
        base_val := 2 ^ (kerLen - dimND),
        F_mat := F_mat,
        BT_radmat := BT_radmat,
        t_rad := t_rad,
        Q := List([1..k], i ->
            List([1..k], j -> (Q1[i][j] + Q2[i][j] + Q3[i][j]) mod 2))
    );
    Add(_gaussCtxKeys, h);
    Add(_gaussCtxVals, ctx);
    return ctx;
end;;


# Fast symplectic basis for an alternating non-degenerate bilinear form
# B on F_2^d (d even, B[i][i] = 0, B[i][j] = B[j][i] mod 2).
#
# Returns a list of 2 * (d/2) vectors [alpha_1, ..., alpha_r, beta_1,
# ..., beta_r] (r = d/2) such that B0(alpha_i, beta_j) = delta_{ij} and
# all other pairings are 0.
#
# Algorithm: standard symplectic Gauss elimination.  At each step:
#   1. Find a non-zero pair (i, j) in the current B (among rows that
#      still need processing).
#   2. Use rows i and j as the next hyperbolic pair (alpha, beta).
#   3. Orthogonalise EVERY OTHER row r_l against (i, j):
#        r_l_new := r_l + B(r_l, beta) * alpha + B(r_l, alpha) * beta.
#      This zeroes B(r_l, alpha) and B(r_l, beta) for all l != i, j.
#   4. After step 3, rows i and j are "done" — no further updates needed
#      (their B-pairings with the other rows are now 0 and 1, fixed).
#   5. Remove rows i and j from the active set; recurse.
#
# Implementation note: we maintain `basis` (a d x d F_2 matrix, each row
# a vector in the ambient F_2^d) and `B` (the bilinear form in the
# CURRENT basis: B[i][j] = B0(basis[i], basis[j])).  Initially basis is
# the identity and B = B0.  After each iteration the invariant holds
# because we update B and basis in lockstep.
#
# `done` flags slots that have been finalised into a pair (their basis
# rows / B entries are frozen; we still need to keep the rows readable
# for the alpha/beta outputs but won't touch them again).
_F2_FastSymplecticBasis := function(B0)
    local d, B, basis, alphas, betas, done, halfd, found, foundI, foundJ,
          i, j, k, l, t, alpha, beta, c_alpha, c_beta, alphaI, betaI;
    d := Length(B0);
    if d = 0 then return []; fi;
    if d mod 2 = 1 then
        Error("_F2_FastSymplecticBasis: B has odd dimension ", d,
              "; cannot be non-degenerate alternating.");
    fi;
    B := List(B0, ShallowCopy);
    basis := IdentityMat(d);
    done := List([1..d], i -> false);
    halfd := d / 2;
    alphas := [];
    betas := [];
    for k in [1..halfd] do
        # Find first pair (foundI, foundJ) of NOT-done slots with B[i][j] = 1.
        found := false; foundI := 0; foundJ := 0;
        for i in [1..d] do
            if done[i] then continue; fi;
            for j in [i+1..d] do
                if done[j] then continue; fi;
                if B[i][j] = 1 then
                    foundI := i; foundJ := j; found := true; break;
                fi;
            od;
            if found then break; fi;
        od;
        if not found then
            Error("_F2_FastSymplecticBasis: form became degenerate at ",
                  "pair ", k, " of ", halfd);
        fi;
        alphaI := foundI; betaI := foundJ;
        alpha := basis[alphaI];
        beta := basis[betaI];
        Add(alphas, alpha);
        Add(betas, beta);
        # Orthogonalise EVERY l != alphaI, betaI (including done ones!) so
        # the B-matrix invariant holds.  We use the current B[alphaI][t]
        # and B[betaI][t] (which reflect the CURRENT basis pairings),
        # update basis[l], then update B[l][t] and B[t][l] for all t.
        # Caveat: alpha and beta rows are STILL pairs of basis vectors;
        # we just won't pair them again in future search.  Their B-rows
        # are now frozen with the pattern: B[alphaI][alphaI] = 0,
        # B[alphaI][betaI] = 1, B[alphaI][other] = 0; ditto for betaI.
        for l in [1..d] do
            if l = alphaI or l = betaI then continue; fi;
            c_alpha := B[l][betaI];   # coefficient of alpha in update
            c_beta  := B[l][alphaI];  # coefficient of beta in update
            if c_alpha = 0 and c_beta = 0 then continue; fi;
            # Update basis[l] -> basis[l] + c_alpha * alpha + c_beta * beta.
            if c_alpha = 1 then
                for t in [1..d] do
                    basis[l][t] := (basis[l][t] + alpha[t]) mod 2;
                od;
            fi;
            if c_beta = 1 then
                for t in [1..d] do
                    basis[l][t] := (basis[l][t] + beta[t]) mod 2;
                od;
            fi;
            # Update B[l][m] for m != alphaI, betaI:
            #   B_new(r_l, r_m) = B(r_l, r_m)
            #                    + c_alpha * B(alpha, r_m)
            #                    + c_beta  * B(beta, r_m).
            # In current coords B(alpha, r_m) = B[alphaI][m],
            # B(beta, r_m) = B[betaI][m].
            for t in [1..d] do
                if t = alphaI or t = betaI then continue; fi;
                B[l][t] := (B[l][t]
                            + c_alpha * B[alphaI][t]
                            + c_beta  * B[betaI][t]) mod 2;
                B[t][l] := B[l][t];
            od;
            # By construction, basis[l]_NEW is orthogonal to alpha and
            # beta, so B[l][alphaI] = B[l][betaI] = 0.
            B[l][alphaI] := 0;  B[alphaI][l] := 0;
            B[l][betaI]  := 0;  B[betaI][l]  := 0;
        od;
        done[alphaI] := true;
        done[betaI] := true;
    od;
    return Concatenation(alphas, betas);
end;;


# Quadratic-form Gauss sum G(Q_psi) = sum_{y in F_2^d} (-1)^{Q_psi(y)} for
# a d x d F_2 matrix Q_psi (with Q_psi[i][i] interpreted as the linear
# coefficient of y_i, since y_i^2 = y_i over F_2).  Returns an integer
# (possibly 0).
#
# Algorithm:
#   1. Compute the associated bilinear form B(u, v) = Q(u+v) + Q(u) + Q(v).
#      In matrix form: B = (Q + Q^T) with diagonal zeroed.
#   2. Find a basis of the radical R = { v : v B = 0 }.
#   3. Q-radical contribution: Q|R is LINEAR (since B = 0 there).
#      If Q|R is non-trivially linear (i.e. takes value 1 anywhere), the
#      Gauss sum vanishes.  Equivalently: if Q(b) = 1 for any radical
#      basis vector b, return 0.
#   4. Otherwise the radical contributes a factor 2^{|R|}.
#   5. Complement of the radical in F_2^d: pick a basis-complement Bn so
#      that <Bn> is a non-degenerate subspace for B.  This subspace has
#      even dim 2 r' (r' = rank(B)/2).
#   6. Symplectic basis for B|<Bn> via `_F2_FastSymplecticBasis` (O(d^3)
#      time, no 2^d enumeration unlike `SymplecticBasisF2`).  Returns
#      [alpha_1, ..., alpha_r', beta_1, ..., beta_r'] with B(alpha_i,
#      beta_j) = delta_ij and other pairings 0.
#   7. Arf invariant: Arf(Q|<Bn>) = sum_i Q(alpha_i) * Q(beta_i)  (mod 2).
#      Sign on non-degenerate part: (-1)^{Arf} = +1 (Arf=0) or -1 (Arf=1).
#   8. Total Gauss sum = (-1)^{Arf} * 2^{|R| + r'}.
#
# Cost: O(d^3).  At m=7 (d <= k = 64) this is ~250K ops per call.  The
# textbook `QuadStandardFormChar2` (in qforms_f2.g) uses
# `FindHyperBolicPair`, enumerating 2^d candidate vectors — that's
# 2^64 = 1.8e19 ops at m=7, infeasible.  The fast symplectic-basis
# algorithm above is what makes the m=7 path tractable.
_F2_QuadGaussSum := function(Q_psi)
    local d, B, Bd, Bn, qval, dimRad, halfND, B_nd,
          i, j, sympBasis, basis_ambient,
          arf, sign, Qval_e, Qval_f, dimBn;
    d := Length(Q_psi);
    if d = 0 then return 1; fi;
    # Bilinear form B = Q_psi + Q_psi^T with zero diagonal.
    B := List([1..d], i -> List([1..d], j -> 0));
    for i in [1..d] do
        for j in [1..d] do
            if i <> j then
                B[i][j] := (Q_psi[i][j] + Q_psi[j][i]) mod 2;
            fi;
        od;
    od;
    # Bd: basis of radical (left nullspace of B).
    Bd := F2LeftNullspace(B);
    dimRad := Length(Bd);
    # Check Q|radical is identically zero.
    for i in [1..dimRad] do
        qval := QFormEval(Q_psi, Bd[i]);
        if qval = 1 then return 0; fi;
    od;
    if dimRad = d then
        # Whole space is radical; Q is identically 0 there.
        return 2 ^ d;
    fi;
    # Bn: standard-basis complement of Bd in F_2^d.
    Bn := F2ComplementStandardBasis(Bd, d);
    dimBn := Length(Bn);
    # Restrict B to <Bn>.  In <Bn>-coords, B_nd[i][j] = B(Bn[i], Bn[j]).
    # Compute as Bn * B * Bn^T (mod 2).
    B_nd := F2_Mul(F2_Mul(Bn, B), F2_Trans(Bn));
    # Force diagonal to 0 (alternating form).
    for i in [1..dimBn] do B_nd[i][i] := 0; od;
    # Symplectic basis for B_nd in <Bn>-coords: returns 2*r' rows
    # [alpha_1, ..., alpha_r', beta_1, ..., beta_r'] each length dimBn.
    # We use the fast poly-time variant (see _F2_FastSymplecticBasis);
    # the textbook `SymplecticBasisF2` from defect_rep_minus_id.g is
    # quintic in dim and untenable at m=7 (dimBn up to 64).
    sympBasis := _F2_FastSymplecticBasis(B_nd);
    halfND := dimBn / 2;
    # Lift each row of sympBasis back to ambient F_2^d: row i in
    # <Bn>-coords -> row * Bn (vector in F_2^d).
    basis_ambient := List(sympBasis, row -> F2_VMul(row, Bn));
    # Arf invariant: sum_i Q(alpha_i) * Q(beta_i) (mod 2).
    arf := 0;
    for i in [1..halfND] do
        Qval_e := QFormEval(Q_psi, basis_ambient[i]);
        Qval_f := QFormEval(Q_psi, basis_ambient[halfND + i]);
        arf := (arf + Qval_e * Qval_f) mod 2;
    od;
    if arf = 0 then sign := 1; else sign := -1; fi;
    return sign * 2 ^ (dimRad + halfND);
end;;


# Returns Tr(T_h | Omega_0) via closed-form Gauss sum.
#   h : centraliser element (E(m)-rep).
#   m : extraspecial 2-group parameter.
# Output: an integer.
TraceOnOmega0Gauss := function(h, m)
    local ctx, n, k, joint_A, joint_b, sol, c_0, B_W, dimW, B_W_mat,
          phi_c0, Q, Q_sym, L_y, Q_psi, i, gsum,
          BWQ, BW_QT_BWT;
    ctx := _BuildGaussCtx(h, m);
    n := ctx.n;
    k := ctx.k;
    # Affine system: rows = F_mat then BT_radmat, RHS = zeros then t_rad.
    if Length(ctx.F_mat) = 0 and Length(ctx.BT_radmat) = 0 then
        # No constraints: M_h = F_2^k.  Use a special path: c_0 = zeros,
        # W_h = F_2^k.
        c_0 := List([1..k], i -> 0);
        B_W := IdentityMat(k);
    else
        joint_A := Concatenation(ctx.F_mat, ctx.BT_radmat);
        joint_b := Concatenation(List([1..Length(ctx.F_mat)], i -> 0),
                                  ctx.t_rad);
        sol := _F2_AffineSolveCols(joint_A, joint_b);
        if sol.particular = fail then
            return 0;
        fi;
        c_0 := sol.particular;
        B_W := sol.kerBasis;
    fi;
    dimW := Length(B_W);
    Q := ctx.Q;
    # phi(c_0) = c_0 * Q * c_0^T mod 2.
    phi_c0 := QFormEval(Q, c_0);
    if dimW = 0 then
        # M_h is a single point c_0.
        if phi_c0 = 0 then
            return ctx.base_val;
        else
            return - ctx.base_val;
        fi;
    fi;
    # Substitute c = c_0 + y * B_W.  Then:
    #   phi(c) = phi(c_0) + B_phi(c_0, y B_W) + phi(y B_W)  (mod 2)
    # where B_phi(u, v) = u (Q + Q^T) v^T.
    # Quadratic part in y: y * B_W * Q * B_W^T * y^T.
    # Cross part: c_0 (Q + Q^T) (y B_W)^T = c_0 (Q + Q^T) B_W^T y^T.
    # As a linear form in y, L_y = c_0 (Q + Q^T) B_W^T  (row of length dimW).
    B_W_mat := B_W;   # dimW x k
    Q_sym := List([1..k], i ->
        List([1..k], j -> (Q[i][j] + Q[j][i]) mod 2));
    # L_y = c_0 * Q_sym * B_W^T  (row of length dimW), reduce mod 2.
    L_y := F2_VMul(F2_VMul(c_0, Q_sym), F2_Trans(B_W_mat));
    # Q_psi (dimW x dimW): B_W * Q * B_W^T  + diag(L_y) (linear-in-y as
    # quadratic over F_2).
    BWQ := F2_Mul(B_W_mat, Q);     # dimW x k
    BW_QT_BWT := F2_Mul(BWQ, F2_Trans(B_W_mat));   # dimW x dimW
    Q_psi := List([1..dimW], i ->
        List([1..dimW], j -> BW_QT_BWT[i][j]));
    for i in [1..dimW] do
        Q_psi[i][i] := (Q_psi[i][i] + L_y[i]) mod 2;
    od;
    # Gauss sum of psi on F_2^dimW.
    gsum := _F2_QuadGaussSum(Q_psi);
    if gsum = 0 then return 0; fi;
    if phi_c0 = 1 then gsum := - gsum; fi;
    return ctx.base_val * gsum;
end;;


# ============================================================
# TraceOnOmega0(h, m): top-level trace dispatcher.  Caches
# results per h.
# ============================================================
#
# Returns the NORMALISED trace Tr(hat{T}_h) = Tr(T_h) / 2^k.
#
# Implementation choice:
#   * m <= 5 : `TraceOnOmega0Batch` (entry-sum over 2^k diagonal entries).
#     Concrete: m=3 has 16 entries; m=5 has 65536. Both fast enough that
#     the closed-form Gauss-sum buys no asymptotic improvement.
#   * m >= 7 : `TraceOnOmega0Gauss` (closed-form Witt-decomposition).
#     At m=7 the entry-sum would be 2^64 entries per trace — infeasible.
#     The Gauss-sum cost is O(k^3) = ~250K ops per trace.
TraceOnOmega0 := function(h, m)
    local j, k, raw, norm;
    for j in [1..Length(_sparseTraceKeys)] do
        if IsIdenticalObj(_sparseTraceKeys[j], h) then
            return _sparseTraceVals[j].Tr_norm;
        fi;
    od;
    k := 2^(m - 1);
    if m >= 7 then
        raw := TraceOnOmega0Gauss(h, m);
    else
        raw := TraceOnOmega0Batch(h, m);
    fi;
    norm := raw / 2^k;
    Add(_sparseTraceKeys, h);
    Add(_sparseTraceVals, rec(Tr_raw := raw, Tr_norm := norm));
    return norm;
end;;


# ============================================================
# Class-function trace computation.
#
# Since hat{T}_h is a representation, Tr(hat{T}_h) is a class function
# on C_G(a) (the centraliser).  At m=5 this saves a factor of ~2
# (the trace is constant on each of the |E(m)|/2 conjugacy classes
# of size 2, plus 2 singletons).  We compute one trace per class.
# ============================================================

# Return parallel lists (class_reps, class_sizes) for C such that
# C = union of size class_sizes[i] orbits, each containing class_reps[i].
CentraliserClassData := function(idx, class_idx)
    local C, cc;
    C := idx.centralisers[class_idx];
    cc := ConjugacyClasses(C);
    return rec(
        classes := cc,
        reps := List(cc, Representative),
        sizes := List(cc, Size),
        num := Length(cc)
    );
end;;


# ============================================================
# CharacterMultiplicities(idx, class_idx, cls_data, traces):
# Given Tr(hat{T}_h) on each conjugacy class of C_G(a) (passed
# as parallel lists `cls_data.reps` / `traces` / `cls_data.sizes`),
# compute the multiplicity m_chi of each chi in Irr(C_G(a)) in W_a.
# ============================================================
#
# Using the class formulation of character orthogonality:
#   mult_chi = (1 / |G|) * sum_{class K} |K| * Tr_K * chi(K)^*
# This needs only |conjugacy classes of C_G(a)| trace values, not
# all |C_G(a)| elements.
#
# Note: idx already has ct_centraliser and cc_centraliser; we use those
# directly, but we need the ConjugacyClasses(C) here to align with
# `cls_data.reps`.  These two lists are *the same* (same C, same
# orderings via GAP's `ConjugacyClasses` determinism), so we can just
# use idx.cc_centraliser[class_idx] order to evaluate characters.
CharacterMultiplicities := function(idx, class_idx, cls_data, traces)
    local C, order, irreps, num_irreps, mults, k, chi, total, j,
          cc_idx, ki, val, h, tr;
    C := idx.centralisers[class_idx];
    order := Size(C);
    irreps := idx.irreps[class_idx];
    num_irreps := idx.num_irreps[class_idx];
    mults := [];
    # Convert each cls_data.reps[j] to the corresponding character-table
    # class index (idx.cc_centraliser[class_idx] ordering).
    cc_idx := List(cls_data.reps,
                   h -> ClassIndexInCentraliser(idx, class_idx, h));
    for k in [1..num_irreps] do
        chi := irreps[k];
        total := 0;
        for j in [1..cls_data.num] do
            tr := traces[j];
            val := chi[cc_idx[j]];
            total := total + cls_data.sizes[j] * tr * ComplexConjugate(val);
        od;
        Add(mults, total / order);
    od;
    return mults;
end;;


# ============================================================
# BuildKRRSpectralCharactersSparse(m): top-level entry point.
# Mirrors the dense `BuildKRRSpectralCharacters(m)` interface.
# ============================================================
#
# Returns rec(
#   group           := EmUnimodGroup(m),
#   idx             := BuildSimpleIndex(G),
#   m               := m,
#   trace_on_W      := function(class_idx, irrep_idx, h) -> ...,
#   character_match := per-class list of
#                      rec(standard_irrep_idx, mult),
#   multiplicities  := per-class list of mult_chi (parallel to
#                      idx.irreps[class_idx]),
#   centraliser_traces := per-class list of (h -> Tr(hat{T}_h)) tables
#                         (parallel to centraliser elements),
#   source          := "krr-sparse"
# )
#
# Semantics for trace_on_W(class_idx, irrep_idx, h):
#   - For the central class -I:
#       returns mult_chi * chi(h)
#     where chi = idx.irreps[class_idx][irrep_idx] (the irrep_idx-th
#     character of C_G(-I)) and mult_chi is the multiplicity computed
#     via orthogonality.
#   - For non-central classes: falls back to EvalIrr (standard
#     centraliser-character functional, same as dense version).
#
# This matches `BuildIntertwinerDataUntwisted` semantics on non-central
# classes; on the central class we return the spectral-trace-weighted
# character per CGR (eq 5.20 / 5.21) under epsilon = 1.

BuildKRRSpectralCharactersSparse := function(m)
    local n, k, dim, G, idx, num_classes, character_match, multiplicities,
          centraliser_traces, trace_on_W, i, a, z, idMat, C, cls_data,
          traces, mults, em, j, h, t0, t1, useLazy;
    n := 2^m;
    k := n / 2;
    dim := 2^k;
    G := EmUnimodGroup(m);
    # For m >= 5, the eager BuildSimpleIndex hits a memory limit while
    # iterating CharacterTable over all 1025 centralisers.  Switch to
    # the lazy variant -- only the central class CT gets materialised
    # by this function; non-central CTs are loaded on-demand by the
    # trace_on_W EvalIrr fallback.
    useLazy := (m >= 5);
    t0 := Runtime();
    if useLazy then
        idx := BuildSimpleIndexLazy(G);
    else
        idx := BuildSimpleIndex(G);
    fi;
    t1 := Runtime();
    Info(InfoWarning, 1,
         "  BuildKRRSpectralCharactersSparse: BuildSimpleIndex",
         (function() if useLazy then return "Lazy"; else return ""; fi; end)(),
         " built in ", (t1 - t0) / 1000., " s for m=", m,
         " (|G|=", idx.order, ", ", Length(idx.classes), " classes)");
    num_classes := Length(idx.classes);
    z := -IdentityMat(n);
    idMat := IdentityMat(n);

    # Per-class outputs:
    # multiplicities[class_idx] is a list aligned with idx.irreps[class_idx]
    #   (the standard Irr(C_G(a)) ordering); entries are cyclotomic rationals
    #   (the multiplicity of each irrep in W_a).
    # centraliser_traces[class_idx] is a list aligned with conjugacy classes
    #   of C_G(a) of normalised traces Tr(hat{T}_h_rep); used for diagnostics.
    # character_match[class_idx][irrep_idx] = rec(standard_irrep_idx, mult)
    #   matching the dense version's interface.  Here standard_irrep_idx
    #   is just irrep_idx itself (since we work in Irr(C_G(a)) ordering
    #   directly, not in joint-eigenspace ordering).
    multiplicities := [];
    centraliser_traces := [];
    character_match := [];

    for i in [1..num_classes] do
        a := idx.reps[i];
        if a <> z then
            # Non-central class (including identity): fall back to standard
            # character data.  Trace_on_W = EvalIrr (loads CT on demand).
            # Mult is stored as `fail` (not used by the non-central
            # trace_on_W codepath); character_match is shaped for
            # interface uniformity but only carries standard_irrep_idx.
            multiplicities[i] := fail;
            centraliser_traces[i] := fail;
            character_match[i] := List([1..idx.num_irreps[i]], irrep_idx ->
                rec(standard_irrep_idx := irrep_idx,
                    mult := fail));
            continue;
        fi;
        # Central class a = -I.  Use class-function trace computation.
        _EnsureClassData(idx, i);    # ensure CT is loaded (no-op for eager idx).
        cls_data := CentraliserClassData(idx, i);
        t0 := Runtime();
        traces := [];
        for j in [1..cls_data.num] do
            h := cls_data.reps[j];
            Add(traces, TraceOnOmega0(h, m));
        od;
        t1 := Runtime();
        Info(InfoWarning, 1,
             "  BuildKRRSpectralCharactersSparse: central class trace ",
             "table built in ", (t1 - t0) / 1000., " s ",
             "(", cls_data.num, " conjugacy classes of |G|=",
             idx.order, ")");
        centraliser_traces[i] := rec(reps := cls_data.reps,
                                      sizes := cls_data.sizes,
                                      traces := traces);
        mults := CharacterMultiplicities(idx, i, cls_data, traces);
        multiplicities[i] := mults;
        character_match[i] := List([1..idx.num_irreps[i]], irrep_idx ->
            rec(standard_irrep_idx := irrep_idx,
                mult := mults[irrep_idx]));
    od;

    # ====================================================================
    # trace_on_W(class_idx, irrep_idx, h) =
    #   For central class: mult_chi * chi(h), where chi is the
    #     irrep_idx-th irrep of C_G(a) (in standard Irr() ordering).
    #   For non-central class: EvalIrr(idx, class_idx, irrep_idx, h)
    #     (same as dense version).
    # ====================================================================
    trace_on_W := function(class_idx, irrep_idx, h)
        local a_loc, mult, chi_val;
        a_loc := idx.reps[class_idx];
        if a_loc <> z then
            return EvalIrr(idx, class_idx, irrep_idx, h);
        fi;
        # Central class.
        if irrep_idx < 1 or irrep_idx > idx.num_irreps[class_idx] then
            Error("trace_on_W: irrep_idx ", irrep_idx,
                  " out of range for class ", class_idx,
                  " (have ", idx.num_irreps[class_idx], " irreps).");
        fi;
        mult := multiplicities[class_idx][irrep_idx];
        chi_val := EvalIrr(idx, class_idx, irrep_idx, h);
        return mult * chi_val;
    end;

    return rec(
        group := G,
        idx := idx,
        m := m,
        trace_on_W := trace_on_W,
        character_match := character_match,
        multiplicities := multiplicities,
        centraliser_traces := centraliser_traces,
        # epsilon is trivial per the T4a research note.
        epsilon := function(g1, g2, a, b) return 1; end,
        source := "krr-sparse"
    );
end;;
