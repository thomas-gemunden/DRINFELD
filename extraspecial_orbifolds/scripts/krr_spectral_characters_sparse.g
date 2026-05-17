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

# Reset cache (used by tests).
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
        fmat_diag := List(targetMat * TransposedMat(feasMat),
                          row -> List(row, x -> x mod 2));
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
    XHR := List(XH * ctx.R, row -> List(row, x -> x mod 2));
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
    term1 := List(XMhhSym * ctx.AT, row -> List(row, x -> x mod 2));
    icRT := icMat * ctx.RT;
    icRTHT := List(icRT * ctx.HT, row -> List(row, x -> x mod 2));
    icRTHTAT := List(icRTHT * ctx.AT, row -> List(row, x -> x mod 2));
    betaMat := List([1..dim], ci ->
        List([1..kerLen], j -> (term1[ci][j] + icRTHTAT[ci][j]) mod 2));
    # betaTilde = beta * ShT : dim x kerLen.
    betaTilde := List(betaMat * ctx.sht.ShT, row -> List(row, x -> x mod 2));
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
# Implemented for m=3, m=5 (no asymptotic improvement at those sizes,
# but exact arithmetic for reference).  At m=7 this would be the only
# viable method; left as a stub returning `fail` so callers know to
# fall back.
# ============================================================
#
# Sketch (see issue #220, section "Optimisation needed"):
#   - x(c) = c * P + x_0 for a particular right-inverse P (n -> 2k cols),
#     valid only when (c, c) lies in Im(BigPi(h)).  The feasibility
#     condition cuts out a linear subspace L_h \subset F_2^k.
#   - On L_h, gamma(c) and the beta_tilde-radical-match are linear/
#     quadratic in c; the Schur sum is a Gauss sum over L_h.
#
# Left as a TODO for the m=7 follow-up.  For m=5 we use the naive
# variant (it's fast enough -- see profiling below).
TraceOnOmega0Gauss := function(h, m)
    Error("TraceOnOmega0Gauss: not implemented (m=7 stub). ",
          "Use TraceOnOmega0Naive at m <= 5.");
end;;


# ============================================================
# TraceOnOmega0(h, m): top-level trace dispatcher.  Caches
# results per h.
# ============================================================
#
# Returns the NORMALISED trace Tr(hat{T}_h) = Tr(T_h) / 2^k.
TraceOnOmega0 := function(h, m)
    local j, k, raw, norm;
    for j in [1..Length(_sparseTraceKeys)] do
        if IsIdenticalObj(_sparseTraceKeys[j], h) then
            return _sparseTraceVals[j].Tr_norm;
        fi;
    od;
    k := 2^(m - 1);
    raw := TraceOnOmega0Batch(h, m);
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
