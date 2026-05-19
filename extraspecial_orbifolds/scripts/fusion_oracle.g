# fusion_oracle.g — streaming/cached access to the fusion tensor N.
#
# Task A-3d (issue #45). Background: at E_+(3) the modular data has
# rank r = 2272. The dense fusion tensor N[i][j][k] has r^3 ~ 11.7B
# entries; a list-of-list-of-list representation is projected to take
# ~94 GB of memory (PR #181). That blocks AutNT(N, T, QD) at m = 3.
#
# This file installs a thin abstraction — a "fusion oracle" — that lets
# downstream callers (V-5b RefineByFusion, V-5c AutNT) request individual
# rows / entries of N without ever materialising the full tensor.
#
# Two backends are supplied:
#
#   * MakeDenseFusionOracle(N) — wraps a precomputed 3D list. Used for
#     small ranks (Q_8, E_+(2)) and for backward compatibility in tests.
#
#   * MakeStreamingFusionOracle(S[, opts]) — computes one fusion row at
#     a time from the S-matrix via the Verlinde formula in
#     matrix-multiply form (P-4/#113):
#
#         N_i = S * diag(S[i] / S[1]) * Sbar^T,
#
#     and caches a bounded number of recently-touched rows. Memory:
#     O(r^2) per cached row.
#
# A "fusion oracle" is a GAP record with fields:
#
#   .kind        : "dense" | "from_S" | <user-supplied tag>
#   .rank        : r (number of simples)
#   .row         : function(i) -> r-by-r matrix Ni such that
#                  Ni[j][k] = N_{ij}^k.  May return a fresh list or a
#                  cached reference; callers must NOT mutate the result.
#   .coef        : function(i, j, k) -> N_{ij}^k.  Default impl on top
#                  of .row; backends may override for speed.
#   .stats       : rec(rows_computed, rows_served_from_cache,
#                       cache_hits, cache_misses, cache_size, max_cache_size).
#                  (Only meaningful for caching backends; always present.)
#   .clear_cache : function() -> (); drop any caches. No-op for dense.
#
# Compatibility helper.  Several existing call sites pass a dense 3D
# list as N (so e.g. `Length(N)` is the rank and `N[i][j][k]` is a
# direct lookup).  `AsFusionOracle(N_or_oracle)` accepts either shape:
# if its argument is already a record with `.kind` it is returned
# unchanged; if it is a list it is wrapped via MakeDenseFusionOracle.
# Use `IsFusionOracle(x)` to test.
#
# ---- A-3d perf-2 (#240): Q -> Z matmul reduction --------------------
#
# At rank r = 2272 the per-row cyclotomic-Q matmul costs ~172 s.  GAP's
# compiled matmul for matrices over Q (cyclotomic field) is dramatically
# slower than the integer-matrix kernel.  When the S-matrix is purely
# rational (the typical case for untwisted modular data of a 2-group:
# entries are rational multiples of 1/|G|; e.g. Q_8 has d=8, E_+(2) has
# d=32, E_+(3) has d ≤ 128), we can scale S to a rational-integer matrix
# and do the per-row matmul over Integers, then divide back by d^2.
#
# Mechanics:
#   1. d := Lcm(denominators of S entries).
#   2. S_int := d * S         (an integer matrix iff S is rational).
#   3. Sbar^T_int := d * Sbar^T.
#   4. ConvertToMatrixRep(S_int, Integers) for compiled-int matmul.
#   5. Per row i:
#        lambda[a] := S_int[i][a] / S_int[1][a]   (integer for MTC from
#                                                  a finite group).
#        S_scaled_int[j][a] := S_int[j][a] * lambda[a]    (integer)
#        prod_int := S_scaled_int * Sbar^T_int            (compiled int matmul)
#        row_i[j][k] := prod_int[j][k] / d^2
#
# The d^2 scaling has a single tight derivation: S_scaled_int = d * S_scaled
# (since lambda[a] is the same rational as S[i][a]/S[1][a], and an
# integer-times-integer divided by integer reduces correctly), and
# Sbar^T_int = d * Sbar^T, so prod_int = d^2 * N_i.
#
# Enable with opts.integer_path := true on MakeStreamingFusionOracle.
# The oracle auto-detects rational S; if any entry is non-rational (i.e.
# a true cyclotomic of order > 1) we fall back to the cyclotomic-Q path.
# Detection cost is O(r^2) and runs once at construction.
#
# Acceptance: rank-22 Q_8 row equality vs cyclotomic path; rank-184
# E_+(2) row equality; rank-2272 E_+(3) per-row matmul under 20 s.

# ---- Sniffing -------------------------------------------------------

IsFusionOracle := function(x)
    return IsRecord(x) and IsBound(x.kind) and IsBound(x.rank)
                       and IsBound(x.row);
end;;

# ---- Dense backend --------------------------------------------------

MakeDenseFusionOracle := function(N)
    local r, oracle;
    if IsFusionOracle(N) then
        return N;
    fi;
    if not IsList(N) then
        Error("MakeDenseFusionOracle: argument must be a 3D list ",
              "(N[i][j][k]); got ", TNAM_OBJ(N), ".");
    fi;
    r := Length(N);
    oracle := rec(
        kind := "dense",
        rank := r,
        _N := N,
        stats := rec(rows_computed := 0,
                     rows_served_from_cache := 0,
                     cache_hits := 0,
                     cache_misses := 0,
                     cache_size := 0,
                     max_cache_size := infinity)
    );
    oracle.row := function(i)
        if i < 1 or i > r then
            Error("FusionOracle.row: index ", i,
                  " out of range [1..", r, "].");
        fi;
        oracle.stats.rows_served_from_cache :=
            oracle.stats.rows_served_from_cache + 1;
        oracle.stats.cache_hits := oracle.stats.cache_hits + 1;
        return N[i];
    end;
    oracle.coef := function(i, j, k)
        if i < 1 or i > r or j < 1 or j > r or k < 1 or k > r then
            Error("FusionOracle.coef: index out of range [1..", r,
                  "]; got (i, j, k) = (", i, ", ", j, ", ", k, ").");
        fi;
        return N[i][j][k];
    end;
    oracle.clear_cache := function() return; end;
    return oracle;
end;;

# ---- Streaming-from-S backend --------------------------------------
#
# We compute N_i = S * diag(S[i] / S[1]) * Sbar^T row-by-row, exactly the
# same matrix-multiply form that V-5b's FusionCoefficientsFromS uses for
# the full tensor (P-4 / #113).  Memory per row: O(r^2).
#
# Cache policy: a simple round-robin replacement keyed by row index.
# Default capacity is 16 (~ 16 * r^2 cyclotomics).  At r = 2272 each row
# is ~5.2M small rationals; the cache fits in roughly 1-2 GB depending
# on rational sizes.  Callers can adjust via opts.cache_size; 0 disables
# caching entirely.

# ---- Q-path precompute & per-row -------------------------------------

_FusionOracle_PrecomputeFromS := function(s_data)
    # Precompute Sbar^T once; cheap (O(r^2) memory) and reused for
    # every row matmul.
    local r, S, Sbar_T, S_unit;
    S := s_data.S;
    r := Length(S);
    S_unit := S[1];
    Sbar_T := TransposedMat(List(S, row -> List(row, ComplexConjugate)));
    return rec(kind := "Q", S := S, Sbar_T := Sbar_T,
               S_unit := S_unit, r := r);
end;;

_FusionOracle_RowFromS_Q := function(pre, i)
    # Returns a fresh r-by-r matrix N_i such that N_i[j][k] = N_{ij}^k.
    # Implementation: scale each column of S by lambda_a = S[i][a]/S[1][a]
    # (a Hadamard pass), then multiply by Sbar^T (one native matmul).
    # Total per row: O(r^3) ops via native matmul; O(r^2) memory.
    local r, S, S_unit, lambdas, S_scaled, a;
    S := pre.S;
    r := pre.r;
    S_unit := pre.S_unit;
    lambdas := [];
    for a in [1..r] do
        if S_unit[a] <> 0 then
            lambdas[a] := S[i][a] / S_unit[a];
        else
            lambdas[a] := 0;
        fi;
    od;
    S_scaled := List(S, row ->
        List([1..r], a -> row[a] * lambdas[a]));
    return S_scaled * pre.Sbar_T;
end;;

# ---- Z-path precompute & per-row (A-3d perf-2 / #240) ----------------
#
# Pre-scaling: pick d := Lcm over all i, a of denominator(S[i][a]).  For
# untwisted modular data of a 2-group this is small (e.g. 8 for Q_8,
# 32 for E_+(2), 128 for E_+(3)).
#
# The oracle stores `S_int` and `Sbar_T_int := d * Sbar^T`, both
# integer matrices.  When called for a row we form the per-row scaled
# matrix `S_scaled_int[j][a] := S_int[j][a] * lambda[a]` where
# lambda[a] = S_int[i][a] / S_int[1][a].  Note that lambda is an
# exact integer for MTCs from finite groups (each Verlinde eigenvalue
# `S[i][a]/S[1][a]` is an algebraic integer; in our rational-S setting
# it is an ordinary integer).  This guarantees `S_scaled_int` is an
# integer matrix, so the matmul `prod_int := S_scaled_int * Sbar_T_int`
# uses GAP's compiled integer kernel.
#
# Recovery: prod_int = d * (d * S_scaled) * Sbar^T / 1 = d^2 * N_i.
# So row_i = prod_int / d^2.

_FusionOracle_AllRationalQ := function(S)
    # Returns true iff every entry of S is a rational (i.e. lies in Q).
    # Cyclotomic-rationals (E(n)) return false even if integer.
    local i, j, r, row;
    r := Length(S);
    for i in [1..r] do
        row := S[i];
        for j in [1..r] do
            if not IsRat(row[j]) then
                return false;
            fi;
        od;
    od;
    return true;
end;;

_FusionOracle_DenominatorLcm := function(S)
    # Computes Lcm over all entries of denominators.  Assumes
    # _FusionOracle_AllRationalQ(S) = true.
    local d, i, j, r, row, e;
    r := Length(S);
    d := 1;
    for i in [1..r] do
        row := S[i];
        for j in [1..r] do
            e := row[j];
            if e <> 0 then
                d := LcmInt(d, DenominatorRat(e));
            fi;
        od;
    od;
    return d;
end;;

_FusionOracle_PrecomputeFromS_Z := function(s_data)
    # Try to build the Z-path precompute.  Returns either a Z-rec or
    # `fail` (when S has non-rational entries).
    local r, S, S_int, Sbar_T_int, S_unit_int, i, j, d, row, conj_row;
    S := s_data.S;
    r := Length(S);
    if not _FusionOracle_AllRationalQ(S) then
        return fail;
    fi;
    d := _FusionOracle_DenominatorLcm(S);
    if d = 1 then
        # S is already integral.  Build S_int := S (still integer).
        S_int := List(S, ShallowCopy);
    else
        S_int := List(S, row -> List(row, e -> e * d));
    fi;
    # Sanity: every entry must now be an actual integer.
    for i in [1..r] do
        row := S_int[i];
        for j in [1..r] do
            if not IsInt(row[j]) then
                # Numerical sanity: S was rational, scaled by Lcm of
                # denominators, so every entry should be integer.
                Error("Z-path precompute: S_int[", i, "][", j,
                      "] = ", row[j], " is not an integer ",
                      "(d = ", d, ").  This is a bug.");
            fi;
        od;
    od;
    # For a real S (which is always the case for untwisted modular
    # data of a finite group; complex conjugation acts trivially), the
    # bar^T is just T.  Otherwise we conjugate explicitly.  We keep the
    # explicit form for correctness under twisted/complex S.
    Sbar_T_int := TransposedMat(
        List(S_int, row -> List(row, ComplexConjugate)));
    # If S has cyclotomic conjugation that produces non-integer entries
    # we caught that already via the rational check.  Sbar_T_int is
    # therefore an integer matrix here.
    # Convert to a matrix representation that triggers the compiled
    # integer kernel (cyclotomic field path is the slow default).
    ConvertToMatrixRep(S_int, Integers);
    ConvertToMatrixRep(Sbar_T_int, Integers);
    S_unit_int := S_int[1];
    return rec(kind := "Z", S_int := S_int, Sbar_T_int := Sbar_T_int,
               S_unit_int := S_unit_int, r := r, d := d);
end;;

_FusionOracle_RowFromS_Z := function(pre, i)
    # Returns N_i as r-by-r list (entries are rationals; for untwisted
    # data of a finite group they are non-negative integers, the fusion
    # coefficients).
    local r, S_int, S_unit_int, lambdas, S_scaled_int, a, d, prod_int,
          row_i, j, k, val;
    S_int := pre.S_int;
    r := pre.r;
    S_unit_int := pre.S_unit_int;
    d := pre.d;
    lambdas := [];
    for a in [1..r] do
        if S_unit_int[a] <> 0 then
            # lambda[a] = S_int[i][a] / S_unit_int[a] = S[i][a] / S[1][a].
            # Per the MTC-from-finite-group structure this is integer.
            # GAP's `/` returns a rational; for an integer-valued
            # quotient we get the integer back.
            lambdas[a] := S_int[i][a] / S_unit_int[a];
        else
            lambdas[a] := 0;
        fi;
    od;
    # Build S_scaled_int: rows scaled column-wise by lambdas.  For the
    # integer kernel to apply, every entry must be an integer.  If
    # lambda is fractional (shouldn't happen for the MTCs we target,
    # but is possible for arbitrary S), fall back to the Q multiplier
    # by working in rationals here and noting we will lose the kernel
    # benefit only for this branch.
    S_scaled_int := List(S_int, row ->
        List([1..r], a -> row[a] * lambdas[a]));
    # If lambdas are all integer (which we expect), S_scaled_int is an
    # integer matrix.  Convert representation accordingly.  We re-check
    # for safety; for a fractional-lambda branch ConvertToMatrixRep will
    # silently no-op for the wrong field.
    if ForAll([1..r], a -> IsInt(lambdas[a])) then
        ConvertToMatrixRep(S_scaled_int, Integers);
    fi;
    prod_int := S_scaled_int * pre.Sbar_T_int;
    # Divide each entry by d^2 to recover N_i.
    if d = 1 then
        return prod_int;
    fi;
    row_i := [];
    for j in [1..r] do
        row_i[j] := List([1..r], k -> prod_int[j][k] / (d * d));
    od;
    return row_i;
end;;

MakeStreamingFusionOracle := function(arg)
    local S, opts, r, pre, cache_size, oracle, cache,
          row_order, want_integer, row_fn;
    if Length(arg) < 1 or Length(arg) > 2 then
        Error("MakeStreamingFusionOracle: expected 1 or 2 arguments ",
              "(S[, opts]); got ", Length(arg), ".");
    fi;
    S := arg[1];
    if Length(arg) = 2 then
        opts := arg[2];
    else
        opts := rec();
    fi;
    if not IsBound(opts.cache_size) then
        opts.cache_size := 16;
    fi;
    if opts.cache_size < 0 then
        Error("MakeStreamingFusionOracle: opts.cache_size must be ",
              ">= 0; got ", opts.cache_size, ".");
    fi;
    if not IsBound(opts.integer_path) then
        opts.integer_path := false;
    fi;
    if not IsList(S) or Length(S) = 0 then
        Error("MakeStreamingFusionOracle: S must be a non-empty ",
              "list of rows.");
    fi;
    r := Length(S);
    want_integer := opts.integer_path = true;
    pre := fail;
    if want_integer then
        pre := _FusionOracle_PrecomputeFromS_Z(rec(S := S));
        if pre = fail then
            # Auto-fall-back to Q-path.  We do NOT error out — the
            # integer_path option is an optimisation hint, not a hard
            # constraint.  Callers wanting strict failure can test
            # `oracle._pre.kind = "Z"`.
            pre := _FusionOracle_PrecomputeFromS(rec(S := S));
        fi;
    else
        pre := _FusionOracle_PrecomputeFromS(rec(S := S));
    fi;
    if pre.kind = "Z" then
        row_fn := i -> _FusionOracle_RowFromS_Z(pre, i);
    else
        row_fn := i -> _FusionOracle_RowFromS_Q(pre, i);
    fi;
    cache_size := opts.cache_size;
    cache := rec();          # key "i" -> row matrix
    row_order := [];          # insertion-order list of cached row ids
    oracle := rec(
        kind := "from_S",
        rank := r,
        _pre := pre,
        stats := rec(rows_computed := 0,
                     rows_served_from_cache := 0,
                     cache_hits := 0,
                     cache_misses := 0,
                     cache_size := 0,
                     max_cache_size := cache_size,
                     path := pre.kind,         # "Q" or "Z"
                     denominator := 0)         # 0 means n/a (Q-path)
    );
    if pre.kind = "Z" then
        oracle.stats.denominator := pre.d;
    fi;
    oracle.row := function(i)
        local key, row, evict_key;
        if i < 1 or i > r then
            Error("FusionOracle.row: index ", i,
                  " out of range [1..", r, "].");
        fi;
        key := String(i);
        if cache_size > 0 and IsBound(cache.(key)) then
            oracle.stats.cache_hits := oracle.stats.cache_hits + 1;
            oracle.stats.rows_served_from_cache :=
                oracle.stats.rows_served_from_cache + 1;
            return cache.(key);
        fi;
        # Cache miss: compute the row.
        oracle.stats.cache_misses := oracle.stats.cache_misses + 1;
        oracle.stats.rows_computed := oracle.stats.rows_computed + 1;
        row := row_fn(i);
        if cache_size = 0 then
            return row;
        fi;
        # Round-robin eviction if at capacity.
        if Length(row_order) >= cache_size then
            evict_key := row_order[1];
            row_order := row_order{[2..Length(row_order)]};
            Unbind(cache.(evict_key));
        fi;
        cache.(key) := row;
        Add(row_order, key);
        oracle.stats.cache_size := Length(row_order);
        return row;
    end;
    oracle.coef := function(i, j, k)
        local row;
        if i < 1 or i > r or j < 1 or j > r or k < 1 or k > r then
            Error("FusionOracle.coef: index out of range [1..", r,
                  "]; got (i, j, k) = (", i, ", ", j, ", ", k, ").");
        fi;
        row := oracle.row(i);
        return row[j][k];
    end;
    oracle.clear_cache := function()
        local key;
        for key in ShallowCopy(row_order) do
            Unbind(cache.(key));
        od;
        row_order := [];
        oracle.stats.cache_size := 0;
    end;
    return oracle;
end;;

# ---- Polymorphic coercion ------------------------------------------

AsFusionOracle := function(x)
    if IsFusionOracle(x) then
        return x;
    fi;
    return MakeDenseFusionOracle(x);
end;;

# ---- Diagnostics ----------------------------------------------------

FusionOracle_StatsString := function(oracle)
    local extra;
    if not IsFusionOracle(oracle) then
        return "(not a fusion oracle)";
    fi;
    extra := "";
    if IsBound(oracle.stats.path) then
        extra := Concatenation(extra, " path=", oracle.stats.path);
    fi;
    if IsBound(oracle.stats.denominator)
       and oracle.stats.denominator <> 0 then
        extra := Concatenation(extra, " d=",
                               String(oracle.stats.denominator));
    fi;
    return Concatenation(
        "kind=", oracle.kind,
        " rank=", String(oracle.rank),
        extra,
        " rows_computed=", String(oracle.stats.rows_computed),
        " cache_hits=", String(oracle.stats.cache_hits),
        " cache_misses=", String(oracle.stats.cache_misses),
        " cache_size=", String(oracle.stats.cache_size),
        "/", String(oracle.stats.max_cache_size));
end;;

Print("Loaded fusion_oracle.g (MakeDenseFusionOracle, ",
      "MakeStreamingFusionOracle, AsFusionOracle, IsFusionOracle, ",
      "FusionOracle_StatsString).\n");
