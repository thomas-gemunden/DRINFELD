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

_FusionOracle_PrecomputeFromS := function(s_data)
    # Precompute Sbar^T once; cheap (O(r^2) memory) and reused for
    # every row matmul.
    local r, S, Sbar_T, S_unit;
    S := s_data.S;
    r := Length(S);
    S_unit := S[1];
    Sbar_T := TransposedMat(List(S, row -> List(row, ComplexConjugate)));
    return rec(S := S, Sbar_T := Sbar_T, S_unit := S_unit, r := r);
end;;

_FusionOracle_RowFromS := function(pre, i)
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

MakeStreamingFusionOracle := function(arg)
    local S, opts, r, pre, cache_size, oracle, cache,
          row_order;
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
    if not IsList(S) or Length(S) = 0 then
        Error("MakeStreamingFusionOracle: S must be a non-empty ",
              "list of rows.");
    fi;
    r := Length(S);
    pre := _FusionOracle_PrecomputeFromS(rec(S := S));
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
                     max_cache_size := cache_size)
    );
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
        row := _FusionOracle_RowFromS(pre, i);
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
    if not IsFusionOracle(oracle) then
        return "(not a fusion oracle)";
    fi;
    return Concatenation(
        "kind=", oracle.kind,
        " rank=", String(oracle.rank),
        " rows_computed=", String(oracle.stats.rows_computed),
        " cache_hits=", String(oracle.stats.cache_hits),
        " cache_misses=", String(oracle.stats.cache_misses),
        " cache_size=", String(oracle.stats.cache_size),
        "/", String(oracle.stats.max_cache_size));
end;;

Print("Loaded fusion_oracle.g (MakeDenseFusionOracle, ",
      "MakeStreamingFusionOracle, AsFusionOracle, IsFusionOracle, ",
      "FusionOracle_StatsString).\n");
