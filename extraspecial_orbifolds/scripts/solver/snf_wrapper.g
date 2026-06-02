# snf_wrapper.g — top-level wrapper for the transgression kernel (T-2).
#
# TransgressionKernelExact(G) computes
#     ker( Tr : H^3(G; U(1))  ->  ⊕_g H^2(C_g; U(1)) )
# by enumerating the (finite) H^3 classes and asking the public dispatcher
# IsCoboundary2Split whether each per-class restriction c_g is a coboundary.
#
# Implementation: brute-force enumeration with a per-class cocycle-basis
# cache. The original plan (lines 896-973) called for an SNF-based approach;
# brute force is correct as-is for E_+(2)-scale computations and avoids the
# stubbed ProjectToH2Basis.
#
# Why per-class basis caching matters (issue #62):
#
#   omega(g, h, k) = sum_i vec[i] * basis[i](g, h, k) is Z-linear in vec.
#   Per class g, c_g(h, k) = omega(g, h, k) - omega(h, g, k) + omega(h, k, g)
#   is also linear in vec. So per class we can precompute an (n^2 x k)
#   integer matrix M_g such that c_g(h_a, h_b) = (M_g * vec)[(a-1)*n+b].
#
#   Without the cache, every (vec, class) inner-step does n^2 HAP cocycle
#   evaluations (~0.36 ms each on E_+(2) centralisers); with the cache it's
#   one matrix-vector product. Profile in #62 shows ~100x speedup, bringing
#   T13 (E_+(2) anchor) from ~100 min to ~1 min wall.
#
# Returned record fields:
#   .setup       — SetupCohomology3(G)
#   .classes     — ConjugacyClasses(G)
#   .kernel      — list of NON-zero kernel coordinate vectors (zero excluded)
#   .kernel_size — total count including zero (so 1 + Length(kernel))
#
# Read-path note: this file uses a CWD shim consistent with iscoboundary2_split.g
# so it works whether Read from solver/ or from solver/tests/.
snf_wrapper_orig_dir := DirectoryCurrent();;
snf_wrapper_target := fail;;
for snf_wrapper_try in [".", "..", "../.."] do
    if IsExistingFile(Concatenation(snf_wrapper_try, "/iscoboundary2_split.g")) then
        snf_wrapper_target := snf_wrapper_try;
        break;
    fi;
od;;
if snf_wrapper_target = fail then
    Error("snf_wrapper.g: cannot locate iscoboundary2_split.g from CWD ",
          Filename(snf_wrapper_orig_dir, ""));
fi;
ChangeDirectoryCurrent(snf_wrapper_target);;
Read("iscoboundary2_split.g");
ChangeDirectoryCurrent(Filename(snf_wrapper_orig_dir, ""));;

# Per-class cocycle-basis cache. For class g, returns the n^2 x k integer
# matrix M_g whose row (a-1)*n+b column i is
#   omega_i(gRep, elts[a], elts[b])
# - omega_i(elts[a], gRep, elts[b])
# + omega_i(elts[a], elts[b], gRep),
# where omega_i := StandardCocycle(setup.R, basis[i], 3, exp). The result rec
# also stores the ordered element list and an index map for O(log n) lookup.
#
# Hot-loop optimisation: the original implementation built `omegas` as k
# separate HAP closures and called each per (a, b) triple, doing the same
# Syzygy(R, [...]) chain encoding k times redundantly. Profile on the
# stalled E_+(3) run (/tmp/a3a_sample.txt) showed 75 % of CPU in `PosPlist`
# inside HAP's Syzygy. HAP's StandardCocycle(R, f, n, q) computes
#     Syzygy(R, [g, h, k]) -> signed integer list S over [1..R.dim(n)]
#     v[|x|] += sign(x)                                  (length-R.dim(n))
#     return (v * f) mod q.
# Hoisting Syzygy out of the i-loop reduces the call count k-fold (here
# k = 35 H^3 generators for E_+(3)). The dot product `contrib * basis[i]`
# replaces a fresh Syzygy + sum.
_basis_cache_by_class := rec();;
# Cache `BuildPerClassCocycleBasis` results across generator calls.
# Profile (perf/raw/eplus3_per_gen_brw_two_calls.txt) showed the
# `BRWH3Action` cache from P-5 (#119) only saved ~4 % of per-call wall,
# because the dominant ~96 % is in 4x `BuildPerClassCocycleBasis` calls
# (one per BRW orbit). The table built by this function depends only on
# (setup, gRep, C) -- NOT on the H^3 generator index `i`. The driver
# loops i in [1..35] and rebuilds the 4 tables every time, for 140
# total builds vs the optimal 4.
#
# Cache key: a string concatenating identifiers of (G, gRep, C).
# Originally used IdGroup for G and C, but IdGroup is only available
# for orders ≤ 2000 in the standard SmallGroup library — breaks at
# m=5 (|G| = 2048). We use Order(G), Order(C), and String(gRep)
# (the strong per-orbit discriminator) instead. The cache scope is
# a single driver run with a fixed G, so dropping IdGroup loses
# nothing.
_SafeIdString := function(grp)
    # GAP's SmallGroups library covers orders 1..2000 EXCEPT 1024,
    # plus a few sparse high orders. The first attempt at this fix
    # (only the `ord > 2000` branch) tripped over E_+(5)'s order-1024
    # centralisers because CALL_WITH_CATCH does not catch the
    # SmallGroups error reliably. Per the module-level comment, the
    # cache scope is a single driver run with a fixed G; `Order(C)` +
    # `String(gRep)` already discriminate uniquely within that scope,
    # so dropping IdGroup entirely loses nothing.
    return Concatenation("order", String(Order(grp)));
end;;

# ------------------------------------------------------------------
# A-7 perf-5b (#281): HAP-level prefix-Syzygy sharing.
#
# HAP's Syzygy(R, [g1, g2, g3]) is built from 4 length-2 sub-Syzygies
# (see /opt/homebrew/.../pkg/hap/lib/Homology/syzygy.gi lines 61-67):
#
#   Syz = Mult(g1, Syz([g2, g3])) + Syz([g1, g2*g3])
#         - Syz([g1*g2, g3]) - Syz([g1, g2]);
#   return Homotopy(2, Syz);
#
# For BuildPerClassCocycleBasis we compute three length-3 Syzygies per
# (a, b) pair, one for each position of gRep:
#
#   Triple #1: Syz([gRep, a, b]) -- ends with - Syz([gRep, a])
#   Triple #2: Syz([a, gRep, b]) -- ends with - Syz([a, gRep])
#   Triple #3: Syz([a, b, gRep]) -- starts with Mult(a, Syz([b, gRep]))
#                                 and ends with - Syz([a, b])
#
# Two sharing opportunities:
#
#   (a) HOIST: within the inner b-loop (fixed a), Syz([gRep, a]) and
#       Syz([a, gRep]) are CONSTANT. We compute them once per a and
#       reuse across all b. Saves 2 length-2 Syzygy calls per (a,b),
#       i.e. 2*(n-1) per a, i.e. 2*n*(n-1) overall.
#
#   (b) SHARE within (a, b): Syz([a, b]) appears in BOTH Triple #1 (as
#       Mult(gRep, Syz([a,b]))) and Triple #3 (as -Syz([a,b])). We
#       compute it once and reuse. Saves 1 length-2 Syzygy call per
#       (a,b), i.e. n*n overall.
#
# Total saving: ~3*n*(n-1) + n*n length-2 Syzygy calls out of the
# original 4*3*n*n = 12*n*n. At m=3, n=128: ~50K of 197K length-2
# calls saved (~25%). At m=5, n=2048: ~13M of 50M (~26%).
#
# CORRECTNESS: We are NOT changing the math. We replicate the exact
# code in syzygy.gi's n=3 branch, just with the b-invariant pieces
# hoisted and the within-(a,b) shared piece computed once. The output
# `Syzygy(R, [g1, g2, g3])` is bit-for-bit identical to a fresh HAP
# call. The per-triple correctness check in tests/test_perf5b_prefix
# verifies this on a sample of m=3 triples.
#
# We DO NOT change the OUTSIDE-Homotopy-2 quadratic AddFreeWords cost
# -- those are the four AddFreeWords calls that combine the length-2
# sub-syzygies. The savings are purely in the SUBSEQUENT length-2
# Syzygy computations.
#
# The helper inlines the n=3 case from syzygy.gi using R!.homotopy
# and R!.elts directly. _MultByElt and _Homotopy2 mirror Mult and the
# word-level Homotopy(2, ...) in syzygy.gi's local closures.
# ------------------------------------------------------------------

_MultByElt := function(R_elts, x, w)
    # w is a word [[sign, elt_idx], ...]; return [[sign, idx(x*elts[idx])], ...].
    return List(w, y -> [y[1], Position(R_elts, x * R_elts[y[2]])]);
end;;

# ------------------------------------------------------------------
# A-7 perf-5c (#282): O(|w1| + |w2|) drop-in for HAP's AddFreeWords.
#
# HAP's AddFreeWords (wordOperations.gi:112-139) is:
#
#   if Length(arg[2]) < Length(arg[1]) then v := arg[1]; w := arg[2];
#   else                                    w := arg[1]; v := arg[2]; fi;
#   if Length(w) = 0 then return v; fi;
#   if Length(v) = 0 then return w; fi;
#   w2 := ShallowCopy(w);
#   u  := ShallowCopy(w);
#   for x in v do
#       r := Position(w2, [-x[1], x[2]]);          # O(|w2|) linear scan over w2
#       if r = fail then Add(u, x);
#       else u[r] := 0; w2[r] := 0; fi;
#   od;
#   return Filtered(u, i -> not i = 0);
#
# Words are lists of [signed_cell_idx, group_elt_idx] pairs; a pair [c, g]
# and [-c, g] cancel. The branch picks the *shorter* of the two arguments
# as `w` (the lookup target) and the longer as `v` (iteration). Position
# returns the *first* occurrence, so when several copies of the same
# [c, g] exist, the pairing with [-c, g] entries from v is left-to-right
# (smallest-index first).
#
# Cost: O(|v| * |w|). Since the smaller is `w`, this is O(max * min).
#
# perf-5b's profile on E_+(3) (perf/raw/eplus3_build_per_class_cocycle_basis
# .txt) showed ~75 % of CPU in PosPlist, almost all of it inside this scan.
# In _Homotopy2's accumulator pattern, AddFreeWords(ans, h_x) is called
# repeatedly with `ans` growing; h_x is bounded but moderately sized
# (~20-100 entries at m=3). The product |ans|*|h_x| stays sub-quadratic
# in |ans| BUT for the dominant minus_one orbit (|C|=128, where the per-
# class cache cost is ~45 s out of ~55 s total) the total per-class
# (a, b)-loop work is 3 length-3 Syzygy computations, each calling
# _Homotopy2 on a length-O(|ans_at_b|) word. Aggregated over n²=128²=16384
# (a, b) pairs, the constant in `O(n^2 * |ans| * |h_x|)` matters.
#
# The fast replacement uses a queue dict keyed on (c, g) pairs to make
# each AddFreeWords O(|v| + |w|). For inputs where one side is small the
# improvement is small (HAP's scan is already O(big*small) — bounded by
# the smaller side). For inputs where both sides are large (e.g. the
# Mult(g1, S_g2g3) + S_g1_g2g3 accumulation in _Syzygy3FromParts), the
# dict win is larger.
#
# Implementation notes:
#   - Keys (c, g) are encoded as positive integers via
#       key := (g - 1) * stride + (c + D + 1)
#     where D bounds |c| and stride := 2*D + 1. Distinct (c, g) -> distinct
#     keys. The "pool" is a module-level plain list indexed by these keys;
#     IsBound/Add/Remove/Unbind on a plain list are compiled C-level
#     operations.
#   - The pool is reused across calls. After each call, only the keys
#     touched in *this* call are unbound, via a `_touched` list. Reset
#     cost is O(|w|), not O(|pool|).
#   - Earlier attempts using NewDictionary (with a 2-list sample object)
#     ended up dispatching to GAP's sorted-list dictionary
#     (DictionaryBySort), which has O(log n) per op and substantial
#     interpretive overhead. Measured: NewDictionary ~0.7x HAP (slower),
#     positional pool ~1.6x HAP (faster), on the m=3 minus_one workload.
#   - The pool capacity grows on demand: any AddFreeWords call that sees
#     |c| > D or g > G_max triggers _AddFreeWordsFast_EnsureCapacity,
#     which bumps D / G_max and resets the pool. After warm-up these
#     bumps stop happening.
#   - When the SMALLER side `w` has only a few entries, HAP's linear scan
#     already costs `O(|v| * |w|)` with a tight constant, and beats the
#     pool-build overhead. The pool path triggers only when |w| >=
#     `_AddFreeWordsFast_MIN_SMALL` (default 24). Captured (ans, h) pairs
#     from m=3 minus_one cache build show most calls have one side <= 5,
#     while a long-tail minority have both sides in the hundreds; the
#     pool targets the long-tail without paying overhead on the bulk.
#
# Output is bit-identical to HAP's AddFreeWords for any inputs:
#   * Same v/w selection by length (smaller -> w).
#   * Same cancellation rule (single [-c,g] cancels at the *earliest*
#     [c,g] in w; then both go to 0).
#   * Same final order: w's surviving entries in their original positions,
#     followed by v's unmatched entries in v's order.
#
# (Verified by test_perf5c_addfreewords.g on 2300+ random + curated +
#  Syzygy-derived inputs, 0 mismatches.)
_AddFreeWordsFast_MIN_SMALL := 24;;

# Positional pool: a flat plain list indexed by an encoded integer key
# (c, g) -> ((g - 1) * stride + (c + D + 1)). `D` is the maximum cell
# index magnitude we expect to see; `G_max` is the maximum group element
# index. Both grow dynamically the first time we see a larger value.
#
# Per-call protocol: only entries for keys that appear in the call are
# bound, and they are unbound at end-of-call. The `_touched` list tracks
# the keys we set so reset is O(|w|) instead of O(|pool|).
#
# Why a positional pool beats `NewDictionary`/record approaches: it
# dispatches to GAP's compiled IsBound/[]/Unbind on a plain integer-
# indexed list, which is just C-level array access. `NewDictionary` for
# 2-list keys uses a *sorted* dictionary internally (DictionaryBySort)
# with O(log n) per op and substantial per-op dispatch overhead.
# Empirical: positional ~1.6x faster than HAP's linear scan on the m=3
# minus_one workload, while NewDictionary is ~0.7x (i.e. slower).
_AddFreeWordsFast_pool := [];;
_AddFreeWordsFast_touched := EmptyPlist(256);;
_AddFreeWordsFast_D := 64;;       # initial guess; grows if needed
_AddFreeWordsFast_G_max := 64;;   # initial guess; grows if needed

# Recompute the stride from D. Capacity = (2*D + 1) * G_max.
_AddFreeWordsFast_stride := 2 * _AddFreeWordsFast_D + 1;;

# Ensure pool capacity covers (c, g) with |c| <= D, g <= G_max.
_AddFreeWordsFast_EnsureCapacity := function(needed_D, needed_G)
    if needed_D > _AddFreeWordsFast_D or needed_G > _AddFreeWordsFast_G_max then
        if needed_D > _AddFreeWordsFast_D then
            _AddFreeWordsFast_D := needed_D;
        fi;
        if needed_G > _AddFreeWordsFast_G_max then
            _AddFreeWordsFast_G_max := needed_G;
        fi;
        _AddFreeWordsFast_stride := 2 * _AddFreeWordsFast_D + 1;
        # On capacity grow, simply reset the pool: any positions stored
        # for old keys are stale because the stride changed.
        _AddFreeWordsFast_pool := [];
        _AddFreeWordsFast_touched := EmptyPlist(256);
    fi;
end;;

_AddFreeWordsFast := function(w1, w2_arg)
    local v, w, w_len, v_len, u, pool, touched, stride, D, max_g, max_c,
          i, x, c, g, key, entry, neg_c;

    # Branch picks shorter as `w` (matches HAP exactly so output order
    # is preserved).
    if Length(w2_arg) < Length(w1) then
        v := w1; w := w2_arg;
    else
        w := w1; v := w2_arg;
    fi;

    w_len := Length(w);
    v_len := Length(v);
    if w_len = 0 then return ShallowCopy(v); fi;
    if v_len = 0 then return ShallowCopy(w); fi;

    # Small-input shortcut: when the smaller side `w` has few entries,
    # HAP's `O(|v| * |w|)` scan is already cheap with a tight constant
    # (PosPlist is a tight C loop). The dict path's pool build + lookup
    # overhead exceeds the savings here. Empirically measured: positional
    # pool beats scan once |w| >= ~24 entries.
    if w_len < _AddFreeWordsFast_MIN_SMALL then
        return AddFreeWords(w1, w2_arg);
    fi;

    # Snapshot pool state. We may need to grow capacity inside the build
    # loop if any (c, g) overflows the current bounds; in that case we
    # bail and fall through to HAP for this call (since growing rewrites
    # `stride` and would invalidate our partially-built keys).
    pool := _AddFreeWordsFast_pool;
    touched := _AddFreeWordsFast_touched;
    stride := _AddFreeWordsFast_stride;
    D := _AddFreeWordsFast_D;

    # Build u as a mutable copy of w; entries get zeroed on cancellation.
    u := ShallowCopy(w);

    # Build pos_by_key (positional pool):
    #   key = (g - 1) * stride + (c + D + 1)
    # where c is the SIGNED cell index. Distinct (c, g) -> distinct keys,
    # including sign discrimination. Pool[key] holds the ascending list
    # of positions in w. `touched` records all keys we set, for cleanup.
    #
    # Capacity check is fused into the loop: if any entry exceeds the
    # current bounds, we abort the pool build, reset the touched keys,
    # grow the pool, and restart by delegating to HAP for this call (the
    # next call will use the grown pool).
    max_c := 0; max_g := 0;
    for i in [1..w_len] do
        c := w[i][1];
        g := w[i][2];
        if AbsInt(c) > max_c then max_c := AbsInt(c); fi;
        if g > max_g then max_g := g; fi;
        if max_c > D or max_g > _AddFreeWordsFast_G_max then
            # Grow and bail. Reset what we set so far.
            for key in touched do Unbind(pool[key]); od;
            _AddFreeWordsFast_touched := EmptyPlist(256);
            _AddFreeWordsFast_EnsureCapacity(max_c, max_g);
            return AddFreeWords(w1, w2_arg);
        fi;
        key := (g - 1) * stride + (c + D + 1);
        if IsBound(pool[key]) then
            Add(pool[key], i);
        else
            pool[key] := [i];
            Add(touched, key);
        fi;
    od;

    # Lookup. For each x = [c, g] in v, look up key for [-c, g].
    # v entries that overflow the current pool bounds (|neg_c| > D or
    # g > G_max) can't match anything in pool (w's keys are bounded by
    # those), so they fall through to `Add(u, x)`. The grow-and-bail
    # path in the build loop above ensures SUBSEQUENT calls get a larger
    # pool. We don't grow during v iteration because growing invalidates
    # `stride` and would require recomputing pool keys.
    #
    # Pool invariant: each pool[key] is a non-empty list of positions in w.
    # On pop, we Remove the head; if the list becomes empty we Unbind it.
    # This keeps the lookup check to a single IsBound (avoiding a separate
    # Length(pool[key]) > 0 check).
    for x in v do
        c := x[1];
        g := x[2];
        neg_c := -c;
        if AbsInt(neg_c) <= D and g <= _AddFreeWordsFast_G_max then
            key := (g - 1) * stride + (neg_c + D + 1);
            if IsBound(pool[key]) then
                entry := pool[key];
                u[entry[1]] := 0;
                if Length(entry) = 1 then
                    Unbind(pool[key]);
                else
                    Remove(entry, 1);
                fi;
                continue;
            fi;
        fi;
        Add(u, x);
    od;

    # Reset touched keys for next call. O(|w|), not O(|pool|).
    for i in [1..Length(touched)] do
        Unbind(pool[touched[i]]);
    od;
    _AddFreeWordsFast_touched := EmptyPlist(256);

    return Filtered(u, i -> not i = 0);
end;;

_Homotopy2 := function(R, w)
    # Word-level Homotopy(2, w): for each cell x in w, look up
    # R!.homotopy(2, x) (which is internally memoised by HAP's
    # Contraction cache) and AddFreeWords accumulate the result.
    #
    # A-7 perf-5c (#282): replaced AddFreeWords with _AddFreeWordsFast,
    # which uses an O(|w1|+|w2|) dictionary lookup instead of HAP's
    # O(|w1|*|w2|) Position scan. The accumulator `ans` grows as we sum
    # |w| homotopy contributions; HAP's linear scan made the per-call cost
    # quadratic in |ans|. The dict path makes it linear.
    local ans, x;
    ans := [];
    for x in w do
        ans := _AddFreeWordsFast(ans, R!.homotopy(2, x));
    od;
    return ans;
end;;

# _Syzygy3FromParts(R, g1, S_g2g3, S_g1_g2g3, S_g1g2_g3, S_g1_g2)
#
# Inlined version of HAP's Syzygy(R, [g1, g2, g3]) that accepts the
# four length-2 sub-syzygies as arguments instead of re-computing them.
# Output is bit-identical to Syzygy(R, [g1, g2, g3]).
_Syzygy3FromParts := function(R, g1, S_g2g3, S_g1_g2g3, S_g1g2_g3, S_g1_g2)
    local R_elts, Syz;
    R_elts := R!.elts;
    # Replicate syzygy.gi lines 62-67:
    #   Syz := Mult(g1, Syz([g2, g3]));
    #   Syz := AddFreeWords(Syz, Syz([g1, g2*g3]));
    #   Syz := AddFreeWords(Syz, NegateWord(Syz([g1*g2, g3])));
    #   Syz := AddFreeWords(Syz, NegateWord(Syz([g1, g2])));
    #   return Homotopy(2, Syz);
    Syz := _MultByElt(R_elts, g1, S_g2g3);
    Syz := _AddFreeWordsFast(Syz, S_g1_g2g3);
    Syz := _AddFreeWordsFast(Syz, NegateWord(S_g1g2_g3));
    Syz := _AddFreeWordsFast(Syz, NegateWord(S_g1_g2));
    return _Homotopy2(R, Syz);
end;;

# _Syzygy3CombinedWord(R, gRep, a, b, S_gRep_a, S_a_gRep, S_a_b,
#                       S_gRep_ab, S_gRep_a_b, S_gRep_b, S_a_gRep_b,
#                       S_a_gRep_b_2, S_b_gRep, S_a_b_gRep, S_ab_gRep)
#
# Combines the THREE length-3 Syzygy words for (gRep, a, b) in all
# three positions of gRep, into ONE word that, when Homotopy(2, _)-ed,
# gives the same per-cell contribution vector as the original three
# Homotopy(2, _) calls combined with signs +1, -1, +1.
#
# Math:
#   contrib(Syz([g1,g2,g3])) = (Homotopy(2, W1 + W2 - W3 - W4))
#
# Letting:
#   W1 := Mult(gRep, S_a_b) + S_gRep_ab - S_gRep_a_b - S_gRep_a       (Triple #1)
#   W2 := Mult(a, S_gRep_b) + S_a_gRep_b - S_a_gRep_b_2 - S_a_gRep    (Triple #2)
#   W3 := Mult(a, S_b_gRep) + S_a_b_gRep - S_ab_gRep - S_a_b          (Triple #3)
#
# Then:
#   Triple_combined := W1 - W2 + W3
#   contrib_b       := Homotopy(2, Triple_combined) extracted to length-ncells vec
#
# Linearity of Homotopy at the word level (it's a Sum over cells of
# AddFreeWords) means Homotopy(2, W1 - W2 + W3) gives the same per-
# cell sum as Homotopy(2,W1) - Homotopy(2,W2) + Homotopy(2,W3) when
# we then sum signs into a length-ncells vector. AddFreeWords reduces
# cancelling cells in (W1 - W2 + W3), so the combined Homotopy(2,_)
# call may be substantially faster than three independent calls.
#
# Names: S_<x>_<y> is Syzygy(R, [x, y]).
# Args (12): (g1*g2 = "g1g2" infix in name to avoid confusion).
#   S_gRep_a    : Syz([gRep, a])       -- T1 last term
#   S_a_gRep    : Syz([a, gRep])       -- T2 last term
#   S_a_b       : Syz([a, b])          -- T3 last term AND T1 inside Mult
#   S_gRep_ab   : Syz([gRep, a*b])     -- T1 second term
#   S_gRep_a_b  : Syz([gRep*a, b])     -- T1 third term (NEGATED in T1)
#   S_gRep_b    : Syz([gRep, b])       -- T2 inside Mult
#   S_a_gRep_b  : Syz([a, gRep*b])     -- T2 second term
#   S_a_gRep_b_2: Syz([a*gRep, b])     -- T2 third term (NEGATED in T2)
#   S_b_gRep    : Syz([b, gRep])       -- T3 inside Mult
#   S_a_b_gRep  : Syz([a, b*gRep])     -- T3 second term
#   S_ab_gRep   : Syz([a*b, gRep])     -- T3 third term (NEGATED in T3)
_Syzygy3CombinedWord := function(R, gRep, a, S_gRep_a, S_a_gRep, S_a_b,
                                 S_gRep_ab, S_gRep_a_b, S_gRep_b,
                                 S_a_gRep_b, S_a_gRep_b_2, S_b_gRep,
                                 S_a_b_gRep, S_ab_gRep)
    local R_elts, W1, W2, W3, W;
    R_elts := R!.elts;
    # W1 (Triple #1 = Syz([gRep, a, b])):
    #   Mult(gRep, S_a_b) + S_gRep_ab - S_gRep_a_b - S_gRep_a
    W1 := _MultByElt(R_elts, gRep, S_a_b);
    W1 := _AddFreeWordsFast(W1, S_gRep_ab);
    W1 := _AddFreeWordsFast(W1, NegateWord(S_gRep_a_b));
    W1 := _AddFreeWordsFast(W1, NegateWord(S_gRep_a));
    # W2 (Triple #2 = Syz([a, gRep, b])):
    #   Mult(a, S_gRep_b) + S_a_gRep_b - S_a_gRep_b_2 - S_a_gRep
    W2 := _MultByElt(R_elts, a, S_gRep_b);
    W2 := _AddFreeWordsFast(W2, S_a_gRep_b);
    W2 := _AddFreeWordsFast(W2, NegateWord(S_a_gRep_b_2));
    W2 := _AddFreeWordsFast(W2, NegateWord(S_a_gRep));
    # W3 (Triple #3 = Syz([a, b, gRep])):
    #   Mult(a, S_b_gRep) + S_a_b_gRep - S_ab_gRep - S_a_b
    W3 := _MultByElt(R_elts, a, S_b_gRep);
    W3 := _AddFreeWordsFast(W3, S_a_b_gRep);
    W3 := _AddFreeWordsFast(W3, NegateWord(S_ab_gRep));
    W3 := _AddFreeWordsFast(W3, NegateWord(S_a_b));
    # W := W1 - W2 + W3
    W := W1;
    W := _AddFreeWordsFast(W, NegateWord(W2));
    W := _AddFreeWordsFast(W, W3);
    return _Homotopy2(R, W);
end;;

BuildPerClassCocycleBasis := function(setup, gRep, C)
    local key, elts, n, basis, basis_T, k, exp, R, ncells, table, idx_map,
          a, b, x, result,
          r_half, table_gf2, table_gf2_bot, table_gf2_top_T, table_T,
          row, one_gf2, table_rows,
          contrib_row, contrib_b, S, chunk,
          a_elt, b_elt, ab_elt, gRep_a, a_gRep, b_gRep, gRep_b,
          S_gRep_a, S_a_gRep, S_a_b, S_gRep_b, S_b_gRep,
          S_T1_S_g1_g2g3, S_T1_S_g1g2_g3,
          S_T2_S_g1_g2g3, S_T2_S_g1g2_g3,
          S_T3_S_g1_g2g3, S_T3_S_g1g2_g3;

    key := Concatenation("G", _SafeIdString(setup.group),
                         "_g", String(gRep),
                         "_C", _SafeIdString(C),
                         "_n", String(Size(C)));
    if IsBound(_basis_cache_by_class.(key)) then
        return _basis_cache_by_class.(key);
    fi;

    elts := AsList(C);
    n := Length(elts);
    basis := setup.UCT.cocyclebasis;
    k := Length(basis);
    exp := setup.UCT.exponent;
    R := setup.R;
    ncells := R!.dimension(3);

    # A-7 perf-5 (#281): row-batched Syzygy table + compiled matmul.
    #
    # Original loop did 3 Syzygy calls per (a, b) plus a k-fold dot-product
    # inner loop `for i in [1..k] do table[r][i] := (contrib * basis[i]) mod exp; od;`.
    # The dot products are interpreted-mode per-element calls dispatching k
    # times. Profile (eplus3_build_per_class_cocycle_basis.txt) showed
    # PosPlist/EqPlist dominating inside the Syzygy chain walk — that cost
    # is unavoidable at this layer (it IS the Syzygy computation), but the
    # post-Syzygy assembly was wasted per-row interpreter dispatch.
    #
    # New strategy (Route A in #281):
    #   1. For each outer row `a`, walk b in [1..n] building ONE dense
    #      contribution vector per b: accumulate +Syzygy(rep, a, b),
    #      -Syzygy(a, rep, b), +Syzygy(a, b, rep) into a single length-
    #      ncells integer vector. Saves 2× length-ncells allocations and
    #      the v1-v2+v3 subtract pass that the original code did.
    #   2. Stack the n contribution vectors into an n × ncells matrix.
    #   3. chunk := (contrib_row * basis_T) mod exp where basis_T is the
    #      ncells × k matrix whose i-th column is basis[i]. This dispatches
    #      to GAP's compiled integer matmul (PROD_MAT_MAT), replacing the
    #      n*k per-(a,b) interpreted dot products with one compiled matmul
    #      per row-batch.
    #   4. Append chunk rows to table_rows.
    #
    # Memory: peak per-row buffer = n × ncells integers. At m=5,
    # n=2048, ncells likely a few hundred → tens of MB temp, negligible
    # vs the n² × k final table.
    #
    # Same 3 × n² length-3 Syzygy outputs as the original. Route A's
    # savings are in:
    #   (a) one compiled matmul per row vs n*k interpreted dot products,
    #   (b) one mod-exp pass per row chunk vs n*k per-cell mods,
    #   (c) one accumulator vector per (a, b) instead of three (v1, v2, v3
    #       + v1-v2+v3 subtraction pass).
    #
    # A-7 perf-5b (this file): inside the (a, b) loop, the three length-3
    # Syzygies are computed by _Syzygy3FromParts which takes pre-computed
    # length-2 sub-syzygies. Hoisting + sharing reduces length-2 Syzygy
    # calls by ~25% (see _Syzygy3FromParts docs above).

    # Build basis_T: ncells × k integer matrix with column i = basis[i].
    # GAP matrices are row-major; we want each row of contrib_row to be
    # multiplied by all k cocycle basis vectors. Standard math: (1 × ncells)
    # × (ncells × k) = (1 × k). So basis_T must have shape (ncells × k),
    # i.e. basis_T[j][i] = basis[i][j].
    basis_T := TransposedMatMutable(basis);
    ConvertToMatrixRep(basis_T);

    # A-7 perf-5b (#281): HAP-level prefix-Syzygy sharing.
    #
    # For each outer `a`, two length-2 Syzygies are constant across the
    # inner b-loop and are hoisted out:
    #   S_gRep_a = Syzygy(R, [gRep, elts[a]])   -- last term of Triple #1
    #   S_a_gRep = Syzygy(R, [elts[a], gRep])   -- last term of Triple #2
    # Within each (a, b), Syz([a, b]) is computed ONCE and shared
    # between Triple #1 (Mult(gRep, S_a_b)) and Triple #3 (-S_a_b).
    #
    # The triples themselves are inlined via _Syzygy3FromParts which
    # accepts pre-computed length-2 sub-syzygies. Output of
    # _Syzygy3FromParts is bit-identical to Syzygy(R, [...]).
    #
    # NOTE on speedup: the wall-time savings are smaller than initially
    # hoped (Route B target was 5-30x; measured at m=3 ~0% wall). The
    # length-2 Syzygy calls we eliminate are individually cheap because
    # HAP's underlying Contraction lookup is memoised at the cell level
    # (resFiniteGroup.gi:282 `ComputedContractions[i][z1][z2]`). After
    # the first few (a, b) iterations the Contraction cache is hot, so
    # the saved length-2 calls cost very little. The dominant cost is
    # in the AddFreeWords combining 4 length-2 sub-syzygies into the
    # length-3 word (3x per (a, b)), which our optimisation does NOT
    # eliminate. See PERF5B_FEASIBILITY.md for the full analysis.
    #
    # We keep the refactor because it's slightly cleaner, costs nothing
    # (within noise vs Route A baseline), and provides infrastructure
    # for follow-up work (e.g. replacing AddFreeWords's quadratic
    # linear-scan Position with a dict, which the profile suggests is
    # the real lever).
    table_rows := EmptyPlist(n * n);
    for a in [1..n] do
        a_elt := elts[a];
        gRep_a := gRep * a_elt;
        a_gRep := a_elt * gRep;
        # HOIST out of b-loop: invariant length-2 syzygies for this a.
        S_gRep_a := Syzygy(R, [gRep, a_elt]);
        S_a_gRep := Syzygy(R, [a_elt, gRep]);

        # Build the (n × ncells) contribution matrix for this fixed `a`.
        # Each row b is the *signed sum* of three Syzygy chain encodings.
        contrib_row := EmptyPlist(n);
        for b in [1..n] do
            b_elt := elts[b];
            ab_elt := a_elt * b_elt;
            b_gRep := b_elt * gRep;
            gRep_b := gRep * b_elt;

            # SHARE between Triple #1 (uses Mult(gRep, S_a_b)) and Triple #3
            # (uses -S_a_b): compute Syz([a, b]) once.
            S_a_b := Syzygy(R, [a_elt, b_elt]);

            # Triple #1 = Syzygy(R, [gRep, a_elt, b_elt]).
            # g1=gRep, g2=a_elt, g3=b_elt.
            #   Sub-Syzygies: S([a,b]), S([gRep, a*b]), S([gRep*a, b]), S([gRep, a])
            S_T1_S_g1_g2g3 := Syzygy(R, [gRep, ab_elt]);
            S_T1_S_g1g2_g3 := Syzygy(R, [gRep_a, b_elt]);

            # Triple #2 = Syzygy(R, [a_elt, gRep, b_elt]).
            # g1=a_elt, g2=gRep, g3=b_elt.
            #   Sub-Syzygies: S([gRep, b]), S([a, gRep*b]), S([a*gRep, b]), S([a, gRep])
            S_gRep_b := Syzygy(R, [gRep, b_elt]);
            S_T2_S_g1_g2g3 := Syzygy(R, [a_elt, gRep_b]);
            S_T2_S_g1g2_g3 := Syzygy(R, [a_gRep, b_elt]);

            # Triple #3 = Syzygy(R, [a_elt, b_elt, gRep]).
            # g1=a_elt, g2=b_elt, g3=gRep.
            #   Sub-Syzygies: S([b, gRep]), S([a, b*gRep]), S([a*b, gRep]), S([a, b])
            S_b_gRep := Syzygy(R, [b_elt, gRep]);
            S_T3_S_g1_g2g3 := Syzygy(R, [a_elt, b_gRep]);
            S_T3_S_g1g2_g3 := Syzygy(R, [ab_elt, gRep]);

            contrib_b := ListWithIdenticalEntries(ncells, 0);
            # + Syzygy(rep, elts[a], elts[b]) via _Syzygy3FromParts.
            S := _Syzygy3FromParts(R, gRep,
                                   S_a_b,
                                   S_T1_S_g1_g2g3,
                                   S_T1_S_g1g2_g3,
                                   S_gRep_a);
            Apply(S, x -> x[1]);
            for x in S do
                contrib_b[AbsoluteValue(x)] := contrib_b[AbsoluteValue(x)]
                                                + SignInt(x);
            od;
            # - Syzygy(elts[a], rep, elts[b]) via _Syzygy3FromParts.
            S := _Syzygy3FromParts(R, a_elt,
                                   S_gRep_b,
                                   S_T2_S_g1_g2g3,
                                   S_T2_S_g1g2_g3,
                                   S_a_gRep);
            Apply(S, x -> x[1]);
            for x in S do
                contrib_b[AbsoluteValue(x)] := contrib_b[AbsoluteValue(x)]
                                                - SignInt(x);
            od;
            # + Syzygy(elts[a], elts[b], rep) via _Syzygy3FromParts.
            S := _Syzygy3FromParts(R, a_elt,
                                   S_b_gRep,
                                   S_T3_S_g1_g2g3,
                                   S_T3_S_g1g2_g3,
                                   S_a_b);
            Apply(S, x -> x[1]);
            for x in S do
                contrib_b[AbsoluteValue(x)] := contrib_b[AbsoluteValue(x)]
                                                + SignInt(x);
            od;
            Add(contrib_row, contrib_b);
        od;
        # Promote to integer matrix rep for compiled matmul.
        ConvertToMatrixRep(contrib_row);
        # chunk := (contrib_row * basis_T) mod exp, shape (n × k).
        chunk := (contrib_row * basis_T) mod exp;
        for b in [1..n] do
            Add(table_rows, chunk[b]);
        od;
    od;
    table := table_rows;
    idx_map := NewDictionary(elts[1], true, elts);
    for a in [1..n] do
        AddDictionary(idx_map, elts[a], a);
    od;
    # R2-1 (#177): promote table to GAP's matrix rep so that the per-target
    # `basis_cache.table * vec_target` in PerVecTransgressionShared dispatches
    # to the compiled integer matrix-vector path instead of the per-row
    # interpreter loop. At m=5 with n² = 1M rows × k = 165 cols, the matmul
    # is ~165M ops; the compiled path is ~10x the interpreted one.
    ConvertToMatrixRep(table);
    # A-5b R2-8 (#258 + #266 follow-up): precompute the GF(2) bit-r-extracted
    # view of `table` for the Path A reduction in
    # PerVecTransgressionShared in the unified driver.
    #
    # Path A (vec_target[exp_index]=0) needs only
    # `bit_{log2(r)}` of (table * vec_target mod exp). Order-2 basis
    # cocycle values are in {0, r} ⊂ Z/exp, so for order-2 columns
    # k != exp_index, vec_target[k]*table[i][k] mod exp ∈ {0, r}, and
    # bit_{log2(r)} of the sum reduces (over GF(2)) to
    #   sum_k (vec_target[k] mod 2) * bit_{log2(r)}(table[i][k]).
    # The order-4 column (k = exp_index) is zeroed by the Path A
    # precondition `vec_target[exp_index] = 0`, so its bit pattern
    # doesn't matter. This single compiled GF(2) matvec replaces the
    # 1M-int `table * vec_target` allocation + the bit-extract List
    # comprehension on the Path A hot path.
    #
    # Formula generalises across exp = 2 (r=1, bit_0) and exp = 4 (r=2, bit_1).
    r_half := exp / 2;   # = 1 at exp=2 (bit_0), 2 at exp=4 (bit_1), 4 at exp=8 (bit_2), ...
    one_gf2 := One(GF(2));
    table_gf2 := List(table, row ->
        List(row, x -> (QuoInt(x, r_half) mod 2) * one_gf2));
    ConvertToMatrixRep(table_gf2, GF(2));
    # Issue #391 (Approach B): also materialise bit_0(table) as a packed
    # GF(2) matrix. At exp=2 this coincides with table_gf2 (bit_0 = bit_r).
    # At exp=4 it's the bottom bit, identically zero on order-2 columns
    # and nontrivial on the exp_idx column. Used by IsCoboundary2Z4VecBits
    # in the Path Z bit-slice route. See
    # docs/superpowers/specs/2026-06-02-path-z-gf2pack-design.md.
    table_gf2_bot := List(table, row ->
        List(row, x -> (x mod 2) * one_gf2));
    ConvertToMatrixRep(table_gf2_bot, GF(2));
    # Issue #391 (Approach A+B combine): column-major view of
    # table_gf2_top, used for sparsity-aware GF(2) column-XOR in the
    # Path Z bit-pack hot path. table_gf2_top_T[j] is the j-th column
    # as a packed-bit GF(2) vector.
    table_gf2_top_T := TransposedMat(table_gf2);
    ConvertToMatrixRep(table_gf2_top_T, GF(2));
    # Issue #396 audit (A-5): column-major INTEGER view of table, mirror
    # of table_gf2_top_T. Used by IsCoboundary2SplitVecAware's unit-support
    # and sparse-accumulate paths to avoid the n²-closure column extract
    # `List(table, row -> row[j])` (CLAUDE.md P3 anti-pattern). table_T[j]
    # is the j-th column of table as a plain integer row vector.
    #
    # Memory caveat (audit §A-5): doubles per-orbit cache size (~1 GB ->
    # ~2 GB at m=5). Acceptable for current heap budgets; revisit at
    # m=8/m=9 (exp=8) where the integer path becomes the hot route.
    # NOT exercised by the A-5b m=5 production driver (bit-pack route is
    # primary at exp=4); defensive optimization for downstream consumers
    # (exp != 4 / non-power-of-2 exponent paths).
    table_T := TransposedMatMutable(table);
    ConvertToMatrixRep(table_T);
    result := rec(C := C, table := table,
                  table_T := table_T,               # column-major integer view
                  table_gf2 := table_gf2,           # back-compat alias = top bit
                  table_gf2_top := table_gf2,       # bit_{log2(r_half)} = bit_1 at exp=4
                  table_gf2_top_T := table_gf2_top_T,  # column-major view
                  table_gf2_bot := table_gf2_bot,   # bit_0
                  elts := elts, n := n, idx_map := idx_map);
    _basis_cache_by_class.(key) := result;
    return result;
end;;

# Make a c_g closure that does a fast dictionary lookup against the
# precomputed integer table.
MakeCgFromCache := function(c_g_table, cache)
    return function(h, kk)
        return c_g_table[(LookupDictionary(cache.idx_map, h) - 1) * cache.n
                         + LookupDictionary(cache.idx_map, kk)];
    end;
end;;

# ------------------------------------------------------------------
# A-7-perf-1 (#271): BRW-orbit-aware cache builder.
#
# BuildPerClassCocycleBasisForOrbit(setup, conj_action, orb_info,
#                                    h3_matrices) builds the integer
# cocycle table for the orbit's representative class via HAP Syzygy
# calls (one-time O(|C(rep)|^2) cost), then materialises tables for the
# other classes in the orbit by transporting through the BRW action.
# This reduces the per-orbit HAP cost from O(|orbit| · |C|^2 · k) to
# O(|C|^2 · k) — the dominant factor at m=7 where one orbit has
# >4000 classes.
#
# Math (issue #271 description):
#   For sibling g' = phi_path(rep) (where phi_path is a BRW-induced
#   automorphism em -> em with phi_path(rep) = rep_sib), and any (h', k')
#   in C(g'),
#     c_{omega_i}(g', h', k') = c_{phi_path^* omega_i}(rep, h, k)
#                              = sum_j M_path[j][i] · c_{omega_j}(rep, h, k)
#                                                                    (mod exp)
#                                                                    (mod 2-coboundary on C(g'))
#   where (h, k) = phi_path^{-1}((h', k')) lives in C(rep), and
#   M_path is the cumulative H^3 matrix of phi_path on the basis.
#
# The "mod 2-coboundary on C(g')" caveat is real and unavoidable at the
# cocycle level: the transport table differs from a brute-force
# BuildPerClassCocycleBasis(setup, sib_rep, sib_C) by a 2-coboundary on
# C(g'). The BOOLEAN coboundary status (which is what
# IsCoboundary2Split tests) is invariant under this perturbation. See
# solver/tests/test_brw_orbit_cache.g for the empirical check
# (m=2: 130/130 generators agreed; m=3: 2135/2135 generators agreed).
#
# Convention: the cumulative BRW element walking the BFS path
# start -> p_1 -> ... -> target via perm_gens[g_1], ..., perm_gens[g_n]
# (with the GAP-canonical conjugacy-class action perm_y(k) = class index
# of y · rep[k] · y^{-1}) is Y = y_{g_n} · y_{g_{n-1}} · ... · y_{g_1}
# (modulo Inn(em)). This is the convention required for
# phi_path(rep_start) = rep_target to hold (modulo inner-aut fixup).
# Note: this differs from H3VecAtTarget's "apply M in path order"
# accumulation, which produces M_{g_n} · ... · M_{g_1} = matrix of
# phi_{y_{g_1} · ... · y_{g_n}}^*. The two conventions agree only when
# the BRW outer image on H^3 is abelian (e.g. small m / restricted
# image). For per-class-table transport we MUST use the convention
# that matches rep_target exactly, so we accumulate M = M_path[parent]
# · M_{g_k} and use ApplyH3Endomorphism on the right (i.e. column-vec
# on the right of M_path).
# ------------------------------------------------------------------

# _Path_PhiAndMatrix(setup, conj_action, orb_info, h3_matrices, target_idx)
#
# Returns rec(phi_path, M_path) where:
#   - phi_path : em -> em is an automorphism with
#                phi_path(reps[orb_info.start_idx]) = reps[target_idx].
#   - M_path is a k×k integer matrix (mod torsion) representing
#                phi_path^* on the cocyclebasis.
#
# Built incrementally by BFS walk start -> target.
_Path_PhiAndMatrix := function(setup, conj_action, orb_info, h3_matrices,
                                target_idx)
    local path, pos, em, iso_em, reps, rep_start, rep_target,
          phi_partial, M_partial, k, g_step, y_step,
          phi_step, phi_next, cur, c_inner, phi_c, M_step, j, j2, l,
          torsion, M_next;
    em := conj_action.em;
    iso_em := conj_action.iso_em;
    reps := conj_action.reps;
    rep_start := reps[orb_info.start_idx];
    rep_target := reps[target_idx];
    torsion := setup.torsion;
    k := setup.num_generators;

    if target_idx = orb_info.start_idx then
        return rec(
            phi_path := IdentityMapping(em),
            M_path := IdentityMat(k));
    fi;

    # Walk path start -> target via parent pointers.
    path := [target_idx];
    pos := target_idx;
    while orb_info.parent[pos] <> orb_info.start_idx do
        pos := orb_info.parent[pos];
        if pos = -1 then
            Error("_Path_PhiAndMatrix: target ", target_idx,
                  " not reachable from start ", orb_info.start_idx);
        fi;
        Add(path, pos);
    od;
    path := Reversed(path);  # [p_1, p_2, ..., target]

    phi_partial := IdentityMapping(em);
    M_partial := IdentityMat(k);

    for pos in path do
        g_step := orb_info.gen_used[pos];
        # y_step is the BRW matrix generator at step g_step.
        y_step := conj_action.gens[g_step];
        # phi_y : em -> em is conjugation by y_step (through iso_em).
        phi_step := ConjugationAutomorphismThroughIso(em, iso_em, y_step);

        # phi_next_naive := phi_step ∘ phi_partial (apply phi_partial
        # first then phi_step). This satisfies the path math:
        # phi_path[child](rep_start) = phi_step(phi_path[parent](rep_start))
        # = phi_step(rep[parent_pos]) = y_step · rep[parent_pos] · y_step^{-1}
        # = some element of class[pos] (modulo inner).
        phi_next := CompositionMapping(phi_step, phi_partial);
        # Fixup with inner-conjugation so phi_path[child](rep_start) = reps[pos].
        cur := Image(phi_next, rep_start);
        if cur <> reps[pos] then
            c_inner := RepresentativeAction(em, cur, reps[pos]);
            if c_inner = fail then
                Error("_Path_PhiAndMatrix: cur=", cur, " not conjugate to ",
                      reps[pos], " in em (step ", pos,
                      ", g_step=", g_step, ")");
            fi;
            phi_c := ConjugatorAutomorphism(em, c_inner);
            phi_next := CompositionMapping(phi_c, phi_next);
            cur := Image(phi_next, rep_start);
            Assert(0, cur = reps[pos],
                   "Inner-conj fixup failed at step pos");
        fi;

        # M_path[child] = M_path[parent] · M_{g_step} (matrix product
        # in left-to-right path order, which matches phi composition
        # on column vectors: phi_path[child]^*(v) = M_partial · M_step · v).
        # Inner-conj contributes trivially to H^3 (Inn acts trivially).
        M_step := h3_matrices[g_step];
        M_next := NullMat(k, k);
        for j in [1..k] do
            for j2 in [1..k] do
                # (M_partial · M_step)[j][j2] = sum_l M_partial[j][l] * M_step[l][j2]
                M_next[j][j2] := 0;
                for l in [1..k] do
                    M_next[j][j2] := M_next[j][j2]
                                     + M_partial[j][l] * M_step[l][j2];
                od;
                M_next[j][j2] := M_next[j][j2] mod torsion[j];
            od;
        od;

        phi_partial := phi_next;
        M_partial := M_next;
    od;

    return rec(phi_path := phi_partial, M_path := M_partial);
end;;

# _BuildSiblingTableViaTransport(setup, rep_cache, conj_action, target_idx,
#                                  phi_path, M_path)
#
# Build the sibling table for class target_idx (≠ orbit start) by
# transporting rep_cache's table via phi_path and M_path. Returns the
# usual cache record (C, table, table_gf2, elts, n, idx_map) for the
# sibling, ready to drop into _basis_cache_by_class.
#
# Implementation: for each (a, b) in [1..n_sib] x [1..n_sib],
#     table_sib[(a-1)*n+b][i] := (sum_j M_path[j][i] * table_rep[T(a,b)][j])
#                                                                   mod exp,
# where T(a, b) = (σ(a)-1)*n + σ(b) and σ(a) = index of phi_path^{-1}(elts_sib[a])
# in elts_rep.
_BuildSiblingTableViaTransport :=
function(setup, rep_cache, conj_action, target_idx, phi_path, M_path)
    local reps, G, sib_rep, sib_C, elts_sib, n_sib,
          k, exp, sigma, b, h_sib, table_sib,
          a, r_idx, r_rep_idx, s, idx_map_sib, r_half, table_gf2_sib,
          table_gf2_bot_sib, table_gf2_top_T_sib, table_T_sib,
          row, one_gf2;
    reps := conj_action.reps;
    G := setup.group;
    sib_rep := reps[target_idx];
    sib_C := Centralizer(G, sib_rep);
    elts_sib := AsList(sib_C);
    n_sib := Length(elts_sib);
    k := setup.num_generators;
    exp := setup.UCT.exponent;

    Assert(0, n_sib = rep_cache.n,
           Concatenation("_BuildSiblingTableViaTransport: sibling ",
                         "centraliser size ", String(n_sib),
                         " differs from rep centraliser size ",
                         String(rep_cache.n),
                         " for target_idx ", String(target_idx)));

    # Build sigma: sigma[a] = index in rep_cache.elts of phi_path^{-1}(elts_sib[a]).
    # We compute via the forward map: for each b in [1..n_rep], image of
    # rep_cache.elts[b] under phi_path is some elt in elts_sib at position
    # s (= sigma^{-1}[b]). Setting sigma[s] := b inverts.
    idx_map_sib := NewDictionary(elts_sib[1], true, elts_sib);
    for a in [1..n_sib] do
        AddDictionary(idx_map_sib, elts_sib[a], a);
    od;
    sigma := List([1..n_sib], a -> 0);
    for b in [1..rep_cache.n] do
        h_sib := Image(phi_path, rep_cache.elts[b]);
        s := LookupDictionary(idx_map_sib, h_sib);
        if s = fail then
            Error("_BuildSiblingTableViaTransport: phi_path image ",
                  h_sib, " not in elts_sib (target_idx ", target_idx,
                  ", b ", b, ")");
        fi;
        sigma[s] := b;
    od;
    # Sanity: sigma should be a permutation of [1..n_sib].
    Assert(0, Set(sigma) = [1..n_sib],
           Concatenation("_BuildSiblingTableViaTransport: sigma not a ",
                         "permutation; got ", String(Set(sigma))));

    # Build T(a, b) = (sigma[a]-1)*n_rep + sigma[b] for fast row lookup.
    # We collect the permuted rows into a (n²) × k matrix, then do ONE
    # compiled matmul `permuted * M_path` to produce the sibling table.
    # This uses GAP's optimised integer matmul instead of n² · k² interp
    # ops, ~10-100x faster at the m=5 scale (n² = 1M, k = 165).
    table_sib := List([1..n_sib * n_sib], r_idx -> 0);
    for a in [1..n_sib] do
        for b in [1..n_sib] do
            r_idx := (a - 1) * n_sib + b;
            r_rep_idx := (sigma[a] - 1) * rep_cache.n + sigma[b];
            table_sib[r_idx] := rep_cache.table[r_rep_idx];
        od;
    od;
    # `table_sib` is now the row-permuted version of rep_cache.table.
    # Apply M_path on the right: table_sib := table_sib * M_path. Each
    # output row is a 1×k row vector · k×k matrix = 1×k row vector.
    ConvertToMatrixRep(table_sib);
    table_sib := table_sib * M_path;
    # Reduce mod exp (the matmul produces unbounded integers).
    # Issue #396 audit (B-7): replaced the nested closure
    # `List(table_sib, row -> List(row, x -> x mod exp))` with the
    # compiled list-mod-int form (CLAUDE.md P6 anti-pattern fix). GAP's
    # `M mod c` on an integer matrix dispatches to compiled list-mod
    # per row instead of the double-closure dispatch (n² × k = 660M
    # closure invocations per sibling avoided at m=5).
    table_sib := table_sib mod exp;
    ConvertToMatrixRep(table_sib);

    # GF(2) bit-r-extracted view (matches BuildPerClassCocycleBasis).
    r_half := exp / 2;
    one_gf2 := One(GF(2));
    table_gf2_sib := List(table_sib, row ->
        List(row, x -> (QuoInt(x, r_half) mod 2) * one_gf2));
    ConvertToMatrixRep(table_gf2_sib, GF(2));
    # Issue #391 (Approach B): bit_0 view.
    table_gf2_bot_sib := List(table_sib, row ->
        List(row, x -> (x mod 2) * one_gf2));
    ConvertToMatrixRep(table_gf2_bot_sib, GF(2));
    # Column-major view for sparsity-aware column-XOR (issue #391 A+B combine).
    table_gf2_top_T_sib := TransposedMat(table_gf2_sib);
    ConvertToMatrixRep(table_gf2_top_T_sib, GF(2));
    # Issue #396 audit (A-5): column-major INTEGER view, mirror of
    # table_gf2_top_T_sib. Used by IsCoboundary2SplitVecAware on
    # transport-built sibling caches. See BuildPerClassCocycleBasis for
    # the design rationale.
    table_T_sib := TransposedMatMutable(table_sib);
    ConvertToMatrixRep(table_T_sib);

    return rec(C := sib_C, table := table_sib,
               table_T := table_T_sib,             # column-major integer view
               table_gf2 := table_gf2_sib,         # back-compat alias
               table_gf2_top := table_gf2_sib,
               table_gf2_top_T := table_gf2_top_T_sib,
               table_gf2_bot := table_gf2_bot_sib,
               elts := elts_sib, n := n_sib, idx_map := idx_map_sib);
end;;

# BuildPerClassCocycleBasisForOrbit(setup, conj_action, orb_info,
#                                    h3_matrices) builds the rep's
# cocycle-basis table via brute force, then transports it to each
# sibling class in the orbit. All caches are stored in
# _basis_cache_by_class so subsequent BuildPerClassCocycleBasis calls
# for sibling classes hit the cache.
#
# Returns the orbit-rep's cache record (same shape as
# BuildPerClassCocycleBasis).
#
# Use case 1 (driver `run_e_plus_m_kernel_hap.g`): the driver's inner
# loop uses `orbit_caches[oi] = <rep cache>` + H3VecAtTarget to walk
# vec across siblings; no need for per-class sibling caches at the
# driver level. The driver can still call this function purely for
# the side-effect of populating per-class caches (e.g. for downstream
# debugging or analysis tools that look up `_basis_cache_by_class`).
#
# Use case 2 (`TransgressionKernelExact`): brute-force per-class
# enumeration. After this function is called per orbit, the per-class
# `BuildPerClassCocycleBasis(setup, sib_rep, sib_C)` calls hit the
# cache.
BuildPerClassCocycleBasisForOrbit :=
function(setup, conj_action, orb_info, h3_matrices)
    local rep_idx, rep, G, rep_C, rep_cache, target_idx, path_data,
          sib_cache, key;
    rep_idx := orb_info.start_idx;
    rep := conj_action.reps[rep_idx];
    G := setup.group;
    rep_C := Centralizer(G, rep);

    # 1. Build the rep cache (brute force; caches itself under its key).
    rep_cache := BuildPerClassCocycleBasis(setup, rep, rep_C);

    # 2. For each sibling target_idx, transport.
    for target_idx in orb_info.orbit do
        if target_idx = rep_idx then continue; fi;
        # Cache key for the sibling. Mirror BuildPerClassCocycleBasis's
        # key construction so a downstream BuildPerClassCocycleBasis(
        #   setup, sib_rep, sib_C) call hits this entry.
        key := Concatenation("G", _SafeIdString(setup.group),
                             "_g", String(conj_action.reps[target_idx]),
                             "_C", _SafeIdString(Centralizer(G,
                                              conj_action.reps[target_idx])),
                             "_n", String(rep_cache.n));
        if IsBound(_basis_cache_by_class.(key)) then
            continue;  # already built
        fi;
        path_data := _Path_PhiAndMatrix(setup, conj_action, orb_info,
                                         h3_matrices, target_idx);
        sib_cache := _BuildSiblingTableViaTransport(setup, rep_cache,
                                                     conj_action, target_idx,
                                                     path_data.phi_path,
                                                     path_data.M_path);
        _basis_cache_by_class.(key) := sib_cache;
    od;

    return rep_cache;
end;;

TransgressionKernelExact := function(G)
    local setup, classes, k, n_classes, caches, t_cache, kernel_vecs, vec,
          all_zero, j, cache, c_g_table, c_g_func, zero_vec, t_solve;
    setup := SetupCohomology3(G);
    classes := ConjugacyClasses(G);
    n_classes := Length(classes);
    k := Length(setup.torsion);

    Print("TransgressionKernelExact: building per-class basis caches for ",
          n_classes, " classes...\n");
    t_cache := Runtime();
    caches := List([1..n_classes],
                   j -> BuildPerClassCocycleBasis(
                            setup,
                            Representative(classes[j]),
                            Centralizer(G, Representative(classes[j]))));
    Print("Caches built in ", (Runtime() - t_cache) / 1000., " s.\n");
    Print("Enumerating ",
          Product(setup.torsion), " cocycle classes x ",
          n_classes, " centralisers...\n");

    t_solve := Runtime();
    kernel_vecs := [];
    for vec in Cartesian(List(setup.torsion, t -> [0..t-1])) do
        all_zero := true;
        for j in [1..n_classes] do
            cache := caches[j];
            # Issue #372 (F3): compiled matvec + Vec API (#370/#371
            # shape).
            c_g_table := cache.table * vec;
            # Early-return: if c_g is identically zero mod exp, it is the
            # zero cocycle and trivially a coboundary. This always holds
            # for the identity class (where c_g(h, k) = omega(id, h, k) -
            # omega(h, id, k) + omega(h, k, id) = 0 for normalized omega),
            # which would otherwise cost ~1.1 s per Path Z vec on E_+(2)
            # via SolutionIntMat (issue #62 diagnostic).
            if ForAll(c_g_table, x -> x mod setup.exponent = 0) then
                continue;
            fi;
            if not IsCoboundary2SplitVec(cache.C, c_g_table, vec, setup) then
                all_zero := false;
                break;
            fi;
        od;
        if all_zero then
            Add(kernel_vecs, vec);
        fi;
    od;
    Print("Solve loop: ", (Runtime() - t_solve) / 1000., " s.\n");

    zero_vec := List(setup.torsion, t -> 0);
    return rec(setup       := setup,
               classes     := classes,
               kernel      := Filtered(kernel_vecs, v -> v <> zero_vec),
               kernel_size := Length(kernel_vecs));
end;;
