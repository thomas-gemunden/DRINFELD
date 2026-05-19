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

BuildPerClassCocycleBasis := function(setup, gRep, C)
    local key, elts, n, basis, k, exp, R, ncells, table, idx_map,
          a, b, r, i, ChainAt, v1, v2, v3, contrib, result,
          r_half, table_gf2, row, one_gf2;

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

    # Chain-level encoding of a triple: same `v` StandardCocycle builds
    # internally, before the dot product with the cocycle vector.
    ChainAt := function(g, h, kk)
        local S, v, x;
        S := Syzygy(R, [g, h, kk]);
        Apply(S, x -> x[1]);
        v := ListWithIdenticalEntries(ncells, 0);
        for x in S do
            v[AbsoluteValue(x)] := v[AbsoluteValue(x)] + SignInt(x);
        od;
        return v;
    end;

    table := List([1..n*n], r -> List([1..k], i -> 0));
    for a in [1..n] do
        for b in [1..n] do
            r := (a-1)*n + b;
            v1 := ChainAt(gRep, elts[a], elts[b]);
            v2 := ChainAt(elts[a], gRep, elts[b]);
            v3 := ChainAt(elts[a], elts[b], gRep);
            contrib := v1 - v2 + v3;   # in Z^ncells
            for i in [1..k] do
                table[r][i] := (contrib * basis[i]) mod exp;
            od;
        od;
    od;
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
    result := rec(C := C, table := table, table_gf2 := table_gf2,
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
    table_sib := List(table_sib, row -> List(row, x -> x mod exp));
    ConvertToMatrixRep(table_sib);

    # GF(2) bit-r-extracted view (matches BuildPerClassCocycleBasis).
    r_half := exp / 2;
    one_gf2 := One(GF(2));
    table_gf2_sib := List(table_sib, row ->
        List(row, x -> (QuoInt(x, r_half) mod 2) * one_gf2));
    ConvertToMatrixRep(table_gf2_sib, GF(2));

    return rec(C := sib_C, table := table_sib, table_gf2 := table_gf2_sib,
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
            c_g_table := List(cache.table,
                              row -> Sum([1..k], i -> vec[i] * row[i]));
            # Early-return: if c_g is identically zero mod exp, it is the
            # zero cocycle and trivially a coboundary. This always holds
            # for the identity class (where c_g(h, k) = omega(id, h, k) -
            # omega(h, id, k) + omega(h, k, id) = 0 for normalized omega),
            # which would otherwise cost ~1.1 s per Path Z vec on E_+(2)
            # via SolutionIntMat (issue #62 diagnostic).
            if ForAll(c_g_table, x -> x mod setup.exponent = 0) then
                continue;
            fi;
            c_g_func := MakeCgFromCache(c_g_table, cache);
            if not IsCoboundary2Split(cache.C, c_g_func, vec, setup) then
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
