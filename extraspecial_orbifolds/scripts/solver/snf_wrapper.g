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
    local r;
    r := CALL_WITH_CATCH(IdGroup, [grp]);
    if r[1] then return String(r[2]); fi;
    return Concatenation("order", String(Order(grp)));
end;;

BuildPerClassCocycleBasis := function(setup, gRep, C)
    local key, elts, n, basis, k, exp, R, ncells, table, idx_map,
          a, b, r, i, ChainAt, v1, v2, v3, contrib, result;

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
    result := rec(C := C, table := table, elts := elts, n := n,
                  idx_map := idx_map);
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
