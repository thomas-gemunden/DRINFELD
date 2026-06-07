# Direct computation of the modular data (S, T) of the untwisted
# Drinfeld center Z(Vec_G) = Mod(D^1(G)) for any finite group G.
#
# Bypasses Gruen's cohomology pipeline (no ResolutionFiniteGroup,
# no IsomorphismFpGroup of centralisers, no projective character
# extension). Uses GAP's native conjugacy classes and character
# tables.
#
# Conventions:
#   * Simples are labelled by pairs (g, rho) where g is a conjugacy
#     class representative of G and rho in Irr(C_G(g)).
#   * T_{(g, rho)} = rho(g) / dim(rho).  (Always a root of unity.)
#   * S_{(g_1, rho_1), (g_2, rho_2)}
#       = (1/|G|) * sum_{(a, b) ∈ [g_1] × [g_2] : ab = ba}
#                   conj( rho_1( t_a^{-1} b t_a ) )
#                 * conj( rho_2( s_b^{-1} a s_b ) )
#     where t_a, s_b ∈ G satisfy t_a g_1 t_a^{-1} = a and
#     s_b g_2 s_b^{-1} = b. (The formula is independent of these
#     choices because rho_1, rho_2 are class functions on the
#     respective centralisers.)
#
# Issue #487 (abelian fast path): when G is abelian,
# `ComputeUntwistedModularData(G)` dispatches to the closed-form
# (q_omega, b_omega) -> (S, T) formula in
# `abelian_modular_data_closed_form.g`. The header guard below loads
# the closed-form file if available so the dispatch wire-in can fire.

# ---- Optional sibling load: closed-form abelian path (#487) ----
# Try to locate and load abelian_modular_data_closed_form.g. We swallow
# any read error so that a standalone Read("untwisted_modular_data.g")
# still works on a clean GAP session. Three resolver attempts in order:
#  (1) INPUT_FILENAME() with abs-path prefix removed (works when this
#      file is Read'd via its absolute path)
#  (2) the bare sibling name "abelian_modular_data_closed_form.g" (works
#      when CWD is already the scripts dir)
#  (3) "../abelian_modular_data_closed_form.g" (works when CWD is the
#      tests/ subdir)
if not IsBound(ComputeAbelianModularDataFromQB) then
    _umd_self := INPUT_FILENAME();;
    _umd_done := false;;
    if _umd_self <> fail and _umd_self <> "stream"
       and Length(_umd_self) > Length("untwisted_modular_data.g") then
        _umd_dir := _umd_self{
            [1..Length(_umd_self)
              - Length("untwisted_modular_data.g")]};;
        _umd_cand := Concatenation(_umd_dir,
            "abelian_modular_data_closed_form.g");;
        if IsExistingFile(_umd_cand) then
            Read(_umd_cand);
            _umd_done := true;
        fi;
    fi;
    if not _umd_done then
        for _umd_p in [ "abelian_modular_data_closed_form.g",
                        "../abelian_modular_data_closed_form.g",
                        Concatenation("extraspecial_orbifolds/scripts/",
                                      "abelian_modular_data_closed_form.g") ] do
            if not _umd_done and IsExistingFile(_umd_p) then
                Read(_umd_p);
                _umd_done := true;
            fi;
        od;
    fi;
fi;

# =================================================================
#  Building the index of simple objects
# =================================================================

# Returns a record summarising the simple-object structure of
# Mod(D^1(G)):
#    .order            : |G|
#    .classes          : list of conjugacy classes
#    .reps             : class representatives (g_1 ... g_k)
#    .class_sizes      : sizes of those classes
#    .centralisers     : C_G(g_i) for each i
#    .ct_centraliser   : CharacterTable of each centraliser
#    .cc_centraliser   : conjugacy classes of each centraliser (for evaluating chars)
#    .irreps           : Irr( ct_centraliser_i ) for each i
#    .irrep_dims       : dim chi for each (i, k)
#    .num_irreps       : |Irr(C_i)| for each i
#    .global_offset    : starting global index for each class i
#                          (so simple indices are
#                           global_offset[i] + 1 .. + num_irreps[i])
#    .rank             : sum of num_irreps  ==  total simples
#    .global_to_local  : map global index -> [class_idx, irrep_idx]
BuildSimpleIndex := function(G)
    local classes, reps, class_sizes, centralisers, ct_cent,
          cc_cent, irreps, irrep_dims, num_irreps, global_offset,
          rank, idx, i, k, glob_to_local;
    classes := ConjugacyClasses(G);
    reps := List(classes, Representative);
    class_sizes := List(classes, Size);
    centralisers := List(reps, x -> Centralizer(G, x));
    ct_cent := List(centralisers, CharacterTable);
    cc_cent := List(ct_cent, ConjugacyClasses);
    irreps := List(ct_cent, Irr);
    num_irreps := List(irreps, Length);
    irrep_dims := List(irreps, l -> List(l, chi -> chi[1]));
    rank := Sum(num_irreps);
    global_offset := [0];
    for i in [1..Length(num_irreps) - 1] do
        global_offset[i + 1] := global_offset[i] + num_irreps[i];
    od;
    glob_to_local := [];
    idx := 0;
    for i in [1..Length(classes)] do
        for k in [1..num_irreps[i]] do
            idx := idx + 1;
            glob_to_local[idx] := [i, k];
        od;
    od;
    return rec(
        group := G,
        order := Order(G),
        classes := classes,
        reps := reps,
        class_sizes := class_sizes,
        centralisers := centralisers,
        ct_centraliser := ct_cent,
        cc_centraliser := cc_cent,
        irreps := irreps,
        irrep_dims := irrep_dims,
        num_irreps := num_irreps,
        global_offset := global_offset,
        global_to_local := glob_to_local,
        rank := rank
    );
end;;

# ============================================================
# Lazy variant — K-2c (#129)
# ============================================================
#
# `BuildSimpleIndexLazy(G)` returns the same record shape as
# `BuildSimpleIndex(G)` but defers the per-class CharacterTable builds
# (and therefore `ct_centraliser[i]`, `cc_centraliser[i]`, `irreps[i]`,
# `irrep_dims[i]`) until the FIRST access to that class. For E_+(7) the
# eager version hits GAP's memory limit during cumulative CT builds for
# ~16K classes; the single-query `SKeller(7, i, j)` path only ever needs
# CTs for 2 classes (c1 and c2), so the lazy variant cuts the CT count
# from O(|classes|) to O(1) per query.
#
# Eager fields (same cost as the non-lazy version):
#   classes, reps, class_sizes, centralisers, num_irreps,
#   global_offset, global_to_local, rank
#
# Lazy fields (each is a length-|classes| list initialised to `fail`;
#   populated by `_EnsureClassData` on first access):
#   ct_centraliser, cc_centraliser, irreps, irrep_dims
#
# `is_lazy := true` marker lets the accessors below auto-materialise.
#
# K-2c FOLLOW-UP (this PR): `BuildTransportsLazy` + `GetTransport`
# defer the per-class BFS the same way. Combined with the lazy index
# above, `BuildIntertwinerDataUntwistedLazy` now pays only O(1) per
# class for the single-query SKeller(m, i, j) path. See
# `BuildTransportsLazy` below for the laziness contract and call-site
# convention.
BuildSimpleIndexLazy := function(G)
    local classes, reps, class_sizes, centralisers, num_irreps,
          global_offset, rank, glob_to_local, idx, i, k;
    classes := ConjugacyClasses(G);
    reps := List(classes, Representative);
    class_sizes := List(classes, Size);
    centralisers := List(reps, x -> Centralizer(G, x));
    # NrConjugacyClasses is enough for global offsets — cheaper than
    # the full CharacterTable build that `BuildSimpleIndex` does eagerly.
    num_irreps := List(centralisers, NrConjugacyClasses);
    rank := Sum(num_irreps);
    global_offset := [0];
    for i in [1..Length(num_irreps) - 1] do
        global_offset[i + 1] := global_offset[i] + num_irreps[i];
    od;
    glob_to_local := [];
    idx := 0;
    for i in [1..Length(classes)] do
        for k in [1..num_irreps[i]] do
            idx := idx + 1;
            glob_to_local[idx] := [i, k];
        od;
    od;
    return rec(
        group := G,
        order := Order(G),
        classes := classes,
        reps := reps,
        class_sizes := class_sizes,
        centralisers := centralisers,
        # Lazy fields — `fail` until first `_EnsureClassData` for this i.
        ct_centraliser := List([1..Length(classes)], _ -> fail),
        cc_centraliser := List([1..Length(classes)], _ -> fail),
        irreps         := List([1..Length(classes)], _ -> fail),
        irrep_dims     := List([1..Length(classes)], _ -> fail),
        num_irreps := num_irreps,
        global_offset := global_offset,
        global_to_local := glob_to_local,
        rank := rank,
        is_lazy := true
    );
end;;

# Materialise the per-class CharacterTable data for class i. No-op if
# already materialised, or if `idx` is the eager version (no `is_lazy`).
#
# Issue #449 A1''' + A1'''' + A1':
# - Central class of E_+(m) with `is_closed_form` flag: bypass
#   `CharacterTable(EmUnimodGroup(m))` entirely via the closed-form
#   evaluator (`EPlusBuildAllCharacterRows` in
#   `eplus_irreps_closed_form.g`). Second OOM-cliff fix at m=7 (after
#   #450 fixed `ConjugacyClasses(G)`).
# - Non-central class with `is_closed_form` and lazy centraliser slot:
#   materialise via `_EPlusCentraliserOf` (in `eplus_classes_closed_form.g`).
_EnsureClassData := function(idx, i)
    local ct, cc, irr, m_inferred, all_rows, C;
    if not IsBound(idx.is_lazy) or idx.is_lazy = false then
        return;
    fi;
    if idx.ct_centraliser[i] <> fail then
        return;
    fi;
    # Closed-form dispatch for central class of E_+(m). Only triggers when:
    #   (a) idx has `.is_closed_form = true` (set by
    #       `BuildSimpleIndexEPlusClosedForm`).
    #   (b) The centraliser is the ambient group itself (i.e. the
    #       class is one of the two central classes {I, -I}).
    #   (c) The closed-form evaluator is loaded
    #       (`EPlusBuildAllCharacterRows` in scope).
    if IsBound(idx.is_closed_form) and idx.is_closed_form = true
       and IsBound(idx.centralisers[i]) and idx.centralisers[i] = idx.group
       and IsBoundGlobal("EPlusBuildAllCharacterRows") then
        m_inferred := LogInt(idx.order, 2) - 1;  # |G| = 2^{2m+1} => 2m+1
        m_inferred := QuoInt(m_inferred, 2);
        idx.cc_centraliser[i] := idx.classes;
        all_rows := EPlusBuildAllCharacterRows(m_inferred, idx.reps);
        idx.irreps[i] := all_rows;
        idx.irrep_dims[i] := List(all_rows, chi -> chi[1]);
        idx.ct_centraliser[i] := "closed-form";
        return;
    fi;
    # Non-central path: route centraliser read through _EPlusCentraliserOf
    # (A1') so lazy slots materialise on first access.
    if IsBoundGlobal("_EPlusCentraliserOf") then
        C := _EPlusCentraliserOf(idx, i);
    else
        C := idx.centralisers[i];
    fi;
    ct := CharacterTable(C);
    cc := ConjugacyClasses(ct);
    irr := Irr(ct);
    idx.ct_centraliser[i] := ct;
    idx.cc_centraliser[i] := cc;
    idx.irreps[i] := irr;
    idx.irrep_dims[i] := List(irr, chi -> chi[1]);
end;;

# Position of element x within ConjugacyClasses(C) (where C = centraliser).
# Used to look up character values.
ClassIndexInCentraliser := function(idx, i, x)
    local cc, j;
    _EnsureClassData(idx, i);
    cc := idx.cc_centraliser[i];
    for j in [1..Length(cc)] do
        if x in cc[j] then return j; fi;
    od;
    Error("element not in centraliser ", i, ": ", x);
end;;

# Evaluate the k-th irrep of C_G(g_i) at element x ∈ C_G(g_i).
#
# Issue #449 A1''' + A1'''': for closed-form idxs at the central
# class, route directly through `EPlusEvalIrrep`. This is faster
# than the lookup path (no class-index search) and works even before
# `_EnsureClassData` has populated `idx.irreps[i]`. For closed-form
# idxs at NON-central classes, fall through to the standard path
# (which currently has no closed-form bypass — the non-central
# centraliser CT is still built generically). For non-closed-form
# idxs the standard lookup path is used unchanged.
EvalIrr := function(idx, i, k, x)
    local m_inferred;
    if IsBound(idx.is_closed_form) and idx.is_closed_form = true
       and IsBound(idx.centralisers[i]) and idx.centralisers[i] = idx.group
       and IsBoundGlobal("EPlusEvalIrrep") then
        m_inferred := LogInt(idx.order, 2) - 1;  # |G| = 2^{2m+1} => 2m+1
        m_inferred := QuoInt(m_inferred, 2);
        return EPlusEvalIrrep(m_inferred, k, x);
    fi;
    _EnsureClassData(idx, i);
    return idx.irreps[i][k][ClassIndexInCentraliser(idx, i, x)];
end;;

# =================================================================
#  T-matrix
# =================================================================

ComputeUntwistedT := function(idx)
    local Tdiag, i, k, glob, ki, dim, val;
    Tdiag := [];
    for i in [1..Length(idx.classes)] do
        # ClassIndexInCentraliser already calls _EnsureClassData for lazy
        # idxs, but we read irrep_dims / irreps directly below, so trigger
        # materialisation here too (no-op for eager idxs).
        _EnsureClassData(idx, i);
        ki := ClassIndexInCentraliser(idx, i, idx.reps[i]);
        for k in [1..idx.num_irreps[i]] do
            dim := idx.irrep_dims[i][k];
            val := idx.irreps[i][k][ki];
            Add(Tdiag, val / dim);
        od;
    od;
    return Tdiag;
end;;

# =================================================================
#  Conjugating-elements cache: for each conjugacy class i and each
#  element a ∈ [g_i], store some t with t * g_i * t^{-1} = a.
# =================================================================

# Returns a list `transport` indexed by class i, where
#   transport[i] is a record with
#       .elements : list of elements of [g_i] (sorted, as before)
#       .t_of     : list of group elements t_a (parallel to .elements)
#                   with t_a * g_i * t_a^{-1} = a.
#
# K-2a (#70) optimisation: the original implementation called
# `RepresentativeAction(G, rep_i, a)` once per class element. Each
# such call does an orbit-stabiliser search costing up to O(|G|),
# so the total cost was sum_i |class_i| * O(|G|) = O(|G|^2). For
# E_+(7) (|G| = 2^15 = 32768) that's ~10^9 ops which is intractable.
#
# We replace with a BFS over the conjugation action of G on each
# class: starting from rep_i with transport = identity, each generator
# g of G takes (a, t_a) to (g a g^{-1}, g t_a). This computes the
# whole orbit AND all transports in O(|class_i| * |gens|) work.
# Total: O(|G| * |gens|) = ~500k ops for E_+(7) -- 2000x faster
# than the RepresentativeAction approach.
#
# Output is byte-for-byte identical: .elements is still the sorted
# AsSSortedList(class) result, .t_of is parallel.
#
# K-2c (#129): per-class BFS extracted into `BuildTransportForClass` so
# the lazy variant below can materialise one class at a time without
# paying the eager iteration cost over all classes. `BuildTransports`
# is now a thin loop over `BuildTransportForClass`.
BuildTransportForClass := function(idx, class_idx)
    local elts, rep, gens, t_by_elt, queue, head, a, t_a, g, b, ts, k,
          elt_to_idx;
    elts := AsSSortedList(idx.classes[class_idx]);
    rep := idx.reps[class_idx];
    gens := GeneratorsOfGroup(idx.group);
    # BFS from rep under conjugation, accumulating transports.
    t_by_elt := NewDictionary(rep, true);
    AddDictionary(t_by_elt, rep, One(idx.group));
    queue := [rep];
    head := 1;
    while head <= Length(queue) do
        a := queue[head];
        t_a := LookupDictionary(t_by_elt, a);
        for g in gens do
            b := g * a * g^(-1);
            if LookupDictionary(t_by_elt, b) = fail then
                AddDictionary(t_by_elt, b, g * t_a);
                Add(queue, b);
            fi;
        od;
        head := head + 1;
    od;
    # Materialise transports in .elements order (sorted) for
    # byte-for-byte compatibility with the original API.
    ts := List(elts, a -> LookupDictionary(t_by_elt, a));
    if ForAny(ts, t -> t = fail) then
        Error("BuildTransportForClass: BFS did not cover class ",
              class_idx);
    fi;
    # P-9 (#126): for ProjectorFormula's centraliser-intersection
    # path, build a `b -> bi` lookup so we can find the transport
    # index of a candidate b in O(log |class|) instead of O(|class|).
    elt_to_idx := NewDictionary(rep, true);
    for k in [1..Length(elts)] do
        AddDictionary(elt_to_idx, elts[k], k);
    od;
    return rec(elements := elts, t_of := ts, elt_to_idx := elt_to_idx);
end;;

BuildTransports := function(idx)
    local transport, i;
    transport := [];
    for i in [1..Length(idx.classes)] do
        Add(transport, BuildTransportForClass(idx, i));
    od;
    return transport;
end;;

# K-2c (#129): lazy variant of `BuildTransports`.
#
# Returns a plain GAP list `transport_lazy` of length
# `Length(idx.classes)`, indexable as `transport_lazy[i]`. Initially
# every slot holds `fail`; the slot for class `i` is materialised
# (replaced by the `rec(elements, t_of, elt_to_idx)` record) only on
# the first call to `GetTransport(transport_lazy, idx, i)` for that i.
#
# At m=7 (E_+(7), ~16K classes, |G|=32768) the eager
# `BuildTransports` does ~16M BFS steps up-front, dominating cache
# build alongside the CT builds (which K-2c already deferred via
# `BuildSimpleIndexLazy`). For the single-query `SKeller(7, i, j)`
# path only 2 class slots ever need materialisation, so this cuts the
# transport cost from O(|classes| * |G|) to O(|G|) per query.
#
# CONSUMER CALL-SITE CONTRACT
# ===========================
# Every consumer that previously wrote
#     elts_i := transport[i].elements;
#     ts_i  := transport[i].t_of;
#     e2i_j := transport[j].elt_to_idx;
# MUST instead do
#     t_i   := GetTransport(transport, idx, i);
#     elts_i := t_i.elements;
#     ts_i  := t_i.t_of;
#     t_j   := GetTransport(transport, idx, j);
#     e2i_j := t_j.elt_to_idx;
# `GetTransport` is a no-op (just a list lookup) for already-
# materialised slots, including transports produced by the eager
# `BuildTransports`, so it is safe to use unconditionally with both
# variants. Backward compatibility is preserved: the returned record
# shape is identical to the eager version.
BuildTransportsLazy := function(idx)
    local transport, i;
    transport := [];
    for i in [1..Length(idx.classes)] do
        Add(transport, fail);
    od;
    return transport;
end;;

# K-2c (#129): accessor used by transport consumers.
# Materialises slot `i` of `transport` (a list returned by either
# `BuildTransports` or `BuildTransportsLazy`) on first access and
# returns the per-class record `rec(elements, t_of, elt_to_idx)`.
#
# Safe under either variant:
#   * eager  transport[i] : already a record; returned unchanged.
#   * lazy   transport[i] : initially `fail`; built via
#                            `BuildTransportForClass(idx, i)` and
#                            cached in-place.
#
# The function mutates `transport[i]` in-place; subsequent calls are
# O(1) list lookups.
GetTransport := function(transport, idx, i)
    if transport[i] = fail then
        transport[i] := BuildTransportForClass(idx, i);
    fi;
    return transport[i];
end;;

# =================================================================
#  S-matrix
# =================================================================

# Compute the S-block for class pair (i, j) — a |Irr(C_i)|×|Irr(C_j)| matrix.
#
# P-9 (#126): enumerate commuting (a, b) pairs via the centraliser
# directly, not by iterating the full class_i × class_j Cartesian
# product. For each a ∈ class_i, C_G(a) = t_a · C_G(g_i) · t_a^{-1};
# the commuting b ∈ class_j are exactly the elements of class_j ∩
# C_G(a). Iterate `c ∈ C_G(g_i)`, conjugate `b := t_a c t_a^{-1}`,
# membership-test against the precomputed `class_j` dictionary.
# Total iterations per (i, j) block: |class_i| × |C_G(g_i)| = |G|
# vs the original |class_i| × |class_j|, saving a factor
# |class_j| / |C_G(g_i)| (~10^3 - 10^4 for E_+(7) typical classes).
ComputeSBlock := function(idx, transport, i, j)
    local M, Ni, Nj, elts_i, elts_j, ts_i, ts_j, ai, bi, a, b, t_a, s_b,
          b_tilde, a_tilde, k, l, ord, cen_i_elts, c, elt_to_idx_j,
          t_i, t_j;
    Ni := idx.num_irreps[i]; Nj := idx.num_irreps[j];
    M := List([1..Ni], k -> List([1..Nj], l -> 0));
    # K-2c (#129): route per-class transport reads through GetTransport
    # so this function transparently supports both eager (BuildTransports)
    # and lazy (BuildTransportsLazy) transport lists.
    t_i := GetTransport(transport, idx, i);
    t_j := GetTransport(transport, idx, j);
    elts_i := t_i.elements;
    elts_j := t_j.elements;
    ts_i := t_i.t_of;
    ts_j := t_j.t_of;
    # Issue #449 A1': lazy centraliser materialisation for closed-form
    # E_+(m) idxs. No-op for eager idxs (slot already holds a group).
    if IsBoundGlobal("_EPlusCentraliserOf") then
        cen_i_elts := AsList(_EPlusCentraliserOf(idx, i));
    else
        cen_i_elts := AsList(idx.centralisers[i]);
    fi;
    elt_to_idx_j := t_j.elt_to_idx;
    ord := idx.order;
    if Length(elts_j) <= Length(cen_i_elts) then
        # Path (A): iterate class_j directly (smaller of the two).
        for ai in [1..Length(elts_i)] do
            a := elts_i[ai];
            t_a := ts_i[ai];
            for bi in [1..Length(elts_j)] do
                b := elts_j[bi];
                if a * b <> b * a then continue; fi;
                s_b := ts_j[bi];
                b_tilde := t_a^-1 * b * t_a;     # in C_G(g_i)
                a_tilde := s_b^-1 * a * s_b;     # in C_G(g_j)
                for k in [1..Ni] do
                    for l in [1..Nj] do
                        M[k][l] := M[k][l]
                            + ComplexConjugate(EvalIrr(idx, i, k, b_tilde))
                            * ComplexConjugate(EvalIrr(idx, j, l, a_tilde));
                    od;
                od;
            od;
        od;
    else
        # Path (B): iterate C_G(g_i) and conjugate by t_a.
        for ai in [1..Length(elts_i)] do
            a := elts_i[ai];
            t_a := ts_i[ai];
            for c in cen_i_elts do
                b := t_a * c * t_a^(-1);
                bi := LookupDictionary(elt_to_idx_j, b);
                if bi = fail then continue; fi;
                s_b := ts_j[bi];
                b_tilde := c;                    # = t_a^{-1} * b * t_a
                a_tilde := s_b^-1 * a * s_b;     # in C_G(g_j)
                for k in [1..Ni] do
                    for l in [1..Nj] do
                        M[k][l] := M[k][l]
                            + ComplexConjugate(EvalIrr(idx, i, k, b_tilde))
                            * ComplexConjugate(EvalIrr(idx, j, l, a_tilde));
                    od;
                od;
            od;
        od;
    fi;
    return M / ord;
end;;

# Compute the full S-matrix.
ComputeUntwistedS := function(idx)
    local transport, S, n, i, j, block, off_i, off_j, k, l;
    transport := BuildTransports(idx);
    n := idx.rank;
    S := List([1..n], i -> List([1..n], j -> 0));
    for i in [1..Length(idx.classes)] do
        for j in [1..Length(idx.classes)] do
            block := ComputeSBlock(idx, transport, i, j);
            off_i := idx.global_offset[i];
            off_j := idx.global_offset[j];
            for k in [1..idx.num_irreps[i]] do
                for l in [1..idx.num_irreps[j]] do
                    S[off_i + k][off_j + l] := block[k][l];
                od;
            od;
        od;
    od;
    return S;
end;;

# Convenience: compute both at once.
#
# Issue #487: when G is abelian, dispatch to the analytical closed-form
# in abelian_modular_data_closed_form.g — O(|G|^2) S-build instead of
# O(|G|^4) Bantay sum. For G = (Z/2)^k k = 5 this is a ~30x speedup at
# |G| = 32; at |G| = 256 (the m = 7 max EA) the generic path is
# ~4 * 10^9 operations versus ~6.5 * 10^4 for the closed form. The
# untwisted case (omega = 0) is always safe under the closed-form
# formula's domain-of-validity rules (see abelian_modular_data_closed_form.g
# header). For non-abelian G we use the generic Bantay build below.
ComputeUntwistedModularData := function(G)
    local idx, cf_zero;
    if IsAbelian(G) and IsBoundGlobal("ComputeAbelianModularDataFromQB") then
        # Closed-form fast path. q_omega = b_omega = 0 for the untwisted
        # case, so the projective phase reduces to 1 everywhere and the
        # T- / S- formulas collapse to T = chi(a), S = chi(b)^{-1} *
        # psi(a)^{-1} / |G|.
        cf_zero := ComputeAbelianModularDataFromQB(
            G,
            ListWithIdenticalEntries(Size(G), 0),
            List([1..Size(G)], i -> ListWithIdenticalEntries(Size(G), 0)),
            1
        );
        return rec(
            T := cf_zero.T,
            S := cf_zero.S,
            simples := cf_zero.simples,
            via_closed_form := true,
            group := G
        );
    fi;
    # Non-abelian path: generic Bantay sum via BuildSimpleIndex +
    # ComputeUntwistedT / ComputeUntwistedS.
    idx := BuildSimpleIndex(G);
    return rec(
        idx := idx,
        T := ComputeUntwistedT(idx),
        S := ComputeUntwistedS(idx),
        via_closed_form := false
    );
end;;
