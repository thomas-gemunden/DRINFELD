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

# Position of element x within ConjugacyClasses(C) (where C = centraliser).
# Used to look up character values.
ClassIndexInCentraliser := function(idx, i, x)
    local cc, j;
    cc := idx.cc_centraliser[i];
    for j in [1..Length(cc)] do
        if x in cc[j] then return j; fi;
    od;
    Error("element not in centraliser ", i, ": ", x);
end;;

# Evaluate the k-th irrep of C_G(g_i) at element x ∈ C_G(g_i).
EvalIrr := function(idx, i, k, x)
    return idx.irreps[i][k][ClassIndexInCentraliser(idx, i, x)];
end;;

# =================================================================
#  T-matrix
# =================================================================

ComputeUntwistedT := function(idx)
    local Tdiag, i, k, glob, ki, dim, val;
    Tdiag := [];
    for i in [1..Length(idx.classes)] do
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
#       .elements : list of elements of [g_i]
#       .t_of     : list of group elements t_a (parallel to .elements)
#                   with t_a * g_i * t_a^{-1} = a.
BuildTransports := function(idx)
    local transport, i, c, elts, ts, a, t;
    transport := [];
    for i in [1..Length(idx.classes)] do
        elts := AsSSortedList(idx.classes[i]);
        ts := [];
        for a in elts do
            t := RepresentativeAction(idx.group, idx.reps[i], a);
            Add(ts, t);
        od;
        Add(transport, rec(elements := elts, t_of := ts));
    od;
    return transport;
end;;

# =================================================================
#  S-matrix
# =================================================================

# Compute the S-block for class pair (i, j) — a |Irr(C_i)|×|Irr(C_j)| matrix.
ComputeSBlock := function(idx, transport, i, j)
    local M, Ni, Nj, elts_i, elts_j, ts_i, ts_j, ai, bi, a, b, t_a, s_b,
          b_tilde, a_tilde, k, l, ord;
    Ni := idx.num_irreps[i]; Nj := idx.num_irreps[j];
    M := List([1..Ni], k -> List([1..Nj], l -> 0));
    elts_i := transport[i].elements;
    elts_j := transport[j].elements;
    ts_i := transport[i].t_of;
    ts_j := transport[j].t_of;
    ord := idx.order;
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
ComputeUntwistedModularData := function(G)
    local idx;
    idx := BuildSimpleIndex(G);
    return rec(
        idx := idx,
        T := ComputeUntwistedT(idx),
        S := ComputeUntwistedS(idx)
    );
end;;
