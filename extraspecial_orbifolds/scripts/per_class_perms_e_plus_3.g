# Per-class irrep relabellings sigma_i for E_+(3).
#
# For each non-canonical class i (relative to its type's canonical
# class), we find the row permutation sigma_i: Irr(C_canonical) ->
# Irr(C_i) such that
#
#   block(canonical_for_type(i), 1)[k][.]  =  block(i, 1)[sigma_i(k)][.]
#
# where j = 1 (the identity class) provides a fixed reference column
# axis.  Once we have all sigma_i, any S-block can be reconstructed
# from the canonical block of its refined group plus the relabellings.
#
# Validation: reconstruct dense S from canonical blocks + sigma_i
# permutations, compare byte-for-byte to computed/E_plus_3/S.g.

Read("untwisted_modular_data.g");

If_ := function(cond, a, b) if cond then return a; else return b; fi; end;;

ClassifyTypes := function(idx)
    local types, i, rep, ord, sz;
    types := [];
    for i in [1..Length(idx.classes)] do
        rep := idx.reps[i]; ord := Order(rep); sz := idx.class_sizes[i];
        if sz = 1 and ord = 1 then Add(types, "id");
        elif sz = 1 and ord = 2 then Add(types, "minus_one");
        elif ord = 2 then Add(types, "sigma2");
        elif ord = 4 then Add(types, "sigma_1sigma_2");
        else Add(types, "UNKNOWN"); fi;
    od;
    return types;
end;;

ComputeCommute := function(idx)
    local n, M, i, j;
    n := Length(idx.classes); M := NullMat(n, n);
    for i in [1..n] do for j in [1..n] do
        if idx.reps[i] * idx.reps[j] = idx.reps[j] * idx.reps[i] then
            M[i][j] := 1;
        fi;
    od; od;
    return M;
end;;

GroupKey := function(types, commute, i, j)
    return Concatenation(types[i], "/", types[j], "/", String(commute[i][j]),
                         "/", If_(i = j, "diag", "off"));
end;;

# Identify canonical class index per type (first occurrence).
CanonicalForType := function(types)
    local canonical, i, t;
    canonical := rec();
    for i in [1..Length(types)] do
        t := types[i];
        if not IsBound(canonical.(t)) then
            canonical.(t) := i;
        fi;
    od;
    return canonical;
end;;

GetBlock := function(S, idx, i, j)
    local off_i, off_j;
    off_i := idx.global_offset[i]; off_j := idx.global_offset[j];
    return List([1..idx.num_irreps[i]], k ->
        List([1..idx.num_irreps[j]], l -> S[off_i + k][off_j + l]));
end;;

# Find row permutation P such that B[k] = A[P[k]] (allowing identity
# col, but with row matching only).  Assumes blocks are row-permutations
# with no column re-ordering (i.e. j = j_anchor in both A and B).
# Returns P or fail.
FindRowPerm := function(A, B)
    local m, k, P, k0, used;
    m := Length(A);
    if m <> Length(B) then return fail; fi;
    P := [];
    used := List([1..m], i -> false);
    for k in [1..m] do
        for k0 in [1..m] do
            if not used[k0] and A[k0] = B[k] then
                P[k] := k0;
                used[k0] := true;
                break;
            fi;
        od;
        if not IsBound(P[k]) then
            return fail;  # no row of A equals B[k] (or all matches used)
        fi;
    od;
    return P;
end;;

# ---------------------------------------------------------------
# Driver
# ---------------------------------------------------------------

Print("Building idx for E_+(3)...\n");
G := SmallGroup(128, 2326);;
idx := BuildSimpleIndex(G);;
n_classes := Length(idx.classes);;
types := ClassifyTypes(idx);;
canonical := CanonicalForType(types);;
Print("  canonical classes per type: ");
for k in RecNames(canonical) do Print(k, "=", canonical.(k), " "); od;
Print("\n");

Print("Loading dense S...\n");
Read("../computed/E_plus_3/S.g");

# Compute sigma_i for each non-canonical class.
# Use j_anchor = 1 (the identity class).
j_anchor := canonical.id;;
Print("Using j_anchor = ", j_anchor, " (the identity class)\n");

sigma := [];
n_canonical := 0;
n_failed := 0;
for i in [1..n_classes] do
    t := types[i];
    canonical_i := canonical.(t);
    if i = canonical_i then
        sigma[i] := List([1..idx.num_irreps[i]], k -> k);  # identity
        n_canonical := n_canonical + 1;
    else
        A := GetBlock(S, idx, canonical_i, j_anchor);
        B := GetBlock(S, idx, i, j_anchor);
        P := FindRowPerm(A, B);
        if P = fail then
            Print("  FAIL at class ", i, " (type ", t, ")\n");
            n_failed := n_failed + 1;
            sigma[i] := fail;
        else
            sigma[i] := P;
        fi;
    fi;
od;
Print("Computed sigma for ", n_classes - n_canonical - n_failed,
      " non-canonical classes  (", n_canonical, " canonical, ",
      n_failed, " failed)\n");

# Verify reconstruction.
# For each (i, j), block(i, j) should equal canonical_block_for_group(i,j)
# with rows permuted by sigma_to_canonical_pair_first(i, group)
# and cols permuted by sigma_to_canonical_pair_second(j, group).
#
# For the canonical pair of each group, sigma_to_canonical_pair_first(i_g, g) = identity
# and sigma_to_canonical_pair_second(j_g, g) = identity.

if n_failed > 0 then
    Print("Some sigma_i failed; not validating reconstruction.\n");
    QUIT;
fi;

# For each refined group, identify canonical pair and store canonical block.
commute := ComputeCommute(idx);;
groups := rec();
canonical_pair := rec();
canonical_block := rec();
for i in [1..n_classes] do
    for j in [1..n_classes] do
        key := GroupKey(types, commute, i, j);
        if not IsBound(canonical_pair.(key)) then
            canonical_pair.(key) := [i, j];
            canonical_block.(key) := GetBlock(S, idx, i, j);
        fi;
    od;
od;

# Composition: sigma_{a -> b} = sigma_a^{-1} composed with sigma_b
# (both relative to canonical_for_type).  Specifically:
# block(b, j)[k] = block(canonical, j)[sigma_b^{-1}(k)]
# block(a, j)[k] = block(canonical, j)[sigma_a^{-1}(k)]
# Want: block(b, j)[k] = block(a, j)[??]
# block(a, j)[?] = block(canonical, j)[sigma_a^{-1}(?)]
# Need sigma_a^{-1}(?) = sigma_b^{-1}(k), so ? = sigma_a(sigma_b^{-1}(k)).
# So sigma_{b -> a}(k) = sigma_a(sigma_b^{-1}(k)).
# i.e., perm_{a -> b} (going from a's labelling to b's) = sigma_b ∘ sigma_a^{-1}.

InvertPerm := function(p)
    local n, q, i;
    n := Length(p);
    q := [];
    for i in [1..n] do q[p[i]] := i; od;
    return q;
end;;

ComposePerms := function(p, q)  # (p ∘ q)(k) = p(q(k))
    local n, r, k;
    n := Length(q);
    r := [];
    for k in [1..n] do r[k] := p[q[k]]; od;
    return r;
end;;

# perm from i_g (the canonical first axis of group g) to i:
#   block(i, j_g)[k][l] = block(i_g, j_g)[??][l]
#   Apply sigma_i^{-1} and sigma_{i_g} sequentially.
#   block(i, j_g)[k][l] = block(canonical_for_type(i), j_g)[sigma_i^{-1}(k)][l]
#   block(i_g, j_g)[k'][l] = block(canonical, j_g)[sigma_{i_g}^{-1}(k')][l]
#   So block(i, j_g)[k] = block(i_g, j_g)[sigma_{i_g}(sigma_i^{-1}(k))][l]
#
# Define perm_first(i, i_g) such that
#   block(i, j_g)[k] = canonical_block[perm_first(i, i_g)(k)]
# perm_first(i, i_g)(k) = sigma_{i_g}(sigma_i^{-1}(k))

PermFirst := function(i, i_g)
    return ComposePerms(sigma[i_g], InvertPerm(sigma[i]));
end;;

PermSecond := function(j, j_g)
    return ComposePerms(sigma[j_g], InvertPerm(sigma[j]));
end;;

# Validate reconstruction.
Print("\nReconstructing dense S from canonical blocks + per-class sigma...\n");
tic := Runtime();;
S_rec := List([1..idx.rank], i -> List([1..idx.rank], j -> 0));;
for i in [1..n_classes] do
    for j in [1..n_classes] do
        key := GroupKey(types, commute, i, j);
        block := canonical_block.(key);
        i_g := canonical_pair.(key)[1];
        j_g := canonical_pair.(key)[2];
        pf := PermFirst(i, i_g);
        ps := PermSecond(j, j_g);
        off_i := idx.global_offset[i];
        off_j := idx.global_offset[j];
        for k in [1..idx.num_irreps[i]] do
            for l in [1..idx.num_irreps[j]] do
                S_rec[off_i + k][off_j + l] := block[pf[k]][ps[l]];
            od;
        od;
    od;
od;
Print("  reconstruction in ", (Runtime() - tic)/1000., " s\n");

Print("\nByte-for-byte match: ", S_rec = S, "\n");

if S_rec = S then
    Print("\n=== Per-class permutations VALIDATED for E_+(3) ===\n");
    # Save sigma
    outdir := "../computed/E_plus_3/structural";;
    Exec(Concatenation("mkdir -p ", outdir));
    PrintTo(Concatenation(outdir, "/sigma_per_class.g"),
        "# Per-class irrep relabellings sigma_i for E_+(3).\n",
        "# sigma[i] = list-permutation taking Irr(C_canonical_for_type(i)) -> Irr(C_i).\n",
        "sigma := ", sigma, ";;\n",
        "canonical_for_type := ", canonical, ";;\n");
    Print("Wrote ", outdir, "/sigma_per_class.g\n");
fi;

QUIT;
