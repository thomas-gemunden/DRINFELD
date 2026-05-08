# E_BRW m=3 step 2.
#
# We saw in step 1 that blocks of S within a (type, type, commute=1)
# group are NOT literally equal in GAP's natural Irr ordering.  We
# now check the structural hypothesis: each block is some row + column
# permutation of a canonical block within the group.  If so, the
# structural rep needs only ~10 canonical blocks plus per-class
# permutations of Irr.
#
# Necessary condition: sorted row-multisets and column-multisets agree
# across all blocks in the group.  We use a stronger canonical-form
# test: lex-sort rows of the matrix and lex-sort columns.  Two matrices
# with the same canonical form are exactly the row/column permutations
# of each other.

Read("untwisted_modular_data.g");

G := SmallGroup(128, 2326);;
idx := BuildSimpleIndex(G);;
n_classes := Length(idx.classes);;

ClassifyTypes := function(idx)
    local types, i, rep, ord, sz;
    types := [];
    for i in [1..Length(idx.classes)] do
        rep := idx.reps[i];
        ord := Order(rep); sz := idx.class_sizes[i];
        if sz = 1 and ord = 1 then Add(types, "id");
        elif sz = 1 and ord = 2 then Add(types, "minus_one");
        elif ord = 2 then Add(types, "sigma2");
        elif ord = 4 then Add(types, "sigma_1sigma_2");
        else Add(types, "UNKNOWN");
        fi;
    od;
    return types;
end;;
types := ClassifyTypes(idx);;

ComputeCommute := function(idx)
    local n, M, i, j;
    n := Length(idx.classes);
    M := NullMat(n, n);
    for i in [1..n] do
        for j in [1..n] do
            if idx.reps[i] * idx.reps[j] = idx.reps[j] * idx.reps[i] then
                M[i][j] := 1;
            fi;
        od;
    od;
    return M;
end;;
commute := ComputeCommute(idx);;

Print("Loading dense S...\n");
Read("../computed/E_plus_3/S.g");
Print("  S is ", Length(S), " x ", Length(S[1]), "\n");

GetBlock := function(S, idx, i, j)
    local off_i, off_j;
    off_i := idx.global_offset[i]; off_j := idx.global_offset[j];
    return List([1..idx.num_irreps[i]], k ->
            List([1..idx.num_irreps[j]], l ->
                S[off_i + k][off_j + l]));
end;;

# Canonical form under row + column permutations: sort rows lex, then
# transpose and sort lex, then transpose back.  Two matrices have the
# same canonical form iff one is a row/col permutation of the other.
CanonicalForm := function(M)
    local sorted_rows;
    sorted_rows := SortedList(M);
    return SortedList(TransposedMat(sorted_rows));
end;;

# Group (i, j) pairs by (type_i, type_j, commute).
groups := rec();
for i in [1..n_classes] do
    for j in [1..n_classes] do
        key := Concatenation(types[i], "/", types[j], "/", String(commute[i][j]));
        if not IsBound(groups.(key)) then groups.(key) := []; fi;
        Add(groups.(key), [i, j]);
    od;
od;

Print("\nWithin-group canonical-form check:\n");
all_perm_equiv := true;
for key in SortedList(RecNames(groups)) do
    pairs := groups.(key);
    if Length(pairs) <= 1 then
        Print("  ", key, ":  ", Length(pairs), " block(s); trivially uniform.\n");
        continue;
    fi;
    canonical_form := CanonicalForm(GetBlock(S, idx, pairs[1][1], pairs[1][2]));
    n_diff := 0;
    for p in pairs do
        if CanonicalForm(GetBlock(S, idx, p[1], p[2])) <> canonical_form then
            n_diff := n_diff + 1;
        fi;
    od;
    Print("  ", key, ":  ", Length(pairs), " blocks; ",
          n_diff, " have a different canonical form.\n");
    if n_diff > 0 then all_perm_equiv := false; fi;
od;

Print("\n=== SUMMARY ===\n");
if all_perm_equiv then
    Print("Within every group, all blocks share the same canonical form.\n");
    Print("=> all blocks in a (type, type, commute) group are row/col\n");
    Print("   permutations of each other.  Structural rep + per-class\n");
    Print("   irrep-permutations is sufficient.\n");
else
    Print("Some groups have blocks with distinct canonical forms.\n");
    Print("=> the BRW relabelling alone is NOT sufficient; some other\n");
    Print("   source of variation is present.  Investigate.\n");
fi;

QUIT;
