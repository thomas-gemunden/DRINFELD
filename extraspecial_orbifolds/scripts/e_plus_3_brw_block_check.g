# E_BRW m=3, step 1.
#
# Empirically check whether the per-(i,j)-class blocks of the dense
# S for E_+(3) are literally equal within each (type_i, type_j,
# commute-flag) group, using GAP's natural Irr-ordering on each
# centraliser.
#
# If yes: ~10 distinct blocks suffice and the structural rep works
#         straight out of the box for E_+(3).
# If no:  we need to track the BRW relabelling between centralisers
#         of conjugate classes; this is a permutation of Irr.

Read("untwisted_modular_data.g");

# ----------------------------------------------------------------------
# Build the index for E_+(3) and classify classes by BRW type.
# ----------------------------------------------------------------------

G := SmallGroup(128, 2326);;
idx := BuildSimpleIndex(G);;
n_classes := Length(idx.classes);;
Print("Number of conjugacy classes: ", n_classes, "\n");

# Classify each class by BRW type:
#   "id"            for the identity class
#   "minus_one"     for the central order-2 class (the {-1} singleton)
#   "sigma2"        for non-central order-2 classes
#   "sigma_1sigma_2" for non-central order-4 classes
ClassifyTypes := function(idx)
    local types, i, rep, ord, sz;
    types := [];
    for i in [1..Length(idx.classes)] do
        rep := idx.reps[i];
        ord := Order(rep);
        sz := idx.class_sizes[i];
        if sz = 1 and ord = 1 then
            Add(types, "id");
        elif sz = 1 and ord = 2 then
            Add(types, "minus_one");
        elif ord = 2 then
            Add(types, "sigma2");
        elif ord = 4 then
            Add(types, "sigma_1sigma_2");
        else
            Add(types, "UNKNOWN");
        fi;
    od;
    return types;
end;;

types := ClassifyTypes(idx);;
type_counts := Collected(types);;
Print("\nClass type counts: ", type_counts, "\n");

# ----------------------------------------------------------------------
# Commute matrix of class representatives.
# ----------------------------------------------------------------------

ComputeCommute := function(idx)
    local n, M, i, j, ai, aj;
    n := Length(idx.classes);
    M := NullMat(n, n);
    for i in [1..n] do
        for j in [1..n] do
            ai := idx.reps[i];
            aj := idx.reps[j];
            if ai * aj = aj * ai then M[i][j] := 1; fi;
        od;
    od;
    return M;
end;;

Print("\nComputing commute matrix...\n");
tic := Runtime();;
commute := ComputeCommute(idx);;
toc := Runtime() - tic;;
Print("  done in ", toc/1000., " s\n");

# ----------------------------------------------------------------------
# Load the precomputed dense S.
# ----------------------------------------------------------------------

Print("\nLoading dense S from computed/E_plus_3/S.g ...\n");
tic := Runtime();;
Read("../computed/E_plus_3/S.g");
toc := Runtime() - tic;;
Print("  done in ", toc/1000., " s.  S has shape ",
      Length(S), " x ", Length(S[1]), "\n");

# ----------------------------------------------------------------------
# Slice S into per-(i, j)-class blocks.
# ----------------------------------------------------------------------

GetBlock := function(S, idx, i, j)
    local off_i, off_j, N_i, N_j, k, l, B;
    off_i := idx.global_offset[i];
    off_j := idx.global_offset[j];
    N_i := idx.num_irreps[i];
    N_j := idx.num_irreps[j];
    return List([1..N_i], k -> List([1..N_j],
        l -> S[off_i + k][off_j + l]));
end;;

# ----------------------------------------------------------------------
# Group (i, j) pairs by (type_i, type_j, commute-flag).
# Within each group, check whether all blocks are equal.
# ----------------------------------------------------------------------

Print("\nGrouping (i, j) pairs by (type_i, type_j, commute-flag) and "
      , "checking block equality...\n");

groups := rec();
for i in [1..n_classes] do
    for j in [1..n_classes] do
        key := Concatenation(types[i], "/", types[j], "/",
                              String(commute[i][j]));
        if not IsBound(groups.(key)) then
            groups.(key) := [];
        fi;
        Add(groups.(key), [i, j]);
    od;
od;

# Report group sizes
Print("\nGroups (sorted by name):\n");
group_keys := SortedList(RecNames(groups));
for key in group_keys do
    Print("  ", key, ":  ", Length(groups.(key)), " (i,j) pairs\n");
od;

# For each group, take the first (i,j) as canonical and compare ALL
# others to it.
Print("\nWithin-group block-equality check:\n");
all_uniform := true;
for key in group_keys do
    pairs := groups.(key);
    if Length(pairs) <= 1 then
        Print("  ", key, ":  only ", Length(pairs), " block; trivially uniform.\n");
        continue;
    fi;
    canonical := GetBlock(S, idx, pairs[1][1], pairs[1][2]);
    n_diff := 0;
    for p in pairs do
        b := GetBlock(S, idx, p[1], p[2]);
        if b <> canonical then n_diff := n_diff + 1; fi;
    od;
    Print("  ", key, ":  ", Length(pairs), " blocks; ",
          n_diff, " differ from canonical (out of ", Length(pairs) - 1,
          " comparisons).\n");
    if n_diff > 0 then all_uniform := false; fi;
od;

Print("\n=== SUMMARY ===\n");
if all_uniform then
    Print("All groups have uniform blocks!  Structural rep works directly.\n");
else
    Print("Some groups have non-uniform blocks.  Relabelling logic needed.\n");
fi;

QUIT;
