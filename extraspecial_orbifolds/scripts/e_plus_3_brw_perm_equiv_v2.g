# E_BRW m=3 step 3.
#
# Refine the grouping with a "diagonal vs off-diagonal" sub-flag
# (i = j as class indices, vs i != j).  Hypothesis: with this
# refinement, all blocks within each refined group share the same
# canonical form.

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
        else Add(types, "UNKNOWN"); fi;
    od;
    return types;
end;;
types := ClassifyTypes(idx);;

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
commute := ComputeCommute(idx);;

Print("Loading dense S...\n");
Read("../computed/E_plus_3/S.g");

GetBlock := function(S, idx, i, j)
    local off_i, off_j;
    off_i := idx.global_offset[i]; off_j := idx.global_offset[j];
    return List([1..idx.num_irreps[i]], k ->
        List([1..idx.num_irreps[j]], l -> S[off_i + k][off_j + l]));
end;;

CanonicalForm := function(M)
    return SortedList(TransposedMat(SortedList(M)));
end;;

If_ := function(cond, a, b) if cond then return a; else return b; fi; end;;

# Refined grouping: (type_i, type_j, commute, i=j?, central pair?)
# "diag" = (i = j) for non-central, irrelevant for central
groups := rec();
for i in [1..n_classes] do
    for j in [1..n_classes] do
        diagFlag := If_(i = j, "diag", "off");
        key := Concatenation(types[i], "/", types[j], "/",
                              String(commute[i][j]), "/", diagFlag);
        if not IsBound(groups.(key)) then groups.(key) := []; fi;
        Add(groups.(key), [i, j]);
    od;
od;

Print("\nRefined within-group canonical-form check:\n");
all_uniform := true;
n_distinct_blocks_total := 0;
for key in SortedList(RecNames(groups)) do
    pairs := groups.(key);
    if Length(pairs) <= 1 then
        Print("  ", key, ":  ", Length(pairs), " block(s); trivially uniform.\n");
        n_distinct_blocks_total := n_distinct_blocks_total + Length(pairs);
        continue;
    fi;
    # Count distinct canonical forms within this group.
    cforms := [];
    for p in pairs do
        Add(cforms, CanonicalForm(GetBlock(S, idx, p[1], p[2])));
    od;
    n_distinct := Length(Set(cforms));
    Print("  ", key, ":  ", Length(pairs), " blocks; ",
          n_distinct, " distinct canonical form(s).\n");
    if n_distinct > 1 then all_uniform := false; fi;
    n_distinct_blocks_total := n_distinct_blocks_total + n_distinct;
od;

Print("\n=== SUMMARY ===\n");
Print("Number of distinct canonical S-blocks across all groups: ",
      n_distinct_blocks_total, "\n");
if all_uniform then
    Print("With (type_i, type_j, commute, diag/off) refinement, every\n");
    Print("group has a uniform canonical form.  Structural rep with\n");
    Print("per-class irrep-relabellings is sufficient.\n");
else
    Print("Even with diag/off refinement, some groups have multiple\n");
    Print("canonical forms.  Need finer-grained classification.\n");
fi;

QUIT;
