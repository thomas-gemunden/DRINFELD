# E_BRW step 2 (refined): compute the 22 canonical S-blocks for any m,
# storing them as a structural rep.  For m=3, cross-validate against
# the dense S already on disk.  For m=5, this is new data.

Read("untwisted_modular_data.g");

If_ := function(cond, a, b) if cond then return a; else return b; fi; end;;

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

# Identify the canonical (i_g, j_g) pair per refined group: the FIRST
# (i, j) in lex order satisfying the group conditions.
PickCanonicalPairs := function(idx, types, commute)
    local n, canonical_pair, i, j, key;
    n := Length(idx.classes);
    canonical_pair := rec();
    for i in [1..n] do
        for j in [1..n] do
            key := GroupKey(types, commute, i, j);
            if not IsBound(canonical_pair.(key)) then
                canonical_pair.(key) := [i, j];
            fi;
        od;
    od;
    return canonical_pair;
end;;

# Compute the canonical block per refined group.
ComputeAllCanonicalBlocks := function(idx, transport, canonical_pairs)
    local blocks, key, pair, tic, toc;
    blocks := rec();
    for key in RecNames(canonical_pairs) do
        pair := canonical_pairs.(key);
        tic := Runtime();
        blocks.(key) := ComputeSBlock(idx, transport, pair[1], pair[2]);
        toc := Runtime() - tic;
        Print("  ", key, "  (i, j) = ", pair, "  time ", toc / 1000., " s, ",
              "block ", Length(blocks.(key)), " x ",
              Length(blocks.(key)[1]), "\n");
    od;
    return blocks;
end;;

# ---------------------------------------------------------------
# Driver
# ---------------------------------------------------------------

ComputeCanonicalBlocksFor := function(G, label, outdir)
    local idx, types, commute, canonical_pairs, transport, blocks,
          tic, toc, tic2, toc2, key, pair;
    Print("\n############ ", label, " ############\n");
    Print("Group order: ", Order(G), "\n");

    Print("Building simple-object index...\n");
    tic := Runtime();
    idx := BuildSimpleIndex(G);
    toc := Runtime() - tic;
    Print("  done in ", toc / 1000., " s, rank = ", idx.rank, ", #classes = ",
          Length(idx.classes), "\n");

    types := ClassifyTypes(idx);
    Print("  class types: ", Collected(types), "\n");

    Print("Computing commute matrix...\n");
    tic := Runtime();
    commute := ComputeCommute(idx);
    Print("  done in ", (Runtime() - tic) / 1000., " s\n");

    canonical_pairs := PickCanonicalPairs(idx, types, commute);
    Print("\n#canonical pairs = #refined groups = ", Length(RecNames(canonical_pairs)), "\n");

    Print("\nBuilding transport (RepresentativeAction over G) for canonical classes...\n");
    tic := Runtime();
    transport := BuildTransports(idx);
    Print("  done in ", (Runtime() - tic) / 1000., " s\n");

    Print("\nComputing 22 canonical S-blocks via ComputeSBlock:\n");
    tic := Runtime();
    blocks := ComputeAllCanonicalBlocks(idx, transport, canonical_pairs);
    toc := Runtime() - tic;
    Print("  total: ", toc / 1000., " s\n");

    # Persist
    Exec(Concatenation("mkdir -p ", outdir));
    PrintTo(Concatenation(outdir, "/canonical_pairs.g"),
        "# Canonical pair per refined group for ", label, "\n",
        "canonical_pairs := ", canonical_pairs, ";;\n");
    PrintTo(Concatenation(outdir, "/canonical_blocks.g"),
        "# 22 canonical S-blocks for ", label, "\n",
        "canonical_blocks := ", blocks, ";;\n");
    Print("\nWrote canonical_pairs.g and canonical_blocks.g to ", outdir, "\n");

    return rec(idx := idx, types := types, commute := commute,
               canonical_pairs := canonical_pairs, blocks := blocks);
end;;
