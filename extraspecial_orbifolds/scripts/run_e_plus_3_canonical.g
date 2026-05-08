Read("compute_canonical_blocks.g");

# E_+(3) = SmallGroup(128, 2326)
G := SmallGroup(128, 2326);;
result := ComputeCanonicalBlocksFor(G, "E_+(3)",
    "../computed/E_plus_3/structural");;

# Cross-check: extract canonical blocks from dense S; verify equality.
Print("\n--- Cross-check against dense S ---\n");
Read("../computed/E_plus_3/S.g");
all_match := true;
for key in RecNames(result.canonical_pairs) do
    pair := result.canonical_pairs.(key);
    i := pair[1]; j := pair[2];
    off_i := result.idx.global_offset[i]; off_j := result.idx.global_offset[j];
    Ni := result.idx.num_irreps[i]; Nj := result.idx.num_irreps[j];
    dense_block := List([1..Ni], k -> List([1..Nj],
        l -> S[off_i + k][off_j + l]));
    if dense_block = result.blocks.(key) then
        Print("  ", key, ": MATCH\n");
    else
        Print("  ", key, ": MISMATCH\n");
        all_match := false;
    fi;
od;

Print("\n=== Cross-check overall: ", all_match, " ===\n");

QUIT;
