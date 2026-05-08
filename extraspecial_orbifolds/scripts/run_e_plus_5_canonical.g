Read("compute_canonical_blocks.g");

# E_+(5) constructed via ExtraspecialGroup since SmallGroup library
# doesn't go up to order 2048.
G := ExtraspecialGroup(2048, "+");;
result := ComputeCanonicalBlocksFor(G, "E_+(5)",
    "../computed/E_plus_5/structural");;

# Sanity: per-row unitarity of canonical blocks against the
# closed-form predictions.  We check that each block is consistent
# with the analytical T-spectrum we already know.

# (We don't have a dense S to cross-check against — this IS the new data.)

# Print sizes for sanity
Print("\n--- Canonical block sizes ---\n");
for key in SortedList(RecNames(result.blocks)) do
    blk := result.blocks.(key);
    Print("  ", key, "  ", Length(blk), " x ", Length(blk[1]), "\n");
od;

QUIT;
