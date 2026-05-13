# Workload: time TWO PerGeneratorTransgressionBRW calls on E_+(3).
# With P-5's cache, the second call should skip the BRWH3Action /
# BRWConjugacyAction rebuild entirely.

ChangeDirectoryCurrent(
    "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-p5b/extraspecial_orbifolds/scripts");

Read("transgression_kernel.g");
Read("transgression_per_generator_brw.g");

LoadPackage("hap");

Print("\n=== workload: PerGeneratorTransgressionBRW x 2 on E_+(3) ===\n");
G := SmallGroup(128, 2326);;

t0 := Runtime();;
r1 := PerGeneratorTransgressionBRW(G, 1);;
wall_1 := (Runtime() - t0) / 1000.;;
Print("call 1 (i=1) wall: ", wall_1, " s\n");

t0 := Runtime();;
r2 := PerGeneratorTransgressionBRW(G, 2);;
wall_2 := (Runtime() - t0) / 1000.;;
Print("call 2 (i=2) wall: ", wall_2, " s\n");

Print("\nSpeedup ratio (cache effect): ", wall_1 / wall_2, "x\n");
Print("Per-call wall extrapolated for 35-gen driver:\n");
Print("  cold:  ", wall_1, " s\n");
Print("  warm:  ", wall_2, " s\n");
Print("  total (1 cold + 34 warm) projection: ",
      wall_1 + 34. * wall_2, " s\n");
Print("DONE\n");
QUIT;
