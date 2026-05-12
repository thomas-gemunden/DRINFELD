# Workload: time PerGeneratorTransgressionBRW(G, 1) for E_+(3).
# This is the full per-generator path the A-3a driver uses; it includes:
#   - Schreier-vector BFS over BRW conjugacy-class action,
#   - per-orbit BuildPerClassCocycleBasis,
#   - per-orbit-member H3VecAtTarget matrix composition,
#   - per-orbit-member IsCoboundary2Split.
#
# The two prior workloads (BuildPerClassCocycleBasis ~125 s,
# IsCoboundary2Split ~13 ms) account for ~126 s of orbit-2 work.
# The A-3a driver stalled for hours on orbit-2-equivalent work,
# so something OUTSIDE those two paths is the bottleneck.

ChangeDirectoryCurrent(
    "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-p5/extraspecial_orbifolds/scripts");

# Load the full chain that the A-3a driver uses.
Read("transgression_kernel.g");
Read("transgression_per_generator_brw.g");

LoadPackage("hap");

Print("\n=== workload: PerGeneratorTransgressionBRW(G, 1) on E_+(3) ===\n");
t_total := Runtime();;
G := SmallGroup(128, 2326);;
Print("Group order: ", Size(G), "\n");

t0 := Runtime();;
result := PerGeneratorTransgressionBRW(G, 1);;
wall := (Runtime() - t0) / 1000.;;
Print("PerGeneratorTransgressionBRW(G, 1) wall: ", wall, " s\n");
Print("  generator: ", result.generator, "\n");
Print("  m: ", result.m, "\n");
Print("  all_in_kernel: ", result.all_in_kernel, "\n");
Print("  per_class summary: ", Length(Filtered(result.per_class, x -> x = true)),
      " true / ", Length(Filtered(result.per_class, x -> x = false)),
      " false / ", Length(Filtered(result.per_class, x -> x = "?")),
      " unknown\n");
Print("  orbits seen: ", Length(result.orbits), "\n");
Print("workload total wall: ", (Runtime() - t_total) / 1000., " s\n");
Print("DONE\n");
QUIT;
