# Workload: time BuildPerClassCocycleBasis on one |C|=64 orbit-2 rep
# of E_+(3). Reused diagnostic from the A-3a optimisation effort.

ChangeDirectoryCurrent(
    "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-p1/extraspecial_orbifolds/scripts");

orig_cwd := DirectoryCurrent();;
ChangeDirectoryCurrent("solver");
Read("snf_wrapper.g");
ChangeDirectoryCurrent(Filename(orig_cwd, ""));;

LoadPackage("hap");

Print("\n=== workload: BuildPerClassCocycleBasis on E_+(3) orbit-2 ===\n");
t_total := Runtime();;
G := SmallGroup(128, 2326);;
Print("Group order: ", Size(G), "\n");

t0 := Runtime();;
setup := SetupCohomology3(G);;
Print("setup wall: ", (Runtime() - t0) / 1000., " s\n");
Print("k = ", Length(setup.UCT.cocyclebasis), " H^3 generators\n");

# Pick a non-central order-2 rep with |C|=64 (the slow orbit-2 case
# in run_e_plus_3_kernel.g).
cc := List(ConjugacyClasses(G), Representative);;
g_rep := First(cc, c -> Order(c) > 1 and Size(Centralizer(G, c)) = 64);;
if g_rep = fail then
    g_rep := First(cc, c -> Order(c) > 1);
fi;
C := Centralizer(G, g_rep);;
Print("orbit-2 rep: ", g_rep, "  (order ", Order(g_rep), ", |C| = ",
      Size(C), ")\n");

# Time the call.
t0 := Runtime();;
cache := BuildPerClassCocycleBasis(setup, g_rep, C);;
wall := (Runtime() - t0) / 1000.;;
Print("BuildPerClassCocycleBasis wall: ", wall, " s\n");
Print("cache table: ", Length(cache.table), " x ",
      Length(cache.table[1]), "\n");
Print("workload total wall: ", (Runtime() - t_total) / 1000., " s\n");
Print("DONE\n");
QUIT;
