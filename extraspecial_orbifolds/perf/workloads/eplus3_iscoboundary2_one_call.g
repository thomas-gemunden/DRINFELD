# Workload: time a single IsCoboundary2Split call on a |C|=64
# centraliser of E_+(3), with the c_g built from a non-trivial
# H^3 generator. This is the per-orbit-member work in
# transgression_per_generator_brw.g (line 302); the driver does this
# 35 times per orbit-2 cache build.
#
# Hypothesis: this is the actual A-3a bottleneck, not the cache build.

ChangeDirectoryCurrent(
    "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-p1/extraspecial_orbifolds/scripts");

orig_cwd := DirectoryCurrent();;
ChangeDirectoryCurrent("solver");
Read("snf_wrapper.g");
ChangeDirectoryCurrent(Filename(orig_cwd, ""));;

LoadPackage("hap");

Print("\n=== workload: IsCoboundary2Split one call on E_+(3) |C|=64 ===\n");
t_total := Runtime();;
G := SmallGroup(128, 2326);;

t0 := Runtime();;
setup := SetupCohomology3(G);;
Print("setup wall: ", (Runtime() - t0) / 1000., " s\n");
k := Length(setup.UCT.cocyclebasis);;
Print("k = ", k, "\n");

# Pick a non-central order-2 rep with |C|=64.
cc := List(ConjugacyClasses(G), Representative);;
g_rep := First(cc, c -> Order(c) > 1 and Size(Centralizer(G, c)) = 64);;
C := Centralizer(G, g_rep);;
Print("rep: ", g_rep, " (|C| = ", Size(C), ")\n");

# Build the cache once.
t0 := Runtime();;
cache := BuildPerClassCocycleBasis(setup, g_rep, C);;
Print("cache build wall: ", (Runtime() - t0) / 1000., " s\n");

# Build a c_g for H^3 generator 1 (a non-trivial unit vector).
vec_target := List([1..k], i -> 0);;
vec_target[1] := 1;;
c_g_table := List(cache.table,
                  row -> Sum([1..k], i -> vec_target[i] * row[i]));;
c_g_func := MakeCgFromCache(c_g_table, cache);;

# Time a single IsCoboundary2Split call.
Print("\nTiming one IsCoboundary2Split call ...\n");
t0 := Runtime();;
result := IsCoboundary2Split(C, c_g_func, vec_target, setup);;
wall := (Runtime() - t0) / 1000.;;
Print("IsCoboundary2Split wall: ", wall, " s   (result = ", result, ")\n");
Print("Projection: 35 calls per orbit = ", 35. * wall / 60., " min wall.\n");
Print("workload total wall: ", (Runtime() - t_total) / 1000., " s\n");
Print("DONE\n");
QUIT;
