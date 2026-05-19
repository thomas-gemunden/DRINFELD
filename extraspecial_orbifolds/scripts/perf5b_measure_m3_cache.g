# perf5b_measure_m3_cache.g
# ---------------------------
# Standalone measurement of the per-orbit cache wall at m=3, using the
# same code path as run_e_plus_m_kernel_hap.g but skipping the per-
# generator sweep + half-vec + Step 4 cross-checks.
#
# Reproduces Step 0 + cache-build only. Wall time prints to stdout as:
#   Per-orbit caches wall: <X> s total
#
# Baseline (post-Route-A, db8fe47): 35.3 s. Target: faster.

Read("transgression_per_generator_brw.g");

t_start := Runtime();;

Print("\n=== perf5b_measure_m3_cache: m=3 per-orbit caches only ===\n");

m := 3;;
Print("Building BRW conjugacy action for m = ", m, "...\n");
t_brw := Runtime();;
conj_action := BRWConjugacyAction(m);;
Print("BRWConjugacyAction wall: ", (Runtime() - t_brw) / 1000., " s\n");

G := conj_action.em;;
Print("|G| = ", Order(G), "\n");
Print("Building setup := SetupCohomology3(G)...\n");
t_setup := Runtime();;
setup := SetupCohomology3(G);;
Print("SetupCohomology3 wall: ", (Runtime() - t_setup) / 1000., " s\n");

Print("Building BRW H^3 action matrices...\n");
t_h3 := Runtime();;
brw_m := BRW(m);;
brw_gens_m := GeneratorsOfGroup(brw_m);;
h3_matrices_consistent := [];;
for i in [1..Length(brw_gens_m)] do
    y_i := brw_gens_m[i];
    phi_i := ConjugationAutomorphismThroughIso(G, conj_action.iso_em, y_i);
    M_y := H3MatrixOfAutomorphism(setup, phi_i);
    Add(h3_matrices_consistent, M_y);
od;
Print("BRW H^3 matrices wall: ", (Runtime() - t_h3) / 1000., " s\n");

torsion := setup.torsion;;
exp := setup.exponent;;
k := setup.num_generators;;
Print("torsion = ", torsion, ", exp = ", exp, ", k = ", k, "\n");

perm_gens := conj_action.perms;;
classes := conj_action.classes;;
n_classes := Length(classes);;
Print("n_classes = ", n_classes, "\n");

Print("Identifying BRW orbits...\n");
visited_all := BlistList([1..n_classes], []);;
orbits_data := [];;
for start_idx in [1..n_classes] do
    if visited_all[start_idx] then continue; fi;
    sv := OrbitWithSchreierVec(perm_gens, n_classes, start_idx);
    for target_idx in sv.orbit do
        visited_all[target_idx] := true;
    od;
    Add(orbits_data, rec(start_idx := start_idx,
                          orbit := sv.orbit,
                          parent := sv.parent,
                          gen_used := sv.gen_used));
od;
Print("Found ", Length(orbits_data), " BRW orbits.\n");
for orb_info in orbits_data do
    Print("  orbit at class ", orb_info.start_idx, ": ",
          Length(orb_info.orbit),
          " members, |C_G(rep)| = ",
          Order(Centralizer(G, Representative(classes[orb_info.start_idx]))),
          ", rep order = ",
          Order(Representative(classes[orb_info.start_idx])), "\n");
od;

# Per-orbit cache build wall (the headline measurement).
Print("\nBuilding per-orbit cocycle-basis caches...\n");
t_caches := Runtime();;
orbit_caches := [];;
for orb_info in orbits_data do
    rep := Representative(classes[orb_info.start_idx]);
    C := Centralizer(G, rep);
    Print("  orbit start ", orb_info.start_idx, " (|C| = ", Order(C),
          ", orbit size ", Length(orb_info.orbit), ") ... ");
    t_one := Runtime();
    if IsOne(rep) then
        cache_elts := AsList(C);
        cache_n := Length(cache_elts);
        cache_table := List([1..cache_n * cache_n],
                            r -> List([1..k], i -> 0));
        ConvertToMatrixRep(cache_table);
        cache_idx_map := NewDictionary(cache_elts[1], true, cache_elts);
        for cache_a in [1..cache_n] do
            AddDictionary(cache_idx_map, cache_elts[cache_a], cache_a);
        od;
        cache_table_gf2 := List([1..cache_n * cache_n],
                                 r -> List([1..k], i -> Zero(GF(2))));
        ConvertToMatrixRep(cache_table_gf2, GF(2));
        Add(orbit_caches, rec(C := C, table := cache_table,
                               table_gf2 := cache_table_gf2,
                               elts := cache_elts, n := cache_n,
                               idx_map := cache_idx_map));
        Print((Runtime() - t_one) / 1000., " s (degenerate identity)\n");
    else
        Add(orbit_caches,
            BuildPerClassCocycleBasisForOrbit(setup, conj_action, orb_info,
                                               h3_matrices_consistent));
        Print((Runtime() - t_one) / 1000., " s (",
              Length(orb_info.orbit), " classes via transport)\n");
    fi;
od;
Print("\nPer-orbit caches wall: ", (Runtime() - t_caches) / 1000., " s total\n");
Print("Total wall (including BRW+setup): ", (Runtime() - t_start) / 1000., " s\n");
QUIT;
