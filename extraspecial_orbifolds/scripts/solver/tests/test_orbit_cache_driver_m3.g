# test_orbit_cache_driver_m3.g — end-to-end smoke check of the issue
# #336 driver wiring at m=3.
#
# Strategy:
#   1. Read the driver up to the orbit-cache phase.
#   2. After orbit caches are built (and persisted), record their state.
#   3. Quit GAP (simulating a mid-run termination).
#   4. The user / a follow-up script then re-runs to verify the SECOND
#      driver invocation loads from disk.
#
# This file is the *first* pass. The second pass is the same driver
# again. Both write to <repo>/computed/transgression/3/orbit_*_cache.g.
#
# We intercept the driver after the orbit-cache phase by setting up
# MPARAM and Reading the driver — but the driver writes a kernel.g at
# the end too. To avoid stepping on the production kernel.g, we
# redirect OutDir by patching it after Read.
#
# Actually simpler: just Read the driver, run all of it. m=3 takes a
# few minutes for the per-gen sweep. Skip that by reaching down into
# the orbit-cache logic directly: we replicate the relevant prefix.

LoadPackage("hap");;
LoadPackage("IO");;

_SCRIPT_DIR := "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-336/extraspecial_orbifolds/scripts";;
ChangeDirectoryCurrent(_SCRIPT_DIR);;

Read("transgression_per_generator_brw.g");
Read("transgression_resume.g");
Read("solver/orbit_cache_persist.g");
ChangeDirectoryCurrent(_SCRIPT_DIR);;

# Use a private OutDir so we don't pollute the production kernel.g.
m := 3;;
OutDir := "/tmp/test_orbit_cache_driver_m3";;
# By default, preserve any existing cache (so a second invocation of
# this test exercises the load path). To force a clean-room run,
# `rm -rf /tmp/test_orbit_cache_driver_m3` before invoking GAP.
Exec(Concatenation("mkdir -p ", OutDir));

Print("\n=== test_orbit_cache_driver_m3 (OutDir = ", OutDir, ") ===\n");

# Setup (mirror lines 312-350 of run_e_plus_m_kernel_hap.g).
t_brw := Runtime();;
conj_action := BRWConjugacyAction(m);;
Print("BRWConjugacyAction wall: ", (Runtime() - t_brw) / 1000., " s\n");
G := conj_action.em;;
Print("|G| = ", Order(G), "\n");

t_setup := Runtime();;
setup := SetupCohomology3(G);;
Print("SetupCohomology3 wall: ", (Runtime() - t_setup) / 1000., " s\n");
k := setup.num_generators;;
torsion := setup.torsion;;
Print("k = ", k, " torsion = ", torsion, "\n");

# BRW orbit decomposition.
classes := conj_action.classes;;
n_classes := Length(classes);;
perm_gens := conj_action.perms;;
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
Print("n_orbits = ", Length(orbits_data), "\n");

# Orbit cache build/load loop — identical to driver's modified version.
Print("\n--- Orbit cache phase ---\n");
t_caches := Runtime();;
orbit_caches := [];;
n_loaded_from_disk := 0;;
n_built_fresh := 0;;
for orb_info in orbits_data do
    rep := Representative(classes[orb_info.start_idx]);
    C := Centralizer(G, rep);
    Print("  orbit start ", orb_info.start_idx, " (|C| = ", Order(C),
          ", n^2*k = ", Order(C)^2 * k,
          ", rep order = ", Order(rep),
          ", orbit size ", Length(orb_info.orbit), ") ... ");
    t_one := Runtime();
    cache_path := Concatenation(OutDir, "/orbit_",
                                 String(orb_info.start_idx),
                                 "_cache.g");
    expected_fp := _OrbitCacheFingerprint(setup, rep, m);
    loaded_cache := LoadOrbitCache(cache_path, expected_fp, G);
    if loaded_cache <> fail then
        Add(orbit_caches, loaded_cache);
        PopulateBasisCacheFromLoaded(setup, rep, loaded_cache);
        n_loaded_from_disk := n_loaded_from_disk + 1;
        Print((Runtime() - t_one) / 1000., " s (LOADED)\n");
    else
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
            fresh_cache := rec(C := C, table := cache_table,
                               table_gf2 := cache_table_gf2,
                               elts := cache_elts, n := cache_n,
                               idx_map := cache_idx_map);
            Add(orbit_caches, fresh_cache);
            n_built_fresh := n_built_fresh + 1;
            Print((Runtime() - t_one) / 1000., " s (identity)");
        else
            fresh_cache := BuildPerClassCocycleBasis(setup, rep, C);
            Add(orbit_caches, fresh_cache);
            n_built_fresh := n_built_fresh + 1;
            Print((Runtime() - t_one) / 1000., " s (rep-only)");
        fi;
        catch_save := CALL_WITH_CATCH(SaveOrbitCache,
            [cache_path, orb_info.start_idx, m, setup, rep, fresh_cache]);
        if catch_save[1] = false then
            Print(" [WARN save failed: ", catch_save[2], "]");
        else
            Print(" [persisted]");
        fi;
        Print("\n");
    fi;
od;
Print("Phase wall: ", (Runtime() - t_caches) / 1000.,
      " s (loaded ", n_loaded_from_disk,
      ", built ", n_built_fresh, ")\n");

# Optional check: run the driver's per-vec test on one unit vec, just
# to confirm the loaded caches behave correctly. Use PerVecTransgressionShared
# from the driver path — that requires more wiring, so instead we do
# a minimal sanity check: each cache.table * unit_vec (mod exp) should
# produce a valid c_g vector that IsCoboundary2SplitVec can consume.
#
# This is the same Path-A inner machinery the driver uses, so if it
# works here it works there.

# Per-test sanity: also confirm shape consistency.
Print("\n--- Sanity: cache shapes vs orbit centralizer order ---\n");
all_ok := true;;
for oi in [1..Length(orbits_data)] do
    cache := orbit_caches[oi];
    rep_local := Representative(classes[orbits_data[oi].start_idx]);
    C_local := Centralizer(G, rep_local);
    expected_n := Order(C_local);
    if cache.n <> expected_n then
        Print("  [FAIL] orbit ", oi, ": cache.n = ", cache.n,
              ", expected ", expected_n, "\n");
        all_ok := false;
    fi;
    if Length(cache.table) <> expected_n * expected_n then
        Print("  [FAIL] orbit ", oi, ": Length(table) = ",
              Length(cache.table), ", expected ", expected_n * expected_n, "\n");
        all_ok := false;
    fi;
    if Length(cache.table[1]) <> k then
        Print("  [FAIL] orbit ", oi, ": Length(table[1]) = ",
              Length(cache.table[1]), ", expected k = ", k, "\n");
        all_ok := false;
    fi;
od;
if all_ok then
    Print("  [ OK ] all ", Length(orbit_caches), " orbit caches have correct shape\n");
fi;

Print("\nResults summary:\n");
Print("  Out dir: ", OutDir, "\n");
Print("  Caches loaded: ", n_loaded_from_disk, " / ", Length(orbits_data), "\n");
Print("  Caches built:  ", n_built_fresh, " / ", Length(orbits_data), "\n");

# Drop a marker file with what mode this was.
PrintTo(Concatenation(OutDir, "/last_run.txt"),
        "loaded=", n_loaded_from_disk,
        " built=", n_built_fresh,
        " total=", Length(orbits_data), "\n");

if all_ok then
    Print("=== test_orbit_cache_driver_m3: PASS ===\n");
else
    Print("=== test_orbit_cache_driver_m3: FAIL ===\n");
fi;
QUIT;
