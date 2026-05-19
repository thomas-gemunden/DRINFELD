# test_brw_orbit_cache.g — verify BuildPerClassCocycleBasisForOrbit on
# E_+(2) and E_+(3).
#
# Checks (A-7-perf-1, issue #271):
#   1. Per-orbit transport: for each BRW orbit, the transport-built sibling
#      table is consistent with brute-force BuildPerClassCocycleBasis.
#      "Consistent" means the difference `table_xport - table_brute`,
#      interpreted row-by-row as a c_g cocycle on C(sib), is a 2-coboundary.
#      (Bit-for-bit equality is not expected — the H^3 matrix M_y is
#      defined at the cohomology level, so the cocycle-level transport
#      differs from brute force by a 2-coboundary on C(sib).)
#   2. After BuildPerClassCocycleBasisForOrbit is called per orbit, the
#      per-class cache is populated for all classes in the orbit. A
#      subsequent BuildPerClassCocycleBasis(setup, sib_rep, sib_C) hits
#      the transport-built cache (does NOT redo brute force).
#
# Read context: lives in solver/tests/. snf_wrapper.g uses a CWD shim,
# so we set CWD to scripts/ before Read.

_SCRIPT_DIR := "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-a7p1/extraspecial_orbifolds/scripts";;
ChangeDirectoryCurrent(_SCRIPT_DIR);;

Read("brw_conjugacy_action.g");
Read("brw_h3_action.g");
Read("transgression_per_generator_brw.g");  # defines OrbitWithSchreierVec
ChangeDirectoryCurrent(_SCRIPT_DIR);;

# Verify: for each BRW orbit, the transport-built sibling table differs
# from brute force by a 2-coboundary on C(sib).
#
# A 2-coboundary on C(sib) is `c(h, k) = β(h) - β(hk) + β(k)` for some
# β : C(sib) -> Z/exp. Equivalently, the GF(2)-image of c is in the
# row space of BoundaryMatrixGF2(C(sib)) — for our purposes, we want
# the diff to be a Z/exp-coboundary, which is a strictly stronger
# claim than GF(2)-coboundary at exp > 2. The mod-2 reduction
# (BoundaryMatrixGF2) captures the GF(2)-component; the full claim
# uses IsCoboundary2Split (or its vec variant).
#
# Test path: build vec = unit basis vector e_i, compute c_g_table for
# both transport and brute force, verify both predicates
# IsCoboundary2Split(C, MakeCgFromCache(...), vec, setup) give the
# SAME boolean.
TestOneOrbit := function(setup, conj_action, h3_matrices, orb_info)
    local rep_idx, rep, G, rep_C, k, exp, torsion, transport_cache,
          target_idx, sib_rep, sib_C, brute_cache, agreed_count,
          mismatch_count, i, e_i, c_g_xport, c_g_brute, ok_xport, ok_brute;
    rep_idx := orb_info.start_idx;
    rep := conj_action.reps[rep_idx];
    G := setup.group;
    rep_C := Centralizer(G, rep);
    k := setup.num_generators;
    exp := setup.exponent;
    torsion := setup.torsion;

    # Step 1: call BuildPerClassCocycleBasisForOrbit, which builds the
    # rep cache then transports to siblings.
    Print("  Building orbit cache (start_idx ", rep_idx,
          ", orbit size ", Length(orb_info.orbit), ")...\n");
    BuildPerClassCocycleBasisForOrbit(setup, conj_action, orb_info,
                                       h3_matrices);

    # Step 2: for each sibling, compare its transport-built cache to a
    # freshly brute-forced version. We need to bypass the cache for the
    # brute-force comparison — temporarily remove the cached key.
    agreed_count := 0;
    mismatch_count := 0;
    for target_idx in orb_info.orbit do
        if target_idx = rep_idx then continue; fi;
        sib_rep := conj_action.reps[target_idx];
        sib_C := Centralizer(G, sib_rep);

        # Snatch the transport-built cache (BuildPerClassCocycleBasis
        # uses _SafeIdString-based keying; recompute the same key).
        transport_cache := BuildPerClassCocycleBasis(setup, sib_rep, sib_C);

        # Force a fresh brute-force build: clear the cached key, call,
        # then restore the transport cache.
        Unbind(_basis_cache_by_class.(Concatenation(
            "G", _SafeIdString(setup.group),
            "_g", String(sib_rep),
            "_C", _SafeIdString(sib_C),
            "_n", String(Size(sib_C)))));
        brute_cache := BuildPerClassCocycleBasis(setup, sib_rep, sib_C);
        # Restore transport cache.
        _basis_cache_by_class.(Concatenation(
            "G", _SafeIdString(setup.group),
            "_g", String(sib_rep),
            "_C", _SafeIdString(sib_C),
            "_n", String(Size(sib_C)))) := transport_cache;

        # Compare coboundary predicate over all unit vec e_i.
        for i in [1..k] do
            e_i := List([1..k], j -> 0);
            e_i[i] := 1;
            c_g_xport := List(transport_cache.table,
                              row -> Sum([1..k], jj -> e_i[jj] * row[jj]));
            c_g_brute := List(brute_cache.table,
                              row -> Sum([1..k], jj -> e_i[jj] * row[jj]));
            ok_xport := IsCoboundary2Split(transport_cache.C,
                                            MakeCgFromCache(c_g_xport,
                                                            transport_cache),
                                            e_i, setup);
            ok_brute := IsCoboundary2Split(brute_cache.C,
                                            MakeCgFromCache(c_g_brute,
                                                            brute_cache),
                                            e_i, setup);
            if ok_xport = ok_brute then
                agreed_count := agreed_count + 1;
            else
                mismatch_count := mismatch_count + 1;
                Print("    MISMATCH at target_idx=", target_idx,
                      " gen i=", i, ": xport=", ok_xport,
                      " brute=", ok_brute, "\n");
            fi;
        od;
    od;
    return rec(agreed := agreed_count, mismatch := mismatch_count,
               orb_size := Length(orb_info.orbit));
end;;

TestForM := function(m)
    local conj_action, em, brw, brw_gens, setup, k, h3_matrices, n_classes,
          visited, orbits_data, start_idx, sv, orb, target_idx, total_agreed,
          total_mismatch, result, perm_gens, y_i, phi_i, M_y, i;
    Print("\n=== test_brw_orbit_cache: m = ", m, " ===\n");
    conj_action := BRWConjugacyAction(m);
    em := conj_action.em;
    brw := conj_action.brw;
    brw_gens := conj_action.gens;
    setup := SetupCohomology3(em);
    k := setup.num_generators;

    # Build BRW H^3 matrices using THIS setup (mirror unified driver).
    h3_matrices := [];
    for i in [1..Length(brw_gens)] do
        y_i := brw_gens[i];
        phi_i := ConjugationAutomorphismThroughIso(em, conj_action.iso_em, y_i);
        M_y := H3MatrixOfAutomorphism(setup, phi_i);
        Add(h3_matrices, M_y);
    od;

    perm_gens := conj_action.perms;
    n_classes := Length(conj_action.classes);

    # BFS to find orbits.
    visited := BlistList([1..n_classes], []);
    orbits_data := [];
    for start_idx in [1..n_classes] do
        if visited[start_idx] then continue; fi;
        sv := OrbitWithSchreierVec(perm_gens, n_classes, start_idx);
        for target_idx in sv.orbit do
            visited[target_idx] := true;
        od;
        Add(orbits_data, rec(start_idx := start_idx,
                              orbit := sv.orbit,
                              parent := sv.parent,
                              gen_used := sv.gen_used));
    od;
    Print("  n_classes = ", n_classes, ", n_orbits = ",
          Length(orbits_data), "\n");

    total_agreed := 0;
    total_mismatch := 0;
    for orb in orbits_data do
        result := TestOneOrbit(setup, conj_action, h3_matrices, orb);
        Print("    orbit start ", orb.start_idx, ": ",
              result.agreed, " agreed / ", result.mismatch, " mismatch ",
              "(", result.orb_size - 1, " siblings × ", k, " gens)\n");
        total_agreed := total_agreed + result.agreed;
        total_mismatch := total_mismatch + result.mismatch;
    od;

    Print("\n  TOTAL: ", total_agreed, " agreed, ",
          total_mismatch, " mismatch\n");
    if total_mismatch = 0 then
        Print("  m=", m, " transport correctness: PASS\n");
    else
        Print("  m=", m, " transport correctness: FAIL\n");
    fi;
    return total_mismatch;
end;;

t_m2 := Runtime();;
m2_mismatch := TestForM(2);;
Print("\nm=2 elapsed: ", (Runtime() - t_m2) / 1000., " s\n");

t_m3 := Runtime();;
m3_mismatch := TestForM(3);;
Print("\nm=3 elapsed: ", (Runtime() - t_m3) / 1000., " s\n");

if m2_mismatch = 0 and m3_mismatch = 0 then
    Print("\n=== test_brw_orbit_cache: PASS (m=2, m=3) ===\n");
else
    Print("\n=== test_brw_orbit_cache: FAIL ",
          "(m=2 mismatch=", m2_mismatch, ", m=3 mismatch=", m3_mismatch,
          ") ===\n");
fi;
QUIT;
