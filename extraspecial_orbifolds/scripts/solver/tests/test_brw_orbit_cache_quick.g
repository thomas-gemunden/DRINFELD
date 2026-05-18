# test_brw_orbit_cache_quick.g — fast smoke check for the BRW-orbit
# cache transport. Tests m=2 (full) and m=3 (subset: 3 unit vecs × 3
# siblings per orbit).
#
# Full bit-for-bit equality is NOT expected — the H^3 matrix M_y is
# defined at the cohomology level, so the cocycle-level transport
# differs from brute force by a 2-coboundary on C(sib). We compare
# the BOOLEAN coboundary status via IsCoboundary2Split.

_SCRIPT_DIR := "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-a7p1/extraspecial_orbifolds/scripts";;
ChangeDirectoryCurrent(_SCRIPT_DIR);;

Read("brw_conjugacy_action.g");
Read("brw_h3_action.g");
Read("transgression_per_generator_brw.g");  # defines OrbitWithSchreierVec
ChangeDirectoryCurrent(_SCRIPT_DIR);;

# Test ONE orbit's first few siblings against brute force for the first
# few unit-vec H^3 generators. Returns (agreed, mismatch).
TestOneOrbitSubset := function(setup, conj_action, h3_matrices, orb_info,
                                max_siblings, max_gens)
    local rep_idx, rep, G, rep_C, k, transport_cache,
          target_idx, sib_rep, sib_C, brute_cache, agreed_count,
          mismatch_count, i, e_i, c_g_xport, c_g_brute, ok_xport, ok_brute,
          siblings_tested, gens_tested, jj;
    rep_idx := orb_info.start_idx;
    rep := conj_action.reps[rep_idx];
    G := setup.group;
    rep_C := Centralizer(G, rep);
    k := setup.num_generators;

    Print("  orbit start ", rep_idx, " (size ",
          Length(orb_info.orbit), ")... ");
    BuildPerClassCocycleBasisForOrbit(setup, conj_action, orb_info,
                                       h3_matrices);

    agreed_count := 0;
    mismatch_count := 0;
    siblings_tested := 0;
    for target_idx in orb_info.orbit do
        if target_idx = rep_idx then continue; fi;
        siblings_tested := siblings_tested + 1;
        if siblings_tested > max_siblings then break; fi;
        sib_rep := conj_action.reps[target_idx];
        sib_C := Centralizer(G, sib_rep);

        transport_cache := BuildPerClassCocycleBasis(setup, sib_rep, sib_C);

        # Force a fresh brute-force build.
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

        gens_tested := 0;
        for i in [1..k] do
            gens_tested := gens_tested + 1;
            if gens_tested > max_gens then break; fi;
            e_i := List([1..k], jj -> 0);
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
                Print("\n    MISMATCH at target_idx=", target_idx,
                      " gen i=", i, ": xport=", ok_xport,
                      " brute=", ok_brute);
            fi;
        od;
    od;
    Print(agreed_count, " agreed / ", mismatch_count, " mismatch ",
          "(", siblings_tested - If_(siblings_tested > max_siblings, 1, 0),
          " siblings × up to ", max_gens, " gens)\n");
    return rec(agreed := agreed_count, mismatch := mismatch_count);
end;;

TestForM := function(m, max_siblings, max_gens)
    local conj_action, em, brw_gens, setup, k, h3_matrices, n_classes,
          visited, orbits_data, start_idx, sv, orb, target_idx, total_agreed,
          total_mismatch, result, perm_gens, y_i, phi_i, M_y, i;
    Print("\n=== test_brw_orbit_cache_quick: m = ", m,
          " (max_siblings = ", max_siblings,
          ", max_gens = ", max_gens, ") ===\n");
    conj_action := BRWConjugacyAction(m);
    em := conj_action.em;
    brw_gens := conj_action.gens;
    setup := SetupCohomology3(em);
    k := setup.num_generators;

    h3_matrices := [];
    for i in [1..Length(brw_gens)] do
        y_i := brw_gens[i];
        phi_i := ConjugationAutomorphismThroughIso(em, conj_action.iso_em, y_i);
        M_y := H3MatrixOfAutomorphism(setup, phi_i);
        Add(h3_matrices, M_y);
    od;

    perm_gens := conj_action.perms;
    n_classes := Length(conj_action.classes);

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

    total_agreed := 0;
    total_mismatch := 0;
    for orb in orbits_data do
        result := TestOneOrbitSubset(setup, conj_action, h3_matrices, orb,
                                      max_siblings, max_gens);
        total_agreed := total_agreed + result.agreed;
        total_mismatch := total_mismatch + result.mismatch;
    od;

    Print("  m=", m, " TOTAL: ", total_agreed, " agreed, ",
          total_mismatch, " mismatch\n");
    return total_mismatch;
end;;

t_m2 := Runtime();;
m2_mismatch := TestForM(2, 100, 100);;  # m=2 is fast, test full
Print("m=2 elapsed: ", (Runtime() - t_m2) / 1000., " s\n");

t_m3 := Runtime();;
m3_mismatch := TestForM(3, 4, 5);;       # m=3: 4 siblings × 5 gens per orbit
Print("m=3 elapsed: ", (Runtime() - t_m3) / 1000., " s\n");

if m2_mismatch = 0 and m3_mismatch = 0 then
    Print("\n=== test_brw_orbit_cache_quick: PASS (m=2, m=3 subset) ===\n");
else
    Print("\n=== test_brw_orbit_cache_quick: FAIL ",
          "(m=2 mismatch=", m2_mismatch, ", m=3 mismatch=", m3_mismatch,
          ") ===\n");
fi;
QUIT;
