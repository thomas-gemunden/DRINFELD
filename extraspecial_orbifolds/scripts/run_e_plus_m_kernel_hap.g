# run_e_plus_m_kernel_hap.g — unified A-7a driver: ker(Tr) for E_+(m)
# via the HAP (LHS) route at m=7.
#
# Implements the re-scoped version of issue #50. Takes `m` as a global
# parameter (set MPARAM := <integer> before reading this file) and
# produces ker Tr(E_+(m)) by the same Tier-4 pipeline as A-5b's
# run_e_plus_5_kernel.g, but with one critical adaptation:
#
#   * For m in {2, 3, 5}: the standard SetupCohomology3(em) chain works
#     (em := pc-form of EmGroup(m), order <= 2048). The driver follows
#     the A-5b model verbatim.
#
#   * For m = 7: ResolutionFiniteGroup(em, 4) OOMs at ~60 GB (PR #137
#     blocker). Instead we use LHSResolutionEPlus(7, 5) from
#     hap_lhs_resolution.g, which builds R_E in ~822 s with 448 MB heap
#     peak (PR #252). The driver pre-populates BRWH3Action(7)'s module-
#     level cache with a manually-constructed setup record built from
#     this LHS resolution.
#
# Usage:
#
#   gap -q -b -o 16g -c 'MPARAM := 2; Read("run_e_plus_m_kernel_hap.g");'
#   gap -q -b -o 16g -c 'MPARAM := 3; Read("run_e_plus_m_kernel_hap.g");'
#   gap -q -b -o 16g -c 'MPARAM := 7; Read("run_e_plus_m_kernel_hap.g");'
#
# All from extraspecial_orbifolds/scripts/.
#
# Probe-only mode (m=7): set PROBE_GEN := <integer in [1..k]> before Read
# to compute just one generator and exit. Used for the smoke probe in
# A-7a acceptance step 3.
#
# Acceptance anchors:
#   * m=2: |ker Tr(E_+(2))| = 2048 (A-2, #41)
#   * m=3: |ker Tr(E_+(3))| = 2^36 = 68719476736 (A-3a, #42)
#   * m=7: gen 1 probe completes with recorded wall + RSS.
#
# Resumability: per-generator state appended to sweep_state.g; kill-and-
# restart picks up where left off, mirroring A-5b's pattern.

# ----------------------------------------------------------------------
# Parameter parsing.
# ----------------------------------------------------------------------

if not IsBoundGlobal("MPARAM") then
    Error("run_e_plus_m_kernel_hap.g: set MPARAM := <integer> before Read");
fi;
m := MPARAM;;
Assert(0, m in [2, 3, 5, 7],
       Concatenation("MPARAM must be in [2, 3, 5, 7]; got ", String(m)));

if IsBoundGlobal("PROBE_GEN") then
    probe_gen := PROBE_GEN;
    Print("PROBE_GEN = ", probe_gen,
          " (probe-only mode: compute one generator and exit)\n");
else
    probe_gen := fail;
fi;

# ----------------------------------------------------------------------
# Setup: load common per-generator BRW path + resumable wrapper. The
# m=7 driver additionally needs hap_lhs_resolution.g.
# ----------------------------------------------------------------------

driver_orig_cwd := DirectoryCurrent();;

# transgression_per_generator_brw.g pulls in transgression_kernel.g (UCT
# setup) and snf_wrapper.g (cocycle-basis cache + dispatcher). Both rely
# on CWD = scripts/ at Read-time.
Read("transgression_per_generator_brw.g");
# transgression_resume.g defines PersistGenerator / LoadResumeState /
# TransgressionKernelResumable. Lives in scripts/.
Read("transgression_resume.g");

if m = 7 then
    if not IsBoundGlobal("LHSResolutionEPlus") then
        Read("hap_lhs_resolution.g");
    fi;
fi;

# Restore CWD (Read() above may have chdir'd inside its shim chain).
ChangeDirectoryCurrent(Filename(driver_orig_cwd, ""));;

t_start := Runtime();;

Print("\n=== A-7a driver: ker(Tr) for E_+(", m, ") ===\n");

# ----------------------------------------------------------------------
# Step 0a (m=7 only): build LHS resolution and pre-populate the
# BRWH3Action / BRWConjugacyAction caches.
#
# Strategy:
#   1. Build BRWConjugacyAction(7) — gives us em (pc-form of EmGroup(7)),
#      iso_em, classes, perm action on classes. No resolution needed for
#      this step.
#   2. Build LHS resolution R_E on `em` (same pc-form), via
#      _LHSResolutionForGroup(em, 7, 5). This avoids slow
#      IsomorphismGroups(em, ExtraspecialGroup(2^15, "+")) at m=7
#      (>>15 min in a probe).
#   3. Manually build setup := SetupCohomology3-equivalent record from R_E.
#   4. Manually compute H^3 matrices for each BRW generator y by building
#      the conjugation hom phi : em -> em through iso_em, then calling
#      H3MatrixOfAutomorphism(setup, phi).
#   5. Pre-populate _brw_h3_action_cache.("m7") with the resulting record
#      so subsequent BRWH3Action(7) calls return it.
# ----------------------------------------------------------------------

# Helper: build an LHS resolution on an arbitrary group G of order
# 2^{2m+1} satisfying the central-last-gen convention (same as
# LHSResolutionEPlusDetailed, but parameterised by G rather than
# hardcoded to ExtraspecialGroup). Returns rec(R_E, R_V, build_time_V,
# build_time_LHS, heap_after_V_mb, heap_after_LHS_mb).
_LHSResolutionForGroup := function(G, m_local, max_n)
    local gens, GensE, Zc, nat, V, GensV, t0, R_V, R_E,
          build_V, build_LHS, heap_after_V, heap_after_LHS;
    gens := GeneratorsOfGroup(G);
    if Length(gens) <> 2*m_local + 1 then
        Error("_LHSResolutionForGroup: expected ", 2*m_local + 1,
              " generators; got ", Length(gens));
    fi;
    GensE := gens{[1..2*m_local]};
    Zc := Centre(G);
    if not gens[2*m_local + 1] in Zc then
        Error("_LHSResolutionForGroup: gens[", 2*m_local + 1,
              "] is not central");
    fi;
    if Order(Zc) <> 2 then
        Error("_LHSResolutionForGroup: |Z(G)| = ", Order(Zc),
              ", expected 2");
    fi;
    nat := NaturalHomomorphismByNormalSubgroup(G, Zc);
    V := Image(nat);
    GensV := List(GensE, g -> Image(nat, g));
    if not IsElementaryAbelian(V) or Order(V) <> 2^(2*m_local) then
        Error("_LHSResolutionForGroup: V not (F_2)^{",
              2*m_local, "}: got ", StructureDescription(V));
    fi;
    Print("[LHS] |E| = ", Order(G), ", |V| = ", Order(V),
          ", |Z| = ", Order(Zc), "\n");
    Print("[LHS] building R_V := ResolutionAbelianGroup(V, ",
          max_n, ")...\n");
    t0 := Runtime();
    R_V := ResolutionAbelianGroup(V, max_n);
    build_V := (Runtime() - t0) / 1000.;
    heap_after_V := -1.0;
    Print("[LHS]   R_V built in ", build_V, " s\n");
    Print("[LHS]   R_V!.dimension(0..", max_n, ") = ",
          List([0..max_n], d -> R_V!.dimension(d)), "\n");

    Print("[LHS] building R_E via ",
          "ResolutionFiniteExtension(GensE, GensV, R_V, ", max_n, ")...\n");
    t0 := Runtime();
    R_E := ResolutionFiniteExtension(GensE, GensV, R_V, max_n);
    build_LHS := (Runtime() - t0) / 1000.;
    heap_after_LHS := -1.0;
    Print("[LHS]   R_E built in ", build_LHS, " s\n");
    Print("[LHS]   R_E!.dimension(0..", max_n, ") = ",
          List([0..max_n], d -> R_E!.dimension(d)), "\n");

    return rec(
        R_V := R_V,
        R_E := R_E,
        build_time_V := build_V,
        build_time_LHS := build_LHS,
        heap_after_V_mb := heap_after_V,
        heap_after_LHS_mb := heap_after_LHS
    );
end;;

# Helper (m=7): manually build a setup record from a pre-built R_E.
# Same shape as SetupCohomology3 but uses the supplied resolution
# instead of ResolutionFiniteGroup(G, 4).
_BuildSetupFromResolution := function(em, R_E)
    local K, UCT;
    K := TensorWithIntegers(R_E);
    UCT := UniversalCoefficientsTheorem(K, 3);
    return rec(group := em, R := R_E, K := K, UCT := UCT,
               exponent := UCT.exponent,
               num_generators := Length(UCT.hombasis),
               torsion := UCT.torsion,
               num_h3_classes := Product(UCT.torsion));
end;;

if m = 7 then
    Print("\n--- Step 0a (m=7): build LHS resolution + setup ---\n");
    Print("\n");
    Print("WARNING: at m=7, BRWConjugacyAction(7) is estimated 6-8h wall\n");
    Print("         (16386 classes x 28 BRW outer gens x O(n) ClassIndexOf).\n");
    Print("         For an m=7 smoke probe demonstrating just LHS+UCT setup,\n");
    Print("         use run_e_plus_7_kernel_probe.g instead.\n");
    Print("\n");
    t_lhs_setup := Runtime();;

    # Step 1: build conjugacy action first (it doesn't need a resolution).
    # This gives us em = pc-form of EmGroup(7).
    Print("Building BRWConjugacyAction(7) (no resolution needed)...\n");
    t_conj := Runtime();;
    conj_action_m7 := BRWConjugacyAction(7);;
    Print("BRWConjugacyAction(7) wall: ", (Runtime() - t_conj) / 1000., " s\n");
    em_m7 := conj_action_m7.em;;
    iso_em_m7 := conj_action_m7.iso_em;;
    Print("|em| = ", Order(em_m7), " (pc-form of EmGroup(7))\n");

    # Step 2: build LHS resolution on em.
    Print("Building LHS resolution R_E on em (m=7, max_n=5)...\n");
    lhs_data := _LHSResolutionForGroup(em_m7, 7, 5);;
    R_E_m7 := lhs_data.R_E;;
    Print("LHS wall: V = ", lhs_data.build_time_V, " s, R_E = ",
          lhs_data.build_time_LHS, " s\n");

    # Step 3: manually build setup record.
    Print("Building setup record from R_E...\n");
    t_uct := Runtime();;
    setup_m7 := _BuildSetupFromResolution(em_m7, R_E_m7);;
    Print("UCT wall: ", (Runtime() - t_uct) / 1000., " s\n");
    Print("setup.torsion = ", setup_m7.torsion, "\n");
    Print("setup.exponent = ", setup_m7.exponent, "\n");
    Print("setup.num_generators (k) = ", setup_m7.num_generators, "\n");

    # Sanity: at m=7, H^3 = (Z/2)^90 per the m=7 LHS outcome on disk.
    Assert(0, setup_m7.num_generators = 90,
           Concatenation("expected k = 90 for E_+(7); got ",
                         String(setup_m7.num_generators)));
    Assert(0, ForAll(setup_m7.torsion, t -> t = 2),
           Concatenation("expected all torsion = 2 at m=7; got ",
                         String(setup_m7.torsion)));

    # Step 4: compute H^3 action matrices for each BRW generator.
    Print("Computing BRW H^3 action matrices (15 generators)...\n");
    t_h3mat := Runtime();;
    brw_m7 := BRW(7);;
    brw_gens_m7 := GeneratorsOfGroup(brw_m7);;
    matrices_m7 := [];;
    valid_endos_m7 := [];;
    for i in [1..Length(brw_gens_m7)] do
        t_one := Runtime();
        y_i := brw_gens_m7[i];
        phi_i := ConjugationAutomorphismThroughIso(em_m7, iso_em_m7, y_i);
        M_y := H3MatrixOfAutomorphism(setup_m7, phi_i);
        Add(matrices_m7, M_y);
        Add(valid_endos_m7, IsValidH3Endomorphism(M_y, setup_m7.torsion));
        Print("  BRW gen ", i, "/", Length(brw_gens_m7), " (",
              (Runtime() - t_one) / 1000., " s, valid = ",
              valid_endos_m7[Length(valid_endos_m7)], ")\n");
    od;
    Print("H^3 matrices total wall: ", (Runtime() - t_h3mat) / 1000., " s\n");
    Print("All valid endomorphisms: ", ForAll(valid_endos_m7, x -> x = true), "\n");

    # Step 5: pre-populate the BRWH3Action cache so any downstream call
    # to BRWH3Action(7) gets our pre-built record.
    h3_action_m7 := rec(
        m := 7,
        em := em_m7,
        em_matrix := conj_action_m7.em_matrix,
        iso_em := iso_em_m7,
        brw := brw_m7,
        setup := setup_m7,
        torsion := setup_m7.torsion,
        num_generators := setup_m7.num_generators,
        brw_gens := brw_gens_m7,
        matrices := matrices_m7,
        valid_endos := valid_endos_m7
    );;
    _brw_h3_action_cache.("m7") := h3_action_m7;;
    Print("Pre-populated _brw_h3_action_cache.m7.\n");
    Print("Step 0a (m=7 LHS setup) wall: ",
          (Runtime() - t_lhs_setup) / 1000., " s\n");
fi;

# ----------------------------------------------------------------------
# Step 1: amortised per-generator BRW sweep with resumable state.
# Follows A-5b's run_e_plus_5_kernel.g pattern.
# ----------------------------------------------------------------------

Print("\n--- Step 1: amortised BRW sweep (resumable) ---\n");

OutDir := Concatenation("../../computed/transgression/", String(m));;
Exec(Concatenation("mkdir -p ", OutDir));
StateFile := Concatenation(OutDir, "/sweep_state.g");;
Print("State file: ", StateFile, "\n");

# IMPORTANT BUG FIX: BRWConjugacyAction(m) and BRWH3Action(m) each call
# IsomorphismPcGroup(EmGroup(m)) separately, giving DIFFERENT pc-group
# objects with different element families. Using conj_action.em as G but
# h3_action.setup as setup causes wrong c_g_table values when the H^3
# basis cocycles are evaluated against elements of the wrong family.
#
# This bug is dormant when all H^3 generators happen to be in the kernel
# (m=3, m=5) but visible at m=2 where some generators are NOT in ker.
#
# Fix: build setup on conj_action.em directly (or, at m=7, use the LHS
# resolution-derived setup we pre-populated above). Then build the BRW
# H^3 matrices using THIS setup so all element identifications match.
Print("Building BRW conjugacy action for m = ", m, "...\n");
t_brw := Runtime();;
conj_action := BRWConjugacyAction(m);;
Print("BRWConjugacyAction wall: ", (Runtime() - t_brw) / 1000., " s\n");

G := conj_action.em;;
Print("|G| = ", Order(G), "\n");

if m = 7 then
    # Use the LHS-derived setup we built in Step 0a. setup_m7's group IS
    # em_m7 = conj_action_m7.em = conj_action.em (since BRWConjugacyAction
    # is cached and returns the same record on the second call).
    setup := setup_m7;;
    Assert(0, IsIdenticalObj(setup.group, G),
           "m=7: setup.group must be identical to conj_action.em");
    # h3_matrices_consistent built in Step 0a using setup_m7.
    h3_matrices_consistent := matrices_m7;;
else
    # m in {2, 3, 5}: build setup on conj_action.em directly.
    Print("Building setup := SetupCohomology3(conj_action.em)...\n");
    t_setup := Runtime();;
    setup := SetupCohomology3(G);;
    Print("SetupCohomology3 wall: ", (Runtime() - t_setup) / 1000., " s\n");
    # Now build BRW H^3 matrices using THIS setup. We cannot reuse
    # BRWH3Action(m) because its internal setup is built on a DIFFERENT
    # IsomorphismPcGroup(EmGroup(m)) call. Build inline here.
    Print("Building BRW H^3 action matrices (using consistent setup)...\n");
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
fi;

# Keep h3_action reference for code that expects it (legacy).
h3_action := rec(matrices := h3_matrices_consistent);;
torsion := setup.torsion;;
exp := setup.exponent;;
k := setup.num_generators;;
Print("torsion = ", torsion, "\n");
Print("exponent = ", exp, "\n");
Print("k = ", k, " generators\n");

# Per-m anchors.
if m = 2 then
    Assert(0, k = 9 or k = 10, # both seen depending on GAP version
           Concatenation("expected k in {9, 10} for E_+(2); got ", String(k)));
elif m = 3 then
    Assert(0, k = 35,
           Concatenation("expected k = 35 for E_+(3); got ", String(k)));
elif m = 7 then
    Assert(0, k = 90,
           Concatenation("expected k = 90 for E_+(7); got ", String(k)));
fi;
sorted_torsion := ShallowCopy(torsion);;
Sort(sorted_torsion);;
Assert(0, ForAll(torsion, t -> IsInt(t) and t >= 2 and IsPrimePowerInt(t)
                              and SmallestRootInt(t) = 2),
       Concatenation("expected all torsion entries to be 2-powers; got ",
                     String(torsion)));

perm_gens := conj_action.perms;;
h3_matrices := h3_action.matrices;;
Assert(0, Length(perm_gens) = Length(h3_matrices),
       "perm_gens / h3_matrices length mismatch");

classes := conj_action.classes;;
n_classes := Length(classes);;
Print("n_classes = ", n_classes, "\n");
Assert(0, n_classes >= 1,
       Concatenation("expected >= 1 class; got ", String(n_classes)));

Print("Identifying BRW orbits + Schreier vectors over ", n_classes,
      " classes...\n");
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
          " members, types = ", Set(conj_action.types{orb_info.orbit}),
          ", |C_G(rep)| = ",
          Order(Centralizer(G,
                            Representative(classes[orb_info.start_idx]))),
          ", rep order = ",
          Order(Representative(classes[orb_info.start_idx])), "\n");
od;

# Build per-orbit cocycle-basis caches.
#
# Driver consumes only the orbit-rep cache (via H3VecAtTarget to transport
# the H^3 vec to sibling classes on-the-fly in PerVecTransgressionShared).
# We therefore use the rep-only `BuildPerClassCocycleBasis(setup, rep, C)`
# call here; the sibling-transport machinery
# `BuildPerClassCocycleBasisForOrbit` from PR #276 stays available in
# solver/snf_wrapper.g for downstream consumers that need per-class
# sibling caches (e.g. the proposed perf-4' transgression-matrix
# re-architecture). See #277 for rationale.
Print("Building per-orbit cocycle-basis caches (rep-only)...\n");
t_caches := Runtime();;
orbit_caches := [];;
for orb_info in orbits_data do
    rep := Representative(classes[orb_info.start_idx]);
    C := Centralizer(G, rep);
    Print("  orbit start ", orb_info.start_idx, " (|C| = ", Order(C),
          ", n*n*k = ", Order(C)^2 * k,
          ", rep order = ", Order(rep),
          ", orbit size ", Length(orb_info.orbit), ") ... ");
    t_one := Runtime();
    if IsOne(rep) then
        # Identity class: c_g(h, k) = omega(id, h, k) - omega(h, id, k)
        # + omega(h, k, id) = 0 for normalized omega. Build an
        # all-zero table without the n²·k Syzygy chain.
        cache_elts := AsList(C);
        cache_n := Length(cache_elts);
        cache_table := List([1..cache_n * cache_n],
                            r -> List([1..k], i -> 0));
        ConvertToMatrixRep(cache_table);
        cache_idx_map := NewDictionary(cache_elts[1], true, cache_elts);
        for cache_a in [1..cache_n] do
            AddDictionary(cache_idx_map, cache_elts[cache_a], cache_a);
        od;
        # GF(2) view: also all zero.
        cache_table_gf2 := List([1..cache_n * cache_n],
                                 r -> List([1..k], i -> Zero(GF(2))));
        ConvertToMatrixRep(cache_table_gf2, GF(2));
        # Identity class is a singleton orbit at m=2, 3, 5, 7; no
        # sibling transport needed.
        Add(orbit_caches, rec(C := C, table := cache_table,
                               table_gf2 := cache_table_gf2,
                               elts := cache_elts, n := cache_n,
                               idx_map := cache_idx_map));
        Print((Runtime() - t_one) / 1000., " s (degenerate, identity class)\n");
    else
        # Non-identity orbit: build the rep cache only. Sibling transport
        # is not consumed by PerVecTransgressionShared (see header comment
        # above this block).
        Add(orbit_caches, BuildPerClassCocycleBasis(setup, rep, C));
        Print((Runtime() - t_one) / 1000., " s (rep-only)\n");
    fi;
od;
Print("Per-orbit caches wall: ", (Runtime() - t_caches) / 1000., " s total\n");

# ----------------------------------------------------------------------
# Per-generator sweep using shared caches.
# ----------------------------------------------------------------------

completed_idx := Set(LoadResumeState(StateFile), r -> r.generator);;
Print("\nAlready completed (resume): ", Length(completed_idx), " / ", k,
      "  ", completed_idx, "\n");

# Helper: BRW-amortised per-vec transgression test. Same as A-5b but
# adapted to handle all-Z/2 torsion (no Path Z hits when exp = 2).
PerVecTransgressionShared := function(vec)
    local results, oi, orb_info, basis_cache, target_idx, vec_target,
          c_g_table, exp_index, r, exp_local, batch_inputs, batch_targets,
          c_prime_bits, batch_results, j, ti, one_gf2, u_gf2;
    results := List([1..n_classes], j -> "?");
    # Precondition: every torsion[i] in {2, exponent}.
    for ti in [1..Length(setup.torsion)] do
        Assert(0, setup.torsion[ti] = 2 or setup.torsion[ti] = setup.exponent,
               Concatenation("PerVecTransgressionShared: torsion[",
                             String(ti), "] = ", String(setup.torsion[ti]),
                             " not in {2, exponent=", String(setup.exponent),
                             "} — mixed sub-exp torsion not supported"));
    od;
    exp_index := Position(setup.torsion, setup.exponent);
    exp_local := setup.exponent;
    r := exp_local / 2;
    one_gf2 := One(GF(2));
    for oi in [1..Length(orbits_data)] do
        orb_info := orbits_data[oi];
        basis_cache := orbit_caches[oi];
        batch_inputs := [];
        batch_targets := [];
        for target_idx in orb_info.orbit do
            vec_target := H3VecAtTarget(orb_info.start_idx, target_idx,
                                         orb_info.parent, orb_info.gen_used,
                                         h3_matrices, torsion, vec);
            if exp_local > 2 and exp_index <> fail and vec_target[exp_index] <> 0 then
                # Path Z: per-call. Needs the full integer c_g_table.
                c_g_table := basis_cache.table * vec_target;
                results[target_idx] :=
                    IsCoboundary2SplitVec(basis_cache.C, c_g_table, vec_target,
                                           setup);
            else
                # Path A: A-5b R2-8 (#258 / #266 follow-up). Single
                # compiled GF(2) matvec replaces the 1M-int matmul
                # `basis_cache.table * vec_target` AND the per-element
                # bit-extract List comprehension. Math:
                #   c_prime_bits[i]
                #     = bit_{log2(r)}((table * vec_target)[i] mod exp)
                #     = sum_k (vec_target[k] mod 2)
                #            * bit_{log2(r)}(table[i][k])  over GF(2)
                # under Path A's `vec_target[exp_index] = 0`
                # precondition. table_gf2 precomputed once per
                # centraliser in BuildPerClassCocycleBasis
                # (solver/snf_wrapper.g). Generalises across exp = 2
                # (r = 1, bit_0) and exp = 4 (r = 2, bit_1).
                u_gf2 := List(vec_target, x -> (x mod 2) * one_gf2);
                ConvertToVectorRep(u_gf2, GF(2));
                c_prime_bits := basis_cache.table_gf2 * u_gf2;
                Add(batch_inputs, c_prime_bits);
                Add(batch_targets, target_idx);
            fi;
        od;
        if not IsEmpty(batch_inputs) then
            batch_results := IsCoboundary2Mod2WithLiftVecBatch(
                basis_cache.C, batch_inputs);
            for j in [1..Length(batch_targets)] do
                results[batch_targets[j]] := batch_results[j];
            od;
        fi;
    od;
    return results;
end;;

# Sweep loop.
t_sweep := Runtime();;
if probe_gen <> fail then
    # Probe mode: compute only one generator.
    sweep_indices := [probe_gen];
else
    sweep_indices := [1..k];
fi;
for i in sweep_indices do
    if i in completed_idx then
        Print("Skipping generator ", i, " (already done)\n");
        continue;
    fi;
    t_gen := Runtime();
    e_i := List([1..k], j -> 0);
    e_i[i] := 1;
    per_class := PerVecTransgressionShared(e_i);
    all_in_kernel := ForAll(per_class, x -> x = true);
    PersistGenerator(StateFile, i, all_in_kernel, per_class);
    Print("Computing generator ", i, "... ",
          If_(all_in_kernel, "IN", "NOT"), " kernel  (",
          (Runtime() - t_gen) / 1000., " s)\n");
od;
sweep_wall := (Runtime() - t_sweep) / 1000.;;
Print("Per-generator sweep wall (this invocation): ", sweep_wall, " s\n");

# Probe-mode early exit: use FORCE_QUIT_GAP since QUIT cannot appear in
# nested blocks parsed via Read.
if probe_gen <> fail then
    Print("\n=== PROBE-MODE EXIT (gen ", probe_gen, " only) ===\n");
    Print("Total wall: ", (Runtime() - t_start) / 1000., " s\n");
    FORCE_QUIT_GAP(0);
fi;

# Re-load state.
final_state := LoadResumeState(StateFile);;
in_kernel_gens := List(Filtered(final_state, r -> r.all_in_kernel),
                        r -> r.generator);;
Print("In-kernel unit generators: ", Length(in_kernel_gens), " / ", k, "\n");
Print("  indices: ", in_kernel_gens, "\n");

exp_index := Position(torsion, exp);;
Print("Order-", exp, " generator index: ", exp_index, "\n");

# ----------------------------------------------------------------------
# Step 2: half-vector check for the order-exp generator (only if exp > 2).
# ----------------------------------------------------------------------

if exp = 2 then
    Print("\n--- Step 2: half-vec check skipped (exp = 2, all gens order 2) ---\n");
    half_in_ker := fail;;
else
    Print("\n--- Step 2: half-vector check (2 * e_", exp_index, ") ---\n");
    half_in_ker := fail;;
    if exp_index in in_kernel_gens then
        half_in_ker := true;
        Print("e_", exp_index, " (order ", exp, ") is in ker; 2*e_",
              exp_index, " is trivially also in ker.\n");
    else
        half_vec := List([1..k], j -> 0);
        half_vec[exp_index] := 2;
        Print("Testing 2 * e_", exp_index, " via BRW path...\n");
        t_half := Runtime();
        half_per_class := PerVecTransgressionShared(half_vec);
        half_wall := (Runtime() - t_half) / 1000.;
        Print("Half-vector test wall: ", half_wall, " s\n");
        half_in_ker := ForAll(half_per_class, x -> x = true);
        Print("2 * e_", exp_index, " in ker: ", half_in_ker, "\n");
        if not half_in_ker then
            Print("Witness classes: ",
                  Filtered([1..Length(half_per_class)],
                           j -> half_per_class[j] = false), "\n");
        fi;
    fi;
fi;

# ----------------------------------------------------------------------
# Step 3: assemble the kernel.
# ----------------------------------------------------------------------

Print("\n--- Step 3: assemble kernel ---\n");

zero_vec := List(torsion, t -> 0);;

basis_vecs := [];;
basis_orders := [];;
for i in in_kernel_gens do
    e_i := List([1..k], j -> 0);
    e_i[i] := 1;
    Add(basis_vecs, e_i);
    Add(basis_orders, torsion[i]);
od;
if exp > 2 and (not (exp_index in in_kernel_gens)) and half_in_ker = true then
    half_vec := List([1..k], j -> 0);
    half_vec[exp_index] := 2;
    Add(basis_vecs, half_vec);
    # Order of 2 * e_{exp_index} in Z/torsion[exp_index] = torsion / gcd(torsion, 2).
    # For exp=4: order 2 (matches A-3a). For exp=8: order 4. General: exp/gcd(exp,2).
    Add(basis_orders, torsion[exp_index] / GcdInt(torsion[exp_index], 2));
fi;

kernel_size_expected := Product(basis_orders);;
Print("Basis vectors: ", Length(basis_vecs), "\n");
Print("Basis orders: ", basis_orders, "\n");
Print("Expected |ker| (from independent basis): ", kernel_size_expected, "\n");

ReduceModTorsion := function(v, t)
    return List([1..Length(v)], j -> v[j] mod t[j]);
end;;

KernelVecFromCoeffs := function(coeffs)
    local v, t;
    v := ShallowCopy(zero_vec);
    for t in [1..Length(basis_vecs)] do
        v := v + coeffs[t] * basis_vecs[t];
    od;
    return ReduceModTorsion(v, torsion);
end;;

kernel_size := kernel_size_expected;;
Print("|ker Tr|: ", kernel_size, "\n");

ENUM_LIMIT := 2^16;;
kernel_vecs := fail;;
if kernel_size <= ENUM_LIMIT then
    kernel_vecs := [];
    if IsEmpty(basis_vecs) then
        Add(kernel_vecs, zero_vec);
    else
        for coeffs in Cartesian(List(basis_orders, o -> [0..o-1])) do
            Add(kernel_vecs, KernelVecFromCoeffs(coeffs));
        od;
    fi;
    kernel_vecs := Set(kernel_vecs);
    Assert(0, Length(kernel_vecs) = kernel_size,
           Concatenation("kernel enumeration size ",
                         String(Length(kernel_vecs)),
                         " disagrees with basis-product ",
                         String(kernel_size)));
    Assert(0, zero_vec in kernel_vecs, "zero vec missing from kernel");
    Print("Full kernel enumerated (", Length(kernel_vecs), " vecs).\n");
else
    Print("Kernel too large to enumerate (", kernel_size, " > ",
          ENUM_LIMIT, "); persisting structurally.\n");
fi;

# ----------------------------------------------------------------------
# Step 4 (optional cross-check): sample 100 kernel vecs + non-kernel vecs.
# Skipped at m=7 to keep probe times short — A-5b model already exercises
# this code path at m=5.
# ----------------------------------------------------------------------

non_ker_ok := true;;
if m <= 5 then
    Print("\n--- Step 4: deterministic-stride cross-check ---\n");
    TestVecAllClasses := function(vec)
        local per_class, j;
        per_class := PerVecTransgressionShared(vec);
        for j in [1..n_classes] do
            if per_class[j] = false then
                return rec(in_kernel := false, witness_class := j);
            fi;
        od;
        return rec(in_kernel := true, witness_class := fail);
    end;;
    DecodeCoeffs := function(n)
        local coeffs, t;
        coeffs := List(basis_orders, o -> 0);
        if IsEmpty(basis_orders) then return coeffs; fi;
        for t in [Length(basis_orders), Length(basis_orders) - 1 .. 1] do
            coeffs[t] := n mod basis_orders[t];
            n := QuoInt(n, basis_orders[t]);
        od;
        return coeffs;
    end;;
    sample_size := Minimum(100, kernel_size);;
    random_kernel_sample := [];;
    if Length(basis_vecs) = 0 then
        Add(random_kernel_sample, zero_vec);
    else
        stride := QuoInt(kernel_size, sample_size);
        if stride < 1 then stride := 1; fi;
        for s in [0..sample_size - 1] do
            encoded := (s * stride) mod kernel_size;
            Add(random_kernel_sample, KernelVecFromCoeffs(DecodeCoeffs(encoded)));
        od;
    fi;
    t_check_k := Runtime();;
    kernel_ok := true;;
    kernel_failures := [];;
    for v in random_kernel_sample do
        r_ := TestVecAllClasses(v);
        if not r_.in_kernel then
            kernel_ok := false;
            Add(kernel_failures, rec(vec := v, witness := r_.witness_class));
        fi;
    od;
    Print("Kernel-sample cross-check: ", sample_size, " vecs, all in ker: ",
          kernel_ok, " (", (Runtime() - t_check_k) / 1000., " s)\n");
    Assert(0, kernel_ok,
           "Random kernel sample failed: some vec we claim is in ker is detected");

    not_in_ker_indices := Difference([1..k], in_kernel_gens);;
    if IsEmpty(not_in_ker_indices) then
        Print("All ", k, " unit gens in ker; non-ker sample trivially skipped.\n");
    else
        Print("Non-ker base indices: ", not_in_ker_indices, "\n");
        sample_size_nk := Minimum(100, kernel_size * Length(not_in_ker_indices));;
        t_check_nk := Runtime();;
        stride_k := Maximum(1, QuoInt(kernel_size, sample_size_nk));;
        non_ker_failures := [];;
        for s in [0..sample_size_nk - 1] do
            encoded := (s * stride_k) mod kernel_size;
            if Length(basis_vecs) = 0 then
                v := ShallowCopy(zero_vec);
            else
                v := KernelVecFromCoeffs(DecodeCoeffs(encoded));
            fi;
            idx_nk := not_in_ker_indices[(s mod Length(not_in_ker_indices)) + 1];
            v[idx_nk] := (v[idx_nk] + 1) mod torsion[idx_nk];
            v := ReduceModTorsion(v, torsion);
            r_ := TestVecAllClasses(v);
            if r_.in_kernel then
                non_ker_ok := false;
                Add(non_ker_failures, rec(vec := v));
            fi;
        od;
        Print("Non-ker sample cross-check: ", sample_size_nk,
              " vecs, none in ker: ", non_ker_ok,
              " (", (Runtime() - t_check_nk) / 1000., " s)\n");
        if not non_ker_ok then
            Print("WARNING: non-ker sample produced unexpected in-ker; ",
                  "kernel basis may be incomplete.\n");
        fi;
    fi;
else
    Print("\n--- Step 4: cross-check SKIPPED (m=", m,
          ", saved for separate test run) ---\n");
fi;

# ----------------------------------------------------------------------
# Step 5: persist to computed/transgression/<m>/kernel.g
# ----------------------------------------------------------------------

OutPath := Concatenation(OutDir, "/kernel.g");;
Print("\n--- Step 5: persist to ", OutPath, " ---\n");

basis_summary := [];;
for i in in_kernel_gens do
    Add(basis_summary, rec(vec := basis_vecs[Position(in_kernel_gens, i)],
                            order := torsion[i],
                            kind := Concatenation("e_", String(i)),
                            generator_index := i));
od;
if exp > 2 and (not (exp_index in in_kernel_gens)) and half_in_ker = true then
    Add(basis_summary, rec(vec := basis_vecs[Length(basis_vecs)],
                            order := 2,
                            kind := Concatenation("2 * e_", String(exp_index)),
                            generator_index := exp_index));
fi;

# Determine id for m=2 (SmallGroup library reaches that); fail for higher.
id_str := fail;;
if m = 2 then
    id_str := IdSmallGroup(G);
elif m = 3 then
    id_str := IdSmallGroup(G);
fi;

kernel_out_stream := OutputTextFile(OutPath, false);;
SetPrintFormattingStatus(kernel_out_stream, false);
PrintTo(kernel_out_stream,
    "# ker(Tr : H^3(E_+(", m, "); U(1)) -> oplus_g H^2(C_g; U(1)))\n",
    "#\n",
    "# Generated by extraspecial_orbifolds/scripts/run_e_plus_m_kernel_hap.g\n",
    "# (issue #50, A-7a, HAP route at m=", m, ").\n",
    "#\n",
    "# G = E_+(", m, "); |G| = ", String(Order(G)), ".\n",
    "# H^3(G; U(1)) torsion: ", String(torsion), ".\n",
    "# |H^3(G; U(1))| = ", String(Product(torsion)), "\n",
    "# |ker Tr|       = ", String(kernel_size), "\n",
    "#\n",
    "# Method: T-3d BRW + T-4 centraliser caches + T-5 resumable sweep.\n",
    If_(m = 7,
        "#         Resolution built via LHSResolutionEPlus(7, 5) (PR #252).\n",
        "#         Resolution built via ResolutionFiniteGroup.\n"),
    "#\n",
    "# Format: see same-shape kernel.g at computed/transgression/{2,3,5}/.\n",
    "\n",
    "local kernel_vecs;\n",
    "kernel_vecs := ", kernel_vecs, ";\n",
    "return rec(\n",
    "    group              := \"E_+(", String(m), ")\",\n",
    "    id                 := ", id_str, ",\n",
    "    torsion            := ", torsion, ",\n",
    "    exponent           := ", exp, ",\n",
    "    kernel_size        := ", kernel_size, ",\n",
    "    kernel_vecs        := kernel_vecs,\n",
    "    in_kernel_gens     := ", in_kernel_gens, ",\n",
    "    exp_index          := ", exp_index, ",\n",
    "    half_vec_in_kernel := ", half_in_ker, ",\n",
    "    basis_summary      := ", basis_summary, "\n",
    ");;\n");
CloseStream(kernel_out_stream);

Print("Wrote ", OutPath, "\n");

# ----------------------------------------------------------------------
# Step 6: confirmation
# ----------------------------------------------------------------------

total_wall := (Runtime() - t_start) / 1000.;;
Print("\n=== A-7a driver: DONE (m=", m, ") ===\n");
Print("Total wall: ", total_wall, " s\n");
Print("|ker Tr|     = ", kernel_size, "\n");
Print("|H^3|        = ", Product(torsion), "\n");
Print("|coker Tr|   = ", Product(torsion) / kernel_size, "\n");
Print("In-ker gens: ", Length(in_kernel_gens), " / ", k,
      " (", in_kernel_gens, ")\n");
if exp > 2 then
    Print("Half-vec 2 * e_", exp_index, " in ker: ", half_in_ker, "\n");
fi;
Print("Output: ", OutPath, "\n");

QUIT;
