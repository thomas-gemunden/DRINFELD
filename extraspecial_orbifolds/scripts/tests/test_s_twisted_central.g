# test_s_twisted_central.g — V-2 acceptance tests for `STwistedCentralEntry`.
#
# Tests:
#   (1) STwistedCentralEntry throws when g1 is not central / has
#       order > 2.
#   (2) ω = 0 case, on G = E_+(3) = SmallGroup(128, 2326): 100 random
#       entries on central rows agree exactly with `ComputeSBlock` from
#       untwisted_modular_data.g (which realises the §4.3 closed form
#       indirectly via the direct Bantay/CGR sum at ω = 0).
#   (3) For G = Q_8 = SmallGroup(8, 4), order-2 cocycle (orbit index 2
#       in modular_data/8/4/), central-row entries agree with the disk
#       data modular_data/8/4/2.txt, modulo the per-block permutation σ
#       already documented in test_epsilon_omega.g.
#
# Run:
#   gap -q -b /Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-v2/extraspecial_orbifolds/scripts/tests/test_s_twisted_central.g
# All paths below are absolute so cwd is irrelevant.

LoadPackage("hap");
LoadPackage("io");

# Load the modular_data.g machinery (StandardCocycle, GenerateSimpleObjects,
# UniversalCoefficientsTheorem, ConjugacyClasses helpers, etc.).
Read("/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-v2/src/modular_data.g");

# Load V-1's EpsilonOmega + V-2's STwistedCentralEntry.
Read("/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-v2/extraspecial_orbifolds/scripts/epsilon_omega.g");
Read("/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-v2/extraspecial_orbifolds/scripts/s_twisted_central.g");

# For test (2) we need the direct ComputeSBlock from
# untwisted_modular_data.g (no cohomology pipeline; raw character tables).
Read("/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-v2/extraspecial_orbifolds/scripts/untwisted_modular_data.g");

############################################################
# (1) Error-on-non-central-g1 test.
############################################################
# Uses CALL_WITH_CATCH under BreakOnError := false to trap the Error()
# raised by STwistedCentralEntry without dropping into the GAP break loop.

TestSTwistedCentralErrorCases := function()
    local G, elts, non_central, omega_zero, m, chi_dummy, g_high_order,
          ok_save, result;
    Print("[1] Error cases (non-central / order > 2)...\n");
    G := SmallGroup(8, 4);   # Q_8
    elts := AsList(G);
    omega_zero := function(a, b, c) return 0; end;
    m := 2;

    # Dummy character callables: just return constants. The error
    # should fire before any character evaluation.
    chi_dummy := x -> 1;

    # Suppress break loops while testing intentional errors.
    ok_save := BreakOnError;
    BreakOnError := false;

    # (1a) Pass a non-central element (one of the order-4 generators of Q_8).
    non_central := First(elts, g ->
        Order(g) = 4 and not IsCentral(G, g));
    if non_central = fail then
        BreakOnError := ok_save;
        Error("Internal: couldn't find a non-central order-4 element of Q_8.");
    fi;
    result := CALL_WITH_CATCH(STwistedCentralEntry,
        [G, omega_zero, m, non_central, chi_dummy,
         One(G), chi_dummy]);
    if result[1] then
        BreakOnError := ok_save;
        Error("  FAIL: STwistedCentralEntry should error on non-central g1, but returned: ", result[2]);
    fi;
    Print("  PASS: non-central g1 raises an error.\n");

    # (1b) Pass a central element of order > 2 in some group. Q_8 has no
    # central element of order > 2, so use C_4 = SmallGroup(4, 1) (cyclic,
    # so every element is central) with the order-4 generator.
    G := SmallGroup(4, 1);
    g_high_order := First(AsList(G), g -> Order(g) = 4);
    if g_high_order = fail then
        BreakOnError := ok_save;
        Error("Internal: couldn't find an order-4 element in C_4.");
    fi;
    result := CALL_WITH_CATCH(STwistedCentralEntry,
        [G, omega_zero, m, g_high_order, chi_dummy,
         One(G), chi_dummy]);
    if result[1] then
        BreakOnError := ok_save;
        Error("  FAIL: STwistedCentralEntry should error on central g1 with order > 2, but returned: ", result[2]);
    fi;
    Print("  PASS: central g1 with Order(g1) > 2 raises an error.\n");

    BreakOnError := ok_save;
end;;

############################################################
# (2) ω = 0 on E_+(3): 100 random central-row entries agree with
#     direct ComputeSBlock.
############################################################

# Helper: locate a class index by class membership test.
ClassIndexOf := function(idx, g)
    local i;
    for i in [1..Length(idx.classes)] do
        if g in idx.classes[i] then return i; fi;
    od;
    return fail;
end;;

# Test (2) uses one-shot closure builders for chi1 and chi2 to avoid
# capture-by-reference pitfalls inside the sampling loop. The chiX
# returned binds (i, k, idx) into a function whose body looks up
# (idx, i, k) explicitly.
MkChi := function(idx_rec, i, k)
    return function(x)
        return EvalIrr(idx_rec, i, k, x);
    end;
end;;

TestSTwistedCentralUntwistedEplus3 := function()
    local G, idx, transport, central_classes,
          omega_zero, m, sample_count, fails, t,
          central_class, rho_idx, target_class, sigma_idx,
          rep_central, rep_target, chi1, chi2,
          got, expected, n_classes,
          minus1_class, identity_class, block_cache,
          checked_one, checked_minus1, sample_idx;
    Print("[2] ω = 0 on E_+(3) = SmallGroup(128, 2326), 100 random central-row entries...\n");

    G := SmallGroup(128, 2326);

    # Direct (no-cohomology) untwisted index/transport.
    idx := BuildSimpleIndex(G);
    transport := BuildTransports(idx);
    n_classes := Length(idx.classes);
    Print("  built idx: ", n_classes, " classes, rank = ", idx.rank, "\n");
    Assert(0, idx.rank = 2272,
        Concatenation("E_+(3) untwisted rank expected 2272, got ", String(idx.rank)));

    # Identify the {1} class (rep = One(G)) and the {-1} class (singleton class of order 2).
    identity_class := ClassIndexOf(idx, One(G));
    minus1_class := First([1..n_classes],
        i -> idx.class_sizes[i] = 1 and Order(idx.reps[i]) = 2);
    if minus1_class = fail then
        Error("E_+(3): couldn't find a singleton class of order 2 (the {-1} class).");
    fi;
    Print("  identity class index: ", identity_class,
          ", -1 class index: ", minus1_class, "\n");
    central_classes := [identity_class, minus1_class];

    omega_zero := function(a, b, c) return 0; end;
    m := 2;   # any m works since ε_ω ≡ 0 mod m.

    # Sample 100 random (central_class, rho_idx, target_class, sigma_idx) tuples.
    Reset(GlobalMersenneTwister, 20260510);
    sample_count := 100;
    fails := 0;
    checked_one := 0;
    checked_minus1 := 0;
    # Cache S-blocks since each call has cost O(|G|^2) — block keys are
    # (central_class, target_class) pairs. Use a nested list indexed by
    # [central_class][target_class].
    block_cache := List([1..n_classes], i -> []);

    t := Runtime();
    for sample_idx in [1..sample_count] do
        central_class := Random(GlobalMersenneTwister, central_classes);
        rho_idx       := Random(GlobalMersenneTwister,
            [1..idx.num_irreps[central_class]]);
        target_class  := Random(GlobalMersenneTwister, [1..n_classes]);
        sigma_idx     := Random(GlobalMersenneTwister,
            [1..idx.num_irreps[target_class]]);
        rep_central   := idx.reps[central_class];
        rep_target    := idx.reps[target_class];

        # χ_1 is an ordinary irrep of G (g1 ∈ Z(G) ⇒ C_G(g1) = G).
        # χ_2 is an ordinary irrep of C_G(rep_target); only its value at
        # rep_central is needed (since g1 is central).
        chi1 := MkChi(idx, central_class, rho_idx);
        chi2 := MkChi(idx, target_class,  sigma_idx);

        got := STwistedCentralEntry(G, omega_zero, m,
                                    rep_central, chi1,
                                    rep_target, chi2);

        # Direct ComputeSBlock for ground truth.
        if not IsBound(block_cache[central_class][target_class]) then
            block_cache[central_class][target_class] :=
                ComputeSBlock(idx, transport, central_class, target_class);
        fi;
        expected := block_cache[central_class][target_class][rho_idx][sigma_idx];

        if got <> expected then
            fails := fails + 1;
            Print("  MISMATCH at sample ", sample_idx, ": ",
                  "central_class=", central_class,
                  " rho_idx=", rho_idx,
                  " target_class=", target_class,
                  " sigma_idx=", sigma_idx, "\n");
            Print("    got      = ", got, "\n");
            Print("    expected = ", expected, "\n");
        else
            if central_class = identity_class then
                checked_one := checked_one + 1;
            else
                checked_minus1 := checked_minus1 + 1;
            fi;
        fi;
    od;
    Print("  wall: ", (Runtime() - t)/1000.0, " s\n");
    if fails > 0 then
        Error("E_+(3) ω=0 test: ", fails, "/", sample_count, " mismatches.");
    fi;
    Print("  PASS: ", sample_count, "/", sample_count,
          " entries agree (", checked_one, " on g1=1, ",
          checked_minus1, " on g1=-1).\n");
end;;

############################################################
# (3) Q_8 order-2 cocycle: central-row entries match
#     modular_data/8/4/2.txt under the per-block permutation σ.
############################################################
# Strategy mirrors test_epsilon_omega.g:
#   - Reconstruct ω for orbit index 2 of Q_8.
#   - Build simples via GenerateSimpleObjects.
#   - Build the full S via the §6.2 formula (so we can find σ).
#   - Build the per-block σ matching the disk order.
#   - For each central-row entry, evaluate via STwistedCentralEntry
#     and compare to the disk value under σ.

# The §6.2 full evaluator (lifted from test_epsilon_omega.g) — only
# used to find σ. Independent of STwistedCentralEntry, which we test
# against the disk values *after* σ is fixed.
ComputeSEntryViaEpsilonFull := function(G, omega, val, exponent, gData, hData)
    local g1, g2, num, m_omega, ii, jj, a, b, ta, sb,
          eps_int, char_g1, char_g2;
    g1 := gData.representative;
    g2 := hData.representative;
    m_omega := exponent * val;
    num := 0;
    for ii in gData.conjugacyClass do
        for jj in hData.conjugacyClass do
            a  := ii[1]; ta := ii[2];
            b  := jj[1]; sb := jj[2];
            if a*b = b*a then
                eps_int := EpsilonOmegaWithSection(omega, g1, g2,
                                                   a, b, ta, sb, m_omega);
                char_g1 := LookupDictionary(gData.character, ta * b * ta^-1);
                char_g2 := LookupDictionary(hData.character, sb * a * sb^-1);
                num := num + E(m_omega)^eps_int * char_g1 * char_g2;
            fi;
        od;
    od;
    return ComplexConjugate(num) / Order(G);
end;;

ComputeFullSMatrixQ8 := function(G, omega, val, exponent, simples)
    local n, S, i, j;
    n := Length(simples);
    S := NullMat(n, n);
    for i in [1..n] do
        for j in [1..n] do
            S[i][j] := ComputeSEntryViaEpsilonFull(G, omega, val, exponent,
                                                    simples[i], simples[j]);
        od;
    od;
    return S;
end;;

# Find the per-block permutation σ that takes our enumeration to the disk
# enumeration. (Copied from test_epsilon_omega.g; specific to Q_8 orbit 2.)
FindBlockPermutationQ8 := function(S_computed, S_disk, T_computed, T_disk)
    local n, sigma, perm_options, perm4, S_perm, i, j;
    n := Length(S_disk);

    perm_options := function(disk_pos_range, comp_pos_range)
        return List(disk_pos_range, i ->
            First(comp_pos_range, j -> T_computed[j] = T_disk[i]));
    end;

    sigma := [1, 2, 3, 4, 5];
    Append(sigma, perm_options([6..9], [6..9]));
    Append(sigma, perm_options([10..13], [10..13]));
    Append(sigma, [14, 15, 16, 17]);
    Add(sigma, 18);
    Append(sigma, perm_options([19..22], [19..22]));

    for perm4 in PermutationsList([14, 15, 16, 17]) do
        sigma{[14..17]} := perm4;
        S_perm := NullMat(n, n);
        for i in [1..n] do
            for j in [1..n] do
                S_perm[i][j] := S_computed[sigma[i]][sigma[j]];
            od;
        od;
        if S_perm = S_disk then
            return sigma;
        fi;
    od;
    return fail;
end;;

TestSTwistedCentralQ8 := function()
    local G, R, K, UCT, cocycle_vec, val, exponent, omega, m_omega,
          loaded, S_disk, T_disk, simples_data, simples, n_simples,
          S_computed, T_computed, sigma, central_simples_disk, pair,
          i_disk, j_disk, i_comp, j_comp, simp_i, simp_j, g1, g2,
          chi1, chi2, computed_entry, disk_entry, mismatches, checked;
    Print("[3] Q_8 order-2 cocycle, central-row entries vs modular_data/8/4/2.txt...\n");
    G := SmallGroup(8, 4);   # Q_8

    R := ResolutionFiniteGroup(G, 4);
    K := TensorWithIntegers(R);
    UCT := UniversalCoefficientsTheorem(K, 3);

    cocycle_vec := UCT.lift * [0, 4, 0];
    val := Gcd(Gcd(cocycle_vec), UCT.exponent);
    exponent := UCT.exponent / val;
    omega := StandardCocycle(R, cocycle_vec, 3, UCT.exponent);
    m_omega := exponent * val;
    Print("  cocycle: vec=", cocycle_vec, ", val=", val, ", exp=", exponent,
          ", m_omega=", m_omega, "\n");

    loaded := ReadAsFunction(
        "/Users/thomasgemunden/Projects/group_cohomology/modular_data/8/4/2.txt")();
    S_disk := loaded.S;
    T_disk := loaded.T;

    simples_data := GenerateSimpleObjects(G, omega, val, exponent);
    simples := simples_data.Simp;
    n_simples := Length(simples);
    Assert(0, n_simples = Length(S_disk),
        Concatenation("Simple count mismatch: built ", String(n_simples),
                      ", on disk ", String(Length(S_disk))));

    # Build full S to find σ.
    S_computed := ComputeFullSMatrixQ8(G, omega, val, exponent, simples);
    T_computed := List(simples,
        s -> LookupDictionary(s.character, s.representative) / s.dimension);
    Assert(0, AsSortedList(T_disk) = AsSortedList(T_computed),
        "T-diagonals disagree as multisets (cocycle reconstruction issue).");

    sigma := FindBlockPermutationQ8(S_computed, S_disk, T_computed, T_disk);
    if sigma = fail then
        Error("Q_8: no per-block σ matches our S to the disk S.");
    fi;
    Print("  found σ: ", sigma, "\n");

    # Central-row entries in the *disk* numbering: those whose g1 is
    # central in Q_8 = {1, -1}. After applying σ, the corresponding
    # *computed* simple is simples[σ[i]]; we check that its g1 is central.
    central_simples_disk := Filtered([1..n_simples], i ->
        IsCentral(G, simples[sigma[i]].representative));
    Print("  central simples in disk numbering: ", central_simples_disk, "\n");
    Assert(0, Length(central_simples_disk) >= 10,
        "Expected ≥ 10 central simples on disk; got fewer.");

    # Check central-row entries. Mirror the choices in test_epsilon_omega.g.
    # 4 entries with g1 = identity (i_disk small), 6 entries with g1 = -1.
    mismatches := 0;
    checked := 0;
    for pair in [
            [1, 1], [1, 5], [1, 14], [5, 18],     # g1 = identity
            [14, 1], [14, 5], [14, 6], [14, 14],
            [14, 18], [18, 18]                    # g1 = -1
        ] do
        i_disk := pair[1]; j_disk := pair[2];
        i_comp := sigma[i_disk]; j_comp := sigma[j_disk];
        simp_i := simples[i_comp];
        simp_j := simples[j_comp];
        g1 := simp_i.representative;
        g2 := simp_j.representative;
        # χ1: G → C via the character dict of simp_i.
        chi1 := x -> LookupDictionary(simp_i.character, x);
        # χ2: C_G(g2) → C via the character dict of simp_j.
        chi2 := x -> LookupDictionary(simp_j.character, x);

        # STwistedCentralEntry requires g1 central. Verify.
        Assert(0, IsCentral(G, g1),
            Concatenation("Test row (i_disk=", String(i_disk),
                          ") corresponds to non-central g1; check σ."));

        computed_entry := STwistedCentralEntry(G, omega, m_omega,
                                               g1, chi1, g2, chi2);
        disk_entry := S_disk[i_disk][j_disk];
        if computed_entry <> disk_entry then
            mismatches := mismatches + 1;
            Print("  MISMATCH at disk-(", i_disk, ", ", j_disk,
                  "): got ", computed_entry, ", disk ", disk_entry, "\n");
            Print("    g1 = ", g1, ", g2 = ", g2, "\n");
        else
            checked := checked + 1;
            Print("  match (i_disk=", i_disk, " g1=", g1,
                  ", j_disk=", j_disk, " g2=", g2, ") = ", disk_entry, "\n");
        fi;
    od;
    if mismatches > 0 then
        Error("Q_8 central-row test: ", mismatches, " mismatches.");
    fi;
    Print("  PASS: ", checked,
          " central-row entries match modular_data/8/4/2.txt under σ.\n");
end;;

############################################################
# Run all tests.
############################################################

Print("=== test_s_twisted_central.g ===\n");
TestSTwistedCentralErrorCases();
TestSTwistedCentralUntwistedEplus3();
TestSTwistedCentralQ8();
Print("=== test_s_twisted_central.g: ALL PASS ===\n");
QUIT;
