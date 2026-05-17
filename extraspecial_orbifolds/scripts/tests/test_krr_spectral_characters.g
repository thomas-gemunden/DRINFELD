# K-4a-T4c verification driver for `krr_spectral_characters.g`.
#
# Acceptance criterion (issue #208):
#   m = 3 character match: BuildKRRSpectralCharacters(3).character_match
#   should have no `fail` entries; each `standard_irrep_idx` appears
#   exactly once per class. This is the K-4a-T4c m=3 anchor: alpha = 0
#   at m=3 forces the KRR-derived characters to match standard up to
#   permutation.
#
# Additional tests:
#   2. Eigenvalue consistency: each T_h acts on its eigenspace by the
#      claimed eigenvalue (verified by direct matrix-vector multiplication).
#   3. Character orthogonality: distinct eigenspaces correspond to
#      distinct eigenvalue tuples (so each carries a distinct character).
#   4. Dim consistency: sum of dims of eigenspaces equals dim(W_a).
#   5. trace_on_W callable: trace_on_W(1, 1, identity) returns multiplicity.
#
# SCOPE:
#   m = 3 only.  At m = 5 the full-matrix approach in
#   BuildIntertwinerOptim has prohibitive cost (~3.7 years for one
#   T_h matrix at m = 5; see comment block in krr_spectral_characters.g).
#   A sparse / trace-only method is needed for m >= 5, tracked as a
#   follow-up.
#
# Run from the scripts/ directory:
#   gap -q -b -c 'Read("tests/test_krr_spectral_characters.g");'

SetInfoLevel(InfoWarning, 0);

Read("bw_lattice.g");
Read("em_construction.g");
Read("twisted_group_algebra.g");
Read("qforms_f2.g");
Read("defect_rep_minus_id.g");
Read("defect_rep_minus_id_optim.g");
Read("untwisted_modular_data.g");
Read("krr_spectral_characters.g");


# ---------------------------------------------------------------
# Helper: report PASS / FAIL on a boolean test.
# ---------------------------------------------------------------

testFailures := [];;

AssertOrLog := function(label, cond)
    if cond then
        Print("  PASS: ", label, "\n");
    else
        Print("  FAIL: ", label, "\n");
        Add(testFailures, label);
    fi;
end;;


# ---------------------------------------------------------------
# Test 1: m = 3 character match (K-4a-T4c m=3 anchor)
# ---------------------------------------------------------------
Print("\n=================================================================\n");
Print("  Test 1: m = 3 character match (K-4a-T4c anchor)\n");
Print("=================================================================\n");

t0 := Runtime();;
sc3 := BuildKRRSpectralCharacters(3);;
t1 := Runtime();;
Print("BuildKRRSpectralCharacters(3) built in ",
      (t1 - t0) / 1000., " s.\n");

# Summary: per-class character_match analysis.
totalNoFail := 0;;
totalUniqMatch := 0;;
totalClasses := Length(sc3.idx.classes);;
Print("\nPer-class character_match summary (", totalClasses, " classes):\n");
for i in [1..totalClasses] do
    em := sc3.character_match[i];;
    n_es := Length(em);;
    fail_count := Length(Filtered(em, x -> x.standard_irrep_idx = fail));;
    std_indices := List(em, x -> x.standard_irrep_idx);;
    nonfail := Filtered(std_indices, x -> x <> fail);;
    uniq := Length(Set(nonfail)) = Length(nonfail);;
    a := sc3.idx.reps[i];;
    is_minus_id := (a = -IdentityMat(2^3));;
    is_id := (a = IdentityMat(2^3));;
    if is_minus_id then
        marker := " [-I]    ";
    elif is_id then
        marker := " [id]    ";
    else
        marker := "         ";
    fi;
    Print("  class ", i, marker,
          ": #eigenspaces ", n_es,
          ", #fail ", fail_count,
          ", #unique std_idx ", Length(Set(nonfail)),
          "/", Length(nonfail),
          " (out of ", sc3.idx.num_irreps[i], " irreps in C_G(a))\n");
    if fail_count = 0 then
        totalNoFail := totalNoFail + 1;
    fi;
    if uniq then
        totalUniqMatch := totalUniqMatch + 1;
    fi;
od;

Print("\nClasses with no `fail` matches: ", totalNoFail,
      "/", totalClasses, "\n");
Print("Classes with all unique std indices: ", totalUniqMatch,
      "/", totalClasses, "\n");

test1Pass := (totalNoFail = totalClasses) and (totalUniqMatch = totalClasses);;
AssertOrLog("Test 1 (no fails, all unique matches at m=3)", test1Pass);

# Diagnostic: spell out the central class (-I) joint-eigenspace structure
# for inspection.
z_3 := -IdentityMat(2^3);;
i_central_diag := PositionProperty(sc3.idx.reps, r -> r = z_3);;
if i_central_diag <> fail then
    Print("\nCentral class -I diagnostics (class index ", i_central_diag, "):\n");
    Print("  Centraliser generators (count): ",
          Length(GeneratorsOfGroup(sc3.idx.centralisers[i_central_diag])), "\n");
    em_diag := sc3.character_match[i_central_diag];;
    cache_diag := sc3.eigenspace_cache[i_central_diag];;
    Print("  Joint eigenspaces (irrep_idx -> multiplicity, std_irrep_idx, eigenvalue tuple):\n");
    for j in [1..Length(em_diag)] do
        Print("    ", j, " -> mult=", cache_diag[j].multiplicity,
              ", std_irrep_idx=", em_diag[j].standard_irrep_idx,
              ", eigvals=", em_diag[j].eigenvalue_pattern, "\n");
    od;
fi;


# ---------------------------------------------------------------
# Test 2: Eigenvalue consistency
# ---------------------------------------------------------------
Print("\n=================================================================\n");
Print("  Test 2: Eigenvalue consistency on central class\n");
Print("=================================================================\n");

# Pick the central class a = -I.
G3 := sc3.group;;
z := -IdentityMat(2^3);;
i_central := PositionProperty(sc3.idx.reps, r -> r = z);;
if i_central = fail then
    Print("  WARNING: -I is not a class rep at m=3 (unusual).\n");
fi;

eigenvalConsistent := true;;
if i_central <> fail then
    em := sc3.character_match[i_central];;
    cache := sc3.eigenspace_cache[i_central];;
    Print("  Central class ", i_central, " has ",
          Length(em), " eigenspaces.\n");
    # Rebuild T_h matrices for the centraliser generators of the central
    # class (which is all of G).
    C := Centralizer(G3, z);;
    cent_gens := GeneratorsOfGroup(C);;
    T_gens := [];;
    n := 2^3;;
    k := 2^(3-1);;
    dim := 2^k;;
    idMat := IdentityMat(n);;
    for h in cent_gens do
        if h = idMat then
            Add(T_gens, IdentityMat(dim));
        else
            Add(T_gens, NormaliseIntertwiner(BuildIntertwinerOptim(h, 3), 3));
        fi;
    od;
    # For each eigenspace, check T_h * basis_vec = eigenvalue * basis_vec.
    nMismatch := 0;;
    nChecks := 0;;
    for irrep_idx in [1..Length(em)] do
        es := cache[irrep_idx];
        for j in [1..Length(T_gens)] do
            T := T_gens[j];
            ev := es.eigenvalues[j];
            for b in es.basis do
                # T * b (column-vec convention): b * T^T  (row times matrix).
                v := b * TransposedMat(T);
                nChecks := nChecks + 1;
                if v <> ev * b then
                    nMismatch := nMismatch + 1;
                    if nMismatch <= 3 then
                        Print("    MISMATCH: eigenspace ", irrep_idx,
                              ", gen ", j, ", basis row ",
                              "(differs from ", ev, " * basis)\n");
                    fi;
                fi;
            od;
        od;
    od;
    Print("  Eigenvalue consistency checks: ", nChecks - nMismatch,
          "/", nChecks, " pass.\n");
    if nMismatch > 0 then
        eigenvalConsistent := false;
    fi;
fi;

test2Pass := eigenvalConsistent;;
AssertOrLog("Test 2 (eigenvalue consistency)", test2Pass);


# ---------------------------------------------------------------
# Test 3: Character orthogonality (distinct eigenspaces have distinct
# eigenvalue tuples)
# ---------------------------------------------------------------
Print("\n=================================================================\n");
Print("  Test 3: Character orthogonality on central class\n");
Print("=================================================================\n");

orthogonal := true;;
if i_central <> fail then
    cache := sc3.eigenspace_cache[i_central];;
    if cache <> false then
        tuples := List(cache, es -> es.eigenvalues);;
        if Length(Set(tuples)) <> Length(tuples) then
            Print("  FAIL: duplicate eigenvalue tuples found.\n");
            orthogonal := false;
        else
            Print("  All ", Length(tuples),
                  " eigenvalue tuples are distinct.\n");
        fi;
    fi;
fi;

test3Pass := orthogonal;;
AssertOrLog("Test 3 (character orthogonality)", test3Pass);


# ---------------------------------------------------------------
# Test 4: Dim consistency
# ---------------------------------------------------------------
Print("\n=================================================================\n");
Print("  Test 4: dim sum = dim(W_a)\n");
Print("=================================================================\n");

dimConsistent := true;;
if i_central <> fail then
    cache := sc3.eigenspace_cache[i_central];;
    if cache <> false then
        dimSum := Sum(cache, es -> es.multiplicity);;
        expected := 2^(2^(3-1));;
        if dimSum <> expected then
            Print("  FAIL: dim sum = ", dimSum, ", expected ",
                  expected, "\n");
            dimConsistent := false;
        else
            Print("  dim sum = ", dimSum, " matches dim(W_a) = ",
                  expected, "\n");
        fi;
    fi;
fi;

test4Pass := dimConsistent;;
AssertOrLog("Test 4 (dim consistency)", test4Pass);


# ---------------------------------------------------------------
# Test 5: trace_on_W callable; trace_on_W(1, 1, identity) = mult
# ---------------------------------------------------------------
Print("\n=================================================================\n");
Print("  Test 5: trace_on_W(1, 1, identity) sanity\n");
Print("=================================================================\n");

idMat := IdentityMat(2^3);;
val := sc3.trace_on_W(1, 1, idMat);;
# The expected value is the multiplicity of the 1st eigenspace.
if sc3.eigenspace_cache[1] = false then
    # Non-central fallback: returns dimension of the 1st irrep of C_G(rep_1).
    expected := sc3.idx.irrep_dims[1][1];;
else
    expected := sc3.eigenspace_cache[1][1].multiplicity;;
fi;
Print("  trace_on_W(1, 1, identity) = ", val,
      ", expected ", expected, "\n");

test5Pass := val = expected;;
AssertOrLog("Test 5 (trace_on_W identity)", test5Pass);


# ---------------------------------------------------------------
# Summary
# ---------------------------------------------------------------
Print("\n=================================================================\n");
Print("  Summary\n");
Print("=================================================================\n");
Print("Test 1 (m=3 character match anchor):     ", test1Pass, "\n");
Print("Test 2 (eigenvalue consistency):         ", test2Pass, "\n");
Print("Test 3 (character orthogonality):        ", test3Pass, "\n");
Print("Test 4 (dim consistency):                ", test4Pass, "\n");
Print("Test 5 (trace_on_W identity sanity):     ", test5Pass, "\n");

allPass := test1Pass and test2Pass and test3Pass and test4Pass and test5Pass;;
Print("\nAll tests pass: ", allPass, "\n");

if allPass then
    Print("\nK-4a-T4c ACCEPTANCE: SPECTRAL TRACE_ON_W IS CORRECT AT m=3.\n");
else
    Print("\nK-4a-T4c FAILURE: ", Length(testFailures), " failure(s).\n");
    Print("Failing tests:\n");
    for f in testFailures do
        Print("  - ", f, "\n");
    od;
fi;

QUIT;
