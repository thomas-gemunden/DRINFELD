# test_q8_regression.g — Q_8 regression suite.
#
# Issue #52 acceptance criteria:
#   (V-5c) |Aut(N^0, T^0)|       = 6   (Q_8 trivial cocycle  — modular_data/8/4/1.txt)
#   (V-5c) |Aut(N^{ω_4}, T^{ω_4})| = 24 (Q_8 order-2 cocycle — modular_data/8/4/2.txt)
#   (V-2)  S^{ω_4} on disk reproducible via STwistedCentralEntry byte-for-byte
#          on central rows.
#   (V-3)  ν_n values on Q_8 (omega = 0) match published [MN05]/classical
#          Frobenius–Schur values:
#            * ν_2 at identity-class projective characters = [1, 1, 1, 1, -1]
#              (Q_8 has 4 real-type and 1 quaternionic-type irrep).
#            * ν_2 at the centre class {-1} is identical (centraliser is Q_8).
#            * ν_2 at each order-4 class = [1, 1, -1, -1] (centraliser ≅ Z/4,
#              2 real + 2 complex irreps).
#            * ν_n at identity for n ∈ {3, 5, 7} = [1, 0, 0, 0, 0] (only the
#              trivial character contributes when m is coprime to |G|).
#
# Cocycle indexing convention (from q8_extension_type/writeup.md and the
# AutomorphismOrbits enumeration in modular_data/8/4/3-cocycles.txt):
#   1.txt: cocycle vector [0,0,0] → H³ class [0,0]      = trivial cocycle.
#   2.txt: cocycle vector [0,4,0] → H³ class [0,4] of order 2 = ω_4.
#
# Run:
#   /opt/homebrew/bin/gap -q -b /Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-x1/extraspecial_orbifolds/scripts/tests/test_q8_regression.g
# All paths below are absolute; this script does NOT chdir except where
# fsi_wrapper.g's relative-path search forces it (it's a GAP-internal
# ChangeDirectoryCurrent, not a shell `cd`).

# ----------------------------------------------------------------------
# Configuration: absolute paths.
# ----------------------------------------------------------------------
Q8_WT_ROOT := "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-x1";;
Q8_SCRIPTS := Concatenation(Q8_WT_ROOT, "/extraspecial_orbifolds/scripts");;
Q8_MD_ROOT := "/Users/thomasgemunden/Projects/group_cohomology/modular_data";;
Q8_DISK_TRIV  := Concatenation(Q8_MD_ROOT, "/8/4/1.txt");;
Q8_DISK_OMEGA4 := Concatenation(Q8_MD_ROOT, "/8/4/2.txt");;

# ----------------------------------------------------------------------
# Test bookkeeping.
# ----------------------------------------------------------------------
Q8_PASSES   := 0;;
Q8_FAILURES := [];;

Q8AssertEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
        Q8_PASSES := Q8_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Print("         expected: ", expected, "\n");
        Print("         got:      ", got, "\n");
        Add(Q8_FAILURES, label);
    fi;
end;;

Q8AssertTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
        Q8_PASSES := Q8_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Add(Q8_FAILURES, label);
    fi;
end;;

Q8LoadDisk := function(path)
    local f;
    f := ReadAsFunction(path);
    if f = fail then
        Error("Q8LoadDisk: cannot ReadAsFunction(", path, ").");
    fi;
    return f();
end;;

# ----------------------------------------------------------------------
# Load dependencies.
#
# IMPORTANT ordering constraint (per CLAUDE.md): `modular_data.g` and
# `universal_coefficients.g` each install their own `ProjectiveCharacters`
# global with INCOMPATIBLE signatures:
#   * modular_data.g:        ProjectiveCharacters(CgExtGens, CgExtPc, iso)
#   * universal_coefficients.g: ProjectiveCharacters(G, alpha, o)
# Reading both in the same session lets the second clobber the first,
# which breaks GenerateSimpleObjects in modular_data.g (called by V-2 in
# section 2 below).
#
# Workaround: load modular_data.g for sections (1) and (2), then load
# fsi_wrapper.g for section (3). The wrapper's ProjectiveCharacters
# override is fine for FSI (which is the only place section 3 uses
# ProjectiveCharacters) — we simply make sure section 2 runs first.
#
# We also load fsi_wrapper.g via ChangeDirectoryCurrent because its
# src/universal_coefficients.g search uses relative paths.
# (This is a GAP-internal cwd change, not a shell `cd`.)
# ----------------------------------------------------------------------
LoadPackage("hap");;
LoadPackage("io");;

# V-5c: Aut(N, T) engine (and its prerequisites V-5a, V-5b).
Read(Concatenation(Q8_SCRIPTS, "/aut_nt_partition.g"));
Read(Concatenation(Q8_SCRIPTS, "/aut_nt_refine.g"));
Read(Concatenation(Q8_SCRIPTS, "/aut_nt.g"));

# V-1: ε_ω phase callable. (Already loaded by V-2 below, but explicit.)
Read(Concatenation(Q8_SCRIPTS, "/epsilon_omega.g"));

# V-2: S^ω closed-form central-row entry.
Read(Concatenation(Q8_SCRIPTS, "/s_twisted_central.g"));

# modular_data.g machinery (StandardCocycle, GenerateSimpleObjects,
# UniversalCoefficientsTheorem, ConjugacyClasses helpers, etc.).
# Loads its own ProjectiveCharacters(CgExtGens, CgExtPc, iso); we will
# load fsi_wrapper.g LATER (just before section 3) to avoid clobbering.
Read(Concatenation(Q8_WT_ROOT, "/src/modular_data.g"));

# ----------------------------------------------------------------------
# (1) |Aut(N, T)| regression — trivial cocycle and ω_4.
# ----------------------------------------------------------------------
Print("\n=== (1) Aut(N, T) regression on Q_8 ===\n");

Print("\n(1a) Trivial cocycle (modular_data/8/4/1.txt) → |Aut(N, T)| = 6.\n");
q8_triv_data := Q8LoadDisk(Q8_DISK_TRIV);;
Q8AssertEqual("Q_8 trivial: rank", Length(q8_triv_data.T), 22);

q8_triv_S  := q8_triv_data.S;;
q8_triv_T  := q8_triv_data.T;;
q8_triv_QD := QuantumDimensionsFromS(q8_triv_S);;
q8_triv_N  := FusionCoefficientsFromS(q8_triv_S);;

Q8_T0 := Runtime();;
q8_triv_aut := AutNT(q8_triv_N, q8_triv_T, q8_triv_QD);;
Q8_DT := Runtime() - Q8_T0;;
Print("  Q_8 trivial: |Aut(N, T)| = ", q8_triv_aut.order,
      " (", Length(q8_triv_aut.generators), " gens, ", Q8_DT, "ms)\n");
Q8AssertEqual("Q_8 trivial: |Aut(N, T)|", q8_triv_aut.order, 6);

# Sanity: every generator preserves T and N.
q8_triv_t_ok := ForAll(q8_triv_aut.generators,
                       sigma -> ForAll([1..22], i -> q8_triv_T[sigma[i]] = q8_triv_T[i]));;
Q8AssertTrue("Q_8 trivial: generators preserve T", q8_triv_t_ok);

q8_triv_n_ok := ForAll(q8_triv_aut.generators,
                       sigma -> IsAutomorphismCandidate(sigma, q8_triv_N));;
Q8AssertTrue("Q_8 trivial: generators preserve N", q8_triv_n_ok);

# Subgroup generated by returned generators has the claimed order.
if Length(q8_triv_aut.generators) > 0 then
    q8_triv_grp := Group(List(q8_triv_aut.generators, PermList));;
    Q8AssertEqual("Q_8 trivial: <generators> order = |Aut(N, T)|",
                  Size(q8_triv_grp), q8_triv_aut.order);
fi;

Print("\n(1b) ω_4 (= order-2 cocycle, modular_data/8/4/2.txt) → |Aut(N, T)| = 24.\n");
q8_w4_data := Q8LoadDisk(Q8_DISK_OMEGA4);;
Q8AssertEqual("Q_8 ω_4: rank", Length(q8_w4_data.T), 22);

q8_w4_S  := q8_w4_data.S;;
q8_w4_T  := q8_w4_data.T;;
q8_w4_QD := QuantumDimensionsFromS(q8_w4_S);;
q8_w4_N  := FusionCoefficientsFromS(q8_w4_S);;

Q8_T0 := Runtime();;
q8_w4_aut := AutNT(q8_w4_N, q8_w4_T, q8_w4_QD);;
Q8_DT := Runtime() - Q8_T0;;
Print("  Q_8 ω_4: |Aut(N, T)| = ", q8_w4_aut.order,
      " (", Length(q8_w4_aut.generators), " gens, ", Q8_DT, "ms)\n");
Q8AssertEqual("Q_8 ω_4: |Aut(N, T)|", q8_w4_aut.order, 24);

q8_w4_t_ok := ForAll(q8_w4_aut.generators,
                     sigma -> ForAll([1..22], i -> q8_w4_T[sigma[i]] = q8_w4_T[i]));;
Q8AssertTrue("Q_8 ω_4: generators preserve T", q8_w4_t_ok);

q8_w4_n_ok := ForAll(q8_w4_aut.generators,
                     sigma -> IsAutomorphismCandidate(sigma, q8_w4_N));;
Q8AssertTrue("Q_8 ω_4: generators preserve N", q8_w4_n_ok);

if Length(q8_w4_aut.generators) > 0 then
    q8_w4_grp := Group(List(q8_w4_aut.generators, PermList));;
    Q8AssertEqual("Q_8 ω_4: <generators> order = |Aut(N, T)|",
                  Size(q8_w4_grp), q8_w4_aut.order);
fi;

# Cross-check the q8_extension_type writeup's claim that |Aut| differs.
Q8AssertTrue("Q_8: |Aut(N^0, T^0)| ≠ |Aut(N^{ω_4}, T^{ω_4})|",
             q8_triv_aut.order <> q8_w4_aut.order);

# ----------------------------------------------------------------------
# (2) S^{ω_4} reproducibility via V-2 (central rows, byte-for-byte).
# ----------------------------------------------------------------------
Print("\n=== (2) S^{ω_4} central rows reproduced via STwistedCentralEntry ===\n");

# Helpers lifted from test_s_twisted_central.g (the V-2 acceptance test);
# we need the §6.2 full S to determine the per-block permutation σ
# matching our enumeration of simples to the disk enumeration.
Q8_ComputeSEntryViaEpsilonFull := function(G, omega, val, exponent, gData, hData)
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
            if a * b = b * a then
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

Q8_ComputeFullSMatrix := function(G, omega, val, exponent, simples)
    local n, S, i, j;
    n := Length(simples);
    S := NullMat(n, n);
    for i in [1..n] do
        for j in [1..n] do
            S[i][j] := Q8_ComputeSEntryViaEpsilonFull(G, omega, val,
                                                     exponent, simples[i],
                                                     simples[j]);
        od;
    od;
    return S;
end;;

# σ recovery from test_s_twisted_central.g, specialised to Q_8/ω_4.
# Per the q8_extension_type writeup the simples partition into 5 g-classes
# (identity, centre, three order-4 classes); for ω_4 the T-eigenvalues
# inside class block [6..9] and [10..13] may have been permuted by our
# (deterministic) enumeration vs the disk enumeration.
Q8_FindBlockPermutation := function(S_computed, S_disk, T_computed, T_disk)
    local n, sigma, perm_options, perm4, S_perm, i, j;
    n := Length(S_disk);
    perm_options := function(disk_pos_range, comp_pos_range)
        return List(disk_pos_range, i ->
            First(comp_pos_range, j -> T_computed[j] = T_disk[i]));
    end;
    sigma := [1, 2, 3, 4, 5];
    Append(sigma, perm_options([6..9],  [6..9]));
    Append(sigma, perm_options([10..13],[10..13]));
    Append(sigma, [14, 15, 16, 17]);
    Add(sigma, 18);
    Append(sigma, perm_options([19..22],[19..22]));
    # Block [14..17] (centre-class non-quaternionic) requires explicit
    # backtracking over permutations: T is identically 1 there.
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

Print("\n(2a) Rebuild ω_4 from cocycle vector [0, 4, 0].\n");
Q8_G    := SmallGroup(8, 4);;
Q8_R    := ResolutionFiniteGroup(Q8_G, 4);;
Q8_K    := TensorWithIntegers(Q8_R);;
Q8_UCT  := UniversalCoefficientsTheorem(Q8_K, 3);;

# The orbit-rep hom vector for ω_4 is [0, 4, 0]; lift to a cocycle vector.
Q8_OMEGA4_VEC := Q8_UCT.lift * [0, 4, 0];;
Q8_VAL        := Gcd(Gcd(Q8_OMEGA4_VEC), Q8_UCT.exponent);;
Q8_EXPONENT   := Q8_UCT.exponent / Q8_VAL;;
Q8_OMEGA      := StandardCocycle(Q8_R, Q8_OMEGA4_VEC, 3, Q8_UCT.exponent);;
Q8_M_OMEGA    := Q8_EXPONENT * Q8_VAL;;
Print("  cocycle: vec = ", Q8_OMEGA4_VEC, ", val = ", Q8_VAL,
      ", exponent = ", Q8_EXPONENT, ", m_omega = ", Q8_M_OMEGA, "\n");
Q8AssertEqual("Q_8 ω_4: UCT exponent = 8", Q8_UCT.exponent, 8);

Print("\n(2b) Generate simples, build full computed S, find σ.\n");
Q8_simples_data := GenerateSimpleObjects(Q8_G, Q8_OMEGA, Q8_VAL, Q8_EXPONENT);;
Q8_simples      := Q8_simples_data.Simp;;
Q8_N_SIMPLES    := Length(Q8_simples);;
Q8AssertEqual("Q_8 ω_4: simple-object count matches disk",
              Q8_N_SIMPLES, Length(q8_w4_S));

Q8_S_DISK := q8_w4_S;;
Q8_T_DISK := q8_w4_T;;

Q8_S_COMPUTED := Q8_ComputeFullSMatrix(Q8_G, Q8_OMEGA, Q8_VAL, Q8_EXPONENT,
                                       Q8_simples);;
Q8_T_COMPUTED := List(Q8_simples,
    s -> LookupDictionary(s.character, s.representative) / s.dimension);;
Q8AssertTrue("Q_8 ω_4: T-multisets agree across enumerations",
             AsSortedList(Q8_T_DISK) = AsSortedList(Q8_T_COMPUTED));

Q8_SIGMA := Q8_FindBlockPermutation(Q8_S_COMPUTED, Q8_S_DISK,
                                    Q8_T_COMPUTED, Q8_T_DISK);;
Q8AssertTrue("Q_8 ω_4: per-block σ aligning computed S to disk S exists",
             Q8_SIGMA <> fail);
if Q8_SIGMA <> fail then
    Print("  σ: ", Q8_SIGMA, "\n");
fi;

Print("\n(2c) For every central-row entry, V-2 closed form = disk entry.\n");
# "Central row" = a row whose g1 (the chosen conjugacy class rep) is
# central in Q_8. Q_8 has centre {1, -1}, so central simples are exactly
# those above the identity class (5 simples: dims 1,1,1,1,2) and above
# the centre class (5 simples: dims 1,1,1,1,2). After σ, in disk
# numbering these are simples 1..5 and 14..18.
if Q8_SIGMA <> fail then
    Q8_CENTRAL_DISK := Filtered([1..Q8_N_SIMPLES], i ->
        IsCentral(Q8_G, Q8_simples[Q8_SIGMA[i]].representative));;
    Print("  central simples in disk numbering: ", Q8_CENTRAL_DISK, "\n");
    Q8AssertEqual("Q_8 ω_4: 10 central simples on disk",
                  Length(Q8_CENTRAL_DISK), 10);

    # Closure builder: bind the simple via function-argument to avoid
    # by-reference capture pitfalls (and to silence the unbound-global
    # warnings GAP emits for the would-be free variables inside a raw
    # function literal at the top level).
    Q8_MkChi := function(simp)
        return function(x)
            return LookupDictionary(simp.character, x);
        end;
    end;;
    # Every (i_disk, j_disk) with i_disk ∈ central simples — byte-for-byte.
    Q8_MISMATCHES := 0;;
    Q8_CHECKED    := 0;;
    for Q8_I_DISK in Q8_CENTRAL_DISK do
        for Q8_J_DISK in [1..Q8_N_SIMPLES] do
            Q8_I_COMP := Q8_SIGMA[Q8_I_DISK];
            Q8_J_COMP := Q8_SIGMA[Q8_J_DISK];
            Q8_SIMP_I := Q8_simples[Q8_I_COMP];
            Q8_SIMP_J := Q8_simples[Q8_J_COMP];
            Q8_G1 := Q8_SIMP_I.representative;
            Q8_G2 := Q8_SIMP_J.representative;
            # χ1 = full character of G; χ2 = character of C_G(g2).
            Q8_CHI1 := Q8_MkChi(Q8_SIMP_I);
            Q8_CHI2 := Q8_MkChi(Q8_SIMP_J);
            Q8_GOT  := STwistedCentralEntry(Q8_G, Q8_OMEGA, Q8_M_OMEGA,
                                            Q8_G1, Q8_CHI1, Q8_G2, Q8_CHI2);
            Q8_WANT := Q8_S_DISK[Q8_I_DISK][Q8_J_DISK];
            if Q8_GOT <> Q8_WANT then
                Q8_MISMATCHES := Q8_MISMATCHES + 1;
                if Q8_MISMATCHES <= 5 then
                    Print("    MISMATCH at disk-(", Q8_I_DISK, ", ", Q8_J_DISK,
                          "): got ", Q8_GOT, ", disk ", Q8_WANT, "\n");
                    Print("      g1 = ", Q8_G1, ", g2 = ", Q8_G2, "\n");
                fi;
            else
                Q8_CHECKED := Q8_CHECKED + 1;
            fi;
        od;
    od;
    Print("  checked ", Q8_CHECKED, " entries, ", Q8_MISMATCHES,
          " mismatches.\n");
    Q8AssertEqual("Q_8 ω_4: V-2 closed form matches disk byte-for-byte on central rows",
                  Q8_MISMATCHES, 0);
    # And we should have checked exactly 10 * 22 = 220 entries.
    Q8AssertEqual("Q_8 ω_4: 10 * 22 = 220 central-row entries checked",
                  Q8_CHECKED, 10 * Q8_N_SIMPLES);
fi;

# ----------------------------------------------------------------------
# (3) ν_n FSI values on Q_8 (omega = 0).
# ----------------------------------------------------------------------
Print("\n=== (3) FSI ν_n values on Z(Vec_{Q_8}) (omega = 0) ===\n");

# Load FSI wrapper now — AFTER sections (1) and (2) so its override of
# ProjectiveCharacters does not break GenerateSimpleObjects. The wrapper's
# relative-path search for src/universal_coefficients.g requires the cwd
# to contain a src/ subdirectory; chdir-ing into the worktree root via
# ChangeDirectoryCurrent (a GAP-internal call) is harmless because all
# subsequent Read calls in this script use absolute paths.
Print("  (loading fsi_wrapper.g — expected to emit syntax warnings/errors\n");
Print("   from broken parts of universal_coefficients.g that the wrapper\n");
Print("   overrides; these are NOT failures of this test.)\n");
ChangeDirectoryCurrent(Q8_WT_ROOT);
Read(Concatenation(Q8_SCRIPTS, "/fsi_wrapper.g"));

# Build the trivial-cocycle FSI context.
Q8_FSI_ZERO_VEC := ListWithIdenticalEntries(Q8_R!.dimension(3), 0);;
Q8_FSI_CTX      := FSIContext(Q8_G, Q8_FSI_ZERO_VEC);;

Print("\n(3a) ν_2 at the identity class.\n");
# At g = 1, the projective characters of C_G(1) = G are the *ordinary*
# characters of Q_8. Classical Frobenius–Schur theory: 4 real (ν_2 = +1)
# + 1 quaternionic (ν_2 = -1). This is the published value going back to
# Frobenius–Schur 1906 / [MN05] / Mason–Ng 2005.
Q8_FSI_G1 := FSIAllAtClass(Q8_FSI_CTX, One(Q8_G), 2);;
Print("  ν_2 at g=1: ", Q8_FSI_G1.nu, "\n");
Q8AssertEqual("ν_2 at g=1 (multiset) matches classical [+1,+1,+1,+1,-1]",
              Collected(Q8_FSI_G1.nu), Collected([1, 1, 1, 1, -1]));

# Dimensions sanity: 1, 1, 1, 1, 2.
Q8_FSI_DIMS := List(Q8_FSI_G1.proj!.table,
                    chi -> One(Q8_FSI_G1.proj!.Gaa)^chi);;
Q8AssertEqual("dim multiset at g=1 matches [1,1,1,1,2]",
              Collected(Q8_FSI_DIMS), Collected([1, 1, 1, 1, 2]));

Print("\n(3b) ν_2 at the centre class {-1}.\n");
# C_G(-1) = G, so the multiset is the same as at the identity.
Q8_CC := List(ConjugacyClasses(Q8_G), Representative);;
# Find the order-2 (= centre {-1}) class rep.
Q8_MINUS1 := First(Q8_CC, g -> Order(g) = 2);;
Q8AssertTrue("found centre class rep g = -1 (order 2)",
             Q8_MINUS1 <> fail);
if Q8_MINUS1 <> fail then
    Q8_FSI_M1 := FSIAllAtClass(Q8_FSI_CTX, Q8_MINUS1, 2);;
    Print("  ν_2 at g=-1: ", Q8_FSI_M1.nu, "\n");
    Q8AssertEqual("ν_2 at g=-1 (multiset) = [+1,+1,+1,+1,-1]",
                  Collected(Q8_FSI_M1.nu), Collected([1, 1, 1, 1, -1]));
fi;

Print("\n(3c) ν_2 at each order-4 class.\n");
# Centraliser of an order-4 element in Q_8 is the cyclic group <g> ≅ Z/4,
# which has 4 1-dim characters: 2 real (1, χ where χ^2 = 1) and 2 complex
# conjugate pairs. Hence ν_2 multiset = [+1, +1, -1, -1].
Q8_ORD4 := Filtered(Q8_CC, g -> Order(g) = 4);;
Q8AssertEqual("Q_8 has exactly 3 order-4 conjugacy classes",
              Length(Q8_ORD4), 3);
for Q8_G4 in Q8_ORD4 do
    Q8_FSI_O4 := FSIAllAtClass(Q8_FSI_CTX, Q8_G4, 2);;
    Print("  ν_2 at order-4 g = ", Q8_G4, ": ", Q8_FSI_O4.nu, "\n");
    Q8AssertEqual(Concatenation("ν_2 at order-4 class g=",
                                String(Q8_G4),
                                " (multiset) = [+1,+1,-1,-1]"),
                  Collected(Q8_FSI_O4.nu),
                  Collected([1, 1, -1, -1]));
od;

Print("\n(3d) ν_n for n ∈ {3, 5, 7} at the identity class.\n");
# For gcd(n, |G|) = 1, ν_n is nontrivial only on the trivial character;
# explicitly ν_n(χ) = (1/|G|) Σ_{g ∈ G} χ(g^n). Since x ↦ x^n is a
# bijection on G when gcd(n, |G|) = 1, this is (1/|G|) Σ χ(g) = δ_{χ,1}.
# So ν_n = [1, 0, 0, 0, 0].
for Q8_N in [3, 5, 7] do
    Q8_FSI_N := FSIAllAtClass(Q8_FSI_CTX, One(Q8_G), Q8_N);;
    Print("  ν_", Q8_N, " at g=1: ", Q8_FSI_N.nu, "\n");
    Q8AssertEqual(Concatenation("ν_", String(Q8_N),
                                " at g=1 (multiset) = [1,0,0,0,0]"),
                  Collected(Q8_FSI_N.nu),
                  Collected([1, 0, 0, 0, 0]));
od;

Print("\n(3e) Total rank of Z(Vec_{Q_8}) at omega = 0 is 22.\n");
Q8_TOTAL_RANK := 0;;
for Q8_GG in Q8_CC do
    Q8_FSI_TOT := FSIAllAtClass(Q8_FSI_CTX, Q8_GG, 2);;
    Q8_TOTAL_RANK := Q8_TOTAL_RANK + Length(Q8_FSI_TOT.nu);
od;
Print("  total rank: ", Q8_TOTAL_RANK, "\n");
Q8AssertEqual("Z(Vec_{Q_8}) total rank at omega=0 = 22",
              Q8_TOTAL_RANK, 22);

# ----------------------------------------------------------------------
# Final report.
# ----------------------------------------------------------------------
Print("\n=== Final summary ===\n");
Print("  passes:   ", Q8_PASSES, "\n");
Print("  failures: ", Length(Q8_FAILURES), "\n");
if Length(Q8_FAILURES) = 0 then
    Print("\ntest_q8_regression: PASS\n");
else
    Print("\ntest_q8_regression: FAIL (", Length(Q8_FAILURES), "):\n");
    for Q8_FAILURE in Q8_FAILURES do
        Print("  - ", Q8_FAILURE, "\n");
    od;
fi;

QUIT;
