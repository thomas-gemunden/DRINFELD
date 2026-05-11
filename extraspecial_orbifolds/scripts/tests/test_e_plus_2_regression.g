# test_e_plus_2_regression.g — E_+(2) end-to-end regression suite.
#
# Issue #54 acceptance criteria:
#   * Tier-4: SNF kernel size = 2048 (cross-checked against brute-force
#             enumeration of all 4096 H^3 classes; persisted by A-2 in
#             computed/transgression/2/kernel.g).
#   * Tier-3: |Aut(N, T)| at m = 2 matches a one-time hand-computed reference.
#             [GATED — V-5c has not yet established E_+(2) ground truth.]
#   * Tier-5: nu_2 values consistent with the classical character-table
#             Frobenius-Schur formula at omega = 0.
#
# E_+(2) = ExtraspecialGroup(32, "+") = SmallGroup(32, 49).
# H^3(G; U(1)) has torsion [2,2,2,2,2,2,2,2,2,8], exponent 8, |H^3| = 4096.
# Per modular_data/32/49/3-cocycles.txt the number of Aut(G)-orbit reps of
# 3-cocycles is small (single orbit at order 0 cocycle is the trivial one).
#
# Run from anywhere (paths are absolute):
#   /opt/homebrew/bin/gap -q -b /Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-x3/extraspecial_orbifolds/scripts/tests/test_e_plus_2_regression.g
#
# Structure follows test_q8_regression.g (X-1, just merged).

# ----------------------------------------------------------------------
# Configuration: absolute paths.
# ----------------------------------------------------------------------
E2_WT_ROOT := "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-x3";;
E2_SCRIPTS := Concatenation(E2_WT_ROOT, "/extraspecial_orbifolds/scripts");;
E2_KERNEL_FILE := Concatenation(E2_WT_ROOT, "/computed/transgression/2/kernel.g");;

# ----------------------------------------------------------------------
# Test bookkeeping.
# ----------------------------------------------------------------------
E2_PASSES   := 0;;
E2_FAILURES := [];;

E2AssertEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
        E2_PASSES := E2_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Print("         expected: ", expected, "\n");
        Print("         got:      ", got, "\n");
        Add(E2_FAILURES, label);
    fi;
end;;

E2AssertTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
        E2_PASSES := E2_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Add(E2_FAILURES, label);
    fi;
end;;

# ----------------------------------------------------------------------
# (1) Tier-4: SNF kernel size = 2048 via persisted A-2 output.
# ----------------------------------------------------------------------
Print("\n=== (1) Tier-4 SNF kernel for E_+(2) ===\n");

# Locate kernel.g (worktrees share git but not computed/, so accept either
# worktree-local or main-tree path).
E2_KERNEL_CANDIDATES := [
    Concatenation(E2_WT_ROOT, "/computed/transgression/2/kernel.g"),
    "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD/computed/transgression/2/kernel.g"
];;
E2_KERNEL_FOUND := fail;;
for E2_P in E2_KERNEL_CANDIDATES do
    if IsExistingFile(E2_P) then
        E2_KERNEL_FOUND := E2_P;
        break;
    fi;
od;
E2AssertTrue("kernel.g exists in at least one searched location",
             E2_KERNEL_FOUND <> fail);
if E2_KERNEL_FOUND <> fail then
    Print("  loaded kernel from: ", E2_KERNEL_FOUND, "\n");
    E2_KERNEL_DATA := ReadAsFunction(E2_KERNEL_FOUND)();;
    E2AssertEqual("E_+(2) Tier-4 |ker Tr| = 2048",
                  E2_KERNEL_DATA.kernel_size, 2048);
    # Cross-check: Length(kernel_vecs) = kernel_size.
    E2AssertEqual("E_+(2) Tier-4 Length(kernel_vecs) = kernel_size",
                  Length(E2_KERNEL_DATA.kernel_vecs),
                  E2_KERNEL_DATA.kernel_size);
    # Cross-check: torsion = [2,2,2,2,2,2,2,2,2,8].
    E2AssertEqual("E_+(2) H^3 torsion = [2,2,2,2,2,2,2,2,2,8]",
                  E2_KERNEL_DATA.torsion,
                  [2, 2, 2, 2, 2, 2, 2, 2, 2, 8]);
    E2AssertEqual("E_+(2) H^3 exponent = 8",
                  E2_KERNEL_DATA.exponent, 8);
    # Cross-check: each kernel vec is in the expected range.
    E2_ALL_VEC_OK := ForAll(E2_KERNEL_DATA.kernel_vecs, v ->
        Length(v) = 10 and ForAll([1..10], i ->
            v[i] >= 0 and v[i] < E2_KERNEL_DATA.torsion[i]));;
    E2AssertTrue("E_+(2) Tier-4 kernel vecs all in correct range",
                 E2_ALL_VEC_OK);
    # The zero vec must be in the kernel.
    E2AssertTrue("E_+(2) Tier-4 zero vec in kernel",
                 ListWithIdenticalEntries(10, 0) in E2_KERNEL_DATA.kernel_vecs);
fi;

# ----------------------------------------------------------------------
# (2) Tier-3 |Aut(N, T)| at m = 2 — GATED.
# ----------------------------------------------------------------------
Print("\n=== (2) Tier-3 |Aut(N, T)| at m = 2 (GATED) ===\n");
Print("  SKIP — V-5c has not yet established E_+(2) ground truth.\n");
Print("  Filed as follow-up: re-enable once V-5c hand-computes |Aut(N, T)|\n");
Print("  for E_+(2) at m = 2.\n");

# ----------------------------------------------------------------------
# (3) Tier-5 nu_2 at omega = 0 — classical FS cross-check.
#
# At omega = 0 the projective characters returned by ProjectiveCharactersDirect
# at C_G(g) split as Irr(C) ⊗ E(exp)-eigenchar of the central Z/exp fibre, so
# the multiset of nu_2 values for the 2 x rank(Irr(C)) projective characters
# reduces to the multiset of classical FS indicators of Irr(C) — multiplied
# by appropriate central-character phases at non-identity classes. We compare
# multisets directly. Reference pattern: test_q8_regression.g §3.
# ----------------------------------------------------------------------
Print("\n=== (3) Tier-5 nu_2 at omega = 0 ===\n");

LoadPackage("hap");;
LoadPackage("io");;

# fsi_wrapper.g's relative-path search for src/universal_coefficients.g
# requires CWD to contain a src/ subdirectory; the worktree root has it.
# ChangeDirectoryCurrent is a GAP-internal cwd change, not a shell cd.
E2_WT_ROOT_FOR_FSI := fail;;
for E2_CAND in [ "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-x3b",
                 "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD" ] do
    if IsExistingFile(Concatenation(E2_CAND, "/src/universal_coefficients.g")) then
        E2_WT_ROOT_FOR_FSI := E2_CAND;
        break;
    fi;
od;
E2AssertTrue("worktree root with src/universal_coefficients.g located",
             E2_WT_ROOT_FOR_FSI <> fail);

if E2_WT_ROOT_FOR_FSI <> fail then
    ChangeDirectoryCurrent(E2_WT_ROOT_FOR_FSI);
    Read(Concatenation(E2_WT_ROOT_FOR_FSI,
                       "/extraspecial_orbifolds/scripts/fsi_wrapper.g"));

    # Build E_+(2) and the trivial-cocycle FSI context.
    E2_G := SmallGroup(32, 49);;
    E2_R := ResolutionFiniteGroup(E2_G, 4);;
    E2_FSI_ZERO_VEC := ListWithIdenticalEntries(E2_R!.dimension(3), 0);;
    E2_FSI_CTX := FSIContext(E2_G, E2_FSI_ZERO_VEC);;
    Print("  FSI context built for E_+(2).\n");
    Print("  H^3 exponent = ", E2_FSI_CTX.exp, ", group exponent = ",
          E2_FSI_CTX.groupExp, ".\n");

    # 17 conjugacy classes.
    E2_CC := List(ConjugacyClasses(E2_G), Representative);;
    E2AssertEqual("E_+(2) has 17 conjugacy classes",
                  Length(E2_CC), 17);

    # ------------------------------------------------------------------
    # (3a) Per-class consistency: at omega = 0, the FSI multiset at g
    # has length 2 * Nirr(C_G(g)) (one for each chi-and-central-character
    # pair). The classical FS indicators on Irr(C) form a sub-multiset
    # that appears (1 * paired) inside FSI multiset; the remaining
    # entries correspond to the "twisted" central characters and equal
    # 0 at any chi with non-real central character.
    #
    # The decisive cross-check at omega = 0 is the IDENTITY class: C = G,
    # the central extension splits as G x Z/exp, and FSI multiset
    # restricted to the "trivial-central" projective characters equals
    # the classical FS multiset on Irr(G).
    # ------------------------------------------------------------------
    Print("\n(3a) ν_2 at the identity class for E_+(2).\n");
    E2_FSI_G1 := FSIAllAtClass(E2_FSI_CTX, One(E2_G), 2);;
    Print("  total ν_2 multiset at g=1: ", Collected(E2_FSI_G1.nu), "\n");
    Print("  ν_2 entry count: ", Length(E2_FSI_G1.nu), "\n");

    # Classical FS indicators on Irr(E_+(2)).
    E2_CT_G := CharacterTable(E2_G);;
    E2_CLASSICAL_FS := Indicator(E2_CT_G, 2);;
    E2_CLASSICAL_FS := List(E2_CLASSICAL_FS, x -> Int(x));;
    Print("  classical FS on Irr(G) (17 irreps): ",
          Collected(E2_CLASSICAL_FS), "\n");
    # E_+(2) = central product D_8 o D_8 has 17 irreps, all of which are
    # real (FS = +1) — unlike Q_8 (which has a quaternionic 2-dim irrep,
    # FS = -1), E_+(2)'s 4-dim faithful representation is real because the
    # central product of two real reps stays real. So classical FS multiset
    # is 17 x [+1].
    E2AssertEqual("classical FS multiset on Irr(E_+(2)) = 17 x [+1]",
                  Collected(E2_CLASSICAL_FS),
                  Collected(ListWithIdenticalEntries(17, 1)));

    # At omega = 0, the FSI multiset at g = 1 equals the classical FS
    # multiset on Irr(G), since alpha = 0 makes ProjectiveCharactersDirect
    # at C = G return characters in bijection with Irr(G) — the trivial
    # central character splits the central extension.
    E2AssertEqual("ν_2 multiset at g=1 = classical FS multiset",
                  Collected(E2_FSI_G1.nu),
                  Collected(E2_CLASSICAL_FS));

    # ------------------------------------------------------------------
    # (3b) ν_n for gcd(n, |G|) = 1: only trivial chi contributes.
    # For E_+(2), |G| = 32 = 2^5, so any odd n is coprime. By the same
    # FS-theory argument as Q_8, ν_n = [1, 0, 0, ..., 0] (1 trivial-chi
    # contribution, rest zero) at the identity class.
    # ------------------------------------------------------------------
    Print("\n(3b) ν_n for n in {3, 5, 7} at the identity class.\n");
    for E2_N in [3, 5, 7] do
        E2_FSI_N := FSIAllAtClass(E2_FSI_CTX, One(E2_G), E2_N);;
        E2_NU_COLLECTED := Collected(E2_FSI_N.nu);;
        Print("  ν_", E2_N, " at g=1: ", E2_NU_COLLECTED, "\n");
        # Trivial character contributes 1; everything else contributes 0.
        E2AssertEqual(Concatenation("ν_", String(E2_N),
                                    " at g=1: number of nonzero entries = 1"),
                      Number(E2_FSI_N.nu, v -> v <> 0), 1);
        E2AssertTrue(Concatenation("ν_", String(E2_N),
                                   " at g=1: the unique nonzero value is 1"),
                     1 in E2_FSI_N.nu);
    od;

    # ------------------------------------------------------------------
    # (3c) Total rank of Z(Vec_{E_+(2)}) at omega = 0.
    # Sum over conjugacy classes of |Irr(C_G(g))| should equal the
    # number of simple objects in D(E_+(2)). Per Lusztig and the
    # general formula for D(G), this equals the number of pairs
    # (g, chi) with [g] in Conj(G) and chi in Irr(C_G(g)).
    # ------------------------------------------------------------------
    Print("\n(3c) Total rank Z(Vec_{E_+(2)}) at omega = 0.\n");
    E2_TOTAL_RANK := 0;;
    for E2_GREP in E2_CC do
        E2_FSI_AT := FSIAllAtClass(E2_FSI_CTX, E2_GREP, 2);;
        E2_TOTAL_RANK := E2_TOTAL_RANK + Length(E2_FSI_AT.nu);
    od;
    # At omega = 0, FSIAllAtClass returns exactly Nirr(C) entries per
    # class (the projective characters with trivial central character).
    # So the sum-of-Nirr-over-classes equals the total FSI entry count.
    E2_CLASSICAL_RANK := Sum(E2_CC,
        g -> Length(Irr(Centralizer(E2_G, g))));;
    Print("  classical sum_[g] |Irr(C_G(g))| = ", E2_CLASSICAL_RANK, "\n");
    Print("  FSI total ν_2 entry count = ", E2_TOTAL_RANK, "\n");
    E2AssertEqual("FSI total count = classical rank (= rank Z(Vec_G) at omega=0)",
                  E2_TOTAL_RANK, E2_CLASSICAL_RANK);
    E2AssertEqual("rank Z(Vec_{E_+(2)}) at omega = 0 is 184",
                  E2_CLASSICAL_RANK, 184);
fi;

# ----------------------------------------------------------------------
# Final report.
# ----------------------------------------------------------------------
Print("\n=== Final summary ===\n");
Print("  passes:   ", E2_PASSES, "\n");
Print("  failures: ", Length(E2_FAILURES), "\n");
if Length(E2_FAILURES) = 0 then
    Print("\ntest_e_plus_2_regression: PASS\n");
else
    Print("\ntest_e_plus_2_regression: FAIL (", Length(E2_FAILURES), "):\n");
    for E2_FAILURE in E2_FAILURES do
        Print("  - ", E2_FAILURE, "\n");
    od;
fi;

QUIT;
