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
# ----------------------------------------------------------------------
Print("\n=== (3) Tier-5 nu_2 at omega = 0 ===\n");
Print("  TODO — fill in nu_2 cross-check via fsi_wrapper.g after stub passes.\n");
Print("  Plan: at omega = 0, FSIAllAtClass at each conjugacy class g must\n");
Print("  reproduce the classical Frobenius-Schur indicator of the ordinary\n");
Print("  characters of C_G(g). For E_+(2) = SmallGroup(32, 49) at the\n");
Print("  identity class, ChiTable(E_+(2)) has 17 irreps (16 1-dim + 1 4-dim)\n");
Print("  giving the expected nu_2 multiset.\n");

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
