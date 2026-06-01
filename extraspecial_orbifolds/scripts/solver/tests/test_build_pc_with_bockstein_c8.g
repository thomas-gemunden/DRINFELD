# test_build_pc_with_bockstein_c8.g — unit test for the C-8 fix in
# BuildPCWithBockstein (transgression_matrix_reduced.g, audit #396).
#
# Goal: verify that the Bockstein-image row block in P_C.M_aug_T_full
# (rows r_base+1 .. r_base+r_bockstein) matches the reference value
# computed by lifting img_rows from GF(2) to integers and scaling by
# exp/2. This is the math the new IntVecFFE-based path computes
# directly; the test pins the row vectors so the C-8 refactor cannot
# silently regress.
#
# Path constraint (see BuildPCWithBockstein line 193): only `exp = 2`
# actually enters the loop that the C-8 fix patches; for `exp >= 4`
# the function returns early without augmentation. So the test uses
# `exp = 2`.
#
# Choice of group: a centraliser C with non-trivial Bockstein image
# H^1(C; F_2) -> H^2(C; F_2). D_8 = SmallGroup(8, 3) has
# C^ab = (Z/2)^2 so BocksteinH1ToH2(D_8) is non-empty.

# CWD shim — same pattern as test_iscoboundary2_z4_vec_bits.g.
c8_test_target := fail;;
for c8_try in [
        ".", "tests", "extraspecial_orbifolds/scripts/solver/tests",
        "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD/extraspecial_orbifolds/scripts/solver/tests"] do
    if IsExistingFile(Concatenation(c8_try,
                                     "/test_build_pc_with_bockstein_c8.g")) then
        c8_test_target := c8_try;
        break;
    fi;
od;;
if c8_test_target = fail then
    Error("test_build_pc_with_bockstein_c8.g: cannot locate self from CWD ",
          Filename(DirectoryCurrent(), ""));
fi;
ChangeDirectoryCurrent(c8_test_target);;
# Read the file under test. From solver/tests/, go up two to scripts/.
ChangeDirectoryCurrent("../..");
Read("solver/transgression_matrix_reduced.g");

Print("\n=== test_build_pc_with_bockstein_c8 ===\n");

# === D_8 with exp = 2 — exercises the Bockstein row-lift loop ===
C_d8 := SmallGroup(8, 3);;     # D_8
exp_local := 2;;
n_d8 := Order(C_d8);;
Print("Group: D_8 = SmallGroup(8, 3); |C| = ", n_d8,
      "; exp = ", exp_local, "\n");

t0 := Runtime();;
P_C := BuildPCWithBockstein(C_d8, exp_local);;
t_build := (Runtime() - t0) / 1000.;;
Print("BuildPCWithBockstein wall: ", t_build, " s\n");

Assert(0, P_C.bockstein_used = true,
       "exp=2 path must produce bockstein_used = true");

# Re-derive the expected Bockstein-image rows directly.
img_rows := BocksteinH1ToH2(C_d8);;
r_bockstein := Length(img_rows);;
Print("|Bockstein image| (r_bockstein) = ", r_bockstein, "\n");
Assert(0, r_bockstein >= 1,
       "D_8 must have non-trivial Bockstein image for this test to bind");

# r_base = rank of the basic UCT_C cocycle basis (everything before the
# Bockstein rows).
r_base := P_C.r;;
Print("r_base = ", r_base, "; r_full = ", P_C.r_full,
      "; expected r_full = ", r_base + r_bockstein, "\n");
Assert(0, P_C.r_full = r_base + r_bockstein,
       "r_full must equal r_base + r_bockstein");

# Check shape of M_aug_T: r_full + n + n^2 rows, each of length n^2.
nn := n_d8 * n_d8;;
expected_total_rows := P_C.r_full + n_d8 + nn;;
Assert(0, Length(P_C.M_aug_T) = expected_total_rows,
       Concatenation("M_aug_T row count mismatch; got ",
                     String(Length(P_C.M_aug_T)),
                     " expected ", String(expected_total_rows)));

# The Bockstein rows live at indices r_base+1 .. r_base+r_bockstein in
# M_aug_T. Each must equal IntVecFFE(img_rows[k_b]) * (exp/2).
exp_half := exp_local / 2;;     # = 1 at exp=2
n_disagree := 0;;
for k_b in [1..r_bockstein] do
    expected_row := IntVecFFE(img_rows[k_b]) * exp_half;
    actual_row := P_C.M_aug_T[r_base + k_b];

    # Length check.
    if Length(expected_row) <> nn then
        Print("FAIL: expected_row length = ", Length(expected_row),
              " (want ", nn, ") at k_b = ", k_b, "\n");
        n_disagree := n_disagree + 1;
        continue;
    fi;
    if Length(actual_row) <> nn then
        Print("FAIL: actual_row length = ", Length(actual_row),
              " (want ", nn, ") at k_b = ", k_b, "\n");
        n_disagree := n_disagree + 1;
        continue;
    fi;

    # Elementwise compare.
    if expected_row <> actual_row then
        Print("FAIL at k_b = ", k_b, ":\n");
        Print("  expected: ", expected_row, "\n");
        Print("  actual:   ", actual_row, "\n");
        n_disagree := n_disagree + 1;
    fi;

    # Cross-check: at exp=2 the row entries must lie in {0, 1}.
    if not ForAll(actual_row, x -> x = 0 or x = 1) then
        Print("FAIL: row entries outside {0, 1} at k_b = ", k_b, "\n");
        n_disagree := n_disagree + 1;
    fi;
od;
Assert(0, n_disagree = 0,
       Concatenation("BuildPCWithBockstein Bockstein-row block disagrees ",
                     "with IntVecFFE-based reference in ",
                     String(n_disagree), " rows"));

# Additional sanity: torsion_full should have entries 2 for each Bockstein row.
for k_b in [1..r_bockstein] do
    Assert(0, P_C.torsion_full[r_base + k_b] = 2,
           Concatenation("torsion_full[r_base+", String(k_b),
                         "] must be 2 for Bockstein-image rows"));
od;

# Final: projection of the FIRST basis cocycle of UCT_C should return the
# canonical unit vector — the rest of P_C must still work after the C-8
# refactor (i.e., the row indices and torsion alignment are preserved).
# We just check that basis_check stays consistent across the refactor by
# re-running the basic project on basis_cocycles[1].
if r_base >= 1 then
    cocy1 := P_C.basis_cocycles[1];;
    f1 := StandardCocycle(P_C.R, cocy1, 2, exp_local);;
    a1 := P_C.project(f1);;
    # project_full returns r_full entries (r_base basis + r_bockstein Bockstein
    # rows). The first should be the basis-cocycle's own coord (e_1 mod
    # torsion[1]); the rest should be 0 (the basis cocycle has no Bockstein-
    # image component by construction).
    expected_a1 := Concatenation(
        [1 mod P_C.torsion[1]],
        ListWithIdenticalEntries(r_base - 1, 0),
        ListWithIdenticalEntries(r_bockstein, 0));
    Assert(0, a1 = expected_a1,
           Concatenation("project(basis_funcs[1]) must yield e_1; got ",
                         String(a1), " expected ", String(expected_a1)));
fi;

Print("test_build_pc_with_bockstein_c8.g: PASS (",
      r_bockstein, " Bockstein-image rows verified)\n");
QUIT;
