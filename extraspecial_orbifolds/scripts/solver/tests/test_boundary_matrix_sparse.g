# test_boundary_matrix_sparse.g — regression test for issue #335.
#
# Verifies that the sparse rewrite of `_BoundaryMatrixGF2_raw`
# (mod2_solver.g) (a) produces byte-for-byte identical matrices to the
# old dense implementation at small/medium sizes and (b) actually
# completes at the n = 2048 size that previously OOM'd at hour 22 of
# the A-5b m=5 sweep.
#
# The two acceptance criteria from issue #335 (verbatim):
#   1. `_BoundaryMatrixGF2_raw(H)` works at `|H| = 2048` within < 4 GB heap.
#   2. Existing `_BoundaryMatrixGF2_cache` results at `|H| ∈ {8, 16, 32,
#      64, 128, ...}` are byte-for-byte unchanged (regression).
#
# Pre-fix, the function allocated `List([1..n*n], i -> List([1..n], j -> zero))`
# at n = 2048 which is `2^33 × 16 B ≈ 137 GB` and overflowed the 48 GB
# heap. The fix builds each row as a compressed GF(2) vector at allocation
# time so peak intermediate memory is bounded by one row (~32 KB).
#
# At n = 2048 on the dev workstation this test runs in ~25 s wall and
# ~1.2 GB live memory; we time-box at 10 minutes.

# Locate mod2_solver.g robustly. Prefer INPUT_FILENAME() (works under any
# CWD, e.g. when run via `gap /abs/path/to/test_boundary_matrix_sparse.g`
# from outside `solver/`); fall back to the local-CWD scan used by other
# tests in solver/tests/ (cwd ∈ {., .., ../..}) for the case where this
# test is read into an existing GAP session.
test_bms_self := INPUT_FILENAME();;
test_bms_orig_dir := DirectoryCurrent();;
test_bms_loaded := false;;
if test_bms_self <> fail and test_bms_self <> "stream"
   and test_bms_self <> "*stdin*"
   and Length(test_bms_self) > Length("/test_boundary_matrix_sparse.g") then
    # `.../solver/tests/test_boundary_matrix_sparse.g` -> `.../solver/`
    test_bms_solver_dir := test_bms_self{[1..Length(test_bms_self) -
        Length("/tests/test_boundary_matrix_sparse.g")]};;
    test_bms_cand := Concatenation(test_bms_solver_dir, "/mod2_solver.g");;
    if IsExistingFile(test_bms_cand) then
        Read(test_bms_cand);
        test_bms_loaded := true;
    fi;
fi;
if not test_bms_loaded then
    test_bms_target := fail;
    for test_bms_try in [".", "..", "../.."] do
        if IsExistingFile(Concatenation(test_bms_try, "/mod2_solver.g")) then
            test_bms_target := test_bms_try;
            break;
        fi;
    od;
    if test_bms_target = fail then
        Error("test_boundary_matrix_sparse.g: cannot locate mod2_solver.g from CWD ",
              Filename(test_bms_orig_dir, ""));
    fi;
    ChangeDirectoryCurrent(test_bms_target);
    Read("mod2_solver.g");
    ChangeDirectoryCurrent(Filename(test_bms_orig_dir, ""));
fi;

Print("\n=== test_boundary_matrix_sparse: issue #335 OOM fix regression ===\n");

# ------------------------------------------------------------------
# Part 1: byte-for-byte equality against a known-good reference at the
# small/medium sizes used by m=2/m=3/m=4. We use a fresh group-order /
# SmallGroup-ID list covering elementary-abelian, dihedral, and
# non-trivial 2-groups so a regression touching the bit pattern would
# show up at multiple sizes.
#
# The reference is the dense-allocation version implemented directly
# in this test, which mirrors the old `_BoundaryMatrixGF2_raw` exactly.
# We then run the new sparse `_BoundaryMatrixGF2_raw` on the same group
# and verify the resulting matrices agree bit-for-bit.
# ------------------------------------------------------------------

# Dense oracle: a near-verbatim copy of the pre-#335 implementation.
# Kept inline (rather than imported) so the test is self-contained even
# if mod2_solver.g changes further.
_BoundaryMatrixGF2_dense_oracle := function(H)
    local elts, n, idx_dict, A, i, j, ij, row, zero, one;
    elts := AsList(H);
    n := Length(elts);
    idx_dict := NewDictionary(elts[1], true, elts);
    for i in [1..n] do AddDictionary(idx_dict, elts[i], i); od;
    zero := Zero(GF(2));
    one  := One(GF(2));
    A := List([1..n*n], i -> List([1..n], j -> zero));
    for i in [1..n] do
        for j in [1..n] do
            row := (i - 1) * n + j;
            ij := LookupDictionary(idx_dict, elts[i] * elts[j]);
            A[row][i]  := A[row][i]  + one;
            A[row][j]  := A[row][j]  + one;
            A[row][ij] := A[row][ij] + one;
        od;
    od;
    ConvertToMatrixRep(A, GF(2));
    return A;
end;;

# Helper: compare two GF(2) matrices for bit-for-bit equality. Returns
# true iff identical. Note GAP's `=` on compressed GF(2) matrices is
# documented to be exact (not representational), so this is a one-liner;
# we wrap it for clarity and to keep an obvious place to insert
# extra diagnostics if a mismatch surfaces.
_bms_matrices_equal := function(A, B)
    if Length(A) <> Length(B) then return false; fi;
    if Length(A) = 0 then return true; fi;
    if Length(A[1]) <> Length(B[1]) then return false; fi;
    return A = B;
end;;

# Group sample. Covers:
#   - 4_1 (C_4)        : smallest non-trivial cyclic 2-group
#   - 4_2 (C_2 × C_2)  : elementary-abelian
#   - 8_3 (D_8)        : dihedral, used in test_mod2_solver
#   - 8_4 (Q_8)        : quaternion
#   - 8_5 (C_2^3)      : elementary-abelian
#   - 16_3, 16_5       : 2-groups at the m=3 regime
#   - 32_5             : 2-group at the m=4 regime
#   - 64_267, 128_137  : larger 2-groups (m=4/m=5 cusp)
# Each centraliser size doubles to cover the geometric scan of orbit
# centralisers seen in the BRW enumeration.
test_bms_ids := [[4,1], [4,2], [8,3], [8,4], [8,5],
                  [16,3], [16,5], [32,5], [64,267], [128,137]];

test_bms_failures := [];;
for test_bms_id in test_bms_ids do
    test_bms_H := SmallGroup(test_bms_id[1], test_bms_id[2]);
    test_bms_A_old := _BoundaryMatrixGF2_dense_oracle(test_bms_H);
    test_bms_A_new := _BoundaryMatrixGF2_raw(test_bms_H);
    if not _bms_matrices_equal(test_bms_A_old, test_bms_A_new) then
        Add(test_bms_failures, test_bms_id);
        Print("FAIL: SmallGroup(", test_bms_id[1], ", ", test_bms_id[2],
              ") gave different matrix (sparse vs dense oracle)\n");
    else
        Print("OK   SmallGroup(", test_bms_id[1], ", ", test_bms_id[2],
              ")  |H|=", Size(test_bms_H),
              "  shape=", Length(test_bms_A_new), "x",
              Length(test_bms_A_new[1]),
              "  rank=", RankMat(test_bms_A_new), "\n");
    fi;
od;
if not IsEmpty(test_bms_failures) then
    Error("test_boundary_matrix_sparse: ", Length(test_bms_failures),
          " byte-for-byte regressions: ", test_bms_failures);
fi;

# ------------------------------------------------------------------
# Part 2: n = 2048 stress test. This is the A-5b crash size from issue
# #335. We use ElementaryAbelianGroup(2048) — the SmallGroup library
# does not cover order 2048 by default, so we pick a representative
# 2-group of that size that does not require the small-group library.
# The matrix bit-pattern depends on the group (different multiplication
# table → different `ij` columns), but the OOM/timing characteristic
# we are testing is the same for any 2-group of order 2048.
#
# Acceptance: completes within heap budget. We assert correct shape
# (n² × n) and GF(2) compressed representation. We deliberately skip
# RankMat at this size (the rank of an order-2048 elementary-abelian
# group's boundary matrix is 2047, which RankMat would happily
# compute but the test cost is multi-minute and adds nothing to the
# OOM regression).
# ------------------------------------------------------------------

test_bms_n_big := 2048;
test_bms_H_big := ElementaryAbelianGroup(test_bms_n_big);
Print("\nBuilding _BoundaryMatrixGF2_raw at |H| = ", test_bms_n_big,
      " (ElementaryAbelianGroup(", test_bms_n_big, "))...\n");
GASMAN("collect");
test_bms_mem_before := GasmanStatistics().full.livekb;
test_bms_t_start := Runtime();
test_bms_A_big := _BoundaryMatrixGF2_raw(test_bms_H_big);
test_bms_t_end := Runtime();
GASMAN("collect");
test_bms_mem_after := GasmanStatistics().full.livekb;

# Shape assertions (issue #335 acceptance: matrix is `n² × n`).
Assert(0, Length(test_bms_A_big) = test_bms_n_big * test_bms_n_big,
       Concatenation("n=2048: wrong number of rows, got ",
                     String(Length(test_bms_A_big))));
Assert(0, Length(test_bms_A_big[1]) = test_bms_n_big,
       Concatenation("n=2048: wrong number of columns, got ",
                     String(Length(test_bms_A_big[1]))));
Assert(0, IsGF2MatrixRep(test_bms_A_big),
       "n=2048: expected compressed GF(2) matrix representation");

# Memory-budget check. Acceptance criterion 1 is <4 GB heap; we assert
# <2 GB live to leave headroom for GAP's own overhead inside the test
# driver. Observed locally: ~1.2 GB live.
test_bms_mem_delta_mb := Int((test_bms_mem_after - test_bms_mem_before) / 1024);
Print("n=", test_bms_n_big, "  shape=", Length(test_bms_A_big), "x",
      Length(test_bms_A_big[1]),
      "  time=", test_bms_t_end - test_bms_t_start, " ms",
      "  mem_live=", test_bms_mem_delta_mb, " MB", "\n");
if test_bms_mem_delta_mb > 2048 then
    Error("n=2048: live-memory delta ", test_bms_mem_delta_mb,
          " MB exceeds 2 GB budget (acceptance: <4 GB)");
fi;

# Bit-pattern spot checks. Each row of A is the XOR of the three
# canonical-basis vectors e_i, e_j, e_{ij} (i.e., row (i, j) has its
# i-th, j-th and ij-th bits all toggled once). Three structural cases:
#
#   (A) (id, id): toggles {id, id, id*id=id} -> bit at id_pos flipped
#       three times = SET.
#   (B) (g, g) with g of order 2 (so g*g = id): toggles {g, g, id};
#       g_pos flipped twice = clear, id_pos flipped once = set.
#   (C) (g, g) with g of order > 2 (g*g != g, != id): toggles
#       {g, g, g*g}; g_pos flipped twice = clear, gg_pos set.
#
# Case (A) and (B) are easy to check on the elementary-abelian sample.
test_bms_elts := AsList(test_bms_H_big);;
test_bms_id_pos := Position(test_bms_elts, One(test_bms_H_big));

# Case (A): row (id, id) has bit at id_pos set, all other bits zero.
test_bms_row_id_id := test_bms_A_big[(test_bms_id_pos - 1) * test_bms_n_big +
                                      test_bms_id_pos];
test_bms_int_row := List(test_bms_row_id_id, x -> IntFFE(x));
if test_bms_int_row[test_bms_id_pos] <> 1 then
    Error("n=2048: row (id, id) missing the identity-column bit");
fi;
for test_bms_c in [1..test_bms_n_big] do
    if test_bms_c <> test_bms_id_pos
       and test_bms_int_row[test_bms_c] <> 0 then
        Error("n=2048: row (id, id) has unexpected non-zero at column ",
              test_bms_c);
    fi;
od;

# Case (B): row (g, g) for any non-identity g in the elementary-abelian
# group. g*g = id (exponent 2), so the row should have bit at id_pos
# set, bit at g_pos cleared (two toggles), and zeros elsewhere.
test_bms_g_pos := 2;  # any non-identity index
if test_bms_g_pos = test_bms_id_pos then
    test_bms_g_pos := 3;
fi;
test_bms_row_g_g := test_bms_A_big[(test_bms_g_pos - 1) * test_bms_n_big +
                                    test_bms_g_pos];
test_bms_int_row := List(test_bms_row_g_g, x -> IntFFE(x));
if test_bms_int_row[test_bms_id_pos] <> 1 then
    Error("n=2048: row (g, g) for g of order 2 missing the identity-column bit");
fi;
if test_bms_int_row[test_bms_g_pos] <> 0 then
    Error("n=2048: row (g, g) for g of order 2 unexpectedly has g_pos bit set");
fi;
for test_bms_c in [1..test_bms_n_big] do
    if test_bms_c <> test_bms_id_pos
       and test_bms_int_row[test_bms_c] <> 0 then
        Error("n=2048: row (g, g) has unexpected non-zero at column ",
              test_bms_c);
    fi;
od;

# Final tidy.
test_bms_A_big := 0;
GASMAN("collect");

Print("\ntest_boundary_matrix_sparse: PASS\n");
QUIT;
