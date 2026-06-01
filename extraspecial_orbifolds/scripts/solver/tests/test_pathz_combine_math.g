# test_pathz_combine_math.g — issue #391 (A+B combine, PR #394).
#
# Verifies that column-XOR over GF(2) reproduces a full GF(2) matvec
# when the input vector has small support:
#
#   table_gf2 * u_bot  ==  sum_{j in supp(u_bot)} table_gf2[*][j]
#
# where supp(u_bot) is {j : u_bot[j] = 1} (treating u_bot as a GF(2)
# vector). The right-hand side is what the new sparsity-aware GF(2)
# dispatcher in run_e_plus_m_kernel_hap.g computes when k_nz <= k/3.
#
# Strategy:
#   1. Build synthetic n²×k GF(2) matrix (random entries).
#   2. For each support-pattern (empty / unit / sparse / dense),
#      compute both paths and assert equality.
#   3. Verify TransposedMat row-major = column-major.

n_squared := 64;;   # n² for a hypothetical n=8 group
k := 35;;           # like m=3
trials := 20;;
one_gf2 := One(GF(2));;
zero_gf2 := Zero(GF(2));;

# Synthetic table_gf2_top with random GF(2) entries.
M := List([1..n_squared], i ->
          List([1..k], j -> Random([zero_gf2, one_gf2])));;
ConvertToMatrixRep(M, GF(2));

# Column-major view.
M_T := TransposedMat(M);;
ConvertToMatrixRep(M_T, GF(2));

# T1: column-correctness.
fails := 0;;
for j_idx in [1, QuoInt(k, 2), k] do
    col_expected := List(M, row -> row[j_idx]);;
    if M_T[j_idx] <> col_expected then
        Print("FAIL T1: column ", j_idx, " mismatch\n");
        fails := fails + 1;
    fi;
od;

# T2: column-XOR vs full matvec across random vec_targets.
for trial in [1..trials] do
    # Random support size: a mix of 0, 1, small, medium, large.
    target_supp_size := Random([0, 1, 2, 5, 8, QuoInt(k, 3), k, k]);
    if target_supp_size > k then target_supp_size := k; fi;
    supp_positions := [];
    while Length(supp_positions) < target_supp_size do
        AddSet(supp_positions, Random([1..k]));
    od;
    # Random vec_target with this support.
    vec_target := ListWithIdenticalEntries(k, 0);
    for j in supp_positions do
        vec_target[j] := Random([1, 3]);   # nonzero mod 2
    od;
    # Optionally add some even entries that should NOT contribute to bit_0.
    for j in [1..k] do
        if not (j in supp_positions) and Random([1..3]) = 1 then
            vec_target[j] := 2;   # mod 2 = 0
        fi;
    od;
    # Recompute supp from vec_target (treat mod 2 == 0 as zero).
    supp := PositionsProperty(vec_target, x -> x mod 2 <> 0);;

    # Dense: full matvec.
    u_bot := (vec_target mod 2) * one_gf2;
    ConvertToVectorRep(u_bot, GF(2));
    slice_dense := M * u_bot;;

    # Sparse: column-XOR.
    slice_sparse := ListWithIdenticalEntries(n_squared, zero_gf2);;
    ConvertToVectorRep(slice_sparse, GF(2));
    for j_supp in supp do
        AddRowVector(slice_sparse, M_T[j_supp]);
    od;

    if slice_dense <> slice_sparse then
        Print("FAIL T2 trial ", trial, ": supp=", Length(supp),
              " dense != sparse\n");
        Print("  dense  (first 8): ", slice_dense{[1..8]}, "\n");
        Print("  sparse (first 8): ", slice_sparse{[1..8]}, "\n");
        fails := fails + 1;
    fi;
od;

# T3: zero-support short-circuit.
zero_vec := ListWithIdenticalEntries(k, 0);
u_bot_zero := (zero_vec mod 2) * one_gf2;
ConvertToVectorRep(u_bot_zero, GF(2));
slice_zero_expected := M * u_bot_zero;
slice_zero_actual := ListWithIdenticalEntries(n_squared, zero_gf2);
ConvertToVectorRep(slice_zero_actual, GF(2));
if slice_zero_expected <> slice_zero_actual then
    Print("FAIL T3: zero-support short-circuit (sparse all-zero) ",
          "doesn't match M * 0\n");
    fails := fails + 1;
fi;

if fails = 0 then
    Print("test_pathz_combine_math: ALL PASS (",
          trials, " random + 3 column-spot + 1 zero, n²=", n_squared,
          ", k=", k, ")\n");
    QuitGap(0);
else
    Print("test_pathz_combine_math: ", fails, " FAILURE(S)\n");
    QuitGap(1);
fi;
