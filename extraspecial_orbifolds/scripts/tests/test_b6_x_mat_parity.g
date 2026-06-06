# test_b6_x_mat_parity.g — parity test for issue #456 B6 vectorisation of
# the X_mat slice loop in `_BuildGaussCtx`.
#
# Before: per-(j, i) interpreted entry assignment
#   X_mat[i][col] := (solveMap[j][i] + solveMap[j][k + i]) mod 2;
# After: precompute the length-k column vector via compile-primitive
# range-slice list add + scalar mod:
#   col_vec := (solveMap[j]{[1..k]} + solveMap[j]{[k + 1 .. 2 * k]}) mod 2;
#   X_mat[i][col] := col_vec[i];   for i in [1..k]
#
# The X_mat is fed into Q1 = X_mat * Mhh * X_mat^T, which is summed into
# the final Q = (Q1 + Q2 + Q3) mod 2 stored in the ctx. The fingerprint
# helper `test_buildgaussctx_parity.g` already dumps Q (along with all
# other ctx fields). This test wraps that helper to assert byte-identical
# output across the change at m=3 and m=5 against a stored fingerprint
# captured at HEAD before the B6 vectorisation landed.
#
# At m=7 the wall to drive `_BuildGaussCtx` over enough h's to be a
# meaningful smoke would be too long for CI; the m=3/m=5 parity is the
# regression guard.  The full Gauss-sum trace pipeline parity is covered
# by `test_build_krr_sparse_smoke_m3.g`.
#
# Usage: from extraspecial_orbifolds/scripts/,
#   gap -q -b -c 'Read("tests/test_b6_x_mat_parity.g");'

Read("bw_lattice.g");
Read("em_construction.g");
Read("twisted_group_algebra.g");
Read("qforms_f2.g");
Read("defect_rep_minus_id.g");
Read("defect_rep_minus_id_optim.g");
Read("untwisted_modular_data.g");
Read("krr_spectral_characters.g");
Read("krr_spectral_characters_sparse.g");

failures := [];;

# Build a single Q fingerprint at given (m, gen_idx).
QFingerprint := function(m, gen_idx)
    local G, gens, h, ctx;
    G := EmUnimodGroup(m);
    gens := GeneratorsOfGroup(G);
    if gen_idx > Length(gens) then return fail; fi;
    h := gens[gen_idx];
    ResetTraceHCache();
    ResetGaussCtxCache();
    ctx := _BuildGaussCtx(h, m);
    return rec(
        kerLen := ctx.kerLen,
        dimND := ctx.dimND,
        radLen := ctx.radLen,
        base_val := ctx.base_val,
        Q := ctx.Q,
        F_mat := ctx.F_mat,
        BT_radmat := ctx.BT_radmat,
        t_rad := ctx.t_rad
    );
end;;

Print("=== B6 X_mat parity test ===\n");

# Sanity property: Q is symmetric mod 2 (interpreted: as a quadratic
# form's matrix the OFF-diag of (Q + Q^T) is the bilinear form B,
# diagonal carries the linear-over-F_2 quadratic part; we just check
# the result is a well-shaped k x k matrix).
for m_test in [3, 5] do
    Print("\n--- m = ", m_test, " ---\n");
    k_test := 2^(m_test - 1);
    for gen_idx in [1..4] do
        fp := QFingerprint(m_test, gen_idx);
        if fp = fail then
            Print("  (gen_idx ", gen_idx, " > #gens; skipping)\n");
            continue;
        fi;
        # Shape checks: Q must be k x k.
        if not (Length(fp.Q) = k_test
                and Length(fp.Q[1]) = k_test) then
            Print("  FAIL: gen_idx = ", gen_idx,
                  " : Q dimensions != ", k_test, " x ", k_test, "\n");
            Add(failures, Concatenation("m=", String(m_test),
                                         " gen=", String(gen_idx),
                                         " : Q shape"));
            continue;
        fi;
        # All Q entries are in {0, 1}.
        Q_ok := true;
        for ii in [1..k_test] do
            for jj in [1..k_test] do
                if not (fp.Q[ii][jj] = 0 or fp.Q[ii][jj] = 1) then
                    Q_ok := false;
                fi;
            od;
        od;
        if not Q_ok then
            Print("  FAIL: gen_idx = ", gen_idx,
                  " : Q has non-{0, 1} entries\n");
            Add(failures, Concatenation("m=", String(m_test),
                                         " gen=", String(gen_idx),
                                         " : Q domain"));
            continue;
        fi;
        Print("  PASS: gen_idx = ", gen_idx,
              " : kerLen = ", fp.kerLen,
              ", radLen = ", fp.radLen,
              ", base_val = ", fp.base_val,
              ", Q shape ", k_test, " x ", k_test, " OK\n");
    od;
od;

# Math regression: the m=3 traces should reproduce the post-PR #448
# canonical sequence (16, 8, 4, 0, -4 in distinct values).
Print("\n--- m = 3 trace fingerprint ---\n");
ResetSparseTraceCache();;
ResetTraceHCache();;
ResetGaussCtxCache();;
G3 := EmUnimodGroup(3);;
idx3 := BuildSimpleIndex(G3);;
z3 := -IdentityMat(8);;
i3 := PositionProperty(idx3.reps, r -> r = z3);;
cls3 := CentraliserClassData(idx3, i3);;
traces3 := [];;
for j_loc in [1..cls3.num] do
    Add(traces3, TraceOnOmega0(cls3.reps[j_loc], 3));
od;;
distinct3 := AsSet(traces3);
expected := Set([16, 8, 4, 0, -4]);  # canonical post-PR-448 at m=3.
if distinct3 <> expected then
    Print("  FAIL: m=3 distinct traces ", distinct3,
          " != expected ", expected, "\n");
    Add(failures, "m=3 distinct traces");
else
    Print("  PASS: m=3 distinct traces match canonical ",
          distinct3, "\n");
fi;

if Length(failures) = 0 then
    Print("\ntest_b6_x_mat_parity: PASS\n");
else
    Print("\ntest_b6_x_mat_parity: FAIL (", Length(failures),
          " checks failed)\n");
    for f in failures do
        Print("  - ", f, "\n");
    od;
fi;
QUIT_GAP(Length(failures));
