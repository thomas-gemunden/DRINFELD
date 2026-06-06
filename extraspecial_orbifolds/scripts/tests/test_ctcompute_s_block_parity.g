# test_ctcompute_s_block_parity.g
#
# Issue #449 / Audit B4 (was 2026-06-02 A-K4-4): parity test for the
# batched `_CTComputeSBlock` in `ct_modular_data.g`.
#
# This test verifies that the new batched implementation produces
# BYTE-IDENTICAL output to the pre-batch reference implementation
# (kept inline below as `_CTComputeSBlockReference`). We rebuild the
# reference using exactly the loop structure that existed on `main`
# at commit 3b49058 (one `trace_on_W` call per (k, l) inner iteration),
# then run both side-by-side on small examples.
#
# COVERAGE
# --------
#   P1: H = Z_2 × Z_2 = SmallGroup(4, 2). Untwisted, 4 simples × 4
#       irreps = 16 simples. Trivial baseline — exercise path (A) and
#       path (B) since all centralisers = H.
#   P2: H = D_8 = SmallGroup(8, 3). Untwisted, rank 22.
#   P3: H = Q_8 = SmallGroup(8, 4). Untwisted, rank 22.
#   P4: H = E_+(3) = SmallGroup(128, 2326). Untwisted, rank 2272.
#       Gated on env `CT_MD_RUN_E_PLUS_3` to keep per-PR suite fast.
#
# Each parity check: for every (i, j) class pair, compare
# `_CTComputeSBlockReference(data, i, j)` vs `_CTComputeSBlock(data, i, j)`.
# Both should agree entry-by-entry in cyclotomic arithmetic.
#
# Run from absolute path:
#   gap -q -b /abs/path/to/test_ctcompute_s_block_parity.g

# ---- Test bookkeeping --------------------------------------------------

PARITY_PASSES   := 0;;
PARITY_FAILURES := [];;

ParityAssertTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
        PARITY_PASSES := PARITY_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Add(PARITY_FAILURES, label);
    fi;
end;;

ParityAssertEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
        PARITY_PASSES := PARITY_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Print("         expected: ", expected, "\n");
        Print("         got:      ", got, "\n");
        Add(PARITY_FAILURES, label);
    fi;
end;;

# ---- Locate worktree, scripts ----------------------------------------

PARITY_SELF := INPUT_FILENAME();;
if PARITY_SELF = fail or PARITY_SELF = "stream" then
    Error("test_ctcompute_s_block_parity.g: INPUT_FILENAME unavailable; ",
          "Read the file by its absolute path.");
fi;
PARITY_SELFDIR := PARITY_SELF{
    [1..Length(PARITY_SELF) - Length("/test_ctcompute_s_block_parity.g")]};;
PARITY_SCRIPTSDIR := PARITY_SELFDIR{
    [1..Length(PARITY_SELFDIR) - Length("/tests")]};;

Read(Concatenation(PARITY_SCRIPTSDIR, "/untwisted_modular_data.g"));
ParityAssertTrue("BuildSimpleIndex bound", IsBound(BuildSimpleIndex));

Read(Concatenation(PARITY_SCRIPTSDIR, "/krr_projector.g"));
ParityAssertTrue("BuildIntertwinerDataUntwisted bound",
                  IsBound(BuildIntertwinerDataUntwisted));

Read(Concatenation(PARITY_SCRIPTSDIR, "/ct_modular_data.g"));
ParityAssertTrue("ComputeCTModularData bound",
                  IsBound(ComputeCTModularData));
ParityAssertTrue("_CTComputeSBlock bound",
                  IsBound(_CTComputeSBlock));
ParityAssertTrue("_CTBatchedTraceOnW bound",
                  IsBound(_CTBatchedTraceOnW));

# ---- Reference (pre-batch) implementation ------------------------------
#
# This is the EXACT shape of `_CTComputeSBlock` as it existed at
# commit 3b49058 (before B4). Used here to verify byte-identity of the
# new batched implementation.

_CTComputeSBlockReference := function(intertwiner_data, i, j)
    local idx, transport, M, Ni, Nj, elts_i, elts_j, ts_i, ts_j,
          ai, bi, a, b, t_a, s_b, b_tilde, a_tilde, k, l, ord,
          cen_i_elts, c, elt_to_idx_j, eps, eps_chi_b, chi2_val,
          g_i, g_j, t_i, t_j;

    idx := intertwiner_data.idx;
    transport := intertwiner_data.transport;
    g_i := idx.reps[i];
    g_j := idx.reps[j];
    Ni := idx.num_irreps[i];
    Nj := idx.num_irreps[j];
    M := List([1..Ni], k -> List([1..Nj], l -> 0));
    t_i := GetTransport(transport, idx, i);
    t_j := GetTransport(transport, idx, j);
    elts_i := t_i.elements;
    elts_j := t_j.elements;
    ts_i := t_i.t_of;
    ts_j := t_j.t_of;
    if IsBoundGlobal("_EPlusCentraliserOf") then
        cen_i_elts := AsList(_EPlusCentraliserOf(idx, i));
    else
        cen_i_elts := AsList(idx.centralisers[i]);
    fi;
    elt_to_idx_j := t_j.elt_to_idx;
    ord := idx.order;

    if Length(elts_j) <= Length(cen_i_elts) then
        for ai in [1..Length(elts_i)] do
            a := elts_i[ai];
            t_a := ts_i[ai];
            for bi in [1..Length(elts_j)] do
                b := elts_j[bi];
                if a * b <> b * a then continue; fi;
                s_b := ts_j[bi];
                b_tilde := t_a^-1 * b * t_a;
                a_tilde := s_b^-1 * a * s_b;
                eps := intertwiner_data.epsilon(g_i, g_j, a, b);
                for k in [1..Ni] do
                    eps_chi_b := eps * ComplexConjugate(
                        intertwiner_data.trace_on_W(i, k, b_tilde));
                    for l in [1..Nj] do
                        chi2_val := ComplexConjugate(
                            intertwiner_data.trace_on_W(j, l, a_tilde));
                        M[k][l] := M[k][l] + eps_chi_b * chi2_val;
                    od;
                od;
            od;
        od;
    else
        for ai in [1..Length(elts_i)] do
            a := elts_i[ai];
            t_a := ts_i[ai];
            for c in cen_i_elts do
                b := t_a * c * t_a^(-1);
                bi := LookupDictionary(elt_to_idx_j, b);
                if bi = fail then continue; fi;
                s_b := ts_j[bi];
                b_tilde := c;
                a_tilde := s_b^-1 * a * s_b;
                eps := intertwiner_data.epsilon(g_i, g_j, a, b);
                for k in [1..Ni] do
                    eps_chi_b := eps * ComplexConjugate(
                        intertwiner_data.trace_on_W(i, k, b_tilde));
                    for l in [1..Nj] do
                        chi2_val := ComplexConjugate(
                            intertwiner_data.trace_on_W(j, l, a_tilde));
                        M[k][l] := M[k][l] + eps_chi_b * chi2_val;
                    od;
                od;
            od;
        od;
    fi;
    return M / ord;
end;;

# Run the per-(i, j) parity sweep on a given intertwiner_data record.
# Returns: rec(num_blocks, num_mismatch, first_mismatch).
RunParitySweep := function(intertwiner_data, label)
    local n_classes, n_mismatch, first_mismatch, i, j, block_new,
          block_ref, n_blocks, t0, t_new, t_ref;
    n_classes := Length(intertwiner_data.idx.classes);
    n_mismatch := 0;
    first_mismatch := fail;
    n_blocks := 0;
    t_new := 0;
    t_ref := 0;
    for i in [1..n_classes] do
        for j in [1..n_classes] do
            t0 := Runtime();
            block_new := _CTComputeSBlock(intertwiner_data, i, j);
            t_new := t_new + (Runtime() - t0);
            t0 := Runtime();
            block_ref := _CTComputeSBlockReference(intertwiner_data, i, j);
            t_ref := t_ref + (Runtime() - t0);
            n_blocks := n_blocks + 1;
            if block_new <> block_ref then
                n_mismatch := n_mismatch + 1;
                if first_mismatch = fail then
                    first_mismatch := rec(i := i, j := j,
                                          new := block_new,
                                          ref := block_ref);
                fi;
            fi;
        od;
    od;
    Print("  [", label, "] blocks: ", n_blocks,
          ", mismatches: ", n_mismatch,
          ", t_new: ", t_new / 1000., " s",
          ", t_ref: ", t_ref / 1000., " s\n");
    if first_mismatch <> fail then
        Print("  [", label, "] first mismatch at (i, j) = (",
              first_mismatch.i, ", ", first_mismatch.j, "):\n");
        Print("    ref: ", first_mismatch.ref, "\n");
        Print("    new: ", first_mismatch.new, "\n");
    fi;
    return rec(num_blocks := n_blocks,
               num_mismatch := n_mismatch,
               first_mismatch := first_mismatch,
               t_new := t_new,
               t_ref := t_ref);
end;;

# =======================================================================
# P1: H = Z_2 x Z_2 (rank 16)
# =======================================================================

Print("\n=== P1: H = Z_2 x Z_2 untwisted parity ===\n");
PARITY_Z22 := SmallGroup(4, 2);;
PARITY_DATA_Z22 := BuildIntertwinerDataUntwisted(PARITY_Z22);;
PARITY_RES_Z22 := RunParitySweep(PARITY_DATA_Z22, "Z_2 x Z_2");;

ParityAssertTrue("Z_2 x Z_2: all blocks match byte-for-byte",
                  PARITY_RES_Z22.num_mismatch = 0);

# =======================================================================
# P2: H = D_8 (rank 22)
# =======================================================================

Print("\n=== P2: H = D_8 untwisted parity ===\n");
PARITY_D8 := SmallGroup(8, 3);;
PARITY_DATA_D8 := BuildIntertwinerDataUntwisted(PARITY_D8);;
PARITY_RES_D8 := RunParitySweep(PARITY_DATA_D8, "D_8");;

ParityAssertTrue("D_8: all blocks match byte-for-byte",
                  PARITY_RES_D8.num_mismatch = 0);

# =======================================================================
# P3: H = Q_8 (rank 22)
# =======================================================================

Print("\n=== P3: H = Q_8 untwisted parity ===\n");
PARITY_Q8 := SmallGroup(8, 4);;
PARITY_DATA_Q8 := BuildIntertwinerDataUntwisted(PARITY_Q8);;
PARITY_RES_Q8 := RunParitySweep(PARITY_DATA_Q8, "Q_8");;

ParityAssertTrue("Q_8: all blocks match byte-for-byte",
                  PARITY_RES_Q8.num_mismatch = 0);

# =======================================================================
# P4: Fallback path (3) — verify path (3) gives identical output to
# path (2) for the same intertwiner_data.
# =======================================================================
# We construct two copies of the Q_8 intertwiner_data, one tagged
# "evalirr" (path 2 in `_CTBatchedTraceOnW`) and one without the tag
# (path 3 fallback). Both should give identical S-blocks.

Print("\n=== P4: trace_on_W_kind tag does not change output ===\n");

# Tagged data (current default).
PARITY_DATA_Q8_TAGGED := BuildIntertwinerDataUntwisted(SmallGroup(8, 4));;
# Untagged data (forces fallback to path 3).
PARITY_DATA_Q8_UNTAGGED := rec(
    group      := PARITY_DATA_Q8_TAGGED.group,
    idx        := PARITY_DATA_Q8_TAGGED.idx,
    transport  := PARITY_DATA_Q8_TAGGED.transport,
    trace_on_W := PARITY_DATA_Q8_TAGGED.trace_on_W,
    epsilon    := PARITY_DATA_Q8_TAGGED.epsilon
    # NOTE: deliberately no trace_on_W_kind field.
);;
ParityAssertTrue("P4 untagged data does NOT have trace_on_W_kind",
                  not IsBound(PARITY_DATA_Q8_UNTAGGED.trace_on_W_kind));

PARITY_P4_MISMATCH := 0;;
PARITY_P4_N_CLASSES := Length(PARITY_DATA_Q8_TAGGED.idx.classes);;
for PARITY_P4_I in [1..PARITY_P4_N_CLASSES] do
    for PARITY_P4_J in [1..PARITY_P4_N_CLASSES] do
        PARITY_P4_BLOCK_T := _CTComputeSBlock(PARITY_DATA_Q8_TAGGED,
                                               PARITY_P4_I, PARITY_P4_J);;
        PARITY_P4_BLOCK_U := _CTComputeSBlock(PARITY_DATA_Q8_UNTAGGED,
                                               PARITY_P4_I, PARITY_P4_J);;
        if PARITY_P4_BLOCK_T <> PARITY_P4_BLOCK_U then
            PARITY_P4_MISMATCH := PARITY_P4_MISMATCH + 1;
        fi;
    od;
od;
Print("  [P4] tagged-vs-untagged mismatches: ", PARITY_P4_MISMATCH, "\n");
ParityAssertTrue("P4: path (2) and path (3) agree byte-for-byte",
                  PARITY_P4_MISMATCH = 0);

# =======================================================================
# P5: Full ComputeCTModularData regression at Q_8 — matches stored
#     trivial-cocycle data after permutation. Re-runs the same case as
#     test_ct_modular_data.g T1 just to ensure the end-to-end pipeline
#     still works.
# =======================================================================

Print("\n=== P5: End-to-end ComputeCTModularData(Q_8) ===\n");
PARITY_OUT_Q8 := ComputeCTModularData(PARITY_DATA_Q8, PARITY_Q8);;
ParityAssertTrue("Q_8: S is 22 x 22",
                  Length(PARITY_OUT_Q8.S) = 22
                  and Length(PARITY_OUT_Q8.S[1]) = 22);
ParityAssertTrue("Q_8: T is 22 x 22 diagonal",
                  Length(PARITY_OUT_Q8.T) = 22
                  and ForAll([1..22], i ->
                      ForAll([1..22], j ->
                          i = j or PARITY_OUT_Q8.T[i][j] = 0)));

# Modular relations (same as T4 in test_ct_modular_data.g) — these are
# strong end-to-end sanity checks since any bug in chi_vec batching
# would corrupt S and break the relations.
PARITY_S_SQ := PARITY_OUT_Q8.S * PARITY_OUT_Q8.S;;
PARITY_ST := PARITY_OUT_Q8.S * PARITY_OUT_Q8.T;;
PARITY_ST_CUBE := PARITY_ST * PARITY_ST * PARITY_ST;;
ParityAssertEqual("Q_8: (ST)^3 = S^2 (trivial cocycle)",
                   PARITY_ST_CUBE, PARITY_S_SQ);
ParityAssertEqual("Q_8: S^4 = I",
                   PARITY_S_SQ * PARITY_S_SQ, IdentityMat(22));

# =======================================================================
# P6: E_+(3) — gated
# =======================================================================

PARITY_RUN_EPLUS3 := fail;;
if IsBound(GAPInfo) and IsBound(GAPInfo.SystemEnvironment) then
    if IsBound(GAPInfo.SystemEnvironment.CT_MD_RUN_E_PLUS_3) then
        PARITY_RUN_EPLUS3 := GAPInfo.SystemEnvironment.CT_MD_RUN_E_PLUS_3;
    fi;
fi;

if PARITY_RUN_EPLUS3 = "1" then
    Print("\n=== P6: H = E_+(3) untwisted parity ===\n");
    PARITY_E3 := SmallGroup(128, 2326);;
    Print("  building intertwiner_data ...\n");
    PARITY_T_BUILD := Runtime();;
    PARITY_DATA_E3 := BuildIntertwinerDataUntwisted(PARITY_E3);;
    PARITY_T_BUILD_WALL := (Runtime() - PARITY_T_BUILD) / 1000.;;
    Print("  intertwiner_data built in ", PARITY_T_BUILD_WALL, " s; ",
          "rank = ", PARITY_DATA_E3.idx.rank, "\n");

    PARITY_RES_E3 := RunParitySweep(PARITY_DATA_E3, "E_+(3)");;
    ParityAssertTrue("E_+(3): all blocks match byte-for-byte",
                      PARITY_RES_E3.num_mismatch = 0);
else
    Print("\n=== P6: H = E_+(3) parity (skipped, set CT_MD_RUN_E_PLUS_3=1) ===\n");
fi;

# ---- Final summary -----------------------------------------------------

Print("\n=== Final summary ===\n");
Print("  passes:   ", PARITY_PASSES, "\n");
Print("  failures: ", Length(PARITY_FAILURES), "\n");
if Length(PARITY_FAILURES) = 0 then
    Print("\ntest_ctcompute_s_block_parity: PASS\n");
else
    Print("\ntest_ctcompute_s_block_parity: FAIL (",
          Length(PARITY_FAILURES), "):\n");
    for PARITY_F in PARITY_FAILURES do
        Print("  - ", PARITY_F, "\n");
    od;
fi;

QUIT;
