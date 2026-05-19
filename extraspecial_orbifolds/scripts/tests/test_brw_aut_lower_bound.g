# test_brw_aut_lower_bound.g — tests for issue #239 (A-3d perf-1).
#
# Tested modules:
#   ../brw_aut_lower_bound.g
#
# Acceptance (issue #239):
#   * Q_8 sanity (m = 1, E_+(1) = D_8; rank 22): build the BRW(1) lift
#     to Sym(22) and verify all |BRW(1)/E_+(1)| = 2 elements are
#     (N, T)-automorphisms. Cross-check against the existing dense
#     AutNT result for D_8 trivial cocycle.
#   * E_+(3) (rank 2272): build the BRW(3) lift to Sym(2272) and verify
#     all |BRW(3)/E_+(3)| = 40320 elements are (N, T)-automorphisms.
#       — Gated behind A3D_INCLUDE_M3 := true; (default: skip).
#
# Note on numbers. Issue #239 (and run_e_plus_3_aut.g) state the
# expected lower bound as 1,451,520 ("|O+(6, F_2)|"). That number does
# not match the actual quotient |BRW(3)/E_+(3)| produced by our
# brw_construction.g, which is 40320 = |GO+(6, F_2)| in GAP's
# convention (matching test_brw_conjugacy_action.g). The discrepancy
# is a math-convention error in the issue spec; the **constructive
# certificate** (the deliverable) is the actual size of the BRW image
# in Sym(rank), which is 40320 here. We therefore use the empirically
# correct value and document the convention in the persisted result.
#
# Run from anywhere:
#     gap test_brw_aut_lower_bound.g
#
# Pass criterion: prints "test_brw_aut_lower_bound: PASS".

# ---- Locate and load sibling modules ---------------------------------
_loaded := false;;
_self_path := INPUT_FILENAME();;
if _self_path <> fail and _self_path <> "stream" then
    _self_dir := _self_path{[1..Length(_self_path)
                              - Length("/test_brw_aut_lower_bound.g")]};;
    _cand := Concatenation(_self_dir, "/../brw_aut_lower_bound.g");;
    if IsExistingFile(_cand) then
        # Read peer modules first so that brw_aut_lower_bound.g's
        # IsBound guards pick them up regardless of CWD.
        ChangeDirectoryCurrent(Concatenation(_self_dir, "/.."));
        Read("brw_aut_lower_bound.g");
        # Also load aut_nt for the IsAutomorphismCandidate helper at m=1.
        Read("aut_nt_partition.g");
        Read("aut_nt_refine.g");
        Read("aut_nt.g");
        _loaded := true;
    fi;
fi;
if not _loaded then
    Error("cannot locate brw_aut_lower_bound.g; run from ",
          "extraspecial_orbifolds/scripts/tests/.");
fi;

failures := [];

CheckEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
    else
        Print("  [FAIL] ", label, "\n");
        Print("        expected: ", expected, "\n");
        Print("        got     : ", got, "\n");
        Add(failures, label);
    fi;
end;;

CheckTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
    else
        Print("  [FAIL] ", label, "\n");
        Add(failures, label);
    fi;
end;;

# ---- Section 1: Q_8 sanity (m = 1) -----------------------------------
# At m=1, BRWConjugacyAction(1).em is the pc-group form of EmGroup(1)
# = D_8 (plus-type extraspecial 2-group of order 8). Rank of D(Vec_{D_8})
# is 22 (5 classes, centraliser irrep counts 5, 5, 4, 4, 4).
# |BRW(1)/E_+(1)| = |O+(2, F_2)| = 2.
#
# The spec (issue #239) calls this "Q_8 sanity" by analogy of rank;
# Q_8 itself (minus-type, SmallGroup(8, 4)) is not in BRW's natural
# scope, so the cross-check below uses the existing dense AutNT for
# the actual D_8 untwisted modular data — equivalent rank-22 sanity.

Print("\n========================================\n");
Print("Section 1: m = 1 (E_+(1) = D_8; \"Q_8 sanity\" per spec)\n");
Print("========================================\n");

t1 := Runtime();;
m1_result := RunBRWAutLowerBound(1, rec(verbose := true));;
t1_wall := (Runtime() - t1) / 1000.;;
Print("m = 1: wall = ", t1_wall, " s\n");

CheckEqual("m=1 rank", m1_result.verification.rank, 22);
CheckEqual("m=1 brw_lower_bound", m1_result.verification.brw_lower_bound, 2);
CheckEqual("m=1 verdict", m1_result.verification.verdict, "BOUND_VERIFIED");
CheckEqual("m=1 count_failed", m1_result.verification.count_failed, 0);
CheckEqual("m=1 count_verified", m1_result.verification.count_verified, 2);

# Cross-check: every BRW generator's sigma preserves N too (not just S),
# using the N derived from S via Verlinde. We re-derive N here for the
# small rank-22 case so we exercise the full IsAutomorphismCandidate
# pipeline.
Print("\nCross-check m=1: every generator preserves N (Verlinde-derived).\n");
m1_S := m1_result.md.S;;
m1_T := m1_result.md.T;;
m1_QD := QuantumDimensionsFromS(m1_S);;
m1_N := FusionCoefficientsFromS(m1_S);;
m1_all_N_ok := ForAll(m1_result.action.image_lists,
                       sigma -> IsAutomorphismCandidate(sigma, m1_N));;
CheckTrue("m=1: every BRW generator preserves N", m1_all_N_ok);

# Cross-check against existing dense AutNT: |Aut(N, T)| for D_8
# trivial cocycle, untwisted center.
Print("\nCross-check m=1: |Aut(N, T)| via dense AutNT vs BRW lower bound.\n");
m1_aut := AutNT(m1_N, m1_T, m1_QD);;
Print("  |Aut(N, T)| (dense) = ", m1_aut.order, "\n");
Print("  |BRW(1)/E_+(1)|     = ", m1_result.verification.brw_lower_bound, "\n");
CheckTrue("m=1: |Aut(N, T)| >= |BRW(1)/E_+(1)|",
          m1_aut.order >= m1_result.verification.brw_lower_bound);
# Anchor inequality must be tight, ratio an integer.
CheckTrue("m=1: ratio integer (|Aut| / |BRW lower bound|)",
          IsInt(m1_aut.order / m1_result.verification.brw_lower_bound));

# Sanity: each BRW-generator permutation is an honest permutation of
# [1..22] and is in <action.perms>.
Print("\nSanity m=1: BRW perms structural checks.\n");
m1_perms := m1_result.action.perms;;
CheckEqual("m=1: # BRW generators", Length(m1_perms),
           Length(GeneratorsOfGroup(m1_result.action.brw)));
m1_grp := Group(m1_perms);;
CheckEqual("m=1: |<BRW perms>| = |BRW(1)/E_+(1)|", Size(m1_grp), 2);

# ---- Section 2: E_+(3) full check (gated) ----------------------------
# Gated by A3D_INCLUDE_M3. Reaches the issue-#239 deliverable.

Print("\n========================================\n");
Print("Section 2: m = 3 (E_+(3) rank 2272, BRW lower bound 40320)\n");
Print("========================================\n");

if IsBound(A3D_INCLUDE_M3) and A3D_INCLUDE_M3 = true then
    t3 := Runtime();;
    m3_result := RunBRWAutLowerBound(3, rec(verbose := true));;
    t3_wall := (Runtime() - t3) / 1000.;;
    Print("\nm = 3: wall = ", t3_wall, " s\n");

    CheckEqual("m=3 rank", m3_result.verification.rank, 2272);
    # Empirically |BRW(3)/E_+(3)| = 40320 (= GAP's |GO+(6, F_2)|),
    # NOT 1451520 as stated in issue #239 — see header note.
    CheckEqual("m=3 brw_lower_bound",
               m3_result.verification.brw_lower_bound, 40320);
    CheckEqual("m=3 verdict", m3_result.verification.verdict,
               "BOUND_VERIFIED");
    CheckEqual("m=3 count_failed", m3_result.verification.count_failed, 0);
    CheckEqual("m=3 count_verified",
               m3_result.verification.count_verified, 40320);

    # Persist the verdict (per issue #239 acceptance criterion 2).
    OutDir := "../../computed/aut_nt/3";;
    Exec(Concatenation("mkdir -p ", OutDir));
    OutPath := Concatenation(OutDir, "/brw_lower_bound.g");;
    stream := OutputTextFile(OutPath, false);;
    SetPrintFormattingStatus(stream, false);
    PrintTo(stream,
        "# BRW lower bound verdict for E_+(3), untwisted modular data.\n",
        "#\n",
        "# Generated by extraspecial_orbifolds/scripts/tests/test_brw_aut_lower_bound.g\n",
        "# (issue #239, A-3d perf-1: BRW lower-bound check).\n",
        "#\n",
        "# Method. For each generator y of BRW(3), build the lifted\n",
        "# permutation sigma_y of the 2272 simples and verify\n",
        "#   T[sigma_y[i]] = T[i] for all i, and\n",
        "#   S[sigma_y[i]][sigma_y[j]] = S[i][j] for all (i, j).\n",
        "# S-preservation implies N-preservation via Verlinde, so each\n",
        "# sigma_y is a valid (N, T)-automorphism. The subgroup of\n",
        "# Sym(2272) generated by the sigma_y has order |BRW(3)/E_+(3)|\n",
        "#   = 40320 (matching GAP's |GO+(6, F_2)|).\n",
        "#\n",
        "# Note on the issue spec. Issue #239 (and the run_e_plus_3_aut.g\n",
        "# driver, pre-fix) state the expected lower bound as 1,451,520,\n",
        "# but the actual |BRW(3)/E_+(3)| produced by our brw_construction.g\n",
        "# is 40320. This is a math-convention error in the issue text;\n",
        "# the constructive certificate (this file) records the empirically\n",
        "# correct value.\n",
        "#\n",
        "# Time breakdown:\n",
        "#   total_wall      : end-to-end (S, T) compute + verification.\n",
        "#   verify_wall     : just the per-generator (S, T) checks plus\n",
        "#                     the subgroup-order computation.\n",
        "#\n",
        "# Reload via:\n",
        "#   data := ReadAsFunction(\"brw_lower_bound.g\")();\n",
        "\n",
        "return rec(\n",
        "    group           := \"E_+(3) untwisted\",\n",
        "    m               := 3,\n",
        "    rank            := 2272,\n",
        "    brw_lower_bound := ", m3_result.verification.brw_lower_bound, ",\n",
        "    count_verified  := ", m3_result.verification.count_verified, ",\n",
        "    count_failed    := ", m3_result.verification.count_failed, ",\n",
        "    subgroup_order  := ", m3_result.verification.subgroup_order, ",\n",
        "    total_wall      := ", t3_wall, ",\n",
        "    verify_wall     := ", m3_result.verification.time, ",\n",
        "    verdict         := \"", m3_result.verification.verdict, "\"\n",
        ");;\n");
    CloseStream(stream);
    Print("Wrote ", OutPath, "\n");
else
    Print("\nm=3 test SKIPPED. To enable, run:\n");
    Print("    A3D_INCLUDE_M3 := true;; Read(\"test_brw_aut_lower_bound.g\");\n");
fi;

# ---- Final report ----------------------------------------------------
if Length(failures) = 0 then
    Print("\ntest_brw_aut_lower_bound: PASS\n");
else
    Print("\ntest_brw_aut_lower_bound: FAIL (", Length(failures),
          " failure(s)):\n");
    for i in [1..Length(failures)] do
        Print("  - ", failures[i], "\n");
    od;
fi;

QUIT;
