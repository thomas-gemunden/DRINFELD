# test_ct_modular_data.g
#
# K-4a-T5b (issue #199): tests for `ComputeCTModularData` in
# `extraspecial_orbifolds/scripts/ct_modular_data.g`.
#
# Per the T4a (#196 / PR #206) downscope, the K-4a-T5b implementation
# computes (S, T) under ε ≡ 1 / σ ≡ 1, so the function reduces to the
# standard untwisted Bantay/CGR formula. The test cases below verify:
#
#   T1: untwisted regression at H = Q_8 — output should match
#       `LoadModularData(8, 4, 1)` (the trivial cocycle) up to a
#       row/column permutation (checked via `JointPermutationMatcher`).
#   T2: untwisted regression at H = D_8 — same idea, against
#       `LoadModularData(8, 3, 1)`.
#   T3: abelian regression at H = Z_2 × Z_2 — agreement with the dense
#       `ComputeUntwistedModularData(H)` (entry-by-entry, fixed order).
#   T4: modular relations at H = Q_8 — verify S^2 commutes with T (i.e.
#       (ST)^3 = c·S^2 for some scalar c) and S^4 is diagonal.
#   T5: T diagonal and unitary — every diagonal entry is a cyclotomic
#       root of unity (|x| = 1), and off-diagonal entries are zero.
#   T6: performance — at H = E_+(3) untwisted, full (S, T) should
#       compute in < 5 min wall.
#
# The performance test (T6) is gated behind the env var
# `CT_MD_RUN_E_PLUS_3=1` so the per-PR test suite stays fast. The
# small-group tests (T1-T5) are always run.
#
# Run from absolute path:
#   gap -q -b /Users/thomasgemunden/.../tests/test_ct_modular_data.g

# ---- Test bookkeeping --------------------------------------------------

CT_MD_PASSES   := 0;;
CT_MD_FAILURES := [];;

CTMDAssertEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
        CT_MD_PASSES := CT_MD_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Print("         expected: ", expected, "\n");
        Print("         got:      ", got, "\n");
        Add(CT_MD_FAILURES, label);
    fi;
end;;

CTMDAssertTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
        CT_MD_PASSES := CT_MD_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Add(CT_MD_FAILURES, label);
    fi;
end;;

# ---- Locate worktree, scripts, sibling files ---------------------------

CTMD_SELF := INPUT_FILENAME();;
if CTMD_SELF = fail or CTMD_SELF = "stream" then
    Error("test_ct_modular_data.g: INPUT_FILENAME() unavailable; ",
          "Read the file by its absolute path.");
fi;
CTMD_SELFDIR := CTMD_SELF{
    [1..Length(CTMD_SELF) - Length("/test_ct_modular_data.g")]};;
CTMD_SCRIPTSDIR := CTMD_SELFDIR{
    [1..Length(CTMD_SELFDIR) - Length("/tests")]};;
CTMD_WT_ROOT := CTMD_SCRIPTSDIR{
    [1..Length(CTMD_SCRIPTSDIR) - Length("/extraspecial_orbifolds/scripts")]};;

# Order of loads matters:
# 1. src/modular_data.g for LoadModularData (writes Modular_Data/...).
# 2. untwisted_modular_data.g for BuildSimpleIndex / EvalIrr / ComputeUntwistedT etc.
# 3. krr_projector.g for BuildIntertwinerDataUntwisted / ProjectorFormula.
# 4. joint_permutation_matcher.g for JointPermutationMatcher.
# 5. ct_modular_data.g for ComputeCTModularData (under test).

Read(Concatenation(CTMD_WT_ROOT, "/src/modular_data.g"));
CTMDAssertTrue("LoadModularData bound (src/modular_data.g)",
               IsBound(LoadModularData));

Read(Concatenation(CTMD_SCRIPTSDIR, "/untwisted_modular_data.g"));
CTMDAssertTrue("BuildSimpleIndex bound",
               IsBound(BuildSimpleIndex));
CTMDAssertTrue("ComputeUntwistedModularData bound",
               IsBound(ComputeUntwistedModularData));

Read(Concatenation(CTMD_SCRIPTSDIR, "/krr_projector.g"));
CTMDAssertTrue("BuildIntertwinerDataUntwisted bound",
               IsBound(BuildIntertwinerDataUntwisted));
CTMDAssertTrue("ProjectorFormula bound", IsBound(ProjectorFormula));

Read(Concatenation(CTMD_SCRIPTSDIR, "/joint_permutation_matcher.g"));
CTMDAssertTrue("JointPermutationMatcher bound",
               IsBound(JointPermutationMatcher));

Read(Concatenation(CTMD_SCRIPTSDIR, "/ct_modular_data.g"));
CTMDAssertTrue("ComputeCTModularData bound",
               IsBound(ComputeCTModularData));

# ---- Locate the modular_data tree --------------------------------------

CTMD_MD_ROOT := fail;;
for CTMD_CAND in
    [ Concatenation(CTMD_WT_ROOT, "/../modular_data"),
      "/Users/thomasgemunden/Projects/group_cohomology/modular_data" ] do
    if CTMD_MD_ROOT = fail
       and IsExistingFile(Concatenation(CTMD_CAND, "/8/4/1.txt")) then
        CTMD_MD_ROOT := CTMD_CAND;
    fi;
od;
if CTMD_MD_ROOT = fail then
    Error("test_ct_modular_data.g: cannot locate modular_data tree.");
fi;
Print("modular_data root: ", CTMD_MD_ROOT, "\n");

# ---- Prepare Modular_Data symlink and chdir there ----------------------
# Mirrors the convention used by test_q8_classifier.g.

CTMD_LINKDIR := Concatenation(CTMD_SELFDIR, "/k4a/ct_modular_data");;
if not IsExistingFile(CTMD_LINKDIR) then
    Exec(Concatenation("mkdir -p '", CTMD_LINKDIR, "'"));
fi;
CTMD_LINKPATH := Concatenation(CTMD_LINKDIR, "/Modular_Data");;
if not IsExistingFile(CTMD_LINKPATH) then
    Exec(Concatenation("ln -s '", CTMD_MD_ROOT, "' '",
                       CTMD_LINKPATH, "'"));
fi;
if not IsExistingFile(Concatenation(CTMD_LINKPATH, "/8/4/1.txt")) then
    Error("test_ct_modular_data.g: Modular_Data symlink at ",
          CTMD_LINKPATH, " does not resolve to a tree containing 8/4/1.txt.");
fi;
ChangeDirectoryCurrent(CTMD_LINKDIR);

# =======================================================================
# T1: Q_8 untwisted regression
# =======================================================================
# H = Q_8 = SmallGroup(8, 4). Compute (S, T) via ComputeCTModularData
# applied to BuildIntertwinerDataUntwisted(Q_8), and verify that this
# matches LoadModularData(8, 4, 1) (the trivial-cocycle stored data) up
# to a permutation of simples (since GAP's class ordering and the on-disk
# data's class ordering need not coincide).

Print("\n=== T1: H = Q_8 untwisted regression ===\n");
CTMD_Q8 := SmallGroup(8, 4);;
CTMD_T_T1 := Runtime();;
CTMD_DATA_Q8 := BuildIntertwinerDataUntwisted(CTMD_Q8);;
CTMD_OUT_Q8 := ComputeCTModularData(CTMD_DATA_Q8, CTMD_Q8);;
CTMD_T_T1_WALL := (Runtime() - CTMD_T_T1) / 1000.;;
Print("  ComputeCTModularData(Q_8) wall: ", CTMD_T_T1_WALL, " s\n");

CTMDAssertTrue("Q_8: S is rank 22 (= |Irr(D^0(Q_8))|)",
               Length(CTMD_OUT_Q8.S) = 22 and Length(CTMD_OUT_Q8.S[1]) = 22);
CTMDAssertTrue("Q_8: T is DiagonalMat 22x22",
               Length(CTMD_OUT_Q8.T) = 22
               and Length(CTMD_OUT_Q8.T[1]) = 22);
CTMDAssertTrue("Q_8: |simples| = 22",
               Length(CTMD_OUT_Q8.simples) = 22);

CTMD_STORED_Q8 := LoadModularData(8, 4, 1);;
CTMD_M_Q8 := JointPermutationMatcher(
    CTMD_STORED_Q8.S, CTMD_STORED_Q8.T,
    CTMD_OUT_Q8.S, DiagonalOfMat(CTMD_OUT_Q8.T));;
Print("  Q_8 matcher: ok = ", CTMD_M_Q8.ok, "\n");
if not CTMD_M_Q8.ok and IsBound(CTMD_M_Q8.reason) then
    Print("    reason: ", CTMD_M_Q8.reason, "\n");
fi;
CTMDAssertTrue("Q_8: matches stored trivial cocycle LoadModularData(8, 4, 1)",
               CTMD_M_Q8.ok);
if CTMD_M_Q8.ok then
    CTMDAssertTrue("Q_8: pi is a permutation of [1..22]",
                   IsList(CTMD_M_Q8.pi)
                   and Length(CTMD_M_Q8.pi) = 22
                   and SortedList(CTMD_M_Q8.pi) = [1..22]);
fi;

# =======================================================================
# T2: D_8 untwisted regression
# =======================================================================
# H = D_8 = SmallGroup(8, 3). Trivial cocycle is at index k=1 (the
# all-zero cocycle vector — see modular_data/8/3/3-cocycles.txt line 1).

Print("\n=== T2: H = D_8 untwisted regression ===\n");
CTMD_D8 := SmallGroup(8, 3);;
CTMD_T_T2 := Runtime();;
CTMD_DATA_D8 := BuildIntertwinerDataUntwisted(CTMD_D8);;
CTMD_OUT_D8 := ComputeCTModularData(CTMD_DATA_D8, CTMD_D8);;
CTMD_T_T2_WALL := (Runtime() - CTMD_T_T2) / 1000.;;
Print("  ComputeCTModularData(D_8) wall: ", CTMD_T_T2_WALL, " s\n");

CTMDAssertTrue("D_8: S is rank 22 (= |Irr(D^0(D_8))|)",
               Length(CTMD_OUT_D8.S) = 22 and Length(CTMD_OUT_D8.S[1]) = 22);
CTMDAssertTrue("D_8: T is DiagonalMat 22x22",
               Length(CTMD_OUT_D8.T) = 22
               and Length(CTMD_OUT_D8.T[1]) = 22);
CTMDAssertTrue("D_8: |simples| = 22",
               Length(CTMD_OUT_D8.simples) = 22);

CTMD_STORED_D8 := LoadModularData(8, 3, 1);;
CTMD_M_D8 := JointPermutationMatcher(
    CTMD_STORED_D8.S, CTMD_STORED_D8.T,
    CTMD_OUT_D8.S, DiagonalOfMat(CTMD_OUT_D8.T));;
Print("  D_8 matcher: ok = ", CTMD_M_D8.ok, "\n");
if not CTMD_M_D8.ok and IsBound(CTMD_M_D8.reason) then
    Print("    reason: ", CTMD_M_D8.reason, "\n");
fi;
CTMDAssertTrue("D_8: matches stored trivial cocycle LoadModularData(8, 3, 1)",
               CTMD_M_D8.ok);
if CTMD_M_D8.ok then
    CTMDAssertTrue("D_8: pi is a permutation of [1..22]",
                   IsList(CTMD_M_D8.pi)
                   and Length(CTMD_M_D8.pi) = 22
                   and SortedList(CTMD_M_D8.pi) = [1..22]);
fi;

# =======================================================================
# T3: Abelian regression at H = Z_2 x Z_2
# =======================================================================
# H = Z_2 x Z_2 = SmallGroup(4, 2). |G| = 4, all classes are singletons,
# all centralisers are H, so |Irr(C_H(g))| = 4 for every class, total
# 16 simples. Compare entry-by-entry against the dense
# ComputeUntwistedModularData(H), which uses the same conventions
# (idx ordering, complex-conjugate convention) — exact equality
# expected, no permutation needed.

Print("\n=== T3: H = Z_2 x Z_2 abelian regression ===\n");
CTMD_Z22 := SmallGroup(4, 2);;  # = Z_2 x Z_2
CTMD_T_T3 := Runtime();;
CTMD_DATA_Z22 := BuildIntertwinerDataUntwisted(CTMD_Z22);;
CTMD_OUT_Z22 := ComputeCTModularData(CTMD_DATA_Z22, CTMD_Z22);;
CTMD_DENSE_Z22 := ComputeUntwistedModularData(CTMD_Z22);;
CTMD_T_T3_WALL := (Runtime() - CTMD_T_T3) / 1000.;;
Print("  ComputeCTModularData(Z_2 x Z_2) wall: ", CTMD_T_T3_WALL, " s\n");
Print("  ComputeUntwistedModularData(Z_2 x Z_2) rank: ",
      CTMD_DENSE_Z22.idx.rank, "\n");

CTMDAssertEqual("Z_2 x Z_2: rank = 16",
                Length(CTMD_OUT_Z22.S), 16);
CTMDAssertEqual("Z_2 x Z_2: S matches dense untwisted S (entry-by-entry)",
                CTMD_OUT_Z22.S, CTMD_DENSE_Z22.S);
CTMDAssertEqual("Z_2 x Z_2: T diag matches dense untwisted T (entry-by-entry)",
                DiagonalOfMat(CTMD_OUT_Z22.T), CTMD_DENSE_Z22.T);

# =======================================================================
# T4: Modular relations at H = Q_8
# =======================================================================
# Verify the modular tensor category axioms:
#   * S^2 = (ST)^3 up to a scalar (the central-charge phase).
#   * S^4 = I (so S^2 is an involution up to sign).
#
# More precisely (Bakalov-Kirillov, Lectures on TQFT, eq 3.1.6):
#   (ST)^3 = e^{2 pi i c / 8} * S^2
#   S^4 = diag of charge-conjugation eigenvalues, lies in {±1}^N.
# For the trivial cocycle, central charge c = 0 (mod 8), so (ST)^3 = S^2.

Print("\n=== T4: Modular relations at H = Q_8 ===\n");
CTMD_S_Q8 := CTMD_OUT_Q8.S;;
CTMD_T_Q8 := CTMD_OUT_Q8.T;;
CTMD_S_Q8_SQ := CTMD_S_Q8 * CTMD_S_Q8;;
CTMD_ST_Q8 := CTMD_S_Q8 * CTMD_T_Q8;;
CTMD_ST_Q8_CUBE := CTMD_ST_Q8 * CTMD_ST_Q8 * CTMD_ST_Q8;;

# (ST)^3 = c · S^2: check ST_cube / S_sq is a scalar matrix where S_sq
# has nonzero entries. Equivalently: there exists c such that
# ST_cube[i][j] = c · S_sq[i][j] for all (i, j) with S_sq[i][j] != 0,
# and ST_cube[i][j] = 0 elsewhere.
# For the trivial cocycle, c = 1 (central charge 0 mod 8). So just check
# ST_cube = S_sq.
CTMDAssertEqual("Q_8 untwisted: (ST)^3 = S^2 (trivial cocycle, c = 0)",
                CTMD_ST_Q8_CUBE, CTMD_S_Q8_SQ);

# S^4 is diagonal with entries in {1} for the trivial cocycle (the
# regular rep is self-dual on Z(Vec_G) for any G).
CTMD_S_Q8_4 := CTMD_S_Q8_SQ * CTMD_S_Q8_SQ;;
CTMDAssertTrue("Q_8 untwisted: S^4 is diagonal",
               ForAll([1..22], i ->
                   ForAll([1..22], j ->
                       i = j or CTMD_S_Q8_4[i][j] = 0)));
# At trivial cocycle, S^4 = I (charge conjugation is identity on the
# self-dual sectors of Vec_{Q_8}).
CTMDAssertTrue("Q_8 untwisted: S^4 = I",
               CTMD_S_Q8_4 = IdentityMat(22));

# =======================================================================
# T5: T diagonal and unitary
# =======================================================================
# Every T entry should be a root of unity (since χ(a) and χ(e) are
# algebraic integers with χ(a) / χ(e) of absolute value 1 when (a, χ)
# is a simple of Z(Vec_G) untwisted). The off-diagonal entries should be
# zero by construction.

Print("\n=== T5: T is diagonal and unitary ===\n");
CTMD_TVEC_Q8 := DiagonalOfMat(CTMD_T_Q8);;

# Off-diagonal zero check.
CTMDAssertTrue("Q_8: T off-diagonal is zero",
               ForAll([1..22], i ->
                   ForAll([1..22], j ->
                       i = j or CTMD_T_Q8[i][j] = 0)));

# Each diagonal entry is a root of unity: x * conj(x) = 1.
CTMDAssertTrue("Q_8: every T_ii * conj(T_ii) = 1 (root of unity)",
               ForAll(CTMD_TVEC_Q8,
                   x -> x * ComplexConjugate(x) = 1));

# All entries are cyclotomic (this is automatic in GAP for our inputs
# but a useful sanity check that we're not getting floats anywhere).
CTMDAssertTrue("Q_8: every T_ii is a cyclotomic",
               ForAll(CTMD_TVEC_Q8, IsCyc));

# =======================================================================
# T6: Performance at H = E_+(3) — gated on env var
# =======================================================================
# The task brief gives a 5-min budget for ComputeCTModularData on
# E_+(3) (rank ~2272). This test is skipped by default; set
# CT_MD_RUN_E_PLUS_3=1 to enable.

CTMD_RUN_EPLUS3 := fail;;
if IsBound(GAPInfo) and IsBound(GAPInfo.SystemEnvironment) then
    if IsBound(GAPInfo.SystemEnvironment.CT_MD_RUN_E_PLUS_3) then
        CTMD_RUN_EPLUS3 := GAPInfo.SystemEnvironment.CT_MD_RUN_E_PLUS_3;
    fi;
fi;

if CTMD_RUN_EPLUS3 = "1" then
    Print("\n=== T6: H = E_+(3) untwisted performance ===\n");
    CTMD_E3 := SmallGroup(128, 2326);;
    Print("  building intertwiner_data ...\n");
    CTMD_T_BUILD := Runtime();;
    CTMD_DATA_E3 := BuildIntertwinerDataUntwisted(CTMD_E3);;
    CTMD_T_BUILD_WALL := (Runtime() - CTMD_T_BUILD) / 1000.;;
    Print("  intertwiner_data built in ", CTMD_T_BUILD_WALL, " s\n");
    Print("  rank = ", CTMD_DATA_E3.idx.rank, "\n");

    CTMD_T_T6 := Runtime();;
    CTMD_OUT_E3 := ComputeCTModularData(CTMD_DATA_E3, CTMD_E3);;
    CTMD_T_T6_WALL := (Runtime() - CTMD_T_T6) / 1000.;;
    Print("  ComputeCTModularData(E_+(3)) wall: ",
          CTMD_T_T6_WALL, " s\n");

    CTMDAssertTrue("E_+(3): rank = 2272",
                   Length(CTMD_OUT_E3.S) = 2272);
    CTMDAssertTrue("E_+(3): wall < 300 s (5 min budget)",
                   CTMD_T_T6_WALL < 300.0);
else
    Print("\n=== T6: H = E_+(3) performance (skipped, set CT_MD_RUN_E_PLUS_3=1 to enable) ===\n");
fi;

# ---- Final summary -----------------------------------------------------

Print("\n=== Final summary ===\n");
Print("  passes:   ", CT_MD_PASSES, "\n");
Print("  failures: ", Length(CT_MD_FAILURES), "\n");
if Length(CT_MD_FAILURES) = 0 then
    Print("\ntest_ct_modular_data: PASS\n");
else
    Print("\ntest_ct_modular_data: FAIL (", Length(CT_MD_FAILURES), "):\n");
    for CTMD_F in CT_MD_FAILURES do
        Print("  - ", CTMD_F, "\n");
    od;
fi;

QUIT;
