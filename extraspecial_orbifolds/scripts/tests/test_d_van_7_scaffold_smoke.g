# test_d_van_7_scaffold_smoke.g
#
# D-VAN-7 scaffold smoke tests. These are intentionally LIGHT — the
# D-VAN-7 deliverables are non-executable scaffolding that wraps two
# upstream pieces still in flight:
#
#   * A-5b (#47, `run_e_plus_5_kernel.g`): the upstream HAP kernel
#     producer; expected to write `computed/transgression/5/kernel.g`.
#   * K-4b (#189 / PR #227, sibling scaffold): the K-4a-m=5 production
#     orchestrator; expected to write `k4b_m5_result.g`.
#
# The full D-VAN-7 production run cannot execute until A-5b lands the
# kernel file. The cross-validation harness against K-4b additionally
# requires k4b_m5_result.g (which itself depends on #200 + #220).
#
# Until those land, these smoke tests verify:
#
#   T1. Driver script syntax (`bash -n run_d_van_7_m5.sh`).
#   T2. Cross-validation harness parses (the file Read's all the way
#       through its prologue, hits the IsExistingFile guard cleanly,
#       and emits a BLOCKED line — no Syntax errors).
#   T3. Interpretation note template is valid markdown with the
#       expected section headers.
#
# Run from absolute path:
#   gap -q -b /Users/.../tests/test_d_van_7_scaffold_smoke.g

# ---- Test bookkeeping --------------------------------------------------
DVAN7S_PASSES   := 0;;
DVAN7S_FAILURES := [];;

DVAN7SAssertEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
        DVAN7S_PASSES := DVAN7S_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Print("         expected: ", expected, "\n");
        Print("         got:      ", got, "\n");
        Add(DVAN7S_FAILURES, label);
    fi;
end;;

DVAN7SAssertTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
        DVAN7S_PASSES := DVAN7S_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Add(DVAN7S_FAILURES, label);
    fi;
end;;

# ---- Locate self and worktree -----------------------------------------
DVAN7S_SELF := INPUT_FILENAME();;
if DVAN7S_SELF = fail or DVAN7S_SELF = "stream" then
    Error("test_d_van_7_scaffold_smoke.g: INPUT_FILENAME() unavailable; ",
          "Read the file by its absolute path.");
fi;
DVAN7S_SELFDIR := DVAN7S_SELF{
    [1..Length(DVAN7S_SELF) - Length("/test_d_van_7_scaffold_smoke.g")]};;
DVAN7S_SCRIPTSDIR := DVAN7S_SELFDIR{
    [1..Length(DVAN7S_SELFDIR) - Length("/tests")]};;
DVAN7S_WT_ROOT := DVAN7S_SCRIPTSDIR{
    [1..Length(DVAN7S_SCRIPTSDIR) - Length("/extraspecial_orbifolds/scripts")]};;

Print("=================================================================\n");
Print("test_d_van_7_scaffold_smoke.g\n");
Print("=================================================================\n");
Print("self          : ", DVAN7S_SELF, "\n");
Print("scripts dir   : ", DVAN7S_SCRIPTSDIR, "\n");
Print("worktree root : ", DVAN7S_WT_ROOT, "\n");

DVAN7S_DRIVER := Concatenation(DVAN7S_SCRIPTSDIR, "/run_d_van_7_m5.sh");;
DVAN7S_XCHECK := Concatenation(DVAN7S_SCRIPTSDIR, "/d_van_7_xcheck_k4a.g");;
DVAN7S_TEMPLATE := Concatenation(DVAN7S_WT_ROOT,
    "/docs/superpowers/research/TEMPLATE-d_van_7_m5_verdict.md");;

DVAN7SAssertTrue("driver exists on disk", IsExistingFile(DVAN7S_DRIVER));
DVAN7SAssertTrue("xcheck harness exists on disk",
                 IsExistingFile(DVAN7S_XCHECK));
DVAN7SAssertTrue("interpretation template exists on disk",
                 IsExistingFile(DVAN7S_TEMPLATE));

# ---- T1: driver script syntax check -----------------------------------
# Use `bash -n` to syntax-check without executing. Exit status 0 = OK.
# `Exec` does not capture exit status directly, so we use a small trick:
# redirect to a tempfile that records the status, then read it back.
Print("\n-----------------------------------------------------------------\n");
Print("T1: bash -n run_d_van_7_m5.sh\n");
Print("-----------------------------------------------------------------\n");

DVAN7S_T1_STATUSFILE := Concatenation(DVAN7S_SELFDIR, "/.dvan7s_t1_status");;
if IsExistingFile(DVAN7S_T1_STATUSFILE) then
    Exec(Concatenation("rm -f '", DVAN7S_T1_STATUSFILE, "'"));
fi;
Exec(Concatenation(
    "bash -n '", DVAN7S_DRIVER, "' 2>&1; echo $? > '",
    DVAN7S_T1_STATUSFILE, "'"));

if IsExistingFile(DVAN7S_T1_STATUSFILE) then
    # The status file holds the literal exit code (e.g. "0\n");
    # InputTextFile + ReadAll gets us the raw bytes, which we then
    # strip and compare to "0".
    DVAN7S_T1_STATUS := InputTextFile(DVAN7S_T1_STATUSFILE);
    DVAN7S_T1_STR := ReadAll(DVAN7S_T1_STATUS);
    CloseStream(DVAN7S_T1_STATUS);
    # Strip whitespace.
    while Length(DVAN7S_T1_STR) > 0
          and DVAN7S_T1_STR[Length(DVAN7S_T1_STR)] in [' ', '\n', '\t', '\r'] do
        DVAN7S_T1_STR := DVAN7S_T1_STR{[1..Length(DVAN7S_T1_STR) - 1]};
    od;
    DVAN7SAssertEqual("bash -n run_d_van_7_m5.sh returns exit 0",
                      DVAN7S_T1_STR, "0");
else
    DVAN7SAssertTrue("status file written by `bash -n`", false);
fi;

# ---- T2: cross-validation harness parses ------------------------------
# Reading the harness should not throw a parse error. The harness will
# itself QUIT or Error if downstream siblings are missing, so we run
# it in a child gap process via Exec rather than via Read in this
# session (which would QUIT us too).
#
# We just want to confirm syntactic well-formedness, NOT functional
# correctness — that needs the upstream pieces (A-5b kernel.g and K-4b
# k4b_m5_result.g) to be present.
Print("\n-----------------------------------------------------------------\n");
Print("T2: cross-validation harness loads\n");
Print("-----------------------------------------------------------------\n");

DVAN7S_XCHECK_STREAM := InputTextFile(DVAN7S_XCHECK);;
DVAN7S_XCHECK_SRC := ReadAll(DVAN7S_XCHECK_STREAM);;
CloseStream(DVAN7S_XCHECK_STREAM);

DVAN7SAssertTrue("xcheck file is non-empty",
                 Length(DVAN7S_XCHECK_SRC) > 100);
DVAN7SAssertTrue("xcheck references d_van_7 result file",
                 PositionSublist(DVAN7S_XCHECK_SRC,
                                  "m5_result.g") <> fail);
DVAN7SAssertTrue("xcheck references RESULT (K-4b binding)",
                 PositionSublist(DVAN7S_XCHECK_SRC, "RESULT") <> fail);
DVAN7SAssertTrue("xcheck references k4b_m5_result.g",
                 PositionSublist(DVAN7S_XCHECK_SRC,
                                  "k4b_m5_result.g") <> fail);
DVAN7SAssertTrue("xcheck has CONSISTENT branch",
                 PositionSublist(DVAN7S_XCHECK_SRC, "CONSISTENT") <> fail);
DVAN7SAssertTrue("xcheck has INCONSISTENT branch",
                 PositionSublist(DVAN7S_XCHECK_SRC, "INCONSISTENT") <> fail);
DVAN7SAssertTrue("xcheck has BLOCKED-D-VAN-7 path",
                 PositionSublist(DVAN7S_XCHECK_SRC,
                                  "BLOCKED-D-VAN-7") <> fail);
DVAN7SAssertTrue("xcheck has BLOCKED-K-4B path",
                 PositionSublist(DVAN7S_XCHECK_SRC,
                                  "BLOCKED-K-4B") <> fail);

# Try a brace-balance heuristic as a syntactic sanity check.
DVAN7S_T2_OPEN := 0;;
DVAN7S_T2_CLOSE := 0;;
DVAN7S_T2_I := 1;;
while DVAN7S_T2_I <= Length(DVAN7S_XCHECK_SRC) do
    if DVAN7S_XCHECK_SRC[DVAN7S_T2_I] = '(' then
        DVAN7S_T2_OPEN := DVAN7S_T2_OPEN + 1;
    elif DVAN7S_XCHECK_SRC[DVAN7S_T2_I] = ')' then
        DVAN7S_T2_CLOSE := DVAN7S_T2_CLOSE + 1;
    fi;
    DVAN7S_T2_I := DVAN7S_T2_I + 1;
od;
DVAN7SAssertEqual("xcheck parens balance",
                  DVAN7S_T2_OPEN, DVAN7S_T2_CLOSE);

# Subprocess parse-check via a child gap process. We want to confirm
# that GAP reads the xcheck file all the way through without a
# SyntaxError, but we don't want to exercise the full D-VAN-3 load
# chain (heavy: HAP + Cohomology3 setup, takes minutes at m = 5).
#
# Strategy: copy the xcheck file into a SCRATCH directory and Read
# *that* copy. The xcheck computes `_DVAN7_XCHECK_DIR` from
# INPUT_FILENAME(), which for the copy resolves to the scratch dir.
# It then looks for `<scratch>/../../computed/d_van_7/m5_result.g`.
# We stage that file as MISSING -> xcheck hits the
# "BLOCKED-D-VAN-7: ... not found" early QUIT, never touching
# detecting_family_vanish.g. Fast (~3 s).
#
# A parse error would show up as a SyntaxError in the subprocess
# output BEFORE the BLOCKED line. The probe checks both.
DVAN7S_T2_PROBE_DIR := Concatenation(DVAN7S_SELFDIR, "/d_van_7_scaffold");;
if not IsExistingFile(DVAN7S_T2_PROBE_DIR) then
    Exec(Concatenation("mkdir -p '", DVAN7S_T2_PROBE_DIR, "'"));
fi;
# Copy the xcheck into the scratch dir so its INPUT_FILENAME-based
# sibling lookups all resolve to the scratch dir (where no result
# file lives, so the early QUIT fires).
DVAN7S_T2_XCHECK_COPY :=
    Concatenation(DVAN7S_T2_PROBE_DIR, "/d_van_7_xcheck_k4a.g");;
Exec(Concatenation("cp '", DVAN7S_XCHECK, "' '",
                   DVAN7S_T2_XCHECK_COPY, "'"));
# Ensure no stale result file exists where the xcheck would look.
# xcheck's path is <_DVAN7_XCHECK_DIR>/../../computed/d_van_7/m5_result.g.
# Relative to the scratch dir at <tests>/d_van_7_scaffold/, the
# computed/d_van_7 dir would resolve outside the scratch tree (two
# levels up). To prevent accidental hits, we don't pre-stage either
# the D-VAN or K-4b result files. The xcheck should hit
# BLOCKED-D-VAN-7 first (since it checks the D-VAN result first).
#
# NOTE: the xcheck reads `<scratch>/../../computed/d_van_7/m5_result.g`
# which on the scratch's path resolves to
# <SCRIPTSDIR>/tests/computed/d_van_7/m5_result.g. As long as no such
# file exists (no real worktree puts data files in <tests>), the
# BLOCKED path fires reliably.

DVAN7S_T2_PROBE := Concatenation(DVAN7S_T2_PROBE_DIR, "/probe_t2.g");;
DVAN7S_T2_OUTFILE :=
    Concatenation(DVAN7S_T2_PROBE_DIR, "/probe_t2.out");;

# Write the probe. PARSE_PROBE_START marks the start of execution;
# the BLOCKED line proves xcheck parsed cleanly AND reached its
# guard logic.
PrintTo(DVAN7S_T2_PROBE,
    "# Probe for test_d_van_7_scaffold_smoke.g T2.\n",
    "Print(\"PARSE_PROBE_START\\n\");\n",
    "Read(\"", DVAN7S_T2_XCHECK_COPY, "\");\n",
    "Print(\"PARSE_PROBE_AFTER_READ\\n\");\n",
    "QUIT;\n"
);

# Run the probe in a child GAP.
Exec(Concatenation("cd '", DVAN7S_T2_PROBE_DIR, "' && ",
    "gap -q -b -c 'Read(\"", DVAN7S_T2_PROBE, "\");' > '",
    DVAN7S_T2_OUTFILE, "' 2>&1"));

if IsExistingFile(DVAN7S_T2_OUTFILE) then
    DVAN7S_T2_STREAM := InputTextFile(DVAN7S_T2_OUTFILE);
    DVAN7S_T2_OUT := ReadAll(DVAN7S_T2_STREAM);
    CloseStream(DVAN7S_T2_STREAM);
    DVAN7SAssertTrue("subprocess emitted PARSE_PROBE_START (file tokenised)",
                     PositionSublist(DVAN7S_T2_OUT,
                                      "PARSE_PROBE_START") <> fail);
    DVAN7SAssertTrue("no Syntax error in xcheck file",
                     PositionSublist(DVAN7S_T2_OUT, "Syntax error") = fail);
    # The xcheck's early-QUIT guard prints "BLOCKED" when a result
    # file is missing — confirming xcheck Read all the way through
    # its prologue and hit the IsExistingFile guard cleanly.
    DVAN7SAssertTrue("xcheck reached its result-file existence guard",
                     PositionSublist(DVAN7S_T2_OUT, "BLOCKED") <> fail);
else
    DVAN7SAssertTrue("subprocess produced output", false);
fi;

# ---- T3: interpretation note template valid ---------------------------
Print("\n-----------------------------------------------------------------\n");
Print("T3: interpretation note template valid markdown\n");
Print("-----------------------------------------------------------------\n");

DVAN7S_TEMPLATE_STREAM := InputTextFile(DVAN7S_TEMPLATE);;
DVAN7S_TEMPLATE_SRC := ReadAll(DVAN7S_TEMPLATE_STREAM);;
CloseStream(DVAN7S_TEMPLATE_STREAM);

DVAN7SAssertTrue("template file is non-empty",
                 Length(DVAN7S_TEMPLATE_SRC) > 100);

# Required H1 / H2 headers, per the K-4b spec § "Interpretation note"
# pattern (mirrored for D-VAN-7).
for DVAN7S_T3_HEADER in
    [ "# D-VAN-7 m = 5 verdict",
      "## Section 1: Verdict",
      "## Section 2: Per-generator detail",
      "## Section 3: Cross-validation against K-4b",
      "## Section 4: Confidence assessment",
      "## Section 5: Implications for Keller's conjecture at m = 5",
      "## Section 6: Reproducibility",
      "## Section 7: Follow-ups" ] do
    DVAN7SAssertTrue(
        Concatenation("template has header: ", DVAN7S_T3_HEADER),
        PositionSublist(DVAN7S_TEMPLATE_SRC, DVAN7S_T3_HEADER) <> fail);
od;

# The template itself should have placeholders rather than concrete
# values. A few sanity tokens:
DVAN7SAssertTrue("template references run_d_van_7_m5.sh",
                 PositionSublist(DVAN7S_TEMPLATE_SRC,
                                  "run_d_van_7_m5.sh") <> fail);
DVAN7SAssertTrue("template references d_van_7_xcheck_k4a.g",
                 PositionSublist(DVAN7S_TEMPLATE_SRC,
                                  "d_van_7_xcheck_k4a.g") <> fail);
DVAN7SAssertTrue("template references the D-VAN spec",
                 PositionSublist(DVAN7S_TEMPLATE_SRC,
                                  "2026-05-15-detecting-family-vanishing-test-design.md") <> fail);
DVAN7SAssertTrue("template references A-5b kernel.g",
                 PositionSublist(DVAN7S_TEMPLATE_SRC,
                                  "kernel.g") <> fail);

# ---- Final summary ----------------------------------------------------
Print("\n=================================================================\n");
Print("Final summary\n");
Print("=================================================================\n");
Print("  passes   : ", DVAN7S_PASSES, "\n");
Print("  failures : ", Length(DVAN7S_FAILURES), "\n");
if Length(DVAN7S_FAILURES) = 0 then
    Print("\ntest_d_van_7_scaffold_smoke: PASS\n");
    QUIT_GAP(0);
else
    Print("\ntest_d_van_7_scaffold_smoke: FAIL (",
          Length(DVAN7S_FAILURES), "):\n");
    for DVAN7S_F in DVAN7S_FAILURES do
        Print("  - ", DVAN7S_F, "\n");
    od;
    QUIT_GAP(1);
fi;
