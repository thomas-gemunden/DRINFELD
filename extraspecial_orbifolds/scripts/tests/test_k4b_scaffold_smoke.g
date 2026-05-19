# test_k4b_scaffold_smoke.g
#
# K-4b scaffold smoke tests. These are intentionally LIGHT — the K-4b
# deliverables are non-executable scaffolding that wraps two upstream
# pieces still in flight:
#
#   * #200 (K-4a-T6 orchestrator, `K4aClassify`)
#   * #220 (sparse trace, `BuildKRRSpectralCharactersSparse`)
#
# The full K-4b production run cannot execute until both merge.
# Until then, these smoke tests verify:
#
#   T1. Driver script syntax (`bash -n run_k4b_m5.sh`).
#   T2. Cross-validation harness parses (GAP `Read` doesn't error;
#       functions may not be callable end-to-end yet — that's expected
#       because dependent siblings are also still in flight — but the
#       file itself must be syntactically valid).
#   T3. Interpretation note template is valid markdown with the
#       expected section headers.
#
# Run from absolute path:
#   gap -q -b /Users/.../tests/test_k4b_scaffold_smoke.g

# ---- Test bookkeeping --------------------------------------------------
K4BS_PASSES   := 0;;
K4BS_FAILURES := [];;

K4BSAssertEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
        K4BS_PASSES := K4BS_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Print("         expected: ", expected, "\n");
        Print("         got:      ", got, "\n");
        Add(K4BS_FAILURES, label);
    fi;
end;;

K4BSAssertTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
        K4BS_PASSES := K4BS_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Add(K4BS_FAILURES, label);
    fi;
end;;

# ---- Locate self and worktree -----------------------------------------
K4BS_SELF := INPUT_FILENAME();;
if K4BS_SELF = fail or K4BS_SELF = "stream" then
    Error("test_k4b_scaffold_smoke.g: INPUT_FILENAME() unavailable; ",
          "Read the file by its absolute path.");
fi;
K4BS_SELFDIR := K4BS_SELF{
    [1..Length(K4BS_SELF) - Length("/test_k4b_scaffold_smoke.g")]};;
K4BS_SCRIPTSDIR := K4BS_SELFDIR{
    [1..Length(K4BS_SELFDIR) - Length("/tests")]};;
K4BS_WT_ROOT := K4BS_SCRIPTSDIR{
    [1..Length(K4BS_SCRIPTSDIR) - Length("/extraspecial_orbifolds/scripts")]};;

Print("=================================================================\n");
Print("test_k4b_scaffold_smoke.g\n");
Print("=================================================================\n");
Print("self          : ", K4BS_SELF, "\n");
Print("scripts dir   : ", K4BS_SCRIPTSDIR, "\n");
Print("worktree root : ", K4BS_WT_ROOT, "\n");

K4BS_DRIVER := Concatenation(K4BS_SCRIPTSDIR, "/run_k4b_m5.sh");;
K4BS_XCHECK := Concatenation(K4BS_SCRIPTSDIR, "/k4b_xcheck_d_van.g");;
K4BS_TEMPLATE := Concatenation(K4BS_WT_ROOT,
    "/docs/superpowers/research/TEMPLATE-k4b-m5-verdict.md");;

K4BSAssertTrue("driver exists on disk", IsExistingFile(K4BS_DRIVER));
K4BSAssertTrue("xcheck harness exists on disk",
               IsExistingFile(K4BS_XCHECK));
K4BSAssertTrue("interpretation template exists on disk",
               IsExistingFile(K4BS_TEMPLATE));

# ---- T1: driver script syntax check -----------------------------------
# Use `bash -n` to syntax-check without executing. Exit status 0 = OK.
# `Exec` does not capture exit status directly, so we use a small trick:
# redirect to a tempfile that records the status, then read it back.
Print("\n-----------------------------------------------------------------\n");
Print("T1: bash -n run_k4b_m5.sh\n");
Print("-----------------------------------------------------------------\n");

K4BS_T1_STATUSFILE := Concatenation(K4BS_SELFDIR, "/.k4bs_t1_status");;
if IsExistingFile(K4BS_T1_STATUSFILE) then
    Exec(Concatenation("rm -f '", K4BS_T1_STATUSFILE, "'"));
fi;
Exec(Concatenation(
    "bash -n '", K4BS_DRIVER, "' 2>&1; echo $? > '",
    K4BS_T1_STATUSFILE, "'"));

if IsExistingFile(K4BS_T1_STATUSFILE) then
    # The status file holds the literal exit code (e.g. "0\n");
    # InputTextFile + ReadAll gets us the raw bytes, which we then
    # strip and compare to "0".
    K4BS_T1_STATUS := InputTextFile(K4BS_T1_STATUSFILE);
    K4BS_T1_STR := ReadAll(K4BS_T1_STATUS);
    CloseStream(K4BS_T1_STATUS);
    # Strip whitespace.
    while Length(K4BS_T1_STR) > 0
          and K4BS_T1_STR[Length(K4BS_T1_STR)] in [' ', '\n', '\t', '\r'] do
        K4BS_T1_STR := K4BS_T1_STR{[1..Length(K4BS_T1_STR) - 1]};
    od;
    K4BSAssertEqual("bash -n run_k4b_m5.sh returns exit 0",
                    K4BS_T1_STR, "0");
else
    K4BSAssertTrue("status file written by `bash -n`", false);
fi;

# ---- T2: cross-validation harness parses ------------------------------
# Reading the harness should not throw a parse error. The harness will
# itself QUIT or Error if downstream siblings are missing, so we run
# it in a child gap process via Exec rather than via Read in this
# session (which would QUIT us too).
#
# We just want to confirm syntactic well-formedness, NOT functional
# correctness — that needs the upstream pieces (#200 + #220) to be
# present. We use `gap -c 'Read("...");'` with a guard to capture
# only the parse phase.
#
# Strategy: write a stub probe to a tempfile that does:
#   Print("PARSE_PROBE_START\n");
#   Read("k4b_xcheck_d_van.g");
#   Print("PARSE_PROBE_AFTER_READ\n");  # not reached, file QUITs.
#   QUIT;
#
# If the file is well-formed, GAP will print PARSE_PROBE_START and then
# execute the harness (which will QUIT inside, possibly with a BLOCKED
# message). A parse error would surface as a SyntaxError BEFORE
# PARSE_PROBE_START is printed.
#
# Easier check: scan the file for the obvious required-binding hooks
# without executing it. We do that as a fast complement and only spend
# the GAP-subprocess budget if the structural check passes.
Print("\n-----------------------------------------------------------------\n");
Print("T2: cross-validation harness loads\n");
Print("-----------------------------------------------------------------\n");

K4BS_XCHECK_STREAM := InputTextFile(K4BS_XCHECK);;
K4BS_XCHECK_SRC := ReadAll(K4BS_XCHECK_STREAM);;
CloseStream(K4BS_XCHECK_STREAM);

K4BSAssertTrue("xcheck file is non-empty",
               Length(K4BS_XCHECK_SRC) > 100);
K4BSAssertTrue("xcheck declares _DVAN_InvertRestriction",
               PositionSublist(K4BS_XCHECK_SRC,
                                "_DVAN_InvertRestriction") <> fail);
K4BSAssertTrue("xcheck references RESULT",
               PositionSublist(K4BS_XCHECK_SRC, "RESULT") <> fail);
K4BSAssertTrue("xcheck loads detecting_family_vanish.g (D-VAN-3)",
               PositionSublist(K4BS_XCHECK_SRC,
                                "detecting_family_vanish.g") <> fail);
K4BSAssertTrue("xcheck has TRIVIAL-AXIS fallback branch",
               PositionSublist(K4BS_XCHECK_SRC, "TRIVIAL-AXIS") <> fail);

# Try a brace-balance heuristic as a syntactic sanity check.
K4BS_T2_OPEN := 0;;
K4BS_T2_CLOSE := 0;;
K4BS_T2_I := 1;;
while K4BS_T2_I <= Length(K4BS_XCHECK_SRC) do
    if K4BS_XCHECK_SRC[K4BS_T2_I] = '(' then
        K4BS_T2_OPEN := K4BS_T2_OPEN + 1;
    elif K4BS_XCHECK_SRC[K4BS_T2_I] = ')' then
        K4BS_T2_CLOSE := K4BS_T2_CLOSE + 1;
    fi;
    K4BS_T2_I := K4BS_T2_I + 1;
od;
K4BSAssertEqual("xcheck parens balance", K4BS_T2_OPEN, K4BS_T2_CLOSE);

# Subprocess parse-check via a child gap process. We want to confirm
# that GAP reads the xcheck file all the way through without a
# SyntaxError, but we don't want to exercise the full D-VAN-3 load
# chain (heavy: HAP + Cohomology3 setup, takes minutes at m = 5).
#
# Strategy: copy the xcheck file into a SCRATCH directory and Read
# *that* copy. The xcheck computes `_K4B_XCHECK_DIR` from
# INPUT_FILENAME(), which for the copy resolves to the scratch dir.
# It then looks for `<scratch>/k4b_m5_result.g`. We stage that file
# as MISSING -> xcheck hits the "BLOCKED: ... not found" early QUIT,
# never touching detecting_family_vanish.g. Fast (~3 s).
#
# A parse error would show up as a SyntaxError in the subprocess
# output BEFORE the BLOCKED line. The probe checks both.
K4BS_T2_PROBE_DIR := Concatenation(K4BS_SELFDIR, "/k4b_scaffold");;
if not IsExistingFile(K4BS_T2_PROBE_DIR) then
    Exec(Concatenation("mkdir -p '", K4BS_T2_PROBE_DIR, "'"));
fi;
# Copy the xcheck into the scratch dir so its INPUT_FILENAME-based
# sibling lookups all resolve to the scratch dir (where no result
# file lives, so the early QUIT fires).
K4BS_T2_XCHECK_COPY :=
    Concatenation(K4BS_T2_PROBE_DIR, "/k4b_xcheck_d_van.g");;
Exec(Concatenation("cp '", K4BS_XCHECK, "' '", K4BS_T2_XCHECK_COPY, "'"));
# Ensure no stale result file exists in the scratch dir.
Exec(Concatenation("rm -f '", K4BS_T2_PROBE_DIR, "/k4b_m5_result.g'"));

K4BS_T2_PROBE := Concatenation(K4BS_T2_PROBE_DIR, "/probe_t2.g");;
K4BS_T2_OUTFILE := Concatenation(K4BS_T2_PROBE_DIR, "/probe_t2.out");;

# Write the probe. PARSE_PROBE_START marks the start of execution;
# the BLOCKED line proves xcheck parsed cleanly AND reached its
# guard logic.
PrintTo(K4BS_T2_PROBE,
    "# Probe for test_k4b_scaffold_smoke.g T2.\n",
    "Print(\"PARSE_PROBE_START\\n\");\n",
    "Read(\"", K4BS_T2_XCHECK_COPY, "\");\n",
    "Print(\"PARSE_PROBE_AFTER_READ\\n\");\n",
    "QUIT;\n"
);

# Run the probe in a child GAP.
Exec(Concatenation("cd '", K4BS_T2_PROBE_DIR, "' && ",
    "gap -q -b -c 'Read(\"", K4BS_T2_PROBE, "\");' > '",
    K4BS_T2_OUTFILE, "' 2>&1"));

if IsExistingFile(K4BS_T2_OUTFILE) then
    K4BS_T2_STREAM := InputTextFile(K4BS_T2_OUTFILE);
    K4BS_T2_OUT := ReadAll(K4BS_T2_STREAM);
    CloseStream(K4BS_T2_STREAM);
    K4BSAssertTrue("subprocess emitted PARSE_PROBE_START (file tokenised)",
                   PositionSublist(K4BS_T2_OUT, "PARSE_PROBE_START") <> fail);
    K4BSAssertTrue("no Syntax error in xcheck file",
                   PositionSublist(K4BS_T2_OUT, "Syntax error") = fail);
    # The xcheck's early-QUIT guard prints "BLOCKED:" when the result
    # file is missing — confirming xcheck Read all the way through
    # its prologue and hit the IsExistingFile guard cleanly.
    K4BSAssertTrue("xcheck reached its result-file existence guard",
                   PositionSublist(K4BS_T2_OUT, "BLOCKED:") <> fail);
else
    K4BSAssertTrue("subprocess produced output", false);
fi;

# ---- T3: interpretation note template valid ---------------------------
Print("\n-----------------------------------------------------------------\n");
Print("T3: interpretation note template valid markdown\n");
Print("-----------------------------------------------------------------\n");

K4BS_TEMPLATE_STREAM := InputTextFile(K4BS_TEMPLATE);;
K4BS_TEMPLATE_SRC := ReadAll(K4BS_TEMPLATE_STREAM);;
CloseStream(K4BS_TEMPLATE_STREAM);

K4BSAssertTrue("template file is non-empty",
               Length(K4BS_TEMPLATE_SRC) > 100);

# Required H1 / H2 headers, per the K-4b spec §3 "Interpretation note".
for K4BS_T3_HEADER in
    [ "# K-4b m = 5 verdict",
      "## Section 1: Verdict",
      "## Section 2: Per-subgroup classes",
      "## Section 3: Cross-validation against D-VAN",
      "## Section 4: Confidence assessment",
      "## Section 5: Implications for Keller's conjecture at m = 5",
      "## Section 6: Reproducibility",
      "## Section 7: Follow-ups" ] do
    K4BSAssertTrue(
        Concatenation("template has header: ", K4BS_T3_HEADER),
        PositionSublist(K4BS_TEMPLATE_SRC, K4BS_T3_HEADER) <> fail);
od;

# The template itself should have placeholders rather than concrete
# values. A few sanity tokens:
K4BSAssertTrue("template references run_k4b_m5.sh",
               PositionSublist(K4BS_TEMPLATE_SRC, "run_k4b_m5.sh") <> fail);
K4BSAssertTrue("template references k4b_xcheck_d_van.g",
               PositionSublist(K4BS_TEMPLATE_SRC,
                                "k4b_xcheck_d_van.g") <> fail);
K4BSAssertTrue("template references the K-4b spec",
               PositionSublist(K4BS_TEMPLATE_SRC,
                                "2026-05-17-k4b-m5-production-spec.md") <> fail);

# ---- Final summary ----------------------------------------------------
Print("\n=================================================================\n");
Print("Final summary\n");
Print("=================================================================\n");
Print("  passes   : ", K4BS_PASSES, "\n");
Print("  failures : ", Length(K4BS_FAILURES), "\n");
if Length(K4BS_FAILURES) = 0 then
    Print("\ntest_k4b_scaffold_smoke: PASS\n");
    QUIT_GAP(0);
else
    Print("\ntest_k4b_scaffold_smoke: FAIL (", Length(K4BS_FAILURES), "):\n");
    for K4BS_F in K4BS_FAILURES do
        Print("  - ", K4BS_F, "\n");
    od;
    QUIT_GAP(1);
fi;
