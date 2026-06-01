# test_dvan_m7_ea_generator_persist.g
#
# Issue #377: regression test for the LoadDVANEAFamily(m) loader added
# to k4a_classify.g, plus the `ea_generators` field added to the
# result rec returned by `_DETF_TrimmedFamily_m7_streaming`.
#
# What we check:
#   T1. LoadDVANEAFamily(m) returns fail for a nonexistent result.g
#       (m where no result file is on disk).
#   T2. LoadDVANEAFamily(m) returns fail for a result.g that lacks the
#       `ea_generators` field. This is the state of the CURRENT
#       PR #361 m7/result.g — it predates issue #377 and contains
#       only `ea_indices_chosen`, not the generator tuples.
#   T3. The result rec produced by `_DETF_TrimmedFamily_m7_streaming`
#       contains an `ea_generators` field. We verify this by reading
#       the function source — running it at m=7 takes hours and at
#       smaller m the streaming variant is not invoked.
#
# Notes:
#   * The positive end-to-end loader test (T1 = subgroups returned for
#     a populated result.g) requires a real m=7 result file, which
#     only exists after a fresh D-VAN m=7 production rerun on top of
#     this PR + PR #379 (#343+#347). Deferred to that rerun.
#   * The classifier-wiring test (`_K4A_ClassifyEBranchMulti` accepts
#     subgroup input) is a separate follow-up — it requires
#     `_DETF_BuildSetupG_LHS` to be loadable, which we don't exercise
#     here because LHS setup at m=7 is ~14 min wall.
#
# Run from absolute path:
#   gap -q -b /abs/path/to/scripts/tests/test_dvan_m7_ea_generator_persist.g

P377_PASSES   := 0;;
P377_FAILURES := [];;

P377AssertEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
        P377_PASSES := P377_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Print("         expected: ", expected, "\n");
        Print("         got:      ", got, "\n");
        Add(P377_FAILURES, label);
    fi;
end;;

P377AssertTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
        P377_PASSES := P377_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Add(P377_FAILURES, label);
    fi;
end;;

P377_SELF := INPUT_FILENAME();;
if P377_SELF = fail or P377_SELF = "stream" then
    Error("test_dvan_m7_ea_generator_persist.g: INPUT_FILENAME() ",
          "unavailable; Read the file by its absolute path.");
fi;
P377_SELFDIR := P377_SELF{
    [1..Length(P377_SELF) - Length("/test_dvan_m7_ea_generator_persist.g")]};;
P377_SCRIPTSDIR := P377_SELFDIR{
    [1..Length(P377_SELFDIR) - Length("/tests")]};;

Print("=================================================================\n");
Print("test_dvan_m7_ea_generator_persist.g (#377)\n");
Print("=================================================================\n");
Print("self        : ", P377_SELF, "\n");
Print("scripts dir : ", P377_SCRIPTSDIR, "\n");

# Load k4a_classify.g from the scripts directory.
P377_ORIG_DIR := DirectoryCurrent();;
ChangeDirectoryCurrent(P377_SCRIPTSDIR);;
Read("k4a_classify.g");
ChangeDirectoryCurrent(Filename(P377_ORIG_DIR, ""));;

# ---- T1: LoadDVANEAFamily returns fail when result.g does not exist --

Print("\nT1. LoadDVANEAFamily(m) returns fail when result.g is absent\n");
P377AssertTrue("LoadDVANEAFamily is bound", IsBoundGlobal("LoadDVANEAFamily"));
# m=99 has no result.g on disk.
P377AssertEqual("LoadDVANEAFamily(99) -> fail",
                 LoadDVANEAFamily(99), fail);

# ---- T2: LoadDVANEAFamily returns fail when ea_generators missing -----

Print("\nT2. LoadDVANEAFamily(7) returns fail (current result.g ",
      "lacks ea_generators)\n");
P377_M7_RESULT_PATH := Concatenation(P377_SCRIPTSDIR,
    "/../computed/dvan_min_family/m7/result.g");;
if IsExistingFile(P377_M7_RESULT_PATH) then
    Print("  m=7 result.g exists at: ", P377_M7_RESULT_PATH, "\n");
    Read(P377_M7_RESULT_PATH);
    if IsBoundGlobal("dvan_m7_result") then
        # Field state in the current on-disk file (PR #361 output):
        # ea_generators should NOT be present until a rerun.
        P377AssertTrue("dvan_m7_result.ea_generators NOT YET present",
                        not IsBound(dvan_m7_result.ea_generators));
        P377AssertEqual("LoadDVANEAFamily(7) -> fail (no ea_generators)",
                         LoadDVANEAFamily(7), fail);
    else
        Print("  [skip] dvan_m7_result global not bound after Read; ",
              "file may be in unexpected format.\n");
    fi;
else
    Print("  [skip] m=7 result.g not present on this checkout; ",
          "T2 cannot run.\n");
fi;

# ---- T3: detecting_family_restriction.g result rec has ea_generators --

Print("\nT3. _DETF_TrimmedFamily_m7_streaming result rec includes ",
      "ea_generators\n");
P377_DETF_SRC := Concatenation(P377_SCRIPTSDIR,
                                "/detecting_family_restriction.g");;
P377AssertTrue("detecting_family_restriction.g is readable",
                IsExistingFile(P377_DETF_SRC));
P377_DETF_STREAM := InputTextFile(P377_DETF_SRC);;
P377_DETF_CONTENTS := ReadAll(P377_DETF_STREAM);;
CloseStream(P377_DETF_STREAM);
P377AssertTrue("source contains 'ea_generators' field assignment",
                PositionSublist(P377_DETF_CONTENTS,
                                "ea_generators            :=") <> fail);
P377AssertTrue("source contains 'sample_basis_tuples[j]' reference",
                PositionSublist(P377_DETF_CONTENTS,
                                "sample_basis_tuples[j]") <> fail);

# ---- Summary -----------------------------------------------------------

Print("\n=================================================================\n");
Print("Passes : ", P377_PASSES, "\n");
Print("Failures: ", Length(P377_FAILURES), "\n");
if Length(P377_FAILURES) > 0 then
    Print("Failed labels:\n");
    for P377_LBL in P377_FAILURES do
        Print("  - ", P377_LBL, "\n");
    od;
    QuitGap(1);
fi;
Print("All #377 persistence checks passed.\n");
Print("=================================================================\n");
QuitGap(0);
