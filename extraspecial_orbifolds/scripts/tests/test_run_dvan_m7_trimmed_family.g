# test_run_dvan_m7_trimmed_family.g — smoke tests for the
# `run_dvan_m7_trimmed_family.g` production driver (issue #427).
#
# We do NOT exercise the ~2-3h m=7 production rerun — that is the
# operator's responsibility. Instead we verify:
#
#   T1. The driver parses without syntax errors
#       (`ReadAsFunction` returns a function rather than erroring).
#   T2. The driver source references the symbols it relies on:
#       _DETF_TrimmedFamily, OutputTextFile, SetPrintFormattingStatus,
#       CloseStream, ea_generators, ea_generators_sorted, and the
#       output path beneath computed/dvan_min_family/m7/.
#   T3. (Gated by `DVAN_M7_DRIVER_SMOKE := true`.) Exercise the
#       full persist + verify codepath at small m (m=2 via the eager
#       _DETF_TrimmedFamily path) by:
#         a. Calling _DETF_TrimmedFamily(2) to get a tiny result rec.
#         b. Running the same `result_to_persist` + OutputTextFile +
#            SetPrintFormattingStatus + PrintTo + post-Read pattern as
#            the production driver, against a temp file.
#         c. Asserting the round-trip readback bound a record with
#            the expected core fields.
#         d. Cleaning up the temp file.
#
# Note on T3 scope: the m=2 eager path does NOT populate ea_generators
# (only the m=7 streaming path does). So T3 asserts the persistence
# *mechanics* — selective record build, OutputTextFile with formatting
# disabled, Re-read — work at small scale, without claiming anything
# about ea_generators content. The ea_generators schema itself is
# already covered by `test_dvan_m7_ea_generator_persist.g`.
#
# Run from extraspecial_orbifolds/scripts/:
#
#   gap -q -b -c 'Read("tests/test_run_dvan_m7_trimmed_family.g"); QUIT;'
#
# To also run T3:
#
#   gap -q -b -c 'DVAN_M7_DRIVER_SMOKE := true;; \
#       Read("tests/test_run_dvan_m7_trimmed_family.g"); QUIT;'

BreakOnError := false;;

P427_PASSES   := 0;;
P427_FAILURES := [];;

P427Assert := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
        P427_PASSES := P427_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Add(P427_FAILURES, label);
    fi;
end;;

Print("\n=================================================================\n");
Print("test_run_dvan_m7_trimmed_family.g (#427)\n");
Print("=================================================================\n");

# ---------------------------------------------------------------------
# Resolve the driver path. This test is meant to be Read from the
# scripts/ directory (the usual convention). Use a relative path with
# a sanity check that the file exists; otherwise fall through with a
# clear error.
# ---------------------------------------------------------------------

P427_DRIVER_REL := "run_dvan_m7_trimmed_family.g";;
P427Assert("driver file is readable",
           IsExistingFile(P427_DRIVER_REL));

# ---------------------------------------------------------------------
# T1. Parse the driver via ReadAsFunction. This compiles the source
# into a function value (deferring execution) and surfaces syntax /
# parse errors without running the driver. CALL_WITH_CATCH wraps
# uncaught errors into the rec returned. We do NOT call the function.
# ---------------------------------------------------------------------

Print("\n--- T1: driver parses without syntax errors ---\n");
P427_PARSE := CALL_WITH_CATCH(ReadAsFunction, [P427_DRIVER_REL]);;
P427Assert("ReadAsFunction(driver) returns successfully",
           P427_PARSE[1]);
if P427_PARSE[1] then
    P427Assert("ReadAsFunction(driver) returns a function value",
               IsFunction(P427_PARSE[2]));
fi;

# ---------------------------------------------------------------------
# T2. Source-level symbol references. Read the file as text and
# confirm the canonical symbols + output path appear. These are
# load-bearing — if any of these is renamed without updating the
# driver, downstream rerun fails silently.
# ---------------------------------------------------------------------

Print("\n--- T2: driver references the expected symbols ---\n");
P427_DRIVER_STREAM   := InputTextFile(P427_DRIVER_REL);;
P427_DRIVER_CONTENTS := ReadAll(P427_DRIVER_STREAM);;
CloseStream(P427_DRIVER_STREAM);

P427_REFS := [
    "_DETF_TrimmedFamily",
    "OutputTextFile",
    "SetPrintFormattingStatus",
    "CloseStream",
    "ea_generators",
    "ea_generators_sorted",
    "../computed/dvan_min_family/m7/result.g",
    "dvan_m7_result",
    "_LogPhase",
    "result_to_persist"
];;

for P427_TOK in P427_REFS do
    P427Assert(Concatenation("driver references '", P427_TOK, "'"),
               PositionSublist(P427_DRIVER_CONTENTS, P427_TOK) <> fail);
od;

# ---------------------------------------------------------------------
# T3 (gated): persistence-mechanics smoke at m=2.
# ---------------------------------------------------------------------

if IsBoundGlobal("DVAN_M7_DRIVER_SMOKE") and DVAN_M7_DRIVER_SMOKE then
    Print("\n--- T3 (smoke): persistence mechanics at m=2 ---\n");

    if not IsBoundGlobal("_DETF_TrimmedFamily") then
        Read("detecting_family_restriction.g");
    fi;

    P427_SMOKE_RES := _DETF_TrimmedFamily(2);;
    P427Assert("smoke: _DETF_TrimmedFamily(2) returned a record",
               IsRecord(P427_SMOKE_RES));
    P427Assert("smoke: result.m = 2",
               P427_SMOKE_RES.m = 2);
    P427Assert("smoke: result.final_ker = 1",
               P427_SMOKE_RES.final_ker = 1);

    # Build the same selective rec the driver builds. The m=2 (eager)
    # path does not populate ea_generators/ea_generators_sorted — they
    # only exist on the m=7 streaming path. We omit them here while
    # keeping the rest of the field set identical to the driver's
    # `result_to_persist`.
    P427_PERSIST := rec(
        m                        := P427_SMOKE_RES.m,
        source                   := P427_SMOKE_RES.source,
        ea_indices_chosen        := P427_SMOKE_RES.ea_indices_chosen,
        ea_indices_chosen_sorted := P427_SMOKE_RES.ea_indices_chosen_sorted,
        include_D8               := P427_SMOKE_RES.include_D8,
        include_Q8               := P427_SMOKE_RES.include_Q8,
        final_ker                := P427_SMOKE_RES.final_ker,
        ea_count                 := P427_SMOKE_RES.ea_count,
        family_size              := P427_SMOKE_RES.family_size,
        greedy_log               := P427_SMOKE_RES.greedy_log,
        locally_tight            := P427_SMOKE_RES.locally_tight,
        drop_one_kers            := P427_SMOKE_RES.drop_one_kers,
        walltime_ms              := P427_SMOKE_RES.walltime_ms
    );;

    # Pick an absolute temp path so the test doesn't depend on CWD.
    P427_TMP := Filename(DirectoryTemporary(),
                         "test_dvan_m7_driver_smoke_m2.g");;
    Print("  smoke: writing temp file: ", P427_TMP, "\n");

    P427_OS := OutputTextFile(P427_TMP, false);;
    SetPrintFormattingStatus(P427_OS, false);
    PrintTo(P427_OS, "# D-VAN m=2 smoke output for test #427.\n");
    PrintTo(P427_OS, "dvan_m7_result := ", P427_PERSIST, ";;\n");
    CloseStream(P427_OS);

    P427Assert("smoke: temp file written",
               IsExistingFile(P427_TMP));

    # Round-trip readback against a fresh global binding.
    if IsBoundGlobal("dvan_m7_result") then
        UnbindGlobal("dvan_m7_result");
    fi;
    Read(P427_TMP);
    P427Assert("smoke: post-Read dvan_m7_result is bound",
               IsBoundGlobal("dvan_m7_result"));
    if IsBoundGlobal("dvan_m7_result") then
        P427Assert("smoke: readback record has m = 2",
                   dvan_m7_result.m = 2);
        P427Assert("smoke: readback record has final_ker = 1",
                   dvan_m7_result.final_ker = 1);
        P427Assert("smoke: readback record has ea_indices_chosen field",
                   IsBound(dvan_m7_result.ea_indices_chosen));
        P427Assert("smoke: readback record has ea_indices_chosen_sorted",
                   IsBound(dvan_m7_result.ea_indices_chosen_sorted));
        P427Assert("smoke: readback record has greedy_log field",
                   IsBound(dvan_m7_result.greedy_log));
    fi;

    # Clean up the temp file.
    RemoveFile(P427_TMP);
    P427Assert("smoke: temp file removed",
               not IsExistingFile(P427_TMP));
else
    Print("\n--- T3 (smoke): SKIPPED ",
          "(set DVAN_M7_DRIVER_SMOKE := true to enable) ---\n");
fi;

# ---------------------------------------------------------------------
# Summary.
# ---------------------------------------------------------------------

Print("\n=================================================================\n");
Print("Passes  : ", P427_PASSES, "\n");
Print("Failures: ", Length(P427_FAILURES), "\n");
if Length(P427_FAILURES) > 0 then
    Print("Failed labels:\n");
    for P427_LBL in P427_FAILURES do
        Print("  - ", P427_LBL, "\n");
    od;
    QuitGap(1);
fi;
Print("All #427 driver smoke checks passed.\n");
Print("=================================================================\n");
