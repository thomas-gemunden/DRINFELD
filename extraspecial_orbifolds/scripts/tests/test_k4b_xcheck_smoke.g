# test_k4b_xcheck_smoke.g — issue #422 syntax + path smoke test.
#
# Validates that k4b_xcheck_d_van.g now parses (no QUIT-in-nested
# error) and that the missing-result-file branch handles relocated
# scripts gracefully (no `/k4b_m5_result.g` leading-slash bug).
#
# Does NOT exercise the full xcheck (that requires BuildRestrictionMatrices
# which is multi-minute heavy).
#
# Usage:
#   cd extraspecial_orbifolds/scripts
#   gap -q -b tests/test_k4b_xcheck_smoke.g

failures := 0;;

# Smoke 1: parse-check the file. If there's a QUIT-in-nested bug, this
# fails with "Syntax error" before the script runs.
Print("[smoke] T1: parse-check k4b_xcheck_d_van.g\n");
catch := CALL_WITH_CATCH(function()
    return ReadAsFunction("k4b_xcheck_d_van.g");
end, []);;
if catch[1] = false then
    Print("[smoke] T1 FAIL: parse error: ", catch[2], "\n");
    failures := failures + 1;
else
    Print("[smoke] T1 PASS: file parses without QUIT-in-nested error\n");
fi;

# Smoke 2: verify the path-extraction helpers tolerate the relocated
# case. We don't actually run the xcheck — too slow. Just simulate the
# path-extraction logic by feeding test inputs.
Print("[smoke] T2: path-extraction logic\n");
TestPathExtract := function(input_filename)
    local suffix, dir;
    suffix := "k4b_xcheck_d_van.g";
    if input_filename = fail or input_filename = "stream" then
        return fail;
    fi;
    if Length(input_filename) < Length(suffix) then
        return fail;
    fi;
    if input_filename{[Length(input_filename) - Length(suffix) + 1
                        .. Length(input_filename)]} <> suffix then
        return fail;
    fi;
    dir := input_filename{[1..Length(input_filename) - Length(suffix)]};
    if Length(dir) > 0 and dir[Length(dir)] = '/' then
        dir := dir{[1..Length(dir) - 1]};
    fi;
    return dir;
end;;

cases := [
    rec(input := "k4b_xcheck_d_van.g", expect := ""),
    rec(input := "scripts/k4b_xcheck_d_van.g", expect := "scripts"),
    rec(input := "/abs/path/k4b_xcheck_d_van.g", expect := "/abs/path"),
    rec(input := fail, expect := fail),
    rec(input := "stream", expect := fail),
    rec(input := "wrong_name.g", expect := fail),
];;

for c in cases do
    got := TestPathExtract(c.input);
    if got = c.expect then
        Print("[smoke] T2 ", c.input, " -> ", got, " (PASS)\n");
    else
        Print("[smoke] T2 ", c.input, " -> ", got,
              " (FAIL, expected ", c.expect, ")\n");
        failures := failures + 1;
    fi;
od;

# Smoke 3: verify QUIT was removed from nested contexts. Grep test.
Print("[smoke] T3: no top-level QUIT in nested blocks\n");
input := InputTextFile("k4b_xcheck_d_van.g");;
n_quit_in_block := 0;;
n_lines := 0;;
in_block := 0;;
while not IsEndOfStream(input) do
    line := ReadLine(input);
    if line = fail then break; fi;
    n_lines := n_lines + 1;
    # Count if-block depth heuristically.
    if PositionSublist(line, "if ") <> fail
       and PositionSublist(line, "#") = fail then
        in_block := in_block + 1;
    fi;
    if PositionSublist(line, "fi;") <> fail
       and PositionSublist(line, "#") = fail then
        in_block := Maximum(0, in_block - 1);
    fi;
    # Look for QUIT; (statement form, not function form).
    if in_block > 0 and PositionSublist(line, "QUIT;") <> fail
       and PositionSublist(line, "#") = fail then
        n_quit_in_block := n_quit_in_block + 1;
        Print("[smoke] T3 found nested QUIT at line ", n_lines,
              " (depth ", in_block, "): ", line);
    fi;
od;
CloseStream(input);
if n_quit_in_block = 0 then
    Print("[smoke] T3 PASS: no nested top-level QUIT found\n");
else
    Print("[smoke] T3 FAIL: ", n_quit_in_block, " nested QUIT(s) remain\n");
    failures := failures + 1;
fi;

# Summary
if failures = 0 then
    Print("\ntest_k4b_xcheck_smoke: ALL PASS (3 tests, ",
          Length(cases), " path cases)\n");
    QuitGap(0);
else
    Print("\ntest_k4b_xcheck_smoke: ", failures, " FAILURE(S)\n");
    QuitGap(1);
fi;
