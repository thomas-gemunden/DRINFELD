# test_dp_i_dispatch.g — tests for the DP-I auto-dispatcher.
#
# Issue #43 (A-3b). Acceptance criteria (per the issue body):
#   - Verdict text follows `DP-I: |ker Tr| = N. Next: <branch label>`.
#   - Status persisted to a verdict file as a GAP rec.
#   - JSON payload listing issues to unblock:
#       kernel = 0  =>  A-3d, A-5a   (skip A-3c)
#       kernel != 0 =>  A-3c, A-3d, A-5a
#   - Tested on a synthetic kernel = 0 input AND a synthetic kernel != 0
#     input; correct branch in each case.
#
# Run from extraspecial_orbifolds/scripts/:
#   gap -q -b -c 'Read("tests/test_dp_i_dispatch.g");'

# Catch errors via CALL_WITH_CATCH rather than entering the break-loop
# (matches the convention in test_skeller_adapter.g and others).
BreakOnError := false;;

# Load the dispatcher WITHOUT auto-invoking against the default A-3a path
# (which may or may not be present in a clean checkout).
BindGlobal("DP_I_DISPATCH_NO_AUTOINVOKE", true);
Read("dp_i_dispatch.g");

Print("\n=== test_dp_i_dispatch.g ===\n");

# --------------------------------------------------------------------
# Synthetic fixture builder: writes a minimal kernel.g to /tmp/ and
# returns its path.
# --------------------------------------------------------------------
WriteSyntheticKernel := function(path, kernel_size_value)
    PrintTo(path,
        "# synthetic kernel.g fixture for test_dp_i_dispatch.g\n",
        "return rec(\n",
        "    group       := \"synthetic\",\n",
        "    id          := [128, 2326],\n",
        "    torsion     := [2, 2, 2],\n",
        "    exponent    := 2,\n",
        "    kernel_size := ", kernel_size_value, ",\n",
        "    kernel_vecs := fail\n",
        ");;\n");
    return path;
end;;

testFailures := [];;

AssertOrLog := function(label, cond)
    Print("  ", label, ": ", If_(cond, "PASS", "FAIL"), "\n");
    if not cond then Add(testFailures, label); fi;
end;;

# --------------------------------------------------------------------
# Test 1: synthetic kernel = 0 (trivial kernel — only zero vec).
# --------------------------------------------------------------------
Print("\n--- Test 1: synthetic kernel_size = 1 (trivial) ---\n");

kpath := "/tmp/test_dp_i_kernel_trivial.g";;
vpath := "/tmp/test_dp_i_verdict_trivial.g";;
WriteSyntheticKernel(kpath, 1);
r := DispatchDPI(kpath, vpath);;

AssertOrLog("kernel_size = 1",
            r.kernel_size = 1);
AssertOrLog("kernel_trivial = true",
            r.kernel_trivial = true);
AssertOrLog("branch_label = tier-3-cross-validation-only",
            r.branch_label = "tier-3-cross-validation-only");
AssertOrLog("issues_to_unblock = [A-3d, A-5a]",
            r.issues_to_unblock = ["A-3d", "A-5a"]);
AssertOrLog("verdict text format",
            r.verdict = "DP-I: |ker Tr| = 1. Next: tier-3-cross-validation-only");
AssertOrLog("verdict file written",
            IsExistingFile(vpath));
AssertOrLog("verdict file reloadable",
            IsRecord(ReadAsFunction(vpath)()));

# Reload the verdict and verify it agrees with the in-memory result.
v_reloaded := ReadAsFunction(vpath)();;
AssertOrLog("reloaded verdict kernel_trivial",
            v_reloaded.kernel_trivial = true);
AssertOrLog("reloaded verdict issues_to_unblock",
            v_reloaded.issues_to_unblock = ["A-3d", "A-5a"]);

AssertOrLog("JSON contains 'kernel_trivial\": true'",
            PositionSublist(r.json, "\"kernel_trivial\": true") <> fail);
AssertOrLog("JSON contains both A-3d and A-5a",
            PositionSublist(r.json, "\"A-3d\"") <> fail
            and PositionSublist(r.json, "\"A-5a\"") <> fail);
AssertOrLog("JSON does NOT contain A-3c",
            PositionSublist(r.json, "\"A-3c\"") = fail);

# --------------------------------------------------------------------
# Test 2: synthetic kernel != 0 (non-trivial — needs A-3c).
# --------------------------------------------------------------------
Print("\n--- Test 2: synthetic kernel_size = 2 (non-trivial) ---\n");

kpath2 := "/tmp/test_dp_i_kernel_nontrivial.g";;
vpath2 := "/tmp/test_dp_i_verdict_nontrivial.g";;
WriteSyntheticKernel(kpath2, 2);
r2 := DispatchDPI(kpath2, vpath2);;

AssertOrLog("kernel_size = 2",
            r2.kernel_size = 2);
AssertOrLog("kernel_trivial = false",
            r2.kernel_trivial = false);
AssertOrLog("branch_label = candidate-elimination",
            r2.branch_label = "candidate-elimination");
AssertOrLog("issues_to_unblock = [A-3c, A-3d, A-5a]",
            r2.issues_to_unblock = ["A-3c", "A-3d", "A-5a"]);
AssertOrLog("verdict text format",
            r2.verdict = "DP-I: |ker Tr| = 2. Next: candidate-elimination");
AssertOrLog("verdict file written",
            IsExistingFile(vpath2));

v2_reloaded := ReadAsFunction(vpath2)();;
AssertOrLog("reloaded verdict kernel_trivial = false",
            v2_reloaded.kernel_trivial = false);
AssertOrLog("reloaded verdict has A-3c",
            "A-3c" in v2_reloaded.issues_to_unblock);

AssertOrLog("JSON contains 'kernel_trivial\": false'",
            PositionSublist(r2.json, "\"kernel_trivial\": false") <> fail);
AssertOrLog("JSON contains A-3c, A-3d, A-5a",
            PositionSublist(r2.json, "\"A-3c\"") <> fail
            and PositionSublist(r2.json, "\"A-3d\"") <> fail
            and PositionSublist(r2.json, "\"A-5a\"") <> fail);

# --------------------------------------------------------------------
# Test 3: large kernel (mirroring the actual A-3a result: 2^36).
# --------------------------------------------------------------------
Print("\n--- Test 3: synthetic kernel_size = 2^36 (E_+(3)-like) ---\n");

kpath3 := "/tmp/test_dp_i_kernel_huge.g";;
vpath3 := "/tmp/test_dp_i_verdict_huge.g";;
WriteSyntheticKernel(kpath3, 2^36);
r3 := DispatchDPI(kpath3, vpath3);;

AssertOrLog("kernel_size = 2^36",
            r3.kernel_size = 2^36);
AssertOrLog("kernel_trivial = false (huge != 1)",
            r3.kernel_trivial = false);
AssertOrLog("branch_label = candidate-elimination",
            r3.branch_label = "candidate-elimination");
AssertOrLog("verdict text contains 2^36",
            PositionSublist(r3.verdict, String(2^36)) <> fail);

# --------------------------------------------------------------------
# Test 4: input validation.
# --------------------------------------------------------------------
Print("\n--- Test 4: input validation ---\n");

err := CALL_WITH_CATCH(DispatchDPI, [42, "/tmp/whatever.g"]);;
AssertOrLog("non-string kernel_path raises",
            not err[1]);

err := CALL_WITH_CATCH(DispatchDPI, ["/tmp/test_dp_i_kernel_trivial.g", 42]);;
AssertOrLog("non-string verdict_path raises",
            not err[1]);

# --------------------------------------------------------------------
# Summary
# --------------------------------------------------------------------
Print("\n=== Summary ===\n");
if IsEmpty(testFailures) then
    Print("test_dp_i_dispatch: ALL PASS\n");
else
    Print("test_dp_i_dispatch: FAIL (", Length(testFailures), " failures)\n");
    for f in testFailures do Print("  - ", f, "\n"); od;
fi;
