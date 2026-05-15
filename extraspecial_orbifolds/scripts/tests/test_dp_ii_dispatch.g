# test_dp_ii_dispatch.g — tests for the DP-II auto-dispatcher.
#
# Issue #46 (A-5a). Acceptance criteria (per the issue body):
#   - Verdict text follows
#       `DP-II: HAP resolution <succeeded|failed>. Next: <branch label>`.
#   - Status persisted to a verdict file as a GAP rec.
#   - JSON payload listing issues to unblock:
#       success = true   =>  A-5b           (HAP route)
#       success = false  =>  A-5c           (Quillen route)
#   - Tested on a synthetic success input AND a synthetic failure input;
#     correct branch in each case.
#
# Run from extraspecial_orbifolds/scripts/:
#   gap -q -b -c 'Read("tests/test_dp_ii_dispatch.g");'

# Catch errors via CALL_WITH_CATCH rather than entering the break-loop.
BreakOnError := false;;

# Load the dispatcher WITHOUT auto-invoking against the default A-5a path
# (which may or may not be present in a clean checkout).
BindGlobal("DP_II_DISPATCH_NO_AUTOINVOKE", true);
Read("dp_ii_dispatch.g");

Print("\n=== test_dp_ii_dispatch.g ===\n");

# --------------------------------------------------------------------
# Synthetic fixture builder: writes a minimal resolution_outcome.g to
# /tmp/ and returns its path.
# --------------------------------------------------------------------
WriteSyntheticOutcome :=
    function(path, success_value, wall_sec, peak_rss, heap_mb, err_msg)
    local success_str, rss_str;
    success_str := If_(success_value, "true", "false");
    if IsString(peak_rss) then
        rss_str := Concatenation("\"", peak_rss, "\"");
    else
        rss_str := String(peak_rss);
    fi;
    PrintTo(path,
        "# synthetic resolution_outcome.g fixture\n",
        "return rec(\n",
        "    group_label      := \"E_+(5)\",\n",
        "    group_order      := 2048,\n",
        "    resolution_arity := 4,\n",
        "    success          := ", success_str, ",\n",
        "    wall_clock_sec   := ", String(wall_sec), ",\n",
        "    gap_heap_mb      := ", String(heap_mb), ",\n",
        "    peak_rss_mb      := ", rss_str, ",\n",
        "    error_msg        := \"", err_msg, "\",\n",
        "    started_at       := \"synthetic-fixture\"\n",
        ");;\n");
    return path;
end;;

testFailures := [];;

AssertOrLog := function(label, cond)
    Print("  ", label, ": ", If_(cond, "PASS", "FAIL"), "\n");
    if not cond then Add(testFailures, label); fi;
end;;

# --------------------------------------------------------------------
# Test 1: synthetic success (HAP route).
# --------------------------------------------------------------------
Print("\n--- Test 1: synthetic success = true (HAP route) ---\n");

opath := "/tmp/test_dp_ii_outcome_success.g";;
vpath := "/tmp/test_dp_ii_verdict_success.g";;
WriteSyntheticOutcome(opath, true, 3600.5, 18432.0, 12000.0, "");
r := DispatchDPII(opath, vpath);;

AssertOrLog("success = true",
            r.success = true);
AssertOrLog("branch_label = hap-route",
            r.branch_label = "hap-route");
AssertOrLog("issues_to_unblock = [A-5b]",
            r.issues_to_unblock = ["A-5b"]);
AssertOrLog("verdict text format",
            r.verdict = "DP-II: HAP resolution succeeded. Next: hap-route");
AssertOrLog("verdict file written",
            IsExistingFile(vpath));
AssertOrLog("verdict file reloadable",
            IsRecord(ReadAsFunction(vpath)()));
AssertOrLog("wall_clock_sec preserved",
            r.wall_clock_sec = 3600.5);
AssertOrLog("peak_rss_mb preserved",
            r.peak_rss_mb = 18432.0);

# Reload the verdict and verify it agrees with the in-memory result.
v_reloaded := ReadAsFunction(vpath)();;
AssertOrLog("reloaded verdict success = true",
            v_reloaded.success = true);
AssertOrLog("reloaded verdict issues_to_unblock",
            v_reloaded.issues_to_unblock = ["A-5b"]);

AssertOrLog("JSON contains 'success\": true'",
            PositionSublist(r.json, "\"success\": true") <> fail);
AssertOrLog("JSON contains A-5b",
            PositionSublist(r.json, "\"A-5b\"") <> fail);
AssertOrLog("JSON does NOT contain A-5c",
            PositionSublist(r.json, "\"A-5c\"") = fail);
AssertOrLog("JSON peak_rss_mb is numeric (not quoted)",
            PositionSublist(r.json, "\"peak_rss_mb\": 18432") <> fail);

# --------------------------------------------------------------------
# Test 2: synthetic failure (Quillen route).
# --------------------------------------------------------------------
Print("\n--- Test 2: synthetic success = false (Quillen route) ---\n");

opath2 := "/tmp/test_dp_ii_outcome_failure.g";;
vpath2 := "/tmp/test_dp_ii_verdict_failure.g";;
WriteSyntheticOutcome(opath2, false, 1234.5, "unknown", -1.0,
                      "OOM: GAP killed by SIGKILL");
r2 := DispatchDPII(opath2, vpath2);;

AssertOrLog("success = false",
            r2.success = false);
AssertOrLog("branch_label = quillen-route",
            r2.branch_label = "quillen-route");
AssertOrLog("issues_to_unblock = [A-5c]",
            r2.issues_to_unblock = ["A-5c"]);
AssertOrLog("verdict text format",
            r2.verdict = "DP-II: HAP resolution failed. Next: quillen-route");
AssertOrLog("verdict file written",
            IsExistingFile(vpath2));
AssertOrLog("error_msg preserved",
            r2.error_msg = "OOM: GAP killed by SIGKILL");

v2_reloaded := ReadAsFunction(vpath2)();;
AssertOrLog("reloaded verdict success = false",
            v2_reloaded.success = false);
AssertOrLog("reloaded verdict has A-5c",
            "A-5c" in v2_reloaded.issues_to_unblock);
AssertOrLog("reloaded verdict peak_rss_mb is the string \"unknown\"",
            v2_reloaded.peak_rss_mb = "unknown");

AssertOrLog("JSON contains 'success\": false'",
            PositionSublist(r2.json, "\"success\": false") <> fail);
AssertOrLog("JSON contains A-5c",
            PositionSublist(r2.json, "\"A-5c\"") <> fail);
AssertOrLog("JSON does NOT contain A-5b",
            PositionSublist(r2.json, "\"A-5b\"") = fail);
AssertOrLog("JSON peak_rss_mb is quoted string",
            PositionSublist(r2.json, "\"peak_rss_mb\": \"unknown\"") <> fail);

# --------------------------------------------------------------------
# Test 3: input validation.
# --------------------------------------------------------------------
Print("\n--- Test 3: input validation ---\n");

err := CALL_WITH_CATCH(DispatchDPII, [42, "/tmp/whatever.g"]);;
AssertOrLog("non-string outcome_path raises",
            not err[1]);

err := CALL_WITH_CATCH(DispatchDPII,
                       ["/tmp/test_dp_ii_outcome_success.g", 42]);;
AssertOrLog("non-string verdict_path raises",
            not err[1]);

# --------------------------------------------------------------------
# Summary
# --------------------------------------------------------------------
Print("\n=== Summary ===\n");
if IsEmpty(testFailures) then
    Print("test_dp_ii_dispatch: ALL PASS\n");
else
    Print("test_dp_ii_dispatch: FAIL (", Length(testFailures), " failures)\n");
    for f in testFailures do Print("  - ", f, "\n"); od;
fi;
