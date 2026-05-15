# dp_ii_dispatch.g — DP-II auto-dispatcher (issue #46, A-5a).
#
# Reads an A-5a `resolution_outcome.g` record for E_+(5), branches on
# the HAP success boolean, persists a verdict record, and emits a JSON
# payload on stdout naming which downstream issues to unblock:
#
#   success = true   (HAP resolution finished within budget)
#                   =>  branch: hap-route
#                       Unblock: A-5b.
#
#   success = false  (HAP failed: OOM, timeout, or GAP error)
#                   =>  branch: quillen-route
#                       Unblock: A-5c.
#
# Verdict text format:
#   `DP-II: HAP resolution <succeeded|failed>. Next: <branch label>`.
#
# Usage (script form, defaults match A-5a's output path):
#   gap -q -b -c 'Read("dp_ii_dispatch.g");'
# from extraspecial_orbifolds/scripts/.
#
# Usage (programmatic):
#   r := DispatchDPII("path/to/resolution_outcome.g",
#                      "path/to/dp_ii_verdict.g");
# Returns a record with fields success, wall_clock_sec, peak_rss_mb,
# gap_heap_mb, branch_label, issues_to_unblock, verdict (text), json.
#
# Setting DP_II_DISPATCH_NO_AUTOINVOKE before Read() suppresses the
# auto-invocation (used by the test suite).

# JSON-encode a list of strings as a JSON array (used for issues list).
_DPII_JsonStringList := function(strs)
    local parts;
    parts := List(strs, s -> Concatenation("\"", s, "\""));
    return Concatenation("[", JoinStringsWithSeparator(parts, ", "), "]");
end;;

# JSON-encode a peak_rss_mb field: numeric → bare number; string → quoted.
_DPII_JsonRssField := function(v)
    if IsString(v) then
        return Concatenation("\"", v, "\"");
    fi;
    return String(v);
end;;

# Local ternary helper, matching the idiom used elsewhere in scripts/.
If_ := function(cond, a, b) if cond then return a; else return b; fi; end;;

# Write the verdict GAP source file with auto-wrapping disabled.
_DPII_WriteVerdict := function(path, src_path, success, wall_sec,
                                peak_rss, heap_mb, error_msg,
                                branch, issues, verdict)
    local stream, rss_field;
    stream := OutputTextFile(path, false);
    Assert(0, stream <> fail,
           Concatenation("could not open ", path, " for writing"));
    SetPrintFormattingStatus(stream, false);
    if IsString(peak_rss) then
        rss_field := Concatenation("\"", peak_rss, "\"");
    else
        rss_field := String(peak_rss);
    fi;
    PrintTo(stream,
        "# DP-II verdict from scripts/dp_ii_dispatch.g (issue #46 ",
        "A-5a).\n",
        "# Source outcome: ", src_path, "\n",
        "# Verdict: ", verdict, "\n",
        "return rec(\n",
        "    success           := ", If_(success, "true", "false"),
        ",\n",
        "    wall_clock_sec    := ", String(wall_sec), ",\n",
        "    peak_rss_mb       := ", rss_field, ",\n",
        "    gap_heap_mb       := ", String(heap_mb), ",\n",
        "    error_msg         := \"", error_msg, "\",\n",
        "    branch_label      := \"", branch, "\",\n",
        "    issues_to_unblock := ", issues, ",\n",
        "    verdict           := \"", verdict, "\"\n",
        ");;\n");
    CloseStream(stream);
end;;

DispatchDPII := function(outcome_path, verdict_path)
    local outcome, success, wall_sec, peak_rss, heap_mb, error_msg,
          branch_label, issues_to_unblock, issues_str, verdict_text,
          json, result;

    if not IsString(outcome_path) then
        Error("DispatchDPII: outcome_path must be a string");
    fi;
    if not IsString(verdict_path) then
        Error("DispatchDPII: verdict_path must be a string");
    fi;

    # The A-5a resolution_outcome.g is a GAP source file whose body
    # returns a rec.
    outcome := ReadAsFunction(outcome_path)();
    Assert(0, IsRecord(outcome),
           Concatenation(outcome_path, " did not return a record"));
    Assert(0, IsBound(outcome.success),
           "outcome record missing success field");

    success     := outcome.success;
    wall_sec    := If_(IsBound(outcome.wall_clock_sec),
                       outcome.wall_clock_sec, -1.0);
    peak_rss    := If_(IsBound(outcome.peak_rss_mb),
                       outcome.peak_rss_mb, "unknown");
    heap_mb     := If_(IsBound(outcome.gap_heap_mb),
                       outcome.gap_heap_mb, -1.0);
    error_msg   := If_(IsBound(outcome.error_msg),
                       outcome.error_msg, "");

    if success then
        branch_label := "hap-route";
        issues_to_unblock := ["A-5b"];
        verdict_text := Concatenation(
            "DP-II: HAP resolution succeeded. Next: ", branch_label);
    else
        branch_label := "quillen-route";
        issues_to_unblock := ["A-5c"];
        verdict_text := Concatenation(
            "DP-II: HAP resolution failed. Next: ", branch_label);
    fi;

    issues_str := _DPII_JsonStringList(issues_to_unblock);

    # Hand-emit JSON (GAP has no standard JSON library; structure is
    # small enough that a literal Concatenation is clearer than a
    # general encoder).
    json := Concatenation(
        "{",
        "\"success\": ", If_(success, "true", "false"), ", ",
        "\"wall_clock_sec\": ", String(wall_sec), ", ",
        "\"peak_rss_mb\": ", _DPII_JsonRssField(peak_rss), ", ",
        "\"gap_heap_mb\": ", String(heap_mb), ", ",
        "\"branch_label\": \"", branch_label, "\", ",
        "\"issues_to_unblock\": ", issues_str,
        "}");

    _DPII_WriteVerdict(verdict_path, outcome_path, success, wall_sec,
                       peak_rss, heap_mb, error_msg, branch_label,
                       issues_str, verdict_text);

    # Stdout output.
    Print(verdict_text, "\n");
    Print("JSON: ", json, "\n");

    result := rec(
        success := success,
        wall_clock_sec := wall_sec,
        peak_rss_mb := peak_rss,
        gap_heap_mb := heap_mb,
        error_msg := error_msg,
        branch_label := branch_label,
        issues_to_unblock := issues_to_unblock,
        verdict := verdict_text,
        json := json);
    return result;
end;;

# Auto-invoke when read as a script (guarded for the test suite).
if not IsBoundGlobal("DP_II_DISPATCH_NO_AUTOINVOKE") then
    DispatchDPII(
        "../../computed/transgression/5/resolution_outcome.g",
        "../../computed/transgression/5/dp_ii_verdict.g");
fi;
