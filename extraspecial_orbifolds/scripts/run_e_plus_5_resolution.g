# run_e_plus_5_resolution.g — A-5a HAP attempt (issue #46).
#
# Attempts ResolutionFiniteGroup(E_+(5), 4) and persists an outcome
# record to ../../computed/transgression/5/resolution_outcome.g for
# dp_ii_dispatch.g to consume.
#
# Run from extraspecial_orbifolds/scripts/:
#   gap -o 60g -q -b -c 'Read("run_e_plus_5_resolution.g"); QUIT;'
#
# The wrapper script run_e_plus_5_resolution.sh provides peak_rss_mb
# via OS-level polling; this GAP driver records GAP-internal metrics
# (wall_clock_sec, gap_heap_mb, success, error_msg).
#
# E_+(5) = central product of 5 copies of D_8, order 2^11 = 2048.
# SmallGroup library does not reach order 2048, so we use
# ExtraspecialGroup(2048, "+"). That already returns a pc-group
# (verified: IsPcGroup = true), so the ~3000x matrix-vs-pc HAP slowdown
# documented in brw_h3_action.g for EmGroup(m) does NOT apply here —
# no IsomorphismPcGroup conversion is needed.

LoadPackage("hap");;
LoadPackage("io");;

# --- helpers --------------------------------------------------------

If_ := function(cond, a, b) if cond then return a; else return b; fi; end;;

# Wall-clock seconds since Unix epoch, as Float.
_A5A_WallClockSec := function()
    return Float(NanosecondsSinceEpoch()) / 1.0e9;
end;;

# Resolve output path relative to this script's directory. We expect to be
# invoked from extraspecial_orbifolds/scripts/, so the canonical path is
# ../../computed/transgression/5/resolution_outcome.g.
_A5A_OUTCOME_PATH :=
    "../../computed/transgression/5/resolution_outcome.g";;

# ISO-8601 UTC timestamp. GAP's CurrentDateTimeString is provided by IO; we
# wrap in CALL_WITH_CATCH to fall back to a Unix-epoch string if it's missing
# (the outcome file still needs to be writable in that degraded case).
_A5A_IsoTimestamp := function()
    local r;
    r := CALL_WITH_CATCH(CurrentDateTimeString, [["-u"]]);
    if r[1] then return r[2]; fi;
    return Concatenation("epoch+",
                         String(Int(_A5A_WallClockSec())));
end;;

# Approximate GAP heap usage in MB (live bag bytes from GasmanStatistics).
# Field layout differs across GAP versions; wrap defensively.
_A5A_GapHeapMB := function()
    local r, s;
    r := CALL_WITH_CATCH(GasmanStatistics, []);
    if not r[1] then return -1.0; fi;
    s := r[2];
    if IsBound(s.full) and IsBound(s.full.livekb) then
        return Float(s.full.livekb) / 1024.0;
    fi;
    return -1.0;
end;;

# Write the outcome record. Uses an OutputTextFile stream with
# PrintFormattingStatus disabled, because the default PrintTo auto-wraps
# long lines at ~80 chars with a backslash continuation, which silently
# breaks single-line comments (same hazard as kernel.g and DP-I verdict).
_A5A_WriteOutcome :=
    function(path, success, wall_sec, heap_mb, error_msg, started_at,
             group_label, group_order)
    local stream;
    stream := OutputTextFile(path, false);
    Assert(0, stream <> fail,
           Concatenation("could not open ", path, " for writing"));
    SetPrintFormattingStatus(stream, false);
    PrintTo(stream,
        "# Resolution outcome from run_e_plus_5_resolution.g (A-5a, ",
        "issue #46).\n",
        "# peak_rss_mb is filled in by run_e_plus_5_resolution.sh; if ",
        "the GAP\n",
        "# process is killed (OOM) the wrapper synthesises a failure ",
        "outcome.\n",
        "return rec(\n",
        "    group_label      := \"", group_label, "\",\n",
        "    group_order      := ", String(group_order), ",\n",
        "    resolution_arity := 4,\n",
        "    success          := ", If_(success, "true", "false"), ",\n",
        "    wall_clock_sec   := ", String(wall_sec), ",\n",
        "    gap_heap_mb      := ", String(heap_mb), ",\n",
        "    peak_rss_mb      := \"unknown\",\n",
        "    error_msg        := \"", error_msg, "\",\n",
        "    started_at       := \"", started_at, "\"\n",
        ");;\n");
    CloseStream(stream);
end;;

# --- driver ---------------------------------------------------------

# Generic resolution attempt; parameterised over the group, label, and
# outcome path so the test suite can exercise the same code path on a
# small group (e.g. D_8) without invoking the real E_+(5) computation.
RunResolutionAttempt := function(G, group_label, group_order, outcome_path)
    local started_at, t0, captured, success, error_msg, R,
          wall_sec, heap_mb;

    started_at := _A5A_IsoTimestamp();
    t0 := _A5A_WallClockSec();

    Print("[A-5a] starting ResolutionFiniteGroup(", group_label,
          ", 4) at ", started_at, "\n");

    captured := CALL_WITH_CATCH(ResolutionFiniteGroup, [G, 4]);
    wall_sec := _A5A_WallClockSec() - t0;

    if captured[1] then
        success := true;
        error_msg := "";
        R := captured[2];
        Print("[A-5a] resolution succeeded in ", wall_sec, " s\n");
        Print("[A-5a] R!.dimension(0..4) = [",
              R!.dimension(0), ", ", R!.dimension(1), ", ",
              R!.dimension(2), ", ", R!.dimension(3), ", ",
              R!.dimension(4), "]\n");
    else
        success := false;
        # CALL_WITH_CATCH returns the error message on failure (string).
        error_msg := String(captured[2]);
        # Sanitise quotes so the outcome.g remains valid GAP source.
        error_msg := ReplacedString(error_msg, "\"", "\\\"");
        Print("[A-5a] resolution FAILED after ", wall_sec, " s: ",
              error_msg, "\n");
    fi;

    heap_mb := _A5A_GapHeapMB();
    Print("[A-5a] GAP heap (live, MB) = ", heap_mb, "\n");

    _A5A_WriteOutcome(outcome_path, success, wall_sec, heap_mb,
                      error_msg, started_at, group_label, group_order);
    Print("[A-5a] wrote ", outcome_path, "\n");

    return rec(success := success, wall_clock_sec := wall_sec,
               gap_heap_mb := heap_mb, error_msg := error_msg);
end;;

RunEPlus5Resolution := function()
    return RunResolutionAttempt(ExtraspecialGroup(2048, "+"),
                                "E_+(5)", 2048, _A5A_OUTCOME_PATH);
end;;

# Auto-invoke when read as a script (guarded for the test suite).
if not IsBoundGlobal("A5A_DRIVER_NO_AUTOINVOKE") then
    RunEPlus5Resolution();
fi;
