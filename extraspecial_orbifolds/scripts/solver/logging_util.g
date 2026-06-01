# logging_util.g — shared timestamped logging helpers (issue #384).
#
# Centralises the timestamping idiom that was scattered across drivers
# (e.g. _A5A_IsoTimestamp in run_e_plus_5_resolution.g) and provides two
# entry points:
#
#   _LogStamped(args...)
#     Prefixes the args with `[YYYY-MM-DDTHH:MM:SSZ] ` and prints via
#     the regular Print(). Use at phase boundaries in driver and
#     library code so `tail -f` shows when each phase started/ended.
#
#   _LogPhase(phase_name, args...)
#     As _LogStamped, but adds a `[phase_name]` tag after the timestamp
#     so log readers can filter on phase. Use for decision-point
#     branches where the line should signal which codepath was taken
#     (e.g. `[cache] orbit 1: LOADED`, `[cache] orbit 2: BUILT`).
#
# Both helpers are GUARANTEED to emit a trailing newline so they can be
# safely chained without worrying about the buffered-decision-line
# anti-pattern (where a `Print("phase ... ")` waits for the work to
# finish before the line becomes visible — see PR #383 LoadOrbitCache).
#
# Implementation: CurrentDateTimeString is provided by the IO package.
# We wrap in CALL_WITH_CATCH so the helpers work even if IO is missing
# (degraded mode: prefix becomes `[epoch+N] ` where N is Unix epoch).
#
# Not for use inside tight loops (per-vec, per-target, per-element):
# the CurrentDateTimeString dispatch adds ~10-50 microseconds per call,
# which would dominate at >1000 iters/sec. For tight loops, keep the
# existing plain Print() lines.

_LOGGING_UTIL_LOADED := true;;

# Returns ISO-8601 UTC timestamp, e.g. "2026-06-01T18:42:03Z".
# Falls back to `epoch+<sec>` if IO's CurrentDateTimeString is absent.
_LogTimestamp := function()
    local r;
    r := CALL_WITH_CATCH(CurrentDateTimeString, [["-u"]]);
    if r[1] then return r[2]; fi;
    # Degraded fallback. NanosecondsSinceEpoch is in core GAP.
    return Concatenation("epoch+",
                         String(QuoInt(NanosecondsSinceEpoch(),
                                       1000000000)));
end;;

# CallFuncList with args list to Print() — GAP idiom for variadic
# forwarding. The internal `args` of a variadic function is a list.
_LogStamped := function(args...)
    CallFuncList(Print,
                 Concatenation([Concatenation("[", _LogTimestamp(), "] ")],
                               args,
                               ["\n"]));
end;;

# Same as _LogStamped but also prefixes a [phase_name] tag.
_LogPhase := function(phase_name, args...)
    CallFuncList(Print,
                 Concatenation([Concatenation("[", _LogTimestamp(),
                                              "][", phase_name, "] ")],
                               args,
                               ["\n"]));
end;;
