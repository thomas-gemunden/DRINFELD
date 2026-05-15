# Resolution outcome from run_e_plus_5_resolution.g (A-5a, issue #46).
# peak_rss_mb is filled in by run_e_plus_5_resolution.sh; if the GAP
# process is killed (OOM) the wrapper synthesises a failure outcome.
return rec(
    group_label      := "E_+(5)",
    group_order      := 2048,
    resolution_arity := 4,
    success          := true,
    wall_clock_sec   := 548.17420845801826,
    gap_heap_mb      := 634.306640625,
    peak_rss_mb      := 1214.44,
    error_msg        := "",
    started_at       := "Fri May 15 11:38:15 UTC 2026"
);;
