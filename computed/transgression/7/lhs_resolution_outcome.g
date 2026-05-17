# E_+(7) LHS-perturbed HAP resolution outcome (Q-int C-2, issue #238).
#
# Recorded by hand from a manual probe (the auto-driver
# run_e_plus_7_lhs.g writes the same record; this file was committed
# in the PR so downstream consumers don't have to re-run the 12-min
# build to discover the values).
#
# Build was on Mac M2 Max, GAP 4.15.1, HAP 1.70, GAP heap cap -o 16g.
return rec(
    group_label         := "E_+(7)",
    group_order         := 32768,
    resolution_arity    := 5,
    builder             := "abelian",
    success             := true,
    wall_clock_sec      := 864.0,
    build_time_V_sec    := 0.077,
    build_time_LHS_sec  := 822.17,
    gap_heap_mb         := 448.03,
    peak_rss_mb         := "unknown",
    R_V_dims            := [ 1, 14, 105, 560, 2380, 8568 ],
    R_E_dims            := [ 1, 15, 120, 680, 3060, 11628 ],
    H3_value            := [ 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
                             2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
                             2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
                             2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
                             2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
                             2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
                             2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
                             2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
                             2, 2, 2, 2, 2, 2, 2, 2, 2, 2 ],
    H3_pretty           := "(Z/2)^90",
    # H^4 has 454 Z/2 summands + one Z/4; the full vector is omitted
    # from this hand-written record for brevity (re-create via the
    # driver to repopulate). It is by construction
    # Concatenation(List([1..454], _ -> 2), [4]).
    H4_value            := "see H4_pretty (full vector elided)",
    H4_pretty           := "(Z/2)^454 (+) Z/4",
    error_msg           := "",
    started_at          := "2026-05-17T16:21:00Z"
);;
