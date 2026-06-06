# test_buildtracectx_perf_m5.g — micro-benchmark for #449 A3 + C4 perf
# of `_BuildTraceCtx(h, m=5)`.  Times a clean rebuild over the first 10
# generators of EmUnimodGroup(5).

Read("bw_lattice.g");
Read("em_construction.g");
Read("twisted_group_algebra.g");
Read("qforms_f2.g");
Read("defect_rep_minus_id.g");
Read("defect_rep_minus_id_optim.g");
Read("untwisted_modular_data.g");
Read("krr_spectral_characters.g");
Read("krr_spectral_characters_sparse.g");

TPPM := 5;;
TPPG := EmUnimodGroup(TPPM);;
TPPGENS := GeneratorsOfGroup(TPPG);;
TPPCOUNT := Minimum(Length(TPPGENS), 10);;

Print("=== _BuildTraceCtx PERF (m = 5) ===\n");
Print("Building over first ", TPPCOUNT, " generators\n");

ResetTraceHCache();
TPPT0 := Runtime();
for TPPI in [1..TPPCOUNT] do
    _BuildTraceCtx(TPPGENS[TPPI], TPPM);
od;
TPPT1 := Runtime();
Print("Wall time: ", (TPPT1 - TPPT0) / 1000.0, " s\n");
Print("Per gen:   ", (TPPT1 - TPPT0) / 1000.0 / TPPCOUNT, " s\n");
Print("=== END PERF ===\n");
