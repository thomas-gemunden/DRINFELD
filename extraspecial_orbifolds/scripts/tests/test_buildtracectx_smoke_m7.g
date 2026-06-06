# test_buildtracectx_smoke_m7.g — smoke for #449 A3 at m=7: just build
# `_BuildTraceCtx(h, 7)` on the first generator and verify it returns
# without error.

Read("bw_lattice.g");
Read("em_construction.g");
Read("twisted_group_algebra.g");
Read("qforms_f2.g");
Read("defect_rep_minus_id.g");
Read("defect_rep_minus_id_optim.g");
Read("untwisted_modular_data.g");
Read("krr_spectral_characters.g");
Read("krr_spectral_characters_sparse.g");

TSM := 7;;
TSG := EmUnimodGroup(TSM);;
TSGENS := GeneratorsOfGroup(TSG);;
Print("=== _BuildTraceCtx SMOKE (m = 7) ===\n");
Print("first gen: ", TSGENS[1], "\n");
ResetTraceHCache();
TST0 := Runtime();
TSCTX := _BuildTraceCtx(TSGENS[1], TSM);;
TST1 := Runtime();
Print("Wall time: ", (TST1 - TST0) / 1000.0, " s\n");
Print("rank = ", TSCTX.rank, ", n = ", TSCTX.n,
      ", kerLen = ", TSCTX.kerLen, "\n");
Print("len(solveMap) = ", Length(TSCTX.solveMap),
      ", len(feasMat) = ", Length(TSCTX.feasMat), "\n");
Print("=== END SMOKE ===\n");
