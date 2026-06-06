# test_buildtracectx_parity.g — fingerprint helper for #449 A3 parity check.
#
# Mirrors `test_buildgaussctx_parity.g`: dumps a byte-stable fingerprint of
# the rec returned by `_BuildTraceCtx(h, m)` for the first 4 generators of
# `EmUnimodGroup(m)`. Used to verify that the compiled-GF(2) RREF rewrite
# of `_BuildTraceCtx` is byte-identical to the interpreted version.

Read("bw_lattice.g");
Read("em_construction.g");
Read("twisted_group_algebra.g");
Read("qforms_f2.g");
Read("defect_rep_minus_id.g");
Read("defect_rep_minus_id_optim.g");
Read("untwisted_modular_data.g");
Read("krr_spectral_characters.g");
Read("krr_spectral_characters_sparse.g");

if not IsBoundGlobal("TEST_M") then
    TEST_M := 3;
fi;
TPTM := TEST_M;;

TPTN := 2^TPTM;;
TPTG := EmUnimodGroup(TPTM);;
TPTGENS := GeneratorsOfGroup(TPTG);;
TPTHCOUNT := Minimum(Length(TPTGENS), 4);;

Print("=== _BuildTraceCtx PARITY FINGERPRINT ===\n");
Print("m = ", TPTM, ", n = ", TPTN,
      ", #gens = ", Length(TPTGENS),
      ", testing first ", TPTHCOUNT, " generators\n\n");

for TPTI in [1..TPTHCOUNT] do
    TPTH := TPTGENS[TPTI];
    Print("--- h_", TPTI, " (gens[", TPTI, "]) ---\n");
    # Reset cache to force a real rebuild for this h.
    ResetTraceHCache();
    TPTCTX := _BuildTraceCtx(TPTH, TPTM);
    Print("n = ", TPTCTX.n, "\n");
    Print("k = ", TPTCTX.k, "\n");
    Print("kerLen = ", TPTCTX.kerLen, "\n");
    Print("rank = ", TPTCTX.rank, "\n");
    Print("pivCols = ", TPTCTX.pivCols, "\n");
    Print("solveMap = ", TPTCTX.solveMap, "\n");
    Print("feasMat = ", TPTCTX.feasMat, "\n");
    Print("BPi = ", TPTCTX.BPi, "\n");
    Print("H = ", TPTCTX.H, "\n");
    Print("R = ", TPTCTX.R, "\n");
    Print("Mhh = ", TPTCTX.Mhh, "\n");
    Print("MhhSym = ", TPTCTX.MhhSym, "\n");
    Print("A = ", TPTCTX.A, "\n");
    Print("AT = ", TPTCTX.AT, "\n");
    Print("HT = ", TPTCTX.HT, "\n");
    Print("RT = ", TPTCTX.RT, "\n");
    Print("\n");
od;
Print("=== END FINGERPRINT ===\n");
