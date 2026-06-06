# test_build_krr_sparse_smoke_m3.g — smoke test that
# `BuildKRRSpectralCharactersSparse(3)` returns a self-consistent result
# under the compile-primitive GF(2) RREF rewrites of `_BuildTraceCtx` and
# `_F2_AffineSolveCols` (#449 A3 + C4).

Read("bw_lattice.g");
Read("em_construction.g");
Read("twisted_group_algebra.g");
Read("qforms_f2.g");
Read("defect_rep_minus_id.g");
Read("defect_rep_minus_id_optim.g");
Read("untwisted_modular_data.g");
Read("krr_spectral_characters.g");
Read("krr_spectral_characters_sparse.g");
if IsBoundGlobal("BuildKRRSpectralCharactersSparse") = false then
    Error("BuildKRRSpectralCharactersSparse not loaded");
fi;

TBKM := 3;;
Print("=== BuildKRRSpectralCharactersSparse(3) FINGERPRINT ===\n");

# Force fresh state.
ResetSparseTraceCache();
ResetTraceHCache();
ResetGaussCtxCache();

TBKR := BuildKRRSpectralCharactersSparse(TBKM);;

Print("\n--- Result summary ---\n");
Print("source = ", TBKR.source, "\n");
Print("m = ", TBKR.m, "\n");
Print("num_classes = ", Length(TBKR.idx.classes), "\n");

# Dump central-class trace data as a fingerprint.
TBKZ := -IdentityMat(2^TBKM);;
TBKCIDX := PositionProperty(TBKR.idx.reps, a -> a = TBKZ);;
Print("central_class_idx = ", TBKCIDX, "\n");

if TBKR.centraliser_traces[TBKCIDX] = fail then
    Print("CENTRAL CLASS HAS NO TRACES\n");
else
    Print("\n--- central class trace table ---\n");
    Print("num conjugacy classes of C_G(-I) = ",
          Length(TBKR.centraliser_traces[TBKCIDX].traces), "\n");
    Print("traces = ", TBKR.centraliser_traces[TBKCIDX].traces, "\n");
    Print("sizes  = ", TBKR.centraliser_traces[TBKCIDX].sizes, "\n");
    Print("multiplicities = ", TBKR.multiplicities[TBKCIDX], "\n");
fi;

Print("=== END FINGERPRINT ===\n");
