# test_f2_affinesolvecols_parity.g — fingerprint helper for #449 C4 parity.
#
# `_F2_AffineSolveCols(A, b)` is invoked from inside `TraceOnOmega0Gauss`
# with the joint matrix `[F_mat; BT_radmat]` and RHS `[0; t_rad]`.  Direct
# fingerprint check via `_BuildGaussCtx` (which feeds it) would be
# indirect; here we build it directly with constant test inputs and dump
# the returned record.  We also smoke-check it via TraceOnOmega0Gauss(h, m).

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
TFAM := TEST_M;;

# ----- Direct test on hand-crafted inputs -----
Print("=== _F2_AffineSolveCols PARITY FINGERPRINT (direct) ===\n");

# Test 1: 3x4 system with non-trivial kernel.
TFA1 := [[1, 0, 1, 0],
         [0, 1, 1, 0],
         [1, 1, 0, 0]];   # row3 = row1+row2 so rank=2
TFB1 := [1, 0, 1];        # consistent
TFR1 := _F2_AffineSolveCols(TFA1, TFB1);
Print("--- Case 1: 3x4 system, rank=2, consistent ---\n");
Print("particular = ", TFR1.particular, "\n");
Print("kerBasis = ", TFR1.kerBasis, "\n");

# Test 2: Inconsistent system.
TFA2 := [[1, 0, 0],
         [0, 1, 0],
         [1, 1, 0]];
TFB2 := [1, 0, 1];        # row3 = row1+row2, but b[3] = 1 != 1+0 = 1, so consistent
TFR2 := _F2_AffineSolveCols(TFA2, TFB2);
Print("--- Case 2: 3x3 system, consistent ---\n");
Print("particular = ", TFR2.particular, "\n");
Print("kerBasis = ", TFR2.kerBasis, "\n");

# Test 3: Inconsistent system.
TFA3 := [[1, 0, 0],
         [0, 1, 0],
         [1, 1, 0]];
TFB3 := [1, 0, 0];        # row3 = row1+row2 but 0 != 1+0
TFR3 := _F2_AffineSolveCols(TFA3, TFB3);
Print("--- Case 3: 3x3 system, INCONSISTENT ---\n");
Print("particular = ", TFR3.particular, "\n");
Print("kerBasis = ", TFR3.kerBasis, "\n");

# Test 4: Larger system at n=4 (m=2 size).
TFA4 := [[1, 0, 1, 1],
         [0, 1, 0, 1],
         [1, 1, 1, 0],
         [0, 0, 1, 0]];
TFB4 := [1, 0, 1, 0];
TFR4 := _F2_AffineSolveCols(TFA4, TFB4);
Print("--- Case 4: 4x4 system ---\n");
Print("particular = ", TFR4.particular, "\n");
Print("kerBasis = ", TFR4.kerBasis, "\n");

# ----- Indirect test via TraceOnOmega0Gauss -----
Print("\n=== TraceOnOmega0Gauss FINGERPRINT (m = ", TFAM, ") ===\n");

TFAG := EmUnimodGroup(TFAM);;
TFAGENS := GeneratorsOfGroup(TFAG);;
TFAHCOUNT := Minimum(Length(TFAGENS), 4);;
for TFAI in [1..TFAHCOUNT] do
    TFAH := TFAGENS[TFAI];
    ResetSparseTraceCache();
    ResetTraceHCache();
    ResetGaussCtxCache();
    Print("h_", TFAI, ": Tr(T_h) = ", TraceOnOmega0Gauss(TFAH, TFAM), "\n");
od;

Print("=== END FINGERPRINT ===\n");
