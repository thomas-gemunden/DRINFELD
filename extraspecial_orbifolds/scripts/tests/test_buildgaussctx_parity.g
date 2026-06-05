# test_buildgaussctx_parity.g — fingerprint helper for #446 parity check.

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
TPGM := TEST_M;;

TPGN := 2^TPGM;;
TPGG := EmUnimodGroup(TPGM);;
TPGGENS := GeneratorsOfGroup(TPGG);;
TPGHCOUNT := Minimum(Length(TPGGENS), 4);;

Print("=== _BuildGaussCtx PARITY FINGERPRINT ===\n");
Print("m = ", TPGM, ", n = ", TPGN,
      ", #gens = ", Length(TPGGENS),
      ", testing first ", TPGHCOUNT, " generators\n\n");

for TPGI in [1..TPGHCOUNT] do
    TPGH := TPGGENS[TPGI];
    Print("--- h_", TPGI, " (gens[", TPGI, "]) ---\n");
    TPGCTX := _BuildGaussCtx(TPGH, TPGM);
    Print("kerLen = ", TPGCTX.kerLen, "\n");
    Print("dimND  = ", TPGCTX.dimND, "\n");
    Print("radLen = ", TPGCTX.radLen, "\n");
    Print("base_val = ", TPGCTX.base_val, "\n");
    Print("Q = ", TPGCTX.Q, "\n");
    Print("F_mat = ", TPGCTX.F_mat, "\n");
    Print("BT_radmat = ", TPGCTX.BT_radmat, "\n");
    Print("t_rad = ", TPGCTX.t_rad, "\n");
    Print("\n");
od;
Print("=== END FINGERPRINT ===\n");
