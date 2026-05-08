# E_+(7) canonical S-blocks (Phase E_BRW step 1 for m=7).
#
# The actual block data lives in canonical_blocks.g (8.7 GB), which
# is gitignored.  Re-create with:
#   cd extraspecial_orbifolds/scripts
#   gap -q -b -o 60G -c 'Read("run_e_plus_7_canonical.g");'
# Wall time ~16 minutes on this machine.
#
# Bypasses GAP's ConjugacyClasses(E_+(7)) memory wall by computing
# only the centralisers of the 6 canonical class representatives
# (orders 16384, GAP can handle these), and using the closed-form
# Irr(E_+(7)) (16384 1-dim factoring through E/Z = (F_2)^14, plus
# 1 faithful of dim 128) for the central sectors via the Phase D
# closed-form formula.

manifest := rec(
    m := 7,
    group_construction := "ExtraspecialGroup(32768, +)",
    group_order := 32768,
    canonical_class_reps := rec(
        id := "One(G)",
        minus_one := "z (= Centre(G).2)",
        sigma2_canon := "GeneratorsOfGroup(G)[1] (a_1)",
        sigma2_second := "GeneratorsOfGroup(G)[3] (a_2)",
        sigma1sigma2_canon := "GeneratorsOfGroup(G)[1] * GeneratorsOfGroup(G)[2] (a_1 b_1)",
        sigma1sigma2_second := "GeneratorsOfGroup(G)[3] * GeneratorsOfGroup(G)[4] (a_2 b_2)"
    ),
    centraliser_orders := rec(
        sigma2 := 16384,                # = |G|/2
        sigma1sigma2 := 16384
    ),
    irrep_counts := rec(
        E_plus_7 := 16385,              # 4^7 + 1 (analytical)
        Z2_x_E6 := 8194,                # 2*(4^6+1) = 2*4^6 + 2
        Z4_circ_E6 := 8194              # same count
    ),
    blocks_computed := [
        "sigma2_sigma2_diag",            # 8194 x 8194
        "sigma2_sigma2_off",             # 8194 x 8194
        "sigma2_sigma1sigma2_off",       # 8194 x 8194
        "sigma1sigma2_sigma1sigma2_diag",
        "sigma1sigma2_sigma1sigma2_off",
        "id_sigma2_off",                 # 16385 x 8194  (closed form)
        "id_sigma1sigma2_off",           # 16385 x 8194  (closed form)
        "minus_one_sigma2_off",          # 16385 x 8194  (closed form)
        "minus_one_sigma1sigma2_off"     # 16385 x 8194  (closed form)
    ],
    blocks_NOT_computed := [
        # The fully-central blocks (id, id), (id, -1), (-1, -1).  These
        # have closed-form entries:
        #   S_(id, rho), (id, sigma) = dim(rho) * dim(sigma) / |G|
        #   S_(id, rho), (-1, sigma) = dim(rho) * sigma(z) / |G|
        #   S_(-1, rho), (-1, sigma) = rho(z) * sigma(z) / |G|
        # so we don't need to materialise them as 16385 x 16385 arrays.
        "id_id_diag (16385 x 16385, materialise on demand)",
        "id_minus_one_off (16385 x 16385, materialise on demand)",
        "minus_one_minus_one_diag (16385 x 16385, materialise on demand)"
    ],
    wall_time_summary := rec(
        setup_centralisers_chartables := "~3 minutes",
        non_central_blocks := "5 blocks at ~130-150 s each",
        central_x_noncentral_blocks := "4 blocks at 13-21 s each (closed form)",
        total := "~16 minutes"
    ),
    storage := rec(
        on_disk_canonical_blocks_g := "8.7 GB"
    )
);;
