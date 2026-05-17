# A-7a m=7 probe outcome (issue #50, re-scoped as HAP route).
#
# Recorded manually from the run of run_e_plus_7_kernel_probe.g
# (the GAP probe was killed mid-Phase 3 UCT after demonstrating
# that the LHS resolution loads successfully and that the Tier-4
# setup machinery configures from R_E without the BRWConjugacyAction
# bottleneck).
#
# What this probe established:
#   - LHS R_E builds successfully on Image(IsomorphismPcGroup(EmGroup(7)))
#     in 716.11 s wall (consistent with PR #252's 822 s on
#     ExtraspecialGroup; minor variation is expected since the underlying
#     pc-presentation differs between IsomorphismPcGroup(EmGroup(m)) and
#     ExtraspecialGroup(2^{2m+1}, "+")).
#   - R_E dimensions [1, 15, 120, 680, 3060, 11628] match the m=7 LHS
#     outcome on disk (lhs_resolution_outcome.g), confirming the LHS
#     route works on the EmGroup-pc-form group object that the rest of
#     the BRW machinery uses.
#   - Heap remains under 400 MB throughout LHS build (peak ~145 MB after
#     R_E built; UCT phase pushes to ~315 MB). Well below 32 GB target.
#   - UCT phase (NullspaceIntMat / BaseIntMat on 3060 x 11628 boundary
#     matrix) is the next bottleneck. Probe was killed after >7 min of
#     Phase 3 with no completion; this matches the rough cost estimate
#     of O(n^2 * m) where n ~ 3060, m ~ 11628.
#
# What was NOT established by this probe:
#   - The H^3 torsion vector (Z/2)^90 — known from disk but not
#     confirmed by THIS probe's UCT computation.
#   - The BRW H^3 action matrices (would need 15+ further
#     H3MatrixOfAutomorphism calls, each involving EquivariantChainMap).
#   - The per-generator sweep wall (would need BuildPerClassCocycleBasis
#     on |C| up to 32768).
#
# Why the unified driver run_e_plus_m_kernel_hap.g (MPARAM := 7) is
# NOT recommended at m=7:
#
#   BRWConjugacyAction(7) is itself prohibitively slow at m=7:
#   ~16386 conjugacy classes x ~28 BRW outer generators x O(n)
#   ClassIndexOf per check = ~13 billion ops. Expected wall: 6-8 hours
#   just for the BRW conjugacy action setup.
#
#   Add to that: per-class basis caches (BuildPerClassCocycleBasis with
#   |C| up to 32768 at the central orbit) would each cost
#   O(|C|^2 * k * cocyclebasis_eval_cost) - for |C| = 32768 and k = 90,
#   that is ~96 billion HAP Syzygy evaluations per cache.
#
#   Estimated full kernel sweep at m=7: weeks of wall time, even with
#   the BRW orbit reduction (4 orbits) caching applied. The Q-int B3 m=7
#   workstream (issue #166) is the right place to tackle this with the
#   sparse-trace / lazy-transports machinery.
#
# Recommended next steps (out of scope for A-7a):
#   - Optimise BRWConjugacyAction(m=7): replace O(n) ClassIndexOf with
#     a dictionary keyed by element, O(1) lookup. Memoise representative
#     conjugation across generators if applicable.
#   - At m=7, consider skipping BRW orbit reduction altogether (4 orbit
#     reps from m=2, m=3, m=5 are the same structurally: id, sigma2,
#     -id, sigma_1sigma_2). Hard-code the orbit representatives and
#     compute the BRW H^3 action matrices via Hadamard-CZ generation,
#     without enumerating all 16386 conjugacy classes.
#   - Cache-to-disk: serialise R_E + UCT data after the 716s + multi-min
#     UCT, so subsequent driver invocations skip rebuild.
return rec(
    group_label                := "E_+(7)",
    group_order                := 32768,

    # Phase 1 (em construction) results.
    phase1_em_pc_form_wall_sec := 5.001,
    heap_after_phase1_mb       := 121.29,

    # Phase 2 (LHS resolution) results.
    phase2_R_V_wall_sec        := 0.078,
    phase2_R_E_wall_sec        := 716.11,
    phase2_total_wall_sec      := 716.189,
    R_E_dimensions             := [ 1, 15, 120, 680, 3060, 11628 ],
    heap_after_phase2_mb       := 145.6,

    # Phase 3 (UCT) results — partial: probe killed before completion.
    phase3_status              := "PARTIAL_KILLED_AT_7_MIN_NO_OUTPUT",
    heap_during_phase3_mb      := 315.0,    # observed peak

    # Setup record fields (from on-disk lhs_resolution_outcome.g; not
    # re-computed by this probe, since UCT did not complete).
    H3_value                   := "(Z/2)^90",
    H3_torsion_known           := [ 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
                                    2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
                                    2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
                                    2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
                                    2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
                                    2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
                                    2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
                                    2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
                                    2, 2, 2, 2, 2, 2, 2, 2, 2, 2 ],
    H3_exponent_known          := 2,
    H3_num_generators_known    := 90,

    # Sweep status (not run).
    sweep_status               := "NOT_RUN",
    sweep_reason_not_run       := "UCT phase did not complete within probe budget; BRWConjugacyAction(7) for the full driver is estimated 6-8h. See report.",

    # Acceptance.
    lhs_resolution_loads       := true,
    setup_machinery_starts     := true,
    full_kernel_sweep_wall_estimate_per_gen_seconds := "see report — multi-hour minimum, weeks for full 90-generator sweep",
    full_kernel_sweep_RSS_estimate_GB := "1-2 GB (dominant cost is BuildPerClassCocycleBasis tables, not memory)"
);;
