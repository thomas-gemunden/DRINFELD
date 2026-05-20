# test_epsilon_omega_phase.g — V-1 production-wiring tests.
#
# Covers the `EpsilonOmegaPhase(omega_vec, G, m_rank, g1, g2, a, b)`
# wrapper added in #316 (V-1 / #14). The integer-phase backbone
# `EpsilonOmega` is already covered by `test_epsilon_omega.g`; here we
# test the vector->callable bridge specifically, since that is what
# `BuildKRRIntertwinerData` invokes from PR #309.
#
# Tests:
#   (1) omega_vec = 0 in hom-basis coordinates  ->  EpsilonOmegaPhase = 1
#       for all sampled (g1, g2, a, b) tuples.  This is the V-1 acceptance
#       criterion (a) — vacuous twist gives trivial phase.
#
#   (2) omega_vec = 0 in R-cocycle coordinates  ->  EpsilonOmegaPhase = 1
#       (the wrapper accepts both lengths).
#
#   (3) For G = Q_8 with the order-2 cocycle (hom-coords [0, 4, 0]) the
#       central-row entries of the §6.2 S-formula computed via
#       EpsilonOmegaPhase match those computed via the lower-level
#       EpsilonOmegaWithSection. This is the "wrapper is consistent
#       with backbone" check (since EpsilonOmegaWithSection is already
#       verified byte-for-byte against modular_data/8/4/2.txt in
#       test_epsilon_omega.g).
#
#   (4) Cache behaviour: two calls with the same (G, omega_vec) reuse
#       the cached context (no second ResolutionFiniteGroup invocation).
#
# Run from a GAP session that has already loaded:
#   - hap, io
#   - extraspecial_orbifolds/scripts/epsilon_omega_phase.g
#     (which transitively loads epsilon_omega.g)
#
# Suggested invocation:
#   gap> Read("extraspecial_orbifolds/scripts/tests/test_epsilon_omega_phase.g");
# from the DRINFELD root.

LoadPackage("hap");;
LoadPackage("io");;

# Absolute-path load (matches test_epsilon_omega.g convention so the test
# can run from any CWD).
if not IsBoundGlobal("EpsilonOmegaPhase") then
    Read("/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-316/extraspecial_orbifolds/scripts/epsilon_omega_phase.g");
fi;

# ----------------------------------------------------------------------
# Test infrastructure (lightweight; matches sibling test files).
# ----------------------------------------------------------------------
TEPP_FAILS := 0;;
TEPP_TOTAL := 0;;
TEPP_Assert := function(label, cond)
    TEPP_TOTAL := TEPP_TOTAL + 1;
    if not cond then
        TEPP_FAILS := TEPP_FAILS + 1;
        Print("  FAIL: ", label, "\n");
    else
        Print("  PASS: ", label, "\n");
    fi;
end;;


# ============================================================
# (1) omega_vec = 0 in hom-basis coordinates -> phase = 1.
# ============================================================
Print("\n[1] Trivial omega (hom-basis zero vector):\n");

T1_G := SmallGroup(8, 4);;   # Q_8 — strong test (non-abelian)
T1_R := ResolutionFiniteGroup(T1_G, 4);;
T1_K := TensorWithIntegers(T1_R);;
T1_UCT := UniversalCoefficientsTheorem(T1_K, 3);;
T1_HOMBASIS_LEN := Length(T1_UCT.hombasis);;
T1_ZERO_HOM := ListWithIdenticalEntries(T1_HOMBASIS_LEN, 0);;

Print("  Q_8: hombasis length = ", T1_HOMBASIS_LEN, "\n");

Reset(GlobalMersenneTwister, 12345);;
T1_ELTS := AsList(T1_G);;
T1_M_RANK := 5;;     # informational; ignored by EpsilonOmegaPhase.

T1_count := 0;;
T1_pass := 0;;
T1_max_samples := 20;;
for T1_i in [1..T1_max_samples] do
    T1_g1 := Random(GlobalMersenneTwister, T1_ELTS);
    T1_g2 := Random(GlobalMersenneTwister, T1_ELTS);
    T1_a := Random(GlobalMersenneTwister, ConjugacyClass(T1_G, T1_g1));
    T1_b := Random(GlobalMersenneTwister, ConjugacyClass(T1_G, T1_g2));
    T1_count := T1_count + 1;
    T1_val := EpsilonOmegaPhase(T1_ZERO_HOM, T1_G, T1_M_RANK,
                                 T1_g1, T1_g2, T1_a, T1_b);
    if T1_val = 1 then
        T1_pass := T1_pass + 1;
    else
        Print("    miss: phase = ", T1_val,
              " for (g1=", T1_g1, ", g2=", T1_g2,
              ", a=", T1_a, ", b=", T1_b, ")\n");
    fi;
od;;
TEPP_Assert(
    Concatenation("(1) Trivial omega -> phase = 1 on ",
                  String(T1_max_samples), " random tuples in Q_8"),
    T1_pass = T1_count);


# ============================================================
# (2) omega_vec = 0 in R-cocycle coordinates -> phase = 1.
# ============================================================
Print("\n[2] Trivial omega (R-cocycle zero vector):\n");

T2_COCY_LEN := T1_R!.dimension(3);;
T2_ZERO_COCY := ListWithIdenticalEntries(T2_COCY_LEN, 0);;
Print("  Q_8: R-cocycle length = ", T2_COCY_LEN, "\n");

T2_pass := true;;
for T2_i in [1..10] do
    T2_g1 := Random(GlobalMersenneTwister, T1_ELTS);
    T2_g2 := Random(GlobalMersenneTwister, T1_ELTS);
    T2_a := Random(GlobalMersenneTwister, ConjugacyClass(T1_G, T2_g1));
    T2_b := Random(GlobalMersenneTwister, ConjugacyClass(T1_G, T2_g2));
    T2_val := EpsilonOmegaPhase(T2_ZERO_COCY, T1_G, T1_M_RANK,
                                 T2_g1, T2_g2, T2_a, T2_b);
    if T2_val <> 1 then
        T2_pass := false;
        Print("    miss: phase = ", T2_val, "\n");
    fi;
od;;
TEPP_Assert("(2) Trivial omega (R-cocycle coords) -> phase = 1",
            T2_pass);


# ============================================================
# (3) Q_8 nontrivial omega: wrapper vs. backbone consistency.
# ============================================================
Print("\n[3] Q_8 order-2 cocycle: EpsilonOmegaPhase vs EpsilonOmegaWithSection:\n");

# The order-2 cocycle of Q_8 lives in H^3(Q_8; Z) = Z/8 with the 4 ·
# (single generator). In hom-basis coordinates this is the length-1
# vector [4]; the matching R-cocycle representative (length R!.dim(3) = 3)
# is 4 · UCT.cocyclebasis[1] = 4 · [6, 1, 0] = [24, 4, 0] ≡ [0, 4, 0] mod 8.
# Both encodings must produce the SAME phase via the wrapper.
T3_OMEGA_HOM := [4];;            # hom-coord (length 1)
T3_OMEGA_RCOCY := [0, 4, 0];;    # R-cocycle coord (length 3)

# Reference cocycle (built manually for the backbone comparison).
T3_R := T1_R;;            # share the resolution.
T3_UCT := T1_UCT;;
T3_M_OMEGA := T3_UCT!.exponent;;
Print("  m_omega = UCT.exponent = ", T3_M_OMEGA, "\n");

T3_OMEGA_R := ListWithIdenticalEntries(T1_R!.dimension(3), 0);;
for T3_i in [1..T1_HOMBASIS_LEN] do
    T3_OMEGA_R := T3_OMEGA_R + T3_OMEGA_HOM[T3_i] * T3_UCT!.cocyclebasis[T3_i];
od;;
T3_OMEGA_R := T3_OMEGA_R mod T3_M_OMEGA;;
Print("  hom-coord [4] -> R-cocycle ", T3_OMEGA_R, "\n");
T3_OMEGA_CB := StandardCocycle(T3_R, T3_OMEGA_R, 3, T3_M_OMEGA);;

# Sample 20 tuples (g1, g2, a, b) with a in [g1], b in [g2]. Compare
# the cyclotomic phase returned by EpsilonOmegaPhase against the
# cyclotomic E(m_omega)^EpsilonOmegaWithSection(...).
Reset(GlobalMersenneTwister, 54321);;

T3_total := 0;;
T3_match_hom := 0;;
T3_match_rcocy := 0;;
T3_match_eq := 0;;
for T3_i in [1..20] do
    T3_g1 := Random(GlobalMersenneTwister, T1_ELTS);
    T3_g2 := Random(GlobalMersenneTwister, T1_ELTS);
    T3_a := Random(GlobalMersenneTwister, ConjugacyClass(T1_G, T3_g1));
    T3_b := Random(GlobalMersenneTwister, ConjugacyClass(T1_G, T3_g2));
    # Sections to feed the backbone.
    T3_ta := RepresentativeAction(T1_G, T3_g1, T3_a);
    T3_sb := RepresentativeAction(T1_G, T3_g2, T3_b);
    if T3_ta = fail or T3_sb = fail then continue; fi;
    T3_total := T3_total + 1;

    T3_int := EpsilonOmegaWithSection(T3_OMEGA_CB, T3_g1, T3_g2,
                                       T3_a, T3_b, T3_ta, T3_sb, T3_M_OMEGA);
    T3_backbone_phase := E(T3_M_OMEGA) ^ T3_int;
    T3_wrapper_hom := EpsilonOmegaPhase(T3_OMEGA_HOM, T1_G, T1_M_RANK,
                                         T3_g1, T3_g2, T3_a, T3_b);
    T3_wrapper_rcocy := EpsilonOmegaPhase(T3_OMEGA_RCOCY, T1_G, T1_M_RANK,
                                           T3_g1, T3_g2, T3_a, T3_b);
    if T3_backbone_phase = T3_wrapper_hom then
        T3_match_hom := T3_match_hom + 1;
    else
        Print("    [hom] mismatch: backbone = ", T3_backbone_phase,
              ", wrapper-hom = ", T3_wrapper_hom, "\n");
    fi;
    if T3_backbone_phase = T3_wrapper_rcocy then
        T3_match_rcocy := T3_match_rcocy + 1;
    else
        Print("    [rcocy] mismatch: backbone = ", T3_backbone_phase,
              ", wrapper-rcocy = ", T3_wrapper_rcocy, "\n");
    fi;
    if T3_wrapper_hom = T3_wrapper_rcocy then
        T3_match_eq := T3_match_eq + 1;
    else
        Print("    [hom vs rcocy] mismatch: hom = ", T3_wrapper_hom,
              ", rcocy = ", T3_wrapper_rcocy, "\n");
    fi;
od;;
TEPP_Assert(
    Concatenation("(3a) Wrapper (hom-coord) agrees with backbone on ",
                  String(T3_total), " Q_8 ω_2 tuples"),
    T3_match_hom = T3_total and T3_total > 0);
TEPP_Assert(
    Concatenation("(3b) Wrapper (R-coord) agrees with backbone on ",
                  String(T3_total), " Q_8 ω_2 tuples"),
    T3_match_rcocy = T3_total and T3_total > 0);
TEPP_Assert(
    Concatenation("(3c) Hom-coord and R-coord paths agree on ",
                  String(T3_total), " Q_8 ω_2 tuples"),
    T3_match_eq = T3_total and T3_total > 0);


# ============================================================
# (4) Cache reuse: second call should not rebuild Resolution.
# ============================================================
Print("\n[4] Cache reuse on repeated (G, omega_vec):\n");

# Inspect the cache directly: a second call with identical (G, omega_vec)
# must find a hit (i.e. the cache size does not grow).
EpsilonOmegaPhaseClearCache();;
T4_status0 := EpsilonOmegaPhaseCacheStatus();;
TEPP_Assert("(4a) cache empty after clear",
            Length(T4_status0) = 0);

T4_g := One(T1_G);;
T4_val := EpsilonOmegaPhase([0, 0, 0], T1_G, T1_M_RANK,
                             T4_g, T4_g, T4_g, T4_g);;
T4_status1 := EpsilonOmegaPhaseCacheStatus();;
TEPP_Assert("(4b) cache has one entry after first call",
            Length(T4_status1) = 1);

T4_val := EpsilonOmegaPhase([0, 0, 0], T1_G, T1_M_RANK,
                             T4_g, T4_g, T4_g, T4_g);;
T4_status2 := EpsilonOmegaPhaseCacheStatus();;
TEPP_Assert("(4c) cache still has one entry after second call",
            Length(T4_status2) = 1);

# Different omega_vec -> distinct cache entry.
T4_val := EpsilonOmegaPhase([0, 4, 0], T1_G, T1_M_RANK,
                             T4_g, T4_g, T4_g, T4_g);;
T4_status3 := EpsilonOmegaPhaseCacheStatus();;
TEPP_Assert("(4d) different omega_vec -> distinct cache entry",
            Length(T4_status3) = 2);


# ============================================================
# Summary.
# ============================================================
Print("\n=== test_epsilon_omega_phase.g summary ===\n");
Print("  Total assertions: ", TEPP_TOTAL, "\n");
Print("  Failures:         ", TEPP_FAILS, "\n");
if TEPP_FAILS > 0 then
    Error("test_epsilon_omega_phase.g: ", TEPP_FAILS, "/", TEPP_TOTAL,
          " assertions failed.");
fi;
Print("test_epsilon_omega_phase.g: ALL PASS (", TEPP_TOTAL, " assertions)\n");
