# Tests for D-VAN slack-trim (issue #313): _DETF_TrimmedFamily.
#
# Run from extraspecial_orbifolds/scripts/:
#   gap -q -b -c 'Read("tests/test_dvan_trimmed_family.g"); QUIT;'
#
# Acceptance anchors (from PR #310's research note,
# `extraspecial_orbifolds/docs/superpowers/research/2026-05-20-minimal-
# detecting-family.md`):
#
#   * m=2: greedy reproduces witness {EA_2, EA_3, EA_5} (one of the two
#     minimum size-3 EA witnesses), family_size = 5 = 3 EAs + D_8 + Q_8.
#     Brute-forced k_*(2) = 5 over all 63 size-0..6 EA subsets.
#
#   * m=3: greedy reproduces witness {EA_4, EA_6, EA_7, EA_11, EA_16,
#     EA_22} sorted, family_size = 8 = 6 EAs + D_8 + Q_8. Brute-forced
#     k_*(3) = 8 by ruling out all 174,437 size-0..5 EA subsets.
#
#   * m=5 (gated by TRIMMED_RUN_M5 := true): smoke test that
#     _DETF_TrimmedFamily(5) terminates with final_ker = 1 and
#     locally_tight = true. THIS PR's reference run with the
#     112-EA production family converged to 9 EAs + D_8 + Q_8 = 11
#     subgroups in ~19 min wall (cold). Wall is dominated by the
#     BuildRestrictionMatrices(5, "hap") build (~18 min for the HAP
#     resolution of E_+(5) + 114 EquivariantChainMap calls); the
#     greedy + SNF itself adds <1 min.
#
# The m=2 / m=3 anchors are bit-for-bit witness checks against PR #310's
# greedy algorithm. If the greedy tie-breaking changes (e.g., a
# different ordering of _DETF_AllMaxEAsIn outputs), update the
# expected witness lists below — but the FAMILY SIZE checks must stay
# (k_*(2) = 5 and k_*(3) = 8 are mathematical invariants, not
# implementation artefacts).

BreakOnError := false;;

Read("detecting_family_restriction.g");

Print("\n=== test_dvan_trimmed_family.g ===\n");

testFailures := [];;
If_ := function(c, a, b) if c then return a; else return b; fi; end;;
AssertOrLog := function(label, cond)
    Print("  ", label, ": ", If_(cond, "PASS", "FAIL"), "\n");
    if not cond then Add(testFailures, label); fi;
end;;

# ---------------------------------------------------------------------
# T1: Bindings and basic shape.
# ---------------------------------------------------------------------

Print("\n--- T1: bindings ---\n");
AssertOrLog("_DETF_TrimmedFamily is bound",
            IsBoundGlobal("_DETF_TrimmedFamily"));
AssertOrLog("_DETF_KernelOrderSNF is bound (internal helper)",
            IsBoundGlobal("_DETF_KernelOrderSNF"));

# ---------------------------------------------------------------------
# T2: Bad-input error paths.
# ---------------------------------------------------------------------

Print("\n--- T2: bad-input error paths ---\n");
err := CALL_WITH_CATCH(_DETF_TrimmedFamily, []);;
AssertOrLog("missing m errors", not err[1]);

err := CALL_WITH_CATCH(_DETF_TrimmedFamily, [0]);;
AssertOrLog("m = 0 errors", not err[1]);

err := CALL_WITH_CATCH(_DETF_TrimmedFamily, [7]);;
AssertOrLog("m = 7 errors (LHS path not implemented in this PR)",
            not err[1]);

err := CALL_WITH_CATCH(_DETF_TrimmedFamily,
                       [2, rec(source := "garbage")]);;
AssertOrLog("unknown source errors", not err[1]);

err := CALL_WITH_CATCH(_DETF_TrimmedFamily,
                       [2, rec(source := "quillen")]);;
AssertOrLog("source = quillen errors (Phase 2 gate, issue #136)",
            not err[1]);

# ---------------------------------------------------------------------
# T3: m=2 anchor — bit-for-bit PR #310 reproduction.
# ---------------------------------------------------------------------
#
# Expected (PR #310 §4.1.2 / §4.1.3): the greedy growth picks
# {EA_3, EA_2, EA_5} in order; sorted this is [2, 3, 5], one of the
# two minimum size-3 EA witnesses. Total family = 3 EAs + D_8 + Q_8 = 5.
#
# If the underlying _DETF_AllMaxEAsIn enumeration order changes (e.g.
# ConjugacyClassesSubgroups gives a different ordering at the GAP
# version we ship), the exact INDICES will shift but the COUNT must
# stay = 3 EAs. We assert both.

Print("\n--- T3: m=2 anchor (PR #310 witness {2, 3, 5}) ---\n");
t2_start := Runtime();;
r2 := _DETF_TrimmedFamily(2);;
t2_wall := Runtime() - t2_start;;
Print("  m=2 wall: ", t2_wall, " ms (cold)\n");

AssertOrLog("r2.m = 2", r2.m = 2);
AssertOrLog("r2.source = \"hap\"", r2.source = "hap");
AssertOrLog("r2.final_ker = 1 (joint restriction injective)",
            r2.final_ker = 1);
AssertOrLog("r2.include_D8 = true", r2.include_D8 = true);
AssertOrLog("r2.include_Q8 = true (Q_8 found at m=2)",
            r2.include_Q8 = true);
AssertOrLog("r2.ea_count = 3 (PR #310 minimum)",
            r2.ea_count = 3);
AssertOrLog("r2.family_size = 5 (= 3 EAs + D_8 + Q_8)",
            r2.family_size = 5);
AssertOrLog("r2.locally_tight = true (drop-one verification)",
            r2.locally_tight = true);
AssertOrLog("every drop_one_kers entry > 1 (no redundant EA)",
            ForAll(r2.drop_one_kers, k -> k > 1));
AssertOrLog("greedy_log has ea_count entries",
            Length(r2.greedy_log) = r2.ea_count);
AssertOrLog("greedy_log[end].ker = 1 (terminated at injectivity)",
            r2.greedy_log[r2.ea_count].ker = 1);

# Strong anchor: the sorted chosen indices match {2, 3, 5} bit-for-bit.
# This is the deterministic greedy-tie-breaking witness from PR #310.
# Both [1, 4, 6] and [2, 3, 5] are valid minimum size-3 EA witnesses
# (PR #310 §4.1.3); the greedy first-index tie-break picks the
# {2, 3, 5} branch.
AssertOrLog("r2 sorted chosen = [2, 3, 5] (PR #310 greedy witness)",
            r2.ea_indices_chosen_sorted = [2, 3, 5]);
AssertOrLog("r2 chosen (greedy order) = [3, 2, 5]",
            r2.ea_indices_chosen = [3, 2, 5]);

# ---------------------------------------------------------------------
# T4: m=3 anchor — bit-for-bit PR #310 reproduction.
# ---------------------------------------------------------------------
#
# Expected (PR #310 §4.2.2): greedy picks EA[4], EA[6], EA[11], EA[22],
# EA[7], EA[16] in that order with ker reduction sequence 4.3e9 →
# 3.4e7 → 2.6e5 → 4096 → 64 → 4 → 1. Sorted witness = [4, 6, 7, 11,
# 16, 22], total family = 6 EAs + D_8 + Q_8 = 8.
#
# Brute-forced minimum is exactly 6 EAs (PR #310 §6 over 174 437
# size-0..5 EA subsets).

Print("\n--- T4: m=3 anchor (PR #310 witness {4, 6, 7, 11, 16, 22}) ---\n");
t3_start := Runtime();;
r3 := _DETF_TrimmedFamily(3);;
t3_wall := Runtime() - t3_start;;
Print("  m=3 wall: ", t3_wall, " ms (cold)\n");

AssertOrLog("r3.m = 3", r3.m = 3);
AssertOrLog("r3.final_ker = 1 (joint restriction injective)",
            r3.final_ker = 1);
AssertOrLog("r3.include_Q8 = true", r3.include_Q8 = true);
AssertOrLog("r3.ea_count = 6 (PR #310 minimum)",
            r3.ea_count = 6);
AssertOrLog("r3.family_size = 8 (= 6 EAs + D_8 + Q_8)",
            r3.family_size = 8);
AssertOrLog("r3.locally_tight = true (drop-one verification)",
            r3.locally_tight = true);
AssertOrLog("every drop_one_kers entry > 1 (no redundant EA)",
            ForAll(r3.drop_one_kers, k -> k > 1));

# Strong anchor: the sorted chosen indices match {4, 6, 7, 11, 16, 22}
# bit-for-bit (PR #310 §4.2.2).
AssertOrLog("r3 sorted chosen = [4, 6, 7, 11, 16, 22] (PR #310)",
            r3.ea_indices_chosen_sorted = [4, 6, 7, 11, 16, 22]);
AssertOrLog("r3 chosen (greedy order) = [4, 6, 11, 22, 7, 16]",
            r3.ea_indices_chosen = [4, 6, 11, 22, 7, 16]);

# Anchor the greedy reduction sequence (PR #310 §4.2.2):
# 4.3e9 → 3.4e7 → 2.6e5 → 4096 → 64 → 4 → 1.
expected_kers := [33554432, 262144, 4096, 64, 4, 1];;
AssertOrLog("r3 greedy kernel sequence matches PR #310",
            List(r3.greedy_log, e -> e.ker) = expected_kers);

# ---------------------------------------------------------------------
# T5: caching cross-checks (second call hits BuildRestrictionMatrices
# cache, so wall should drop dramatically).
# ---------------------------------------------------------------------

Print("\n--- T5: caching (second call hits BuildRestrictionMatrices cache) ---\n");
t_warm := Runtime();;
r3_again := _DETF_TrimmedFamily(3);;
t_warm := Runtime() - t_warm;;
Print("  m=3 wall (warm cache): ", t_warm, " ms\n");
AssertOrLog("warm m=3 wall < 50% of cold m=3 wall",
            t_warm * 2 < t3_wall);
AssertOrLog("warm rec.data is the same reference as cold rec.data",
            IsIdenticalObj(r3.data, r3_again.data));
AssertOrLog("warm and cold give the same chosen indices",
            r3.ea_indices_chosen = r3_again.ea_indices_chosen);

# ---------------------------------------------------------------------
# T6: m=5 smoke (gated, slow: ~10-15 min cold).
# ---------------------------------------------------------------------
#
# Skipped by default to keep this test under 1 minute. To exercise:
#
#   gap -q -b -c 'TRIMMED_RUN_M5 := true; Read("tests/test_dvan_trimmed_family.g"); QUIT;'
#
# Or override via the env-passed global TRIMMED_RUN_M5 from a wrapper.

run_m5 := IsBoundGlobal("TRIMMED_RUN_M5")
          and ValueGlobal("TRIMMED_RUN_M5") = true;;

if run_m5 then
    Print("\n--- T6: m=5 smoke (TRIMMED_RUN_M5 set; ~15-20 min cold) ---\n");
    t5_start := Runtime();;
    r5 := _DETF_TrimmedFamily(5);;
    t5_wall := Runtime() - t5_start;;
    Print("  m=5 wall: ", t5_wall, " ms\n");
    Print("  m=5 chosen (greedy order) = ", r5.ea_indices_chosen, "\n");
    Print("  m=5 chosen sorted         = ", r5.ea_indices_chosen_sorted, "\n");
    Print("  m=5 ea_count              = ", r5.ea_count, "\n");
    Print("  m=5 family_size           = ", r5.family_size, "\n");
    Print("  m=5 final_ker             = ", r5.final_ker, "\n");
    Print("  m=5 locally_tight         = ", r5.locally_tight, "\n");
    Print("  m=5 drop_one_kers         = ", r5.drop_one_kers, "\n");
    AssertOrLog("m=5 final_ker = 1 (injective)", r5.final_ker = 1);
    AssertOrLog("m=5 locally_tight = true", r5.locally_tight = true);
    AssertOrLog("m=5 ea_count in plausible range [3, 30]",
                r5.ea_count >= 3 and r5.ea_count <= 30);
    AssertOrLog("m=5 ea_count < 112 (production family size)",
                r5.ea_count < 112);
    AssertOrLog("m=5 every drop_one_kers entry > 1 (no redundant EA)",
                ForAll(r5.drop_one_kers, k -> k > 1));
    # Greedy-determinism anchor for THIS PR's reference run. With the
    # current _DETF_AllMaxEAsIn ordering for m=5 (32 axis-aligned +
    # 80 pair-swap = 112 EAs) and the deterministic first-index
    # tie-break, the greedy converges to:
    #   chosen (greedy order) = [33, 48, 76, 89, 88, 54, 109, 57, 70]
    #   chosen sorted = [33, 48, 54, 57, 70, 76, 88, 89, 109]
    #   ker reduction: 1.74e41 -> 5.19e33 -> 6.19e26 -> 7.38e19 ->
    #                  3.52e13 -> 6.71e7 -> 1024 -> 8 -> 1
    #   drop_one_kers = [128, 1024, 64, 4096, 256, 32, 128, 32, 8]
    # If `_DETF_AllMaxEAsIn`'s ordering ever changes (e.g. a switch
    # to full Witt enumeration at m=5, or a PC-generator convention
    # swap), update these anchors. The MATHEMATICAL invariant is the
    # existence of a small locally-tight family; the SPECIFIC indices
    # are implementation-dependent.
    AssertOrLog("m=5 ea_count = 9 (THIS PR's reference witness)",
                r5.ea_count = 9);
    AssertOrLog("m=5 sorted chosen = [33, 48, 54, 57, 70, 76, 88, 89, 109]",
                r5.ea_indices_chosen_sorted
                    = [33, 48, 54, 57, 70, 76, 88, 89, 109]);
else
    Print("\n--- T6: m=5 smoke SKIPPED (set TRIMMED_RUN_M5 := true to run) ---\n");
fi;

# ---------------------------------------------------------------------
# Summary.
# ---------------------------------------------------------------------

if IsEmpty(testFailures) then
    Print("\n=== test_dvan_trimmed_family: PASS ===\n");
else
    Print("\n=== test_dvan_trimmed_family: FAIL (",
          Length(testFailures), ") ===\n");
    for f in testFailures do Print("  - ", f, "\n"); od;
fi;
