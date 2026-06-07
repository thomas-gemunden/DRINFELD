# test_ct_modular_data_abelian_closed_form.g
#
# PR #492: tests for the abelian-H closed-form specialization of
# `ComputeCTModularData(intertwiner_data, H)`.
#
# The closed-form for abelian H replaces the generic O(|H|^4) S-block loop
# with an O(|H|^2) (q, b) -> (S, T) factored modular-data build via PR
# #487's `ComputeAbelianModularDataFactored`. At H = (Z/2)^8 (m=7 max EA),
# the generic loop is ~10 h per EA × 8 EAs = ~80 h; the closed-form is
# minutes per EA.
#
# Test cases:
#
#   T1: V_4 = (Z/2)^2 — entry-by-entry parity vs the generic
#       `ComputeCTModularData` output (under the EvalIrr / ε ≡ 1 baseline
#       intertwiner_data from `BuildIntertwinerDataUntwisted`). The closed-
#       form must produce a factored record whose `T_vec` and `S_at`
#       reproduce the same modular data, up to a row/column permutation
#       discoverable by `JointPermutationMatcher`. (Permutation only — the
#       closed-form indexes simples in PR #487 order; the generic loop
#       indexes in BuildSimpleIndex/Irr(H) order.)
#
#   T2: (Z/2)^3 — same anchor at the next k. Tractable for both paths
#       (generic: |H|^4 = 4096 entries, fast).
#
#   T3: (Z/2)^4 — same anchor. Generic: |H|^4 = 65536, still fast.
#
#   T4: ClassifyEAFromModularData consumption parity at (Z/2)^k k ∈ {2, 3, 4}.
#       Both paths' outputs must yield the same `is_trivial` verdict when
#       routed through `ClassifyEAFromModularData(H, S, T)`. For untwisted
#       (ε ≡ 1) input both should report is_trivial = true.
#
#   T5: H = Z/4 — non-elementary-abelian abelian. Confirms the closed-form
#       handles general abelian H (not just (Z/2)^k).
#
#   T6: H = (Z/2)^5 — feasibility anchor for the m=5 EA scale (|H|^4 ~ 1M).
#       This is the scale where the generic loop is still tractable but
#       the closed-form should clearly win. Gated on env var
#       CT_ABELIAN_CF_RUN_5=1.
#
#   T7: H = (Z/2)^6 — feasibility anchor for the m=5 max-EA scale (|H|^4
#       = 16.8M; generic ~130 s). Verify the closed-form wall is sub-second.
#       Gated on env var CT_ABELIAN_CF_RUN_6=1.
#
#   T8: H = (Z/2)^8 — feasibility anchor for the m=7 max-EA scale (|H|^4 =
#       4.3B; generic infeasible). Verify the closed-form completes in
#       under 5 min. Gated on env var CT_ABELIAN_CF_RUN_8=1.
#
# Run from absolute path:
#   gap -q -b /Users/thomasgemunden/.../tests/test_ct_modular_data_abelian_closed_form.g

# ---- Test bookkeeping --------------------------------------------------

CTABELIAN_PASSES   := 0;;
CTABELIAN_FAILURES := [];;

CTAbelianAssertEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
        CTABELIAN_PASSES := CTABELIAN_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Print("         expected: ", expected, "\n");
        Print("         got:      ", got, "\n");
        Add(CTABELIAN_FAILURES, label);
    fi;
end;;

CTAbelianAssertTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
        CTABELIAN_PASSES := CTABELIAN_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Add(CTABELIAN_FAILURES, label);
    fi;
end;;

# ---- Locate worktree, scripts, sibling files ---------------------------

CTAB_SELF := INPUT_FILENAME();;
if CTAB_SELF = fail or CTAB_SELF = "stream" then
    Error("test_ct_modular_data_abelian_closed_form.g: ",
          "INPUT_FILENAME() unavailable; ",
          "Read the file by its absolute path.");
fi;
CTAB_SELFDIR := CTAB_SELF{
    [1..Length(CTAB_SELF) - Length(
        "/test_ct_modular_data_abelian_closed_form.g")]};;
CTAB_SCRIPTSDIR := CTAB_SELFDIR{
    [1..Length(CTAB_SELFDIR) - Length("/tests")]};;

# Load order:
# 1. untwisted_modular_data.g
# 2. krr_projector.g (BuildIntertwinerDataUntwisted)
# 3. joint_permutation_matcher.g
# 4. abelian_modular_data_closed_form.g (the closed-form (q,b) -> (S,T))
# 5. ct_modular_data.g (under test — the new abelian dispatch)
# 6. ea_modular_data_classifier.g (downstream consumer)

Read(Concatenation(CTAB_SCRIPTSDIR, "/untwisted_modular_data.g"));
CTAbelianAssertTrue("BuildSimpleIndex bound",
                    IsBound(BuildSimpleIndex));
CTAbelianAssertTrue("ComputeUntwistedModularData bound",
                    IsBound(ComputeUntwistedModularData));

Read(Concatenation(CTAB_SCRIPTSDIR, "/krr_projector.g"));
CTAbelianAssertTrue("BuildIntertwinerDataUntwisted bound",
                    IsBound(BuildIntertwinerDataUntwisted));

Read(Concatenation(CTAB_SCRIPTSDIR, "/joint_permutation_matcher.g"));
CTAbelianAssertTrue("JointPermutationMatcher bound",
                    IsBound(JointPermutationMatcher));

# abelian_modular_data_closed_form.g is auto-loaded by
# untwisted_modular_data.g (see the header guard there). It also calls
# DeclareGlobalFunction(...) at load, so a second Read would error
# "must be unbound" — skip the duplicate Read here.
CTAbelianAssertTrue("ComputeAbelianModularDataFactored bound",
                    IsBound(ComputeAbelianModularDataFactored));

Read(Concatenation(CTAB_SCRIPTSDIR, "/ct_modular_data.g"));
CTAbelianAssertTrue("ComputeCTModularData bound",
                    IsBound(ComputeCTModularData));

Read(Concatenation(CTAB_SCRIPTSDIR, "/ea_modular_data_classifier.g"));
CTAbelianAssertTrue("ClassifyEAFromModularData bound",
                    IsBound(ClassifyEAFromModularData));

# ---- Helper: factored-record S to full matrix --------------------------
# For comparing the closed-form (factored) output to the generic
# (full-matrix) output via JointPermutationMatcher, we materialise the
# full S from the factored record. Only used in the test driver — never
# in production at |H| >= 128.

_CTAB_FactoredToFullS := function(fac)
    local n, m, total, S, i, j;
    n := fac.n;
    m := n;  # |Hat(H)| = |H| for abelian H
    total := n * m;
    S := List([1..total], i -> List([1..total], j -> 0));
    for i in [1..total] do
        for j in [1..total] do
            S[i][j] := fac.S_at(i, j);
        od;
    od;
    return S;
end;;


# =======================================================================
# T1: H = (Z/2)^2 — parity vs ComputeUntwistedModularData
# =======================================================================
# After PR #492, ComputeCTModularData(V_4, ...) dispatches to the abelian
# closed-form (factored record). To verify correctness we cross-check
# against `ComputeUntwistedModularData(V_4)` which is the ground-truth
# closed-form full (S, T) for abelian H (it uses the same PR #487 closed
# form internally, returning a full matrix at this scale). Both must
# describe the same MTC, witnessed by JointPermutationMatcher.

Print("\n=== T1: H = (Z/2)^2 closed-form parity ===\n");

CTAB_V4 := SmallGroup(4, 2);;
CTAB_DATA_V4 := BuildIntertwinerDataUntwisted(CTAB_V4);;

# Ground-truth path: ComputeUntwistedModularData(V_4) — closed-form full
# (S, T) via PR #487.
CTAB_T_GT_V4 := Runtime();;
CTAB_OUT_GT_V4 := ComputeUntwistedModularData(CTAB_V4);;
CTAB_T_GT_V4_WALL := (Runtime() - CTAB_T_GT_V4) / 1000.;;
Print("  ComputeUntwistedModularData(V_4) wall: ",
      CTAB_T_GT_V4_WALL, " s\n");
CTAbelianAssertTrue("V_4: ground-truth S is 16x16",
                    Length(CTAB_OUT_GT_V4.S) = 16
                    and Length(CTAB_OUT_GT_V4.S[1]) = 16);

# New dispatch path: ComputeCTModularData(BuildIntertwinerDataUntwisted(V_4), V_4)
# fires the abelian closed-form (factored record).
CTAB_T_CF_V4 := Runtime();;
CTAB_OUT_CF_V4 := ComputeCTModularData(CTAB_DATA_V4, CTAB_V4);;
CTAB_T_CF_V4_WALL := (Runtime() - CTAB_T_CF_V4) / 1000.;;
Print("  ComputeCTModularData(V_4) [dispatch] wall: ",
      CTAB_T_CF_V4_WALL, " s\n");
CTAbelianAssertTrue("V_4: dispatched output is factored",
                    IsBound(CTAB_OUT_CF_V4.is_factored)
                    and CTAB_OUT_CF_V4.is_factored = true);

# Materialize closed-form S from factored record.
CTAB_S_CF_V4 := _CTAB_FactoredToFullS(CTAB_OUT_CF_V4);;
CTAB_T_CF_V4_VEC := CTAB_OUT_CF_V4.T_vec;;
CTAbelianAssertTrue("V_4: closed-form rank = 16",
                    Length(CTAB_S_CF_V4) = 16
                    and Length(CTAB_T_CF_V4_VEC) = 16);

# Cross-check via JointPermutationMatcher.
CTAB_M_V4 := JointPermutationMatcher(
    CTAB_OUT_GT_V4.S, CTAB_OUT_GT_V4.T,
    CTAB_S_CF_V4, CTAB_T_CF_V4_VEC);;
Print("  V_4 matcher: ok = ", CTAB_M_V4.ok, "\n");
if not CTAB_M_V4.ok and IsBound(CTAB_M_V4.reason) then
    Print("    reason: ", CTAB_M_V4.reason, "\n");
fi;
CTAbelianAssertTrue(
    "V_4: closed-form (S, T) matches ComputeUntwistedModularData",
    CTAB_M_V4.ok);

# Convenience alias for downstream tests that refer to "OUT_GEN".
CTAB_OUT_GEN_V4 := CTAB_OUT_GT_V4;;
CTAB_FAC_V4 := CTAB_OUT_CF_V4;;


# =======================================================================
# T2: H = (Z/2)^3 — parity vs ComputeUntwistedModularData
# =======================================================================

Print("\n=== T2: H = (Z/2)^3 closed-form parity ===\n");
CTAB_V8 := ElementaryAbelianGroup(8);;
CTAB_DATA_V8 := BuildIntertwinerDataUntwisted(CTAB_V8);;

CTAB_T_GT_V8 := Runtime();;
CTAB_OUT_GT_V8 := ComputeUntwistedModularData(CTAB_V8);;
CTAB_T_GT_V8_WALL := (Runtime() - CTAB_T_GT_V8) / 1000.;;
Print("  ComputeUntwistedModularData(V_8) wall: ",
      CTAB_T_GT_V8_WALL, " s\n");

CTAB_T_CF_V8 := Runtime();;
CTAB_OUT_CF_V8 := ComputeCTModularData(CTAB_DATA_V8, CTAB_V8);;
CTAB_T_CF_V8_WALL := (Runtime() - CTAB_T_CF_V8) / 1000.;;
Print("  ComputeCTModularData(V_8) [dispatch] wall: ",
      CTAB_T_CF_V8_WALL, " s\n");
CTAbelianAssertTrue("V_8: dispatched output is factored",
                    IsBound(CTAB_OUT_CF_V8.is_factored)
                    and CTAB_OUT_CF_V8.is_factored = true);

CTAB_S_CF_V8 := _CTAB_FactoredToFullS(CTAB_OUT_CF_V8);;
CTAB_T_CF_V8_VEC := CTAB_OUT_CF_V8.T_vec;;
CTAB_M_V8 := JointPermutationMatcher(
    CTAB_OUT_GT_V8.S, CTAB_OUT_GT_V8.T,
    CTAB_S_CF_V8, CTAB_T_CF_V8_VEC);;
Print("  V_8 matcher: ok = ", CTAB_M_V8.ok, "\n");
CTAbelianAssertTrue(
    "V_8: closed-form (S, T) matches ComputeUntwistedModularData",
    CTAB_M_V8.ok);

CTAB_FAC_V8 := CTAB_OUT_CF_V8;;


# =======================================================================
# T3: H = (Z/2)^4 — parity vs ComputeUntwistedModularData
# =======================================================================

Print("\n=== T3: H = (Z/2)^4 closed-form parity ===\n");
CTAB_V16 := ElementaryAbelianGroup(16);;
CTAB_DATA_V16 := BuildIntertwinerDataUntwisted(CTAB_V16);;

CTAB_T_GT_V16 := Runtime();;
CTAB_OUT_GT_V16 := ComputeUntwistedModularData(CTAB_V16);;
CTAB_T_GT_V16_WALL := (Runtime() - CTAB_T_GT_V16) / 1000.;;
Print("  ComputeUntwistedModularData(V_16) wall: ",
      CTAB_T_GT_V16_WALL, " s\n");

CTAB_T_CF_V16 := Runtime();;
CTAB_OUT_CF_V16 := ComputeCTModularData(CTAB_DATA_V16, CTAB_V16);;
CTAB_T_CF_V16_WALL := (Runtime() - CTAB_T_CF_V16) / 1000.;;
Print("  ComputeCTModularData(V_16) [dispatch] wall: ",
      CTAB_T_CF_V16_WALL, " s\n");
CTAbelianAssertTrue("V_16: dispatched output is factored",
                    IsBound(CTAB_OUT_CF_V16.is_factored)
                    and CTAB_OUT_CF_V16.is_factored = true);

CTAB_S_CF_V16 := _CTAB_FactoredToFullS(CTAB_OUT_CF_V16);;
CTAB_T_CF_V16_VEC := CTAB_OUT_CF_V16.T_vec;;
CTAB_M_V16 := JointPermutationMatcher(
    CTAB_OUT_GT_V16.S, CTAB_OUT_GT_V16.T,
    CTAB_S_CF_V16, CTAB_T_CF_V16_VEC);;
Print("  V_16 matcher: ok = ", CTAB_M_V16.ok, "\n");
CTAbelianAssertTrue(
    "V_16: closed-form (S, T) matches ComputeUntwistedModularData",
    CTAB_M_V16.ok);


# =======================================================================
# T4: ClassifyEAFromModularData consumption parity
# =======================================================================
# Both the legacy full-(S, T) and the new closed-form factored record
# must produce the same `is_trivial` verdict when fed into the EA
# classifier. For untwisted (ε ≡ 1, χ = EvalIrr) baseline both must
# report is_trivial = true.

Print("\n=== T4: ClassifyEAFromModularData consumption parity ===\n");

# Legacy path: full-(S, T) from ComputeUntwistedModularData(V_4).
CTAB_VERDICT_GT_V4 := ClassifyEAFromModularData(
    CTAB_V4, CTAB_OUT_GT_V4.S, CTAB_OUT_GT_V4.T);;
Print("  V_4 full-(S, T) verdict: is_trivial = ",
      CTAB_VERDICT_GT_V4.is_trivial,
      ", method = ", CTAB_VERDICT_GT_V4.method, "\n");
CTAbelianAssertTrue("V_4: full-(S,T) verdict is_trivial = true",
                    CTAB_VERDICT_GT_V4.is_trivial = true);

# Factored path: dispatched output from ComputeCTModularData(V_4).
CTAB_VERDICT_CF_V4 := ClassifyEAFromModularData(
    CTAB_V4, CTAB_FAC_V4, CTAB_FAC_V4.T_vec);;
Print("  V_4 factored verdict: is_trivial = ",
      CTAB_VERDICT_CF_V4.is_trivial,
      ", method = ", CTAB_VERDICT_CF_V4.method, "\n");
CTAbelianAssertTrue("V_4: factored verdict is_trivial = true",
                    CTAB_VERDICT_CF_V4.is_trivial = true);
CTAbelianAssertTrue("V_4: factored method = qb_extraction",
                    CTAB_VERDICT_CF_V4.method = "qb_extraction");

# (Z/2)^3 case: factored path.
CTAB_VERDICT_CF_V8 := ClassifyEAFromModularData(
    CTAB_V8, CTAB_FAC_V8, CTAB_FAC_V8.T_vec);;
Print("  V_8 factored verdict: is_trivial = ",
      CTAB_VERDICT_CF_V8.is_trivial, "\n");
CTAbelianAssertTrue("V_8: factored verdict is_trivial = true",
                    CTAB_VERDICT_CF_V8.is_trivial = true);


# =======================================================================
# T5: H = Z/4 — non-elementary-abelian abelian (sanity check)
# =======================================================================

Print("\n=== T5: H = Z/4 closed-form parity ===\n");
CTAB_Z4 := SmallGroup(4, 1);;
CTAB_DATA_Z4 := BuildIntertwinerDataUntwisted(CTAB_Z4);;

CTAB_T_GT_Z4 := Runtime();;
CTAB_OUT_GT_Z4 := ComputeUntwistedModularData(CTAB_Z4);;
CTAB_T_GT_Z4_WALL := (Runtime() - CTAB_T_GT_Z4) / 1000.;;
Print("  ComputeUntwistedModularData(Z/4) wall: ",
      CTAB_T_GT_Z4_WALL, " s\n");

CTAB_T_CF_Z4 := Runtime();;
CTAB_OUT_CF_Z4 := ComputeCTModularData(CTAB_DATA_Z4, CTAB_Z4);;
CTAB_T_CF_Z4_WALL := (Runtime() - CTAB_T_CF_Z4) / 1000.;;
Print("  ComputeCTModularData(Z/4) [dispatch] wall: ",
      CTAB_T_CF_Z4_WALL, " s\n");
CTAbelianAssertTrue("Z/4: dispatched output is factored",
                    IsBound(CTAB_OUT_CF_Z4.is_factored)
                    and CTAB_OUT_CF_Z4.is_factored = true);

CTAB_S_CF_Z4 := _CTAB_FactoredToFullS(CTAB_OUT_CF_Z4);;
CTAB_T_CF_Z4_VEC := CTAB_OUT_CF_Z4.T_vec;;
CTAB_M_Z4 := JointPermutationMatcher(
    CTAB_OUT_GT_Z4.S, CTAB_OUT_GT_Z4.T,
    CTAB_S_CF_Z4, CTAB_T_CF_Z4_VEC);;
Print("  Z/4 matcher: ok = ", CTAB_M_Z4.ok, "\n");
CTAbelianAssertTrue(
    "Z/4: closed-form (S, T) matches ComputeUntwistedModularData",
    CTAB_M_Z4.ok);


# =======================================================================
# T6: Non-abelian H falls through to generic loop (regression guard)
# =======================================================================
# The dispatch must not engage for non-abelian H. Verify with H = Q_8:
# ComputeCTModularData(Q_8, ...) must return the legacy full-(S, T)
# shape (rec.S, rec.T), NOT a factored record.

Print("\n=== T6: Non-abelian H falls through to generic loop ===\n");
CTAB_Q8 := SmallGroup(8, 4);;
CTAB_DATA_Q8 := BuildIntertwinerDataUntwisted(CTAB_Q8);;
CTAB_OUT_Q8 := ComputeCTModularData(CTAB_DATA_Q8, CTAB_Q8);;

CTAbelianAssertTrue("Q_8: ComputeCTModularData returns full-(S, T) shape",
                    IsBound(CTAB_OUT_Q8.S)
                    and not IsBound(CTAB_OUT_Q8.is_factored));
CTAbelianAssertTrue("Q_8: S is 22x22 (= |Z(Vec_{Q_8})|)",
                    Length(CTAB_OUT_Q8.S) = 22
                    and Length(CTAB_OUT_Q8.S[1]) = 22);


# =======================================================================
# T7: H = (Z/2)^5 — m=5 EA scale (gated)
# =======================================================================

CTAB_RUN_5 := fail;;
if IsBound(GAPInfo) and IsBound(GAPInfo.SystemEnvironment) then
    if IsBound(GAPInfo.SystemEnvironment.CT_ABELIAN_CF_RUN_5) then
        CTAB_RUN_5 := GAPInfo.SystemEnvironment.CT_ABELIAN_CF_RUN_5;
    fi;
fi;

if CTAB_RUN_5 = "1" then
    Print("\n=== T7: H = (Z/2)^5 closed-form feasibility ===\n");
    CTAB_V32 := ElementaryAbelianGroup(32);;
    CTAB_DATA_V32 := BuildIntertwinerDataUntwisted(CTAB_V32);;

    CTAB_T_DISP_V32 := Runtime();;
    CTAB_OUT_DISP_V32 := ComputeCTModularData(CTAB_DATA_V32, CTAB_V32);;
    CTAB_T_DISP_V32_WALL := (Runtime() - CTAB_T_DISP_V32) / 1000.;;
    Print("  dispatched ComputeCTModularData(V_32) wall: ",
          CTAB_T_DISP_V32_WALL, " s\n");

    CTAbelianAssertTrue("V_32: dispatched output is factored",
                        IsBound(CTAB_OUT_DISP_V32.is_factored)
                        and CTAB_OUT_DISP_V32.is_factored = true);
    CTAbelianAssertTrue("V_32: dispatched wall < 30 s",
                        CTAB_T_DISP_V32_WALL < 30.0);
else
    Print("\n=== T7: V_32 feasibility (skipped; set CT_ABELIAN_CF_RUN_5=1) ===\n");
fi;


# =======================================================================
# T8: H = (Z/2)^6 — m=5 max-EA scale (gated)
# =======================================================================

CTAB_RUN_6 := fail;;
if IsBound(GAPInfo) and IsBound(GAPInfo.SystemEnvironment) then
    if IsBound(GAPInfo.SystemEnvironment.CT_ABELIAN_CF_RUN_6) then
        CTAB_RUN_6 := GAPInfo.SystemEnvironment.CT_ABELIAN_CF_RUN_6;
    fi;
fi;

if CTAB_RUN_6 = "1" then
    Print("\n=== T8: H = (Z/2)^6 closed-form feasibility (m=5 EA scale) ===\n");
    CTAB_V64 := ElementaryAbelianGroup(64);;
    CTAB_DATA_V64 := BuildIntertwinerDataUntwisted(CTAB_V64);;

    CTAB_T_DISP_V64 := Runtime();;
    CTAB_OUT_DISP_V64 := ComputeCTModularData(CTAB_DATA_V64, CTAB_V64);;
    CTAB_T_DISP_V64_WALL := (Runtime() - CTAB_T_DISP_V64) / 1000.;;
    Print("  dispatched ComputeCTModularData(V_64) wall: ",
          CTAB_T_DISP_V64_WALL, " s\n");

    CTAbelianAssertTrue("V_64: dispatched output is factored",
                        IsBound(CTAB_OUT_DISP_V64.is_factored)
                        and CTAB_OUT_DISP_V64.is_factored = true);
    CTAbelianAssertTrue("V_64: dispatched wall < 60 s",
                        CTAB_T_DISP_V64_WALL < 60.0);
else
    Print("\n=== T8: V_64 feasibility (skipped; set CT_ABELIAN_CF_RUN_6=1) ===\n");
fi;


# =======================================================================
# T9: H = (Z/2)^8 — m=7 max-EA scale (gated)
# =======================================================================

CTAB_RUN_8 := fail;;
if IsBound(GAPInfo) and IsBound(GAPInfo.SystemEnvironment) then
    if IsBound(GAPInfo.SystemEnvironment.CT_ABELIAN_CF_RUN_8) then
        CTAB_RUN_8 := GAPInfo.SystemEnvironment.CT_ABELIAN_CF_RUN_8;
    fi;
fi;

if CTAB_RUN_8 = "1" then
    Print("\n=== T9: H = (Z/2)^8 closed-form feasibility (m=7 EA scale) ===\n");
    CTAB_V256 := ElementaryAbelianGroup(256);;
    CTAB_DATA_V256 := BuildIntertwinerDataUntwisted(CTAB_V256);;

    CTAB_T_DISP_V256 := Runtime();;
    CTAB_OUT_DISP_V256 := ComputeCTModularData(CTAB_DATA_V256, CTAB_V256);;
    CTAB_T_DISP_V256_WALL := (Runtime() - CTAB_T_DISP_V256) / 1000.;;
    Print("  dispatched ComputeCTModularData(V_256) wall: ",
          CTAB_T_DISP_V256_WALL, " s\n");

    CTAbelianAssertTrue("V_256: dispatched output is factored",
                        IsBound(CTAB_OUT_DISP_V256.is_factored)
                        and CTAB_OUT_DISP_V256.is_factored = true);
    CTAbelianAssertTrue("V_256: dispatched wall < 300 s (5 min budget)",
                        CTAB_T_DISP_V256_WALL < 300.0);
else
    Print("\n=== T9: V_256 feasibility (skipped; set CT_ABELIAN_CF_RUN_8=1) ===\n");
fi;


# ---- Final summary -----------------------------------------------------

Print("\n=== Final summary ===\n");
Print("  passes:   ", CTABELIAN_PASSES, "\n");
Print("  failures: ", Length(CTABELIAN_FAILURES), "\n");
if Length(CTABELIAN_FAILURES) = 0 then
    Print("\ntest_ct_modular_data_abelian_closed_form: PASS\n");
else
    Print("\ntest_ct_modular_data_abelian_closed_form: FAIL (",
          Length(CTABELIAN_FAILURES), "):\n");
    for CTAB_F in CTABELIAN_FAILURES do
        Print("  - ", CTAB_F, "\n");
    od;
fi;

QUIT;
