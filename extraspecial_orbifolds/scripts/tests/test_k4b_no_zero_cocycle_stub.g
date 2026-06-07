# test_k4b_no_zero_cocycle_stub.g
#
# PR #485 regression test: K-4b architectural-correctness anchor.
#
# Three prior PRs (#475, #483, #484) introduced "fast paths" in
# k4a_classify.g that bypassed the actual α-twisted spectral
# restriction with stubs:
#
#   1. E-branch (PR #475/#483): injected
#         omega_cocycle := function(x, y, z) return 0; end
#         modulus := 1
#      onto the restricted record, causing
#      `ClassifyAbelianBranchFast` to compute q_ω = 0 and b_ω = 0
#      and report `is_coboundary = true` regardless of the actual
#      KRR α-cocycle.
#
#   2. D_8 branch (PR #484): at default opts replaced the restricted
#      spectral data with `ComputeUntwistedModularData(d8_rec.subgroup)`
#      — i.e., compared D_8's untwisted modular data against itself.
#      Always a trivial match.
#
#   3. Q_8 branch (PR #484): same pattern as D_8.
#
# All three made K-4b verdicts mathematically vacuous: the verdict
# became "0 is a coboundary" (a tautology) instead of "KRR α is a
# coboundary".
#
# PR #485 removed them. This test greps the k4a_classify.g source
# and FAILS if any of the offending patterns reappear. It does NOT
# exercise the K-4b pipeline (the heavy regression run is in
# test_k4a_classify.g / test_k4a_classify_m5_smoke.g); it is a static
# source-level guard against regression.
#
# Run from absolute path:
#   gap -q -b /Users/thomasgemunden/.../tests/test_k4b_no_zero_cocycle_stub.g

# ---- Test bookkeeping --------------------------------------------------

K4BNZS_PASSES   := 0;;
K4BNZS_FAILURES := [];;

K4BNZSAssertNotPresent := function(label, needle, haystack)
    local pos;
    pos := PositionSublist(haystack, needle);
    if pos = fail then
        Print("  [ok] ", label, "\n");
        K4BNZS_PASSES := K4BNZS_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Print("         found at character offset ", pos, "\n");
        Print("         needle: ", needle, "\n");
        Add(K4BNZS_FAILURES, label);
    fi;
end;;

K4BNZSAssertPresent := function(label, needle, haystack)
    local pos;
    pos := PositionSublist(haystack, needle);
    if pos <> fail then
        Print("  [ok] ", label, " (offset ", pos, ")\n");
        K4BNZS_PASSES := K4BNZS_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Print("         expected to find: ", needle, "\n");
        Add(K4BNZS_FAILURES, label);
    fi;
end;;

# ---- Locate k4a_classify.g --------------------------------------------

K4BNZS_SELF := INPUT_FILENAME();;
if K4BNZS_SELF = fail or K4BNZS_SELF = "stream" then
    Error("test_k4b_no_zero_cocycle_stub.g: INPUT_FILENAME() unavailable; ",
          "Read the file by its absolute path.");
fi;
K4BNZS_SELFDIR := K4BNZS_SELF{
    [1..Length(K4BNZS_SELF)
        - Length("/test_k4b_no_zero_cocycle_stub.g")]};;
K4BNZS_SCRIPTSDIR := K4BNZS_SELFDIR{
    [1..Length(K4BNZS_SELFDIR) - Length("/tests")]};;
K4BNZS_K4A_PATH := Concatenation(K4BNZS_SCRIPTSDIR, "/k4a_classify.g");;

Print("\n=================================================================\n");
Print("PR #485: K-4b zero-cocycle stub / skip-restriction guard\n");
Print("=================================================================\n");
Print("Source under test: ", K4BNZS_K4A_PATH, "\n\n");

if not IsExistingFile(K4BNZS_K4A_PATH) then
    Error("test_k4b_no_zero_cocycle_stub.g: k4a_classify.g not found at ",
          K4BNZS_K4A_PATH);
fi;

K4BNZS_SRC := StringFile(K4BNZS_K4A_PATH);;
Print("Loaded ", Length(K4BNZS_SRC),
      " bytes of k4a_classify.g source\n\n");

# ---- C1: zero-cocycle stub function literal is NOT present ------------
#
# The lambda literal previously injected at the E-branch was
#   omega_cocycle := function(x, y, z) return 0; end
# We test against the bare lambda body, which is the load-bearing
# signature. Allowed variants: PR #475's source spelled this as
#   `function(x, y, z) return 0; end` (5-token return-zero body).
#
# The token sequence `function(x, y, z) return 0` is the irreducible
# fingerprint: any future regression of the stub pattern must include
# it.

Print("C1: zero-cocycle stub function literal\n");
Print("-----------------------------------------------------------------\n");

K4BNZSAssertNotPresent(
    "no `function(x, y, z) return 0` literal anywhere",
    "function(x, y, z) return 0",
    K4BNZS_SRC);

# The companion `restricted_E.omega_cocycle :=` post-restriction
# injection (PR #475's slow-path side):
K4BNZSAssertNotPresent(
    "no `restricted_E.omega_cocycle :=` field assignment",
    "restricted_E.omega_cocycle :=",
    K4BNZS_SRC);

# The companion `restricted_E.modulus := 1` field assignment:
K4BNZSAssertNotPresent(
    "no `restricted_E.modulus := 1` field assignment",
    "restricted_E.modulus := 1",
    K4BNZS_SRC);

Print("\n");

# ---- C2: D_8 / Q_8 untwisted-override at dispatch is NOT present ------
#
# The pre-PR-#485 D_8 / Q_8 fast paths read
#   modular_ct_untwisted := ComputeUntwistedModularData(d8_rec.subgroup);
#   restricted_D8 := rec(modular_ct_override := rec(S := ..., T := ...));
# and analogously for q8_rec. ComputeUntwistedModularData is a
# legitimate function used elsewhere in K-4a (inside
# `_K4A_ClassifyAbelianBranch` to compute the reference H-untwisted
# data for the JointPermutationMatcher); we cannot blanket-ban it.
# What we ban is its specific dispatch-point usage on d8_rec.subgroup
# or q8_rec.subgroup at the orchestrator level (PR #484's shortcut).

Print("C2: D_8/Q_8 untwisted-override at dispatch\n");
Print("-----------------------------------------------------------------\n");

K4BNZSAssertNotPresent(
    "no `ComputeUntwistedModularData(d8_rec.subgroup)` at dispatch",
    "ComputeUntwistedModularData(d8_rec.subgroup)",
    K4BNZS_SRC);

K4BNZSAssertNotPresent(
    "no `ComputeUntwistedModularData(q8_rec.subgroup)` at dispatch",
    "ComputeUntwistedModularData(q8_rec.subgroup)",
    K4BNZS_SRC);

# The full skip-restriction rec(modular_ct_override := ...) shape is
# PR #484's footprint at the D_8 / Q_8 branches.
K4BNZSAssertNotPresent(
    "no `restricted_D8 := rec(` at all (skip-restriction shape)",
    "restricted_D8 := rec(",
    K4BNZS_SRC);

K4BNZSAssertNotPresent(
    "no `restricted_Q8 := rec(` at all (skip-restriction shape)",
    "restricted_Q8 := rec(",
    K4BNZS_SRC);

Print("\n");

# ---- C3: positive controls (the real spectral restriction IS used) ----
#
# Confirm the actual `RestrictTraceOnWToSubgroupHonourParent` call
# expressions remain at the E, D_8, and Q_8 dispatch points. We check
# for the call shape (function name + first arg) per branch.

Print("C3: spectral restriction IS present at all three branches\n");
Print("-----------------------------------------------------------------\n");

K4BNZSAssertPresent(
    "E-branch: RestrictTraceOnWToSubgroupHonourParent(<...>data_E, H_EA)",
    "RestrictTraceOnWToSubgroupHonourParent(",
    K4BNZS_SRC);

K4BNZSAssertPresent(
    "D_8-branch: ...(data_D8, d8_rec.subgroup) call site",
    "data_D8, d8_rec.subgroup",
    K4BNZS_SRC);

K4BNZSAssertPresent(
    "Q_8-branch: ...(data_Q8, q8_rec.subgroup) call site",
    "data_Q8, q8_rec.subgroup",
    K4BNZS_SRC);

Print("\n");

# ---- Summary ----------------------------------------------------------

Print("=================================================================\n");
Print("Summary: ", K4BNZS_PASSES, " passes / ",
      Length(K4BNZS_FAILURES), " failures\n");
Print("=================================================================\n");

if Length(K4BNZS_FAILURES) > 0 then
    Print("FAILED checks:\n");
    for K4BNZS_F in K4BNZS_FAILURES do
        Print("  - ", K4BNZS_F, "\n");
    od;
    Print("\nFAIL: PR #485 invariant violated. ",
          "Zero-cocycle stub or skip-restriction shortcut ",
          "has reappeared in k4a_classify.g.\n");
    Print("PR #485 removed three architectural shortcuts that made ",
          "K-4b verdicts mathematically vacuous. Reintroducing any ",
          "of them downscopes the K-4b claim from 'KRR alpha is a ",
          "coboundary' back to '0 is a coboundary' (a tautology).\n");
    QUIT_GAP(1);
else
    Print("PASS: no zero-cocycle stub / skip-restriction shortcut detected.\n");
fi;
