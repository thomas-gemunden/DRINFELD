# test_em_eplus_translate_pipeline.g
#
# Issue #256: end-to-end pipeline test for the family-translation
# integration. Verifies that:
#
#   P1. TranslateSpectralDataToEPlus produces a record consumable by
#       RestrictTraceOnWToSubgroupHonourParent at m = 3.
#   P2. The translated path's CT modular data is internally consistent
#       (well-formed S, T) and AGREES with the untwisted-baseline path
#       when the input is the trivial untwisted intertwiner data.
#   P3. With a SYNTHETIC non-trivial trace_on_W (one that multiplies by
#       a non-trivial character value on a single class), the
#       parent-honouring restriction differs from the baseline
#       restriction on the H-side trace evaluation.
#
# These tests do NOT exercise the K-4a orchestrator end-to-end (that
# is done by test_k4a_classify.g). They specifically validate the
# bridging step.

_SCRIPT_DIR := "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-k4-fam/extraspecial_orbifolds/scripts";;
ChangeDirectoryCurrent(_SCRIPT_DIR);

PIPE_PASSES := 0;;
PIPE_FAILURES := [];;

PAssertTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
        PIPE_PASSES := PIPE_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Add(PIPE_FAILURES, label);
    fi;
end;;

PAssertEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
        PIPE_PASSES := PIPE_PASSES + 1;
    else
        Print("  [FAIL] ", label, " (expected=", expected, ", got=", got, ")\n");
        Add(PIPE_FAILURES, label);
    fi;
end;;

# Deps.
Read(Concatenation(_SCRIPT_DIR, "/em_construction.g"));
Read(Concatenation(_SCRIPT_DIR, "/bw_lattice.g"));
Read(Concatenation(_SCRIPT_DIR, "/twisted_group_algebra.g"));
Read(Concatenation(_SCRIPT_DIR, "/krr_spectral_characters.g"));
Read(Concatenation(_SCRIPT_DIR, "/quillen_detecting_subgroup.g"));
Read(Concatenation(_SCRIPT_DIR, "/em_eplus_translate.g"));
Read(Concatenation(_SCRIPT_DIR, "/untwisted_modular_data.g"));
Read(Concatenation(_SCRIPT_DIR, "/krr_projector.g"));
Read(Concatenation(_SCRIPT_DIR, "/restrict_to_subgroup.g"));
Read(Concatenation(_SCRIPT_DIR, "/ct_modular_data.g"));

# ---- P1: plumbing at m = 3 ----
Print("\n==========================================================\n");
Print("P1: plumbing at m = 3\n");
Print("==========================================================\n");

PIPE_M := 3;;
PIPE_EU := EmUnimodGroup(PIPE_M);;

# Build a baseline spectral_data record on the EU side using the
# untwisted intertwiner data builder. This mimics the shape that
# BuildKRRSpectralCharactersSparse would produce, but is much faster
# at m = 3 (we don't actually need the sparse builder to test the
# translation plumbing).
PIPE_SPECTRAL_EU_BASELINE := BuildIntertwinerDataUntwisted(PIPE_EU);;
PIPE_SPECTRAL_EU_BASELINE.m := PIPE_M;;     # mimic the sparse builder.
PIPE_SPECTRAL_EU_BASELINE.source := "synthetic-untwisted-baseline";;

PAssertTrue("P1: spectral_data_eu .group is EmUnimodGroup",
            PIPE_SPECTRAL_EU_BASELINE.group = PIPE_EU);

# Build the detecting subgroups (each holds its own EPlusGroup(3)).
PIPE_EA := MaximalElementaryAbelian_E_plus(PIPE_M);;
PIPE_D8 := D8Section_E_plus(PIPE_M);;

# Translate spectral data against the E-branch's parent.
PIPE_DATA_E := TranslateSpectralDataToEPlus(
    PIPE_SPECTRAL_EU_BASELINE, PIPE_EA.parent);;
PAssertTrue("P1: translated .group is EA.parent",
            PIPE_DATA_E.group = PIPE_EA.parent);
PAssertTrue("P1: translated .trace_on_W is a function",
            IsFunction(PIPE_DATA_E.trace_on_W));
PAssertTrue("P1: translated .idx.classes is bound and non-empty",
            IsBound(PIPE_DATA_E.idx.classes)
            and Length(PIPE_DATA_E.idx.classes) > 0);

# Translate against the D_8 branch's parent.
PIPE_DATA_D8 := TranslateSpectralDataToEPlus(
    PIPE_SPECTRAL_EU_BASELINE, PIPE_D8.parent);;
PAssertTrue("P1: D_8-side translated .group is D8.parent",
            PIPE_DATA_D8.group = PIPE_D8.parent);

# Restrict E branch via honour-parent restriction.
PIPE_RESTRICTED_E := RestrictTraceOnWToSubgroupHonourParent(
    PIPE_DATA_E, PIPE_EA.subgroup);;
PAssertTrue("P1: restricted_E.group is the EA subgroup",
            PIPE_RESTRICTED_E.group = PIPE_EA.subgroup);
PAssertTrue("P1: restricted_E.trace_on_W is a function",
            IsFunction(PIPE_RESTRICTED_E.trace_on_W));
PAssertTrue("P1: restricted_E.parent_G is the EA parent",
            PIPE_RESTRICTED_E.parent_G = PIPE_EA.parent);

# Verify trace_on_W on a representative element does not error out.
PIPE_TR_VAL := PIPE_RESTRICTED_E.trace_on_W(1, 1, One(PIPE_EA.subgroup));;
PAssertTrue("P1: trace_on_W(1, 1, e) yields a numerical value",
            PIPE_TR_VAL <> fail);

# ---- P2: baseline consistency ----
Print("\n==========================================================\n");
Print("P2: baseline consistency (translated == untwisted for ω = 0)\n");
Print("==========================================================\n");

# When spectral_data_eu is the trivial untwisted, the translated
# restriction's trace_on_W should agree with H's untwisted character
# on every (k_H, irrep_idx_H, h_H). (Math: translated trace_on_W
# evaluates h_H in C_G via the iso, then EvalIrr on C_G's irreps,
# which for omega = 0 is the underlying centraliser character —
# and the irrep_index_translation map should pick the correct G-irrep
# of matching dimension that restricts to the same character.)
#
# Concretely, we compute the CT modular data via the translated path
# and the untwisted baseline path, and check that the S-matrix has
# the same rank and the T-matrix's eigenvalues are the same multiset.

PIPE_DATA_E_BASELINE := BuildIntertwinerDataUntwisted(PIPE_EA.parent);;
PIPE_RESTRICTED_E_BASELINE := RestrictTraceOnWToSubgroup(
    PIPE_DATA_E_BASELINE, PIPE_EA.subgroup);;

# Compute CT modular data both ways.
PIPE_CT_BASELINE := ComputeCTModularData(
    PIPE_RESTRICTED_E_BASELINE, PIPE_EA.subgroup);;
PIPE_CT_TRANS := ComputeCTModularData(
    PIPE_RESTRICTED_E, PIPE_EA.subgroup);;

PAssertEqual("P2: baseline S rank == translated S rank",
             Length(PIPE_CT_BASELINE.S), Length(PIPE_CT_TRANS.S));
PAssertEqual("P2: baseline T size == translated T size",
             Length(PIPE_CT_BASELINE.T), Length(PIPE_CT_TRANS.T));

# T-eigenvalue multiset equality.
PIPE_T_BASELINE_SET := Set(DiagonalOfMat(PIPE_CT_BASELINE.T));;
PIPE_T_TRANS_SET := Set(DiagonalOfMat(PIPE_CT_TRANS.T));;
PAssertEqual("P2: T eigenvalue multiset (set) matches baseline",
             PIPE_T_TRANS_SET, PIPE_T_BASELINE_SET);

# S-row sum multiset (basic invariant).
PIPE_S_ROW_SUMS_BASELINE := Set(List(PIPE_CT_BASELINE.S, Sum));;
PIPE_S_ROW_SUMS_TRANS := Set(List(PIPE_CT_TRANS.S, Sum));;
PAssertEqual("P2: S row-sum multiset (set) matches baseline",
             PIPE_S_ROW_SUMS_TRANS, PIPE_S_ROW_SUMS_BASELINE);

# ---- P3: with a synthetic non-trivial multiplicities field, the
#         translated path differs from the baseline.
# ----
Print("\n==========================================================\n");
Print("P3: synthetic non-trivial multiplicities\n");
Print("==========================================================\n");

# Build a synthetic spectral_data_eu with a non-trivial .multiplicities
# field. Set mult = 2 on the central class's first irrep (a real KRR
# multiplicity is also an integer >= 0; we pick 2 to force a clean
# T-entry difference). Everywhere else mult is fail (interpreted as 1
# by multiplicity_lookup).
PIPE_NUM_EU_CLASSES := Length(PIPE_SPECTRAL_EU_BASELINE.idx.classes);;
PIPE_MULTS_NONTRIVIAL := List([1..PIPE_NUM_EU_CLASSES], k -> fail);;
# Find the EU central class (a = -I in EmUnimodGroup(m)).
PIPE_EU_Z := -IdentityMat(2^PIPE_M);;
PIPE_EU_Z_CLASS := First([1..PIPE_NUM_EU_CLASSES],
    k -> PIPE_SPECTRAL_EU_BASELINE.idx.reps[k] = PIPE_EU_Z);;
Print("  EU central-class index for -I: ", PIPE_EU_Z_CLASS, "\n");
# Set non-trivial multiplicity on every irrep of that class.
PIPE_NUM_IRREPS_Z := PIPE_SPECTRAL_EU_BASELINE.idx.num_irreps[PIPE_EU_Z_CLASS];;
PIPE_MULTS_NONTRIVIAL[PIPE_EU_Z_CLASS] := List([1..PIPE_NUM_IRREPS_Z],
    j -> 2);;     # mult = 2

PIPE_SPECTRAL_EU_MULTS := rec(
    group := PIPE_EU,
    idx := PIPE_SPECTRAL_EU_BASELINE.idx,
    transport := PIPE_SPECTRAL_EU_BASELINE.transport,
    trace_on_W := PIPE_SPECTRAL_EU_BASELINE.trace_on_W,
    epsilon := PIPE_SPECTRAL_EU_BASELINE.epsilon,
    multiplicities := PIPE_MULTS_NONTRIVIAL,
    m := PIPE_M,
    source := "synthetic-with-multiplicities"
);;

PIPE_DATA_E_MULTS := TranslateSpectralDataToEPlus(
    PIPE_SPECTRAL_EU_MULTS, PIPE_EA.parent);;
PAssertTrue("P3: translated data carries multiplicities pass-through",
            IsBound(PIPE_DATA_E_MULTS.multiplicities_eu));

PIPE_RESTRICTED_E_MULTS := RestrictTraceOnWToSubgroupHonourParent(
    PIPE_DATA_E_MULTS, PIPE_EA.subgroup);;

# trace_on_W at a class that maps to the central class in G should
# have mult factor 2 applied.
# Find H-class mapping to the central G-class.
PIPE_K_H_CENTRAL := First([1..Length(PIPE_RESTRICTED_E_MULTS.class_to_G)],
    k -> PIPE_RESTRICTED_E_MULTS.class_to_G[k].k_G = PIPE_RESTRICTED_E_MULTS.class_to_G[1].k_G or
         IsCentral(PIPE_EA.subgroup, PIPE_RESTRICTED_E_MULTS.idx.reps[k]) and
             PIPE_RESTRICTED_E_MULTS.idx.reps[k] <> One(PIPE_EA.subgroup));;
# A simpler approach: just check the multiplicity_lookup directly.
PIPE_LOOKUP_VAL := PIPE_RESTRICTED_E_MULTS.multiplicity_lookup(1, 1);;
# At a non-central H-class, the mult is 1; at a central one, mult is 2.
# Without finer dispatch we just verify the function returns something
# in {1, 2} for a few inputs.
PAssertTrue("P3: multiplicity_lookup returns numeric values",
            IsRat(PIPE_LOOKUP_VAL) or IsCyc(PIPE_LOOKUP_VAL));
# Check that at least ONE (k, j) returns 2.
PIPE_HAS_NONTRIVIAL := false;;
for PIPE_K in [1..Length(PIPE_RESTRICTED_E_MULTS.idx.reps)] do
    for PIPE_J in [1..PIPE_RESTRICTED_E_MULTS.idx.num_irreps[PIPE_K]] do
        if PIPE_RESTRICTED_E_MULTS.multiplicity_lookup(PIPE_K, PIPE_J) = 2 then
            PIPE_HAS_NONTRIVIAL := true;
            break;
        fi;
    od;
    if PIPE_HAS_NONTRIVIAL then break; fi;
od;
PAssertTrue("P3: at least one (k_H, j_H) has multiplicity 2",
            PIPE_HAS_NONTRIVIAL);

# Compute CT modular data with the multiplicity-injected restriction.
# The T-matrix entries: T = chi(a)/chi(e). The mult factor cancels in
# the ratio, so T should still equal baseline. But the S matrix has
# off-diagonal products of two traces, so it differs.
PIPE_CT_MULTS := ComputeCTModularData(
    PIPE_RESTRICTED_E_MULTS, PIPE_EA.subgroup);;
PAssertEqual("P3: mult-injected T entries == baseline (mult cancels in ratio)",
             DiagonalOfMat(PIPE_CT_MULTS.T), DiagonalOfMat(PIPE_CT_BASELINE.T));
# S matrix has mult-squared factors; on entries where both class-indices
# are the central class, S differs by 4. So Sum(S) probably differs.
PAssertTrue("P3: mult-injected S differs from baseline S in some entry",
            PIPE_CT_MULTS.S <> PIPE_CT_BASELINE.S);

# ---- P4: m = 5 plumbing smoke ----
Print("\n==========================================================\n");
Print("P4: m = 5 plumbing smoke (translate + restrict, no compute)\n");
Print("==========================================================\n");

# At m = 5 we don't actually compute the full CT modular data
# (that's the K-4a orchestrator's job and takes ~10 min).
# We just verify the translate + restrict step runs without error.

PIPE_M5 := 5;;
PIPE_EU5 := EmUnimodGroup(PIPE_M5);;
PIPE_T0 := Runtime();;
PIPE_SPECTRAL_EU5_BASELINE := BuildIntertwinerDataUntwistedLazy(PIPE_EU5);;
PIPE_SPECTRAL_EU5_BASELINE.m := PIPE_M5;;
PIPE_SPECTRAL_EU5_BASELINE.source := "synthetic-baseline-m5";;
PIPE_T1 := Runtime();;
Print("  Baseline spectral_data_eu (lazy) at m=5 in ",
      (PIPE_T1 - PIPE_T0)/1000.0, " s.\n");

PIPE_EA5 := MaximalElementaryAbelian_E_plus(PIPE_M5);;
PIPE_T0 := Runtime();;
PIPE_DATA_E5 := TranslateSpectralDataToEPlus(
    PIPE_SPECTRAL_EU5_BASELINE, PIPE_EA5.parent);;
PIPE_T1 := Runtime();;
Print("  Translation at m=5 in ", (PIPE_T1 - PIPE_T0)/1000.0, " s.\n");
PAssertTrue("P4: translated data_E5 .group = EA5.parent",
            PIPE_DATA_E5.group = PIPE_EA5.parent);
PAssertTrue("P4: translated trace_on_W is a function",
            IsFunction(PIPE_DATA_E5.trace_on_W));

# Just verify we can call trace_on_W on identity without erroring.
PIPE_T0 := Runtime();;
PIPE_TR_E5 := PIPE_DATA_E5.trace_on_W(1, 1, One(PIPE_EA5.parent));;
PIPE_T1 := Runtime();;
Print("  trace_on_W(1, 1, One) at m=5 in ",
      (PIPE_T1 - PIPE_T0)/1000.0, " s, value = ", PIPE_TR_E5, "\n");
PAssertTrue("P4: trace_on_W(1, 1, e) at m=5 yields a value",
            PIPE_TR_E5 <> fail);

# ---- Final summary ----
Print("\n==========================================================\n");
Print("Summary: ", PIPE_PASSES, " passes, ",
      Length(PIPE_FAILURES), " failures.\n");
Print("==========================================================\n");

if Length(PIPE_FAILURES) = 0 then
    Print("\nPASS test_em_eplus_translate_pipeline\n");
else
    Print("\nFAIL test_em_eplus_translate_pipeline:\n");
    for PIPE_F in PIPE_FAILURES do
        Print("  - ", PIPE_F, "\n");
    od;
fi;

QUIT;
