# test_k4a_honour_parent_m3_nontrivial.g
#
# Synthetic m=3 K-4a-with-non-trivial-ω test for the normalization fix in
# `RestrictTraceOnWToSubgroupHonourParent` (#275 / approach A: mult is
# categorical labeling, not scalar weight in S/T).
#
# CONTEXT
# =======
# The K-4a anchor `tests/test_k4a_classify.g` runs the orchestrator at
# m=3 with ω = trivial (verdict "trivial", class_idx=1 on every branch).
# That test does NOT exercise `RestrictTraceOnWToSubgroupHonourParent`:
# the m=3 path in `k4a_classify.g` uses the non-honour
# `RestrictTraceOnWToSubgroup` variant since the orchestrator branches on
# `m >= 5` for the honour-parent path.
#
# The existing `tests/test_em_eplus_translate_pipeline.g` (P3) tests
# HonourParent at m=3 BUT only over the E-branch (abelian, classify
# only via is_coboundary), and only over untwisted+multiplicities
# injection. There is no test that feeds HonourParent a NON-TRIVIAL
# parent epsilon at m=3 and verifies the propagation through the
# D_8 / Q_8 classifiers.
#
# This test fills that gap. It runs four scenarios at m=3:
#
#   S1: mult-only injection on D_8 (regression).
#       Inject non-trivial multiplicities (mult=2) on the parent
#       central class. Restrict via HonourParent to D_8. Compute CT
#       modular data and classify. Expect class_idx = 1 (the
#       multiplicity is categorical labeling under the fix, so the
#       H-side CT data matches the untwisted D_8 baseline = class 1).
#       If this fails: the fix's normalization claim is wrong.
#
#   S2: mult-only injection on Q_8 (regression).
#       Same as S1 but on Q_8. Expect class_idx = 1.
#
#   S3: non-trivial epsilon injection on D_8 (positive twist propagation).
#       Inject a non-trivial epsilon callable on the parent
#       (epsilon = -1 on selected (a, b) pairs where a, b are in
#       the central H-class). Restrict via HonourParent to D_8.
#       Compute CT modular data and classify. Verify the resulting
#       S matrix DIFFERS from the untwisted D_8 baseline (twist
#       propagates through). Report class_idx (may be > 1 if the
#       injected ε happens to align with a stored cocycle class;
#       may be fail otherwise — both outcomes are informative).
#
#   S4: HonourParent untwisted invariance.
#       With NEITHER mult nor epsilon injected (i.e. plain untwisted
#       parent intertwiner_data), HonourParent restriction should
#       produce IDENTICAL CT modular data to the non-honour
#       RestrictTraceOnWToSubgroup variant. This is the m=3 anchor
#       compatibility check: it ensures HonourParent does not
#       silently corrupt the untwisted baseline.
#
# WHY APPROACH (combination of 2 and 3, not 1)
# =============================================
# Approach 1 (full KRR spectral data + e_i unit at m=3) would require
# running BuildKRRSpectralCharactersSparse(3), which is fast but the
# resulting data has only trivial multiplicities (since at m=3 Keller's
# α=0 holds and the central class's spectral characters reduce to the
# standard untwisted ones). So a "real" α at m=3 is not naturally
# available from the KRR side — it would need a custom-built twisted
# trace_on_W which is more work than the budget allows.
#
# Approach 2 (ground-truth round-trip from stored tables) requires
# constructing a forward-injected synthetic intertwiner_data on E_+(3)
# whose restriction to D_8 reproduces the stored Drinfeld-double
# modular data for a specific class k > 1. This is approach 2 in the
# task description. Under the corrected normalization, the H-side
# trace_on_W is `chi_l_H(h_H)` (the H-untwisted character) regardless
# of parent mult; so reproducing class k > 1 requires injecting
# **either** a twisted ε on the parent (S3 in this test) or a
# twisted trace_on_W on H (impractical without full projective
# character machinery at m=3, see `universal_coefficients.g`).
#
# This test takes the ε route: it injects a synthetic non-trivial ε on
# the parent and observes whether the resulting (S, T) on D_8 differs
# from the untwisted baseline. The ε is constructed to be a
# straightforward (not necessarily a cocycle representative of any
# specific class) phase function, so the resulting (S, T) is
# unpredictable in advance. The test asserts that
# (a) S differs from baseline (the fix's machinery propagates ε to
#     S correctly),
# (b) T is unchanged (T = chi(a)/chi(e) doesn't pick up ε in this
#     formula),
# (c) ClassifyOnD8 returns SOME answer (class_idx in {1..12} or fail).
# Whatever the result, this is one piece of evidence about the
# pipeline's behaviour at non-trivial-ω inputs.
#
# Run by absolute path:
#   gap -q -b /Users/.../tests/test_k4a_honour_parent_m3_nontrivial.g

# ---- Test bookkeeping --------------------------------------------------

HP_PASSES   := 0;;
HP_FAILURES := [];;

HPAssertEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
        HP_PASSES := HP_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Print("         expected: ", expected, "\n");
        Print("         got:      ", got, "\n");
        Add(HP_FAILURES, label);
    fi;
end;;

HPAssertTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
        HP_PASSES := HP_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Add(HP_FAILURES, label);
    fi;
end;;

# ---- Locate worktree / scripts ----------------------------------------

HP_SELF := INPUT_FILENAME();;
if HP_SELF = fail or HP_SELF = "stream" then
    Error("test_k4a_honour_parent_m3_nontrivial.g: ",
          "INPUT_FILENAME() unavailable; Read by absolute path.");
fi;
HP_SELFDIR := HP_SELF{
    [1..Length(HP_SELF)
       - Length("/test_k4a_honour_parent_m3_nontrivial.g")]};;
HP_SCRIPTSDIR := HP_SELFDIR{
    [1..Length(HP_SELFDIR) - Length("/tests")]};;
HP_WT_ROOT := HP_SCRIPTSDIR{
    [1..Length(HP_SCRIPTSDIR) - Length("/extraspecial_orbifolds/scripts")]};;

# Load src/modular_data.g (provides LoadModularData -- required by
# the d8/q8 classifiers).
Read(Concatenation(HP_WT_ROOT, "/src/modular_data.g"));
HPAssertTrue("LoadModularData bound (from src/modular_data.g)",
             IsBound(LoadModularData));

# Load deps in the same order as the K-4a orchestrator does, so we
# get the same code paths.
Read(Concatenation(HP_SCRIPTSDIR, "/untwisted_modular_data.g"));
Read(Concatenation(HP_SCRIPTSDIR, "/krr_projector.g"));
Read(Concatenation(HP_SCRIPTSDIR, "/joint_permutation_matcher.g"));
Read(Concatenation(HP_SCRIPTSDIR, "/restrict_to_subgroup.g"));
Read(Concatenation(HP_SCRIPTSDIR, "/ct_modular_data.g"));
Read(Concatenation(HP_SCRIPTSDIR, "/quillen_detecting_subgroup.g"));
Read(Concatenation(HP_SCRIPTSDIR, "/d8_classifier.g"));
Read(Concatenation(HP_SCRIPTSDIR, "/q8_classifier.g"));

HPAssertTrue("RestrictTraceOnWToSubgroupHonourParent bound",
             IsBound(RestrictTraceOnWToSubgroupHonourParent));
HPAssertTrue("ComputeCTModularData bound",
             IsBound(ComputeCTModularData));
HPAssertTrue("ClassifyOnD8 bound", IsBound(ClassifyOnD8));
HPAssertTrue("ClassifyOnQ8 bound", IsBound(ClassifyOnQ8));

# ---- Prepare Modular_Data symlink and chdir there ----------------------
# Same pattern as test_k4a_classify.g / test_d8_classifier.g.

HP_MD_ROOT := fail;;
for HP_CAND in
    [ Concatenation(HP_WT_ROOT, "/../modular_data"),
      "/Users/thomasgemunden/Projects/group_cohomology/modular_data" ] do
    if HP_MD_ROOT = fail
       and IsExistingFile(Concatenation(HP_CAND, "/8/3/1.txt")) then
        HP_MD_ROOT := HP_CAND;
    fi;
od;
if HP_MD_ROOT = fail then
    Error("test_k4a_honour_parent_m3_nontrivial.g: cannot locate ",
          "modular_data tree.");
fi;
Print("modular_data root: ", HP_MD_ROOT, "\n");

HP_LINKDIR := Concatenation(HP_SELFDIR, "/k4a/orchestrator");;
if not IsExistingFile(HP_LINKDIR) then
    Exec(Concatenation("mkdir -p '", HP_LINKDIR, "'"));
fi;
HP_LINKPATH := Concatenation(HP_LINKDIR, "/Modular_Data");;
if not IsExistingFile(HP_LINKPATH) then
    Exec(Concatenation("ln -s '", HP_MD_ROOT, "' '", HP_LINKPATH, "'"));
fi;
if not IsExistingFile(Concatenation(HP_LINKPATH, "/8/3/1.txt")) then
    Error("test_k4a_honour_parent_m3_nontrivial.g: Modular_Data symlink ",
          "at ", HP_LINKPATH, " does not resolve to a tree containing ",
          "8/3/1.txt.");
fi;
ChangeDirectoryCurrent(HP_LINKDIR);

# ---- Setup: E_+(3), D_8 section, Q_8 section --------------------------

Print("\n=================================================================\n");
Print("Setup: E_+(3), D_8 section, Q_8 section, parent intertwiner_data\n");
Print("=================================================================\n");

HP_T0 := Runtime();;
HP_M := 3;;
HP_D8 := D8Section_E_plus(HP_M);;
HP_Q8 := Q8Section_E_plus(HP_M);;
Print("  D_8 section parent: order = ", Order(HP_D8.parent),
      ", subgroup order = ", Order(HP_D8.subgroup), "\n");
Print("  Q_8 section parent: order = ", Order(HP_Q8.parent),
      ", subgroup order = ", Order(HP_Q8.subgroup), "\n");
HPAssertEqual("D_8 section has order 8",
              Order(HP_D8.subgroup), 8);
HPAssertEqual("Q_8 section has order 8",
              Order(HP_Q8.subgroup), 8);

# Build parent untwisted intertwiner_data on D_8.parent. We use this
# E_+(3) instance as G throughout: the D_8 section was constructed
# inside this same EPlusGroup instance, so element-membership tests
# pass.
HP_DATA_G_D8 := BuildIntertwinerDataUntwisted(HP_D8.parent);;
HP_DATA_G_Q8 := BuildIntertwinerDataUntwisted(HP_Q8.parent);;
HP_SETUP_DT := (Runtime() - HP_T0) / 1000.0;;
Print("  Setup (parent intertwiner_data x 2) wall: ",
      HP_SETUP_DT, " s\n");

# Build the BASELINE: untwisted-baseline restriction (non-honour
# variant), then CT data. This is the reference we compare against.
Print("\n  Building baseline CT data (untwisted, non-honour) on D_8...\n");
HP_T0 := Runtime();;
HP_BASELINE_RESTRICTED_D8 := RestrictTraceOnWToSubgroup(
    HP_DATA_G_D8, HP_D8.subgroup);;
HP_BASELINE_CT_D8 := ComputeCTModularData(
    HP_BASELINE_RESTRICTED_D8, HP_D8.subgroup);;
Print("    D_8 baseline CT rank: ", Length(HP_BASELINE_CT_D8.S),
      " (expected 22), wall: ",
      (Runtime() - HP_T0) / 1000.0, " s\n");
HPAssertEqual("D_8 baseline CT rank = 22",
              Length(HP_BASELINE_CT_D8.S), 22);

# Independent baseline classification: this should give class_idx=1 for
# untwisted D_8 (the K-4a anchor result).
Print("  Building baseline CT data (untwisted, non-honour) on Q_8...\n");
HP_T0 := Runtime();;
HP_BASELINE_RESTRICTED_Q8 := RestrictTraceOnWToSubgroup(
    HP_DATA_G_Q8, HP_Q8.subgroup);;
HP_BASELINE_CT_Q8 := ComputeCTModularData(
    HP_BASELINE_RESTRICTED_Q8, HP_Q8.subgroup);;
Print("    Q_8 baseline CT rank: ", Length(HP_BASELINE_CT_Q8.S),
      " (expected 22), wall: ",
      (Runtime() - HP_T0) / 1000.0, " s\n");
HPAssertEqual("Q_8 baseline CT rank = 22",
              Length(HP_BASELINE_CT_Q8.S), 22);

# Sanity baseline classifications.
HP_BASELINE_D8_CLASS := ClassifyOnD8(
    HP_BASELINE_CT_D8.S,
    DiagonalOfMat(HP_BASELINE_CT_D8.T));;
HP_BASELINE_Q8_CLASS := ClassifyOnQ8(
    HP_BASELINE_CT_Q8.S,
    DiagonalOfMat(HP_BASELINE_CT_Q8.T));;
Print("    D_8 baseline classification: class_idx = ",
      HP_BASELINE_D8_CLASS.class_idx, "\n");
Print("    Q_8 baseline classification: class_idx = ",
      HP_BASELINE_Q8_CLASS.class_idx, "\n");
HPAssertEqual("D_8 baseline classifies to class_idx = 1 (anchor sanity)",
              HP_BASELINE_D8_CLASS.class_idx, 1);
HPAssertEqual("Q_8 baseline classifies to class_idx = 1 (anchor sanity)",
              HP_BASELINE_Q8_CLASS.class_idx, 1);

# ---- S1: mult-only injection on D_8 (regression for #275) -------------

Print("\n=================================================================\n");
Print("S1: mult-only injection on D_8 (regression for #275)\n");
Print("=================================================================\n");

# Build a synthetic parent intertwiner_data with non-trivial multiplicities
# on the central class. Under the corrected normalisation, the
# multiplicity field is a diagnostic label and does NOT propagate into
# the H-side trace_on_W or epsilon. The H-side CT modular data should
# therefore equal the untwisted baseline -> class_idx = 1.
HP_NUM_CLASSES_G_D8 := Length(HP_DATA_G_D8.idx.classes);;
HP_MULTS_S1 := List([1..HP_NUM_CLASSES_G_D8], k -> fail);;
# Find the central class index in G (the unique non-identity central
# element of E_+(3) is z = gen[2m+1] in the EPlusGroup PC convention).
HP_Z_G_D8 := GeneratorsOfGroup(HP_D8.parent)[2*HP_M+1];;
Print("  Central element of E_+(", HP_M, ") (gen[", 2*HP_M+1, "]): ",
      HP_Z_G_D8, "\n");
HP_Z_CLASS_G_D8 := First([1..HP_NUM_CLASSES_G_D8],
    k -> HP_DATA_G_D8.idx.reps[k] = HP_Z_G_D8);;
if HP_Z_CLASS_G_D8 = fail then
    # Fall back to: the central element is in a singleton class, and is
    # not the identity. Find a class with one element that is non-identity.
    HP_Z_CLASS_G_D8 := First([1..HP_NUM_CLASSES_G_D8],
        k -> Size(HP_DATA_G_D8.idx.classes[k]) = 1
             and HP_DATA_G_D8.idx.reps[k] <> One(HP_D8.parent));;
fi;
Print("  Central-class index in G (E_+(3)): ", HP_Z_CLASS_G_D8, "\n");
HPAssertTrue("S1: central class found in G",
             HP_Z_CLASS_G_D8 <> fail);

HP_NUM_IRREPS_Z_G_D8 := HP_DATA_G_D8.idx.num_irreps[HP_Z_CLASS_G_D8];;
HP_MULTS_S1[HP_Z_CLASS_G_D8] := List([1..HP_NUM_IRREPS_Z_G_D8], j -> 2);;
Print("  Injecting mult = 2 on each of the ", HP_NUM_IRREPS_Z_G_D8,
      " irreps at the central class.\n");

# Build the synthetic parent record. Pass through everything from the
# untwisted baseline EXCEPT add the .multiplicities field.
HP_DATA_G_D8_S1 := rec(
    group        := HP_DATA_G_D8.group,
    idx          := HP_DATA_G_D8.idx,
    transport    := HP_DATA_G_D8.transport,
    trace_on_W   := HP_DATA_G_D8.trace_on_W,
    epsilon      := HP_DATA_G_D8.epsilon,
    multiplicities := HP_MULTS_S1,
    m            := HP_M,
    source       := "synthetic-mult-only-D8"
);;

Print("\n  Restricting to D_8 via HonourParent...\n");
HP_T0 := Runtime();;
HP_RESTRICTED_S1_D8 := RestrictTraceOnWToSubgroupHonourParent(
    HP_DATA_G_D8_S1, HP_D8.subgroup);;
HP_S1_RESTRICT_DT := (Runtime() - HP_T0) / 1000.0;;
Print("    HonourParent restriction wall: ", HP_S1_RESTRICT_DT, " s\n");

# Sanity-check the new multiplicity_lookup callable: with mult = 2
# injected on every irrep of the parent's central class, the lookup
# at some H-class mapping to the parent's central class should return
# a value that is NOT 1 (the trivial pass-through). The exact value
# is sum_{j_G} a_{j_H, j_G} * mult[k_G, j_G] = 2 * sum_{j_G} a_{j_H, j_G};
# this can be any positive even integer >= 2 depending on the
# restriction-decomposition row sums (typically num_irreps_G in the
# Frobenius-reciprocity sense).
HP_S1_NONTRIVIAL_LOOKUP := false;;
HP_S1_MAX_LOOKUP := 1;;
for HP_K in [1..Length(HP_RESTRICTED_S1_D8.idx.reps)] do
    for HP_J in [1..HP_RESTRICTED_S1_D8.idx.num_irreps[HP_K]] do
        HP_S1_LOOKUP_VAL := HP_RESTRICTED_S1_D8.multiplicity_lookup(HP_K, HP_J);
        if IsInt(HP_S1_LOOKUP_VAL) and HP_S1_LOOKUP_VAL > HP_S1_MAX_LOOKUP then
            HP_S1_MAX_LOOKUP := HP_S1_LOOKUP_VAL;
        fi;
        if HP_S1_LOOKUP_VAL <> 1 then
            HP_S1_NONTRIVIAL_LOOKUP := true;
        fi;
    od;
od;
Print("  S1: max multiplicity_lookup value across (k_H, j_H): ",
      HP_S1_MAX_LOOKUP, "\n");
HPAssertTrue(
    "S1: multiplicity_lookup returns at least one non-trivial value (!=1)",
    HP_S1_NONTRIVIAL_LOOKUP);

Print("\n  Computing CT modular data on D_8 with mult-injected restriction...\n");
HP_T0 := Runtime();;
HP_CT_S1_D8 := ComputeCTModularData(
    HP_RESTRICTED_S1_D8, HP_D8.subgroup);;
HP_S1_CT_DT := (Runtime() - HP_T0) / 1000.0;;
Print("    CT modular data wall: ", HP_S1_CT_DT, " s, rank = ",
      Length(HP_CT_S1_D8.S), "\n");

# Core assertion: with mult-only injection, the CT modular data must
# equal the untwisted baseline (since mult is categorical labeling under
# the fix). If this fails, the fix is wrong and mult-scaling has crept
# back in somewhere.
HPAssertEqual("S1: mult-injected D_8 S == baseline D_8 S",
              HP_CT_S1_D8.S, HP_BASELINE_CT_D8.S);
HPAssertEqual("S1: mult-injected D_8 T == baseline D_8 T",
              DiagonalOfMat(HP_CT_S1_D8.T),
              DiagonalOfMat(HP_BASELINE_CT_D8.T));

# Classifier verdict: also class_idx = 1.
HP_S1_CLASS := ClassifyOnD8(HP_CT_S1_D8.S, DiagonalOfMat(HP_CT_S1_D8.T));;
Print("    D_8 classification under mult-injection: class_idx = ",
      HP_S1_CLASS.class_idx, "\n");
HPAssertEqual("S1: mult-injected D_8 classifies to class_idx = 1",
              HP_S1_CLASS.class_idx, 1);

# ---- S2: mult-only injection on Q_8 (regression for #275) -------------

Print("\n=================================================================\n");
Print("S2: mult-only injection on Q_8 (regression for #275)\n");
Print("=================================================================\n");

HP_NUM_CLASSES_G_Q8 := Length(HP_DATA_G_Q8.idx.classes);;
HP_MULTS_S2 := List([1..HP_NUM_CLASSES_G_Q8], k -> fail);;
HP_Z_G_Q8 := GeneratorsOfGroup(HP_Q8.parent)[2*HP_M+1];;
HP_Z_CLASS_G_Q8 := First([1..HP_NUM_CLASSES_G_Q8],
    k -> HP_DATA_G_Q8.idx.reps[k] = HP_Z_G_Q8);;
if HP_Z_CLASS_G_Q8 = fail then
    HP_Z_CLASS_G_Q8 := First([1..HP_NUM_CLASSES_G_Q8],
        k -> Size(HP_DATA_G_Q8.idx.classes[k]) = 1
             and HP_DATA_G_Q8.idx.reps[k] <> One(HP_Q8.parent));;
fi;
HP_NUM_IRREPS_Z_G_Q8 := HP_DATA_G_Q8.idx.num_irreps[HP_Z_CLASS_G_Q8];;
HP_MULTS_S2[HP_Z_CLASS_G_Q8] := List([1..HP_NUM_IRREPS_Z_G_Q8], j -> 2);;

HP_DATA_G_Q8_S2 := rec(
    group        := HP_DATA_G_Q8.group,
    idx          := HP_DATA_G_Q8.idx,
    transport    := HP_DATA_G_Q8.transport,
    trace_on_W   := HP_DATA_G_Q8.trace_on_W,
    epsilon      := HP_DATA_G_Q8.epsilon,
    multiplicities := HP_MULTS_S2,
    m            := HP_M,
    source       := "synthetic-mult-only-Q8"
);;

HP_T0 := Runtime();;
HP_RESTRICTED_S2_Q8 := RestrictTraceOnWToSubgroupHonourParent(
    HP_DATA_G_Q8_S2, HP_Q8.subgroup);;
HP_CT_S2_Q8 := ComputeCTModularData(
    HP_RESTRICTED_S2_Q8, HP_Q8.subgroup);;
HP_S2_DT := (Runtime() - HP_T0) / 1000.0;;
Print("  S2: HonourParent + CT (Q_8) wall: ", HP_S2_DT, " s\n");

HPAssertEqual("S2: mult-injected Q_8 S == baseline Q_8 S",
              HP_CT_S2_Q8.S, HP_BASELINE_CT_Q8.S);
HPAssertEqual("S2: mult-injected Q_8 T == baseline Q_8 T",
              DiagonalOfMat(HP_CT_S2_Q8.T),
              DiagonalOfMat(HP_BASELINE_CT_Q8.T));
HP_S2_CLASS := ClassifyOnQ8(HP_CT_S2_Q8.S, DiagonalOfMat(HP_CT_S2_Q8.T));;
Print("  Q_8 classification under mult-injection: class_idx = ",
      HP_S2_CLASS.class_idx, "\n");
HPAssertEqual("S2: mult-injected Q_8 classifies to class_idx = 1",
              HP_S2_CLASS.class_idx, 1);

# ---- S3: non-trivial epsilon injection on D_8 (twist propagation) ----

Print("\n=================================================================\n");
Print("S3: non-trivial epsilon injection on D_8 (twist propagation)\n");
Print("=================================================================\n");

# Build a synthetic parent intertwiner_data with a non-trivial epsilon
# callable. Strategy: use a sign-based phase function whose value is
# -1 when both a and b are non-identity elements of the H-side D_8
# subgroup; else 1. This is a deliberate "hand-crafted" twist not
# claimed to be a true 3-cocycle representative; the goal is to verify
# that ε propagates through HonourParent -> _CTComputeSBlock and
# changes the resulting S.
#
# This is approach (3) in the task description (cocycle pullback,
# manual injection) restricted to the simplest possible non-trivial ε.

HP_DATA_G_D8_S3 := rec(
    group        := HP_DATA_G_D8.group,
    idx          := HP_DATA_G_D8.idx,
    transport    := HP_DATA_G_D8.transport,
    trace_on_W   := HP_DATA_G_D8.trace_on_W,
    # Custom epsilon: -1 when both a and b are NOT the identity AND
    # both lie in the D_8 subgroup AND both are NOT central. This is
    # very crude — most (a, b) pairs in C_G(g_i) x C_G(g_j) will not
    # satisfy this. Crucially: the new_epsilon in HonourParent calls
    # parent_data.epsilon(g1, g2, a, b) where (g1, g2) = (H-class reps),
    # (a, b) are in the same H-classes. We will route via the H-side
    # check, so ε will be non-trivial whenever both class reps and
    # both elements are in D_8.
    epsilon      := function(g1, g2, a, b)
        local id;
        id := One(HP_D8.parent);
        # Phase = -1 only on a very specific subset of (a, b) pairs to
        # actually flip some S entries.  We pick: a in D_8 \ {e},
        # b in D_8 \ {e}, a*b = b*a (which always holds in the CGR sum,
        # since the formula restricts to commuting pairs), and a^2 = e,
        # b^2 = e (the order-2 elements of D_8). This gives ε = -1 on
        # a non-empty set of (a, b) pairs.
        if a = id or b = id then
            return 1;
        fi;
        if not (a in HP_D8.subgroup) then return 1; fi;
        if not (b in HP_D8.subgroup) then return 1; fi;
        if Order(a) <> 2 then return 1; fi;
        if Order(b) <> 2 then return 1; fi;
        return -1;
    end,
    m            := HP_M,
    source       := "synthetic-epsilon-twist-D8"
);;

Print("  Injecting epsilon(g1, g2, a, b) = -1 when a, b in D_8, ",
      "Order(a) = Order(b) = 2, a, b != e\n");

HP_T0 := Runtime();;
HP_RESTRICTED_S3_D8 := RestrictTraceOnWToSubgroupHonourParent(
    HP_DATA_G_D8_S3, HP_D8.subgroup);;
HP_S3_RESTRICT_DT := (Runtime() - HP_T0) / 1000.0;;
Print("    HonourParent restriction (twisted ε) wall: ",
      HP_S3_RESTRICT_DT, " s\n");

# Verify the new_epsilon in the restricted record DOES return -1 for
# some valid input -- otherwise the ε propagation is itself broken.
HP_GENS_D8 := GeneratorsOfGroup(HP_D8.subgroup);;
HP_S3_ORDER2_ELTS := Filtered(AsList(HP_D8.subgroup),
                              g -> Order(g) = 2);;
Print("  Order-2 elements in D_8: ", Length(HP_S3_ORDER2_ELTS), "\n");
HP_S3_EPS_HAS_NEG := false;;
if Length(HP_S3_ORDER2_ELTS) >= 2 then
    HP_S3_A := HP_S3_ORDER2_ELTS[1];;
    HP_S3_B := HP_S3_ORDER2_ELTS[2];;
    if HP_S3_A * HP_S3_B = HP_S3_B * HP_S3_A then
        HP_S3_EPS_VAL := HP_RESTRICTED_S3_D8.epsilon(
            HP_S3_A, HP_S3_B, HP_S3_A, HP_S3_B);
        Print("  epsilon(a, b, a, b) for a, b commuting order-2: ",
              HP_S3_EPS_VAL, "\n");
        if HP_S3_EPS_VAL = -1 then
            HP_S3_EPS_HAS_NEG := true;
        fi;
    else
        # Fall back to a brute force search.
        for HP_S3_A in HP_S3_ORDER2_ELTS do
            for HP_S3_B in HP_S3_ORDER2_ELTS do
                if HP_S3_A <> HP_S3_B
                   and HP_S3_A * HP_S3_B = HP_S3_B * HP_S3_A then
                    HP_S3_EPS_VAL := HP_RESTRICTED_S3_D8.epsilon(
                        HP_S3_A, HP_S3_B, HP_S3_A, HP_S3_B);
                    if HP_S3_EPS_VAL = -1 then
                        HP_S3_EPS_HAS_NEG := true;
                        Print("  found a commuting (a, b) pair with eps = -1\n");
                        break;
                    fi;
                fi;
            od;
            if HP_S3_EPS_HAS_NEG then break; fi;
        od;
    fi;
fi;
HPAssertTrue(
    "S3: restricted epsilon returns -1 for at least one valid (a, b)",
    HP_S3_EPS_HAS_NEG);

Print("\n  Computing CT modular data on D_8 with epsilon-injected restriction...\n");
HP_T0 := Runtime();;
HP_CT_S3_D8 := ComputeCTModularData(
    HP_RESTRICTED_S3_D8, HP_D8.subgroup);;
HP_S3_CT_DT := (Runtime() - HP_T0) / 1000.0;;
Print("    CT modular data wall: ", HP_S3_CT_DT, " s, rank = ",
      Length(HP_CT_S3_D8.S), "\n");

# T-matrix: per CGR, T = chi(a)/chi(e) and does NOT see ε.
HPAssertEqual("S3: epsilon-injected D_8 T == baseline D_8 T (T independent of ε)",
              DiagonalOfMat(HP_CT_S3_D8.T),
              DiagonalOfMat(HP_BASELINE_CT_D8.T));

# S-matrix: the non-trivial ε MUST change at least one entry; else
# the twist did not propagate through HonourParent -> _CTComputeSBlock.
HPAssertTrue("S3: epsilon-injected D_8 S DIFFERS from baseline D_8 S",
             HP_CT_S3_D8.S <> HP_BASELINE_CT_D8.S);

# Count how many S entries differ.
HP_S3_DIFF_COUNT := 0;;
HP_S3_N := Length(HP_CT_S3_D8.S);;
for HP_I in [1..HP_S3_N] do
    for HP_J in [1..HP_S3_N] do
        if HP_CT_S3_D8.S[HP_I][HP_J] <> HP_BASELINE_CT_D8.S[HP_I][HP_J] then
            HP_S3_DIFF_COUNT := HP_S3_DIFF_COUNT + 1;
        fi;
    od;
od;
Print("  Number of differing S entries: ", HP_S3_DIFF_COUNT,
      " out of ", HP_S3_N * HP_S3_N, "\n");
HPAssertTrue("S3: at least 1 S entry differs from baseline",
             HP_S3_DIFF_COUNT >= 1);

# Classifier diagnostic: does the twisted result match any stored class?
HP_S3_CLASS := ClassifyOnD8(HP_CT_S3_D8.S, DiagonalOfMat(HP_CT_S3_D8.T));;
Print("  D_8 classification under epsilon-injection: class_idx = ",
      HP_S3_CLASS.class_idx,
      ", all_matches = ", HP_S3_CLASS.all_matches, "\n");
# We do not strongly assert class_idx > 1 — the hand-crafted ε may or
# may not align with a stored cocycle class. We assert only that the
# classifier returns SOMETHING valid (either a class in {1..12} or fail).
HPAssertTrue("S3: classifier returns a valid result (class_idx in {1..12} or fail)",
             HP_S3_CLASS.class_idx = fail
             or (IsInt(HP_S3_CLASS.class_idx)
                 and HP_S3_CLASS.class_idx in [1..12]));
# If we got class_idx > 1, log that as a notable positive result.
if HP_S3_CLASS.class_idx <> fail and HP_S3_CLASS.class_idx > 1 then
    Print("  NOTABLE: ε-injection produced a NON-TRIVIAL class match: ",
          HP_S3_CLASS.class_idx, "\n");
fi;

# ---- S4: HonourParent untwisted-invariance ----------------------------

Print("\n=================================================================\n");
Print("S4: HonourParent untwisted-invariance vs non-honour\n");
Print("=================================================================\n");

# With no mult and no twisted epsilon, HonourParent should match the
# non-honour RestrictTraceOnWToSubgroup variant exactly on CT data.
# This is the m=3 anchor compatibility check.

# Build a clean parent record without .multiplicities.
HP_DATA_G_D8_S4 := rec(
    group        := HP_DATA_G_D8.group,
    idx          := HP_DATA_G_D8.idx,
    transport    := HP_DATA_G_D8.transport,
    trace_on_W   := HP_DATA_G_D8.trace_on_W,
    epsilon      := HP_DATA_G_D8.epsilon,
    # NB: no multiplicities, no source/m. The HonourParent function
    # short-circuits to the baseline H character for has_mults = false.
    source       := "synthetic-untwisted-D8"
);;

HP_T0 := Runtime();;
HP_RESTRICTED_S4_D8 := RestrictTraceOnWToSubgroupHonourParent(
    HP_DATA_G_D8_S4, HP_D8.subgroup);;
HP_CT_S4_D8 := ComputeCTModularData(
    HP_RESTRICTED_S4_D8, HP_D8.subgroup);;
HP_S4_DT := (Runtime() - HP_T0) / 1000.0;;
Print("  S4: HonourParent + CT (D_8, untwisted) wall: ",
      HP_S4_DT, " s\n");

HPAssertEqual("S4: HonourParent (untwisted) D_8 S == non-honour D_8 S",
              HP_CT_S4_D8.S, HP_BASELINE_CT_D8.S);
HPAssertEqual("S4: HonourParent (untwisted) D_8 T == non-honour D_8 T",
              DiagonalOfMat(HP_CT_S4_D8.T),
              DiagonalOfMat(HP_BASELINE_CT_D8.T));

HP_S4_CLASS := ClassifyOnD8(HP_CT_S4_D8.S, DiagonalOfMat(HP_CT_S4_D8.T));;
HPAssertEqual("S4: HonourParent (untwisted) D_8 classifies to class_idx = 1",
              HP_S4_CLASS.class_idx, 1);

# ---- Final summary ----------------------------------------------------

Print("\n=================================================================\n");
Print("Summary: ", HP_PASSES, " passes, ",
      Length(HP_FAILURES), " failures.\n");
Print("=================================================================\n");

if Length(HP_FAILURES) = 0 then
    Print("\nPASS test_k4a_honour_parent_m3_nontrivial\n");
else
    Print("\nFAIL test_k4a_honour_parent_m3_nontrivial:\n");
    for HP_F in HP_FAILURES do
        Print("  - ", HP_F, "\n");
    od;
fi;

QUIT;
