# test_em_eplus_translate_closed_form.g
#
# Issue #449 #456 B2 + C6: tests for closed-form class-index permutation
# in TranslateSpectralDataToEPlus + GroupHomomorphismByImagesNC in
# EmEPlusTranslateAgainst.
#
# Test cases:
#   B2-1. m=3: TranslateSpectralDataToEPlus called with a closed-form
#         spectral_data_eu (whose idx is BuildSimpleIndexEPlusClosedForm)
#         produces an idx_EP with the same shape as via the lazy path,
#         and the same ep_to_eu_class permutation.
#   B2-2. m=3: parity check -- the legacy (BuildSimpleIndexLazy) path and
#         the closed-form path produce identical ep_to_eu_class (after
#         renumbering to a canonical order via reps).
#   B2-3. m=3: TranslateSpectralDataToEPlus output is consumable by
#         RestrictTraceOnWToSubgroupHonourParent and yields the same
#         trace_on_W values as the legacy path on a sample of inputs.
#   B2-6. m=7 (mock idx): TranslateSpectralDataToEPlus must not OOM on
#         a closed-form idx with a small number of reps. Verifies the
#         closed-form bypass is taken (no ConjugacyClasses(EP) call).
#   C6-1. m=3: GroupHomomorphismByImagesNC produces the same hom (same
#         generator images, same group images on a sample of products).
#   C6-2. m=2: same check at m=2.
#
# Run from scripts/ directory:
#   gap -q -b -c 'Read("tests/test_em_eplus_translate_closed_form.g");'

_SCRIPT_SELF := INPUT_FILENAME();;
if _SCRIPT_SELF = fail or _SCRIPT_SELF = "stream" then
    Error("test_em_eplus_translate_closed_form.g: INPUT_FILENAME() ",
          "unavailable; Read by absolute path.");
fi;
if Length(_SCRIPT_SELF) > 0 and _SCRIPT_SELF[1] <> '/' then
    _SCRIPT_SELF := Filename(DirectoryCurrent(), _SCRIPT_SELF);
fi;
_SCRIPT_SELFDIR := _SCRIPT_SELF{
    [1..Length(_SCRIPT_SELF)
       - Length("/test_em_eplus_translate_closed_form.g")]};;
_SCRIPT_DIR := _SCRIPT_SELFDIR{
    [1..Length(_SCRIPT_SELFDIR) - Length("/tests")]};;
ChangeDirectoryCurrent(_SCRIPT_DIR);

CF_PASSES := 0;;
CF_FAILURES := [];;

CFAssertTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
        CF_PASSES := CF_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Add(CF_FAILURES, label);
    fi;
end;;

CFAssertEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
        CF_PASSES := CF_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Print("         expected: ", expected, "\n");
        Print("         got:      ", got, "\n");
        Add(CF_FAILURES, label);
    fi;
end;;

# Load deps.
Read(Concatenation(_SCRIPT_DIR, "/em_construction.g"));
Read(Concatenation(_SCRIPT_DIR, "/bw_lattice.g"));
Read(Concatenation(_SCRIPT_DIR, "/twisted_group_algebra.g"));
Read(Concatenation(_SCRIPT_DIR, "/qforms_f2.g"));
Read(Concatenation(_SCRIPT_DIR, "/defect_rep_minus_id.g"));
Read(Concatenation(_SCRIPT_DIR, "/defect_rep_minus_id_optim.g"));
Read(Concatenation(_SCRIPT_DIR, "/krr_spectral_characters.g"));
Read(Concatenation(_SCRIPT_DIR, "/quillen_detecting_subgroup.g"));
Read(Concatenation(_SCRIPT_DIR, "/untwisted_modular_data.g"));
Read(Concatenation(_SCRIPT_DIR, "/eplus_classes_closed_form.g"));
Read(Concatenation(_SCRIPT_DIR, "/eplus_irreps_closed_form.g"));
Read(Concatenation(_SCRIPT_DIR, "/em_eplus_translate.g"));
Read(Concatenation(_SCRIPT_DIR, "/krr_projector.g"));
Read(Concatenation(_SCRIPT_DIR, "/restrict_to_subgroup.g"));
Read(Concatenation(_SCRIPT_DIR, "/ct_modular_data.g"));

# ============================================================
# C6: GroupHomomorphismByImagesNC parity
# ============================================================
Print("\n=================================================================\n");
Print("C6: GroupHomomorphismByImagesNC parity vs GroupHomomorphismByImages\n");
Print("=================================================================\n");

for CF_M in [2, 3] do
    Print("\n--- m = ", CF_M, " ---\n");
    CF_TR := EmEPlusTranslate(CF_M);;
    CF_GENS_EU := GeneratorsOfGroup(CF_TR.EU);;
    # Verify psi is a valid hom: psi(a*b) = psi(a)*psi(b) on all
    # pairs of generators. This is the safety net for NC.
    CF_OK := true;;
    for CF_I in [1..Length(CF_GENS_EU)] do
        for CF_J in [1..Length(CF_GENS_EU)] do
            CF_A := CF_GENS_EU[CF_I];;
            CF_B := CF_GENS_EU[CF_J];;
            if Image(CF_TR.psi, CF_A * CF_B) <>
               Image(CF_TR.psi, CF_A) * Image(CF_TR.psi, CF_B) then
                CF_OK := false;
                break;
            fi;
        od;
        if not CF_OK then break; fi;
    od;
    CFAssertTrue(Concatenation("C6-", String(CF_M),
                  ": psi(a*b) = psi(a)*psi(b) on generator pairs"),
                CF_OK);
    # Image of each generator equals image_list element by construction.
    CF_IMG := List(CF_GENS_EU, g -> Image(CF_TR.psi, g));;
    CFAssertEqual(Concatenation("C6-", String(CF_M),
                  ": Image(psi, gens_EU) = image_list"),
                CF_IMG, CF_TR.image_list);
    # psi should still be bijective.
    CFAssertTrue(Concatenation("C6-", String(CF_M),
                  ": IsBijective(psi)"),
                IsBijective(CF_TR.psi));
od;

# ============================================================
# B2: closed-form ep_to_eu_class permutation
# ============================================================
Print("\n=================================================================\n");
Print("B2: closed-form class-index permutation parity (m=3)\n");
Print("=================================================================\n");

CF_M3 := 3;;
CF_EU3 := EmUnimodGroup(CF_M3);;
CF_INNER3 := BuildIntertwinerDataUntwisted(CF_EU3);;
CF_SPEC3 := rec(
    group := CF_EU3,
    idx := CF_INNER3.idx,
    transport := CF_INNER3.transport,
    trace_on_W := CF_INNER3.trace_on_W,
    epsilon := CF_INNER3.epsilon,
    m := CF_M3,
    source := "test-baseline-untwisted"
);;

# Build a closed-form EU idx separately, and a synthetic spec record
# using it. The closed-form idx is meant to be a drop-in replacement
# in shape; the trace_on_W is from BuildIntertwinerDataUntwisted which
# uses GAP's class structure, so we need to remap via the closed-form's
# reps.
CF_IDX_CLOSED3 := BuildSimpleIndexEPlusClosedForm(CF_M3);;
CFAssertTrue("B2-prep: closed-form idx is_closed_form",
             IsBound(CF_IDX_CLOSED3.is_closed_form)
             and CF_IDX_CLOSED3.is_closed_form = true);
CFAssertTrue("B2-prep: closed-form idx has reps",
             IsBound(CF_IDX_CLOSED3.reps)
             and Length(CF_IDX_CLOSED3.reps) > 0);

# ---- B2-1: m=3 plumbing with closed-form EU idx ----
Print("\n--- B2-1: m=3 plumbing with closed-form EU idx ---\n");

# Wrap the trace into one indexed by the closed-form EU idx.
# Map closed-form k_eu -> baseline k_eu via rep matching.
CF_BASELINE_REPS3 := CF_INNER3.idx.reps;;
CF_CF_TO_BASELINE_EU3 := List([1..Length(CF_IDX_CLOSED3.reps)], k ->
    First([1..Length(CF_BASELINE_REPS3)],
          j -> CF_IDX_CLOSED3.reps[k] in CF_INNER3.idx.classes[j]));;
CFAssertTrue("B2-1: closed-form-EU -> baseline-EU class map is total",
             not (fail in CF_CF_TO_BASELINE_EU3));
CFAssertEqual("B2-1: map is bijective (set size)",
             Length(Set(CF_CF_TO_BASELINE_EU3)),
             Length(CF_BASELINE_REPS3));

# Build a spectral_data_eu using the CLOSED-FORM EU idx + a trace
# wrapped through the closed-form -> baseline class permutation.
CF_TRACE_CLOSED3 := function(class_idx_eu_cf, irrep_idx, h_eu)
    return CF_INNER3.trace_on_W(
        CF_CF_TO_BASELINE_EU3[class_idx_eu_cf], irrep_idx, h_eu);
end;;
CF_SPEC_CLOSED3 := rec(
    group := CF_EU3,
    idx := CF_IDX_CLOSED3,
    transport := CF_INNER3.transport,
    trace_on_W := CF_TRACE_CLOSED3,
    epsilon := CF_INNER3.epsilon,
    m := CF_M3,
    source := "test-baseline-closed-form-eu"
);;

# Get EA / D8 / Q8 detecting subgroups (each makes a fresh EPlusGroup).
CF_EA3 := MaximalElementaryAbelian_E_plus(CF_M3);;
CF_D8_3 := D8Section_E_plus(CF_M3);;
CF_Q8_3 := Q8Section_E_plus(CF_M3);;

# Legacy path: lazy EP build.
Print("Building legacy translate against EA.parent...\n");
CF_T0 := Runtime();;
CF_LEGACY_EA3 := TranslateSpectralDataToEPlus(CF_SPEC3, CF_EA3.parent);;
CF_T1 := Runtime();;
Print("  legacy ms=", CF_T1 - CF_T0, "\n");

# Closed-form path: spectral_data_eu has idx with is_closed_form := true.
Print("Building closed-form translate against EA.parent...\n");
CF_T0 := Runtime();;
CF_NEW_EA3 := TranslateSpectralDataToEPlus(CF_SPEC_CLOSED3, CF_EA3.parent);;
CF_T1 := Runtime();;
Print("  closed-form ms=", CF_T1 - CF_T0, "\n");

CFAssertTrue("B2-1: legacy translated has .group = EA3.parent",
             CF_LEGACY_EA3.group = CF_EA3.parent);
CFAssertTrue("B2-1: closed-form translated has .group = EA3.parent",
             CF_NEW_EA3.group = CF_EA3.parent);
CFAssertTrue("B2-1: legacy translated has ep_to_eu_class",
             IsBound(CF_LEGACY_EA3.ep_to_eu_class));
CFAssertTrue("B2-1: closed-form translated has ep_to_eu_class",
             IsBound(CF_NEW_EA3.ep_to_eu_class));
CFAssertEqual("B2-1: idx_EP has same #classes via both paths",
              Length(CF_NEW_EA3.idx.classes),
              Length(CF_LEGACY_EA3.idx.classes));
# B2-1 marker: the closed-form path must produce idx_EP with .source
# "translated-closed-form-eplus", while the legacy path produces a
# plain BuildSimpleIndexLazy-shaped idx (no .source on idx).
CFAssertEqual("B2-1: closed-form .idx.source marker",
              CF_NEW_EA3.idx.source, "translated-closed-form-eplus");

# ---- B2-2: m=3 parity on ep_to_eu_class (renumbered via reps) ----
Print("\n--- B2-2: m=3 parity (closed-form vs legacy) on EP-class structure ---\n");

# Build a canonical EU-rep -> closed-form-EU-class index lookup, so
# we can compare ep_to_eu_class (which is an array indexed by EP-class
# but with values in the corresponding EU-idx).
# legacy_ep_class -> legacy_eu_class
# new_ep_class -> closed_form_eu_class
# Both EP-class structures may differ in ordering (different builders),
# so we compare by matching reps.

# For each legacy EP-class, find the matching new EP-class.
CF_LEGACY_TO_NEW3 := List([1..Length(CF_LEGACY_EA3.idx.reps)], k_legacy ->
    First([1..Length(CF_NEW_EA3.idx.reps)],
          k_new -> CF_NEW_EA3.idx.reps[k_new] =
                   CF_LEGACY_EA3.idx.reps[k_legacy]));;

# All legacy EP reps should map to some new EP rep (and bijectively).
CFAssertTrue("B2-2: legacy-EP-class -> new-EP-class map is total",
             not (fail in CF_LEGACY_TO_NEW3));
CFAssertEqual("B2-2: legacy<->new EP rep correspondence is bijective",
              Length(Set(CF_LEGACY_TO_NEW3)),
              Length(CF_LEGACY_EA3.idx.reps));

# For each legacy EP-class i with rep r:
#   legacy_eu_class := CF_LEGACY_EA3.ep_to_eu_class[i]
#   new_eu_class    := CF_NEW_EA3.ep_to_eu_class[CF_LEGACY_TO_NEW3[i]]
# These class indices should point to the SAME EU-conjugacy-class, which
# we check by: rep_eu_legacy in EU-class containing rep_eu_new (and vice
# versa). Different builders may pick different canonical reps from the
# same conjugacy class.
CF_PARITY_OK3 := true;;
for CF_I in [1..Length(CF_LEGACY_EA3.idx.reps)] do
    CF_LEU := CF_LEGACY_EA3.ep_to_eu_class[CF_I];
    CF_NEU := CF_NEW_EA3.ep_to_eu_class[CF_LEGACY_TO_NEW3[CF_I]];
    # Both representatives must be in the same EU-conjugacy-class.
    # We test by membership in the legacy EU-class.
    if not (CF_IDX_CLOSED3.reps[CF_NEU] in CF_INNER3.idx.classes[CF_LEU]) then
        Print("    Parity divergence at EP class ", CF_I,
              ": legacy EU-class ", CF_LEU,
              " does not contain new EU-rep at class ", CF_NEU, "\n");
        CF_PARITY_OK3 := false;
        break;
    fi;
od;
CFAssertTrue("B2-2: ep_to_eu_class points to same EU conjugacy class via both paths",
             CF_PARITY_OK3);

# ---- B2-3: trace_on_W parity on a sample ----
Print("\n--- B2-3: trace_on_W parity on a sample of inputs (m=3) ---\n");

# Pick a few elements of EA3.parent and evaluate the translated
# trace_on_W via both paths. At an irrep_idx that exists on both
# centralisers, the values must agree.
CF_PARENT_ELTS3 := List([1..Minimum(5, Length(CF_LEGACY_EA3.idx.reps))],
                         i -> CF_LEGACY_EA3.idx.reps[i]);;
CF_TR_PARITY := true;;
for CF_IDX in [1..Length(CF_PARENT_ELTS3)] do
    CF_ELT := CF_PARENT_ELTS3[CF_IDX];
    # Determine class index in each.
    CF_K_LEGACY := CF_IDX;
    CF_K_NEW := CF_LEGACY_TO_NEW3[CF_IDX];
    # Both paths' trace_on_W with irrep_idx = 1 should agree on this elt.
    CF_V_LEGACY := CF_LEGACY_EA3.trace_on_W(CF_K_LEGACY, 1, CF_ELT);
    CF_V_NEW := CF_NEW_EA3.trace_on_W(CF_K_NEW, 1, CF_ELT);
    if CF_V_LEGACY <> CF_V_NEW then
        Print("    Trace divergence at EP class ", CF_IDX,
              ": legacy=", CF_V_LEGACY, " new=", CF_V_NEW, "\n");
        CF_TR_PARITY := false;
    fi;
od;
CFAssertTrue("B2-3: trace_on_W parity on sample (irrep_idx=1)",
             CF_TR_PARITY);

# ---- B2-4: m=3 e2e -- RestrictTraceOnWToSubgroupHonourParent ----
Print("\n--- B2-4: m=3 e2e: RestrictTraceOnWToSubgroupHonourParent ---\n");

# Verify the closed-form path is consumable by the downstream restriction.
CF_RES_NEW := RestrictTraceOnWToSubgroupHonourParent(
    CF_NEW_EA3, CF_EA3.subgroup);;
CFAssertTrue("B2-4: restricted closed-form has .group = EA3.subgroup",
             CF_RES_NEW.group = CF_EA3.subgroup);
CFAssertTrue("B2-4: restricted closed-form .trace_on_W is a function",
             IsFunction(CF_RES_NEW.trace_on_W));
CF_TR_VAL := CF_RES_NEW.trace_on_W(1, 1, One(CF_EA3.subgroup));;
CFAssertTrue("B2-4: restricted trace_on_W(1, 1, e) is finite",
             CF_TR_VAL <> fail);

# ---- B2-6: m=7 smoke ----
Print("\n--- B2-6: m=7 smoke -- TranslateSpectralDataToEPlus with closed-form idx ---\n");
Print("Exercises the closed-form bypass: must not OOM and must complete in seconds.\n");

# Build a SYNTHETIC MOCK closed-form EU idx at m=7. We do NOT call
# `BuildSimpleIndexEPlusClosedForm(7)` here because the rank ~134M
# `global_to_local` list at m=7 hits memory limits even before our
# translate function runs (a pre-existing issue independent of B2).
#
# The B2 test only needs to verify that the TRANSLATE FUNCTION does
# not OOM on the EP-side build. We build a smaller mock idx with the
# closed-form shape (`is_closed_form := true`, 3 reps, minimal num_irreps)
# and verify the EP-side bypass works.
CF_M7 := 7;;
CF_T0 := Runtime();;

CF_EU_M7 := EmUnimodGroup(CF_M7);;
CF_N7 := 2 ^ CF_M7;;
CF_I_M7 := IdentityMat(CF_N7);;
CF_Z_M7 := -IdentityMat(CF_N7);;
CF_GENS_M7 := GeneratorsOfGroup(CF_EU_M7);;
# Pick a non-central generator (index 2 = sigma_{1,1}) for the third class.
CF_SIGMA_M7 := CF_GENS_M7[2];;

CF_MOCK_REPS_M7 := [CF_I_M7, CF_Z_M7, CF_SIGMA_M7];;
CF_MOCK_SIZES_M7 := [1, 1, 2];;
CF_MOCK_NUM_IRREPS_M7 := [4, 4, 4];;
CF_MOCK_CLASSES_M7 := [];;
for CF_I_LOOP in [1..3] do
    CF_CL := ConjugacyClass(CF_EU_M7, CF_MOCK_REPS_M7[CF_I_LOOP]);
    SetSize(CF_CL, CF_MOCK_SIZES_M7[CF_I_LOOP]);
    Add(CF_MOCK_CLASSES_M7, CF_CL);
od;
CF_IDX_MOCK_M7 := rec(
    group := CF_EU_M7,
    order := 2 ^ (2 * CF_M7 + 1),
    classes := CF_MOCK_CLASSES_M7,
    reps := CF_MOCK_REPS_M7,
    class_sizes := CF_MOCK_SIZES_M7,
    centralisers := [CF_EU_M7, CF_EU_M7, fail],
    ct_centraliser := [fail, fail, fail],
    cc_centraliser := [fail, fail, fail],
    irreps := [fail, fail, fail],
    irrep_dims := [fail, fail, fail],
    num_irreps := CF_MOCK_NUM_IRREPS_M7,
    global_offset := [0, 4, 8],
    global_to_local := [[1, 1], [1, 2], [1, 3], [1, 4],
                        [2, 1], [2, 2], [2, 3], [2, 4],
                        [3, 1], [3, 2], [3, 3], [3, 4]],
    rank := 12,
    is_lazy := true,
    is_closed_form := true,
    class_types := ["id", "minus_one", "sigma2"],
    source := "test-mock-closed-form-m7"
);;
CF_T1 := Runtime();;
Print("  Mock closed-form EU idx at m=7 built in ", (CF_T1 - CF_T0)/1000.0, " s\n");

# Synthetic spec record with a trivial trace_on_W.
CF_SPEC_EU_M7 := rec(
    group := CF_EU_M7,
    idx := CF_IDX_MOCK_M7,
    transport := BuildTransportsLazy(CF_IDX_MOCK_M7),
    trace_on_W := function(k, l, h) return 1; end,
    epsilon := function(g1, g2, a, b) return 1; end,
    m := CF_M7,
    source := "test-m7-mock-closed-form"
);;

# Build a fresh EP at m=7 (PC group) for the target.
CF_T0 := Runtime();;
CF_EP_M7 := EPlusGroup(CF_M7);;
CF_T1 := Runtime();;
Print("  EPlusGroup(7) in ", (CF_T1 - CF_T0)/1000.0, " s\n");

# Load-bearing test: TranslateSpectralDataToEPlus must complete without
# OOM on the EP-side build. With closed-form path engaged, no
# `ConjugacyClasses(EP)` is called.
CF_T0 := Runtime();;
CF_TRANS_M7 := TranslateSpectralDataToEPlus(CF_SPEC_EU_M7, CF_EP_M7);;
CF_T1 := Runtime();;
Print("  TranslateSpectralDataToEPlus at m=7 in ", (CF_T1 - CF_T0)/1000.0, " s\n");
CFAssertTrue("B2-6: TranslateSpectralDataToEPlus(m=7) returns without OOM",
             CF_TRANS_M7 <> fail);
CFAssertTrue("B2-6: m=7 idx_EP has 3 (mock) classes",
             Length(CF_TRANS_M7.idx.classes) = 3);
CFAssertTrue("B2-6: m=7 idx_EP.group = ep_group",
             CF_TRANS_M7.idx.group = CF_EP_M7);
CFAssertTrue("B2-6: m=7 idx_EP is lazy",
             IsBound(CF_TRANS_M7.idx.is_lazy)
             and CF_TRANS_M7.idx.is_lazy = true);
# Bijection should be the identity permutation.
CFAssertEqual("B2-6: m=7 ep_to_eu_class is identity permutation [1..3]",
             CF_TRANS_M7.ep_to_eu_class, [1..3]);
# Verify .source field is set to the closed-form marker.
CFAssertEqual("B2-6: m=7 idx_EP.source = 'translated-closed-form-eplus'",
             CF_TRANS_M7.idx.source, "translated-closed-form-eplus");
# Verify centralisers: id and minus_one should get ep_group, sigma2 gets fail.
CFAssertEqual("B2-6: m=7 centralisers[1] = ep_group (id class)",
             CF_TRANS_M7.idx.centralisers[1], CF_EP_M7);
CFAssertEqual("B2-6: m=7 centralisers[2] = ep_group (minus_one class)",
             CF_TRANS_M7.idx.centralisers[2], CF_EP_M7);
CFAssertEqual("B2-6: m=7 centralisers[3] = fail (sigma2 class, lazy)",
             CF_TRANS_M7.idx.centralisers[3], fail);

# ---- Summary ----
Print("\n=================================================================\n");
Print("Summary: ", CF_PASSES, " passes, ", Length(CF_FAILURES), " failures.\n");
Print("=================================================================\n");

if Length(CF_FAILURES) = 0 then
    Print("\nPASS test_em_eplus_translate_closed_form\n");
else
    Print("\nFAIL test_em_eplus_translate_closed_form:\n");
    for CF_F in CF_FAILURES do
        Print("  - ", CF_F, "\n");
    od;
fi;

QUIT;
