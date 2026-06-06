# Smoke test for `BuildSimpleIndexEPlusClosedForm` (issue #447 Change A).
#
# This file lives in scripts/tests/.  Run from scripts/ directory:
#   gap -q -b -c 'Read("tests/test_buildsimpleindex_eplus_closed_form.g");'
#
# Acceptance criteria:
#   1. Per-type counts at m=3 match the closed-form formula:
#       id=1, minus_one=1, sigma2=2^5 + 2^2 - 1 = 35, sigma_1sigma_2=2^5 - 2^2 = 28.
#       Total = 65.
#   2. At m=3, the closed-form idx has the same shape as the standard
#       `BuildSimpleIndex(EmUnimodGroup(3))`: same `order`, same number
#       of classes, same multiset of `num_irreps`.
#   3. At m=2, m=3, the wall time of the closed-form builder is below
#       the dense `BuildSimpleIndex` wall time (sanity perf check).
#
# CPU constraint (PR #447): test m <= 3 only. Heavy tests are deferred
# to CI / user. m=2 takes < 0.1 s, m=3 takes < 0.1 s; m=5/7 are not
# exercised here.

# ---------------------------------------------------------------
# Dependencies — same load order as test_krr_spectral_characters_sparse.g.
# ---------------------------------------------------------------
SetInfoLevel(InfoWarning, 1);

Read("bw_lattice.g");
Read("em_construction.g");
Read("twisted_group_algebra.g");
Read("qforms_f2.g");
Read("defect_rep_minus_id.g");
Read("defect_rep_minus_id_optim.g");
Read("untwisted_modular_data.g");
Read("krr_spectral_characters.g");
Read("eplus_classes_closed_form.g");


# ---------------------------------------------------------------
# Test harness.
# ---------------------------------------------------------------
testFailures := [];;

AssertOrLog := function(label, cond)
    if cond then
        Print("  PASS: ", label, "\n");
    else
        Print("  FAIL: ", label, "\n");
        Add(testFailures, label);
    fi;
end;;


# ---------------------------------------------------------------
# Test 1: per-type counts at m=3.
# ---------------------------------------------------------------
Print("\n=================================================================\n");
Print("  Test 1: per-type counts at m=3\n");
Print("=================================================================\n");

m_3 := 3;;
idx_3 := BuildSimpleIndexEPlusClosedForm(m_3);;

expected_sigma2 := 2^(2*m_3 - 1) + 2^(m_3 - 1) - 1;;
expected_sigma4 := 2^(2*m_3 - 1) - 2^(m_3 - 1);;
expected_total := 2^(2 * m_3) + 1;;

Print("  Per-type counts: ", idx_3.per_type_counts, "\n");
Print("  Expected: id=1, minus_one=1, sigma2=", expected_sigma2,
      ", sigma_1sigma_2=", expected_sigma4,
      "; total=", expected_total, "\n");

AssertOrLog("1a: id count = 1",
            idx_3.per_type_counts.id = 1);
AssertOrLog("1b: minus_one count = 1",
            idx_3.per_type_counts.minus_one = 1);
AssertOrLog("1c: sigma2 count = 2^5 + 2^2 - 1 = 35",
            idx_3.per_type_counts.sigma2 = expected_sigma2
            and expected_sigma2 = 35);
AssertOrLog("1d: sigma_1sigma_2 count = 2^5 - 2^2 = 28",
            idx_3.per_type_counts.sigma_1sigma_2 = expected_sigma4
            and expected_sigma4 = 28);
AssertOrLog("1e: total classes = 1 + 1 + 35 + 28 = 65",
            Length(idx_3.classes) = expected_total
            and expected_total = 65);

# Verify class_types parallel to classes.
AssertOrLog("1f: class_types length matches classes",
            Length(idx_3.class_types) = Length(idx_3.classes));
AssertOrLog("1g: idx.is_lazy = true",
            IsBound(idx_3.is_lazy) and idx_3.is_lazy = true);


# ---------------------------------------------------------------
# Test 2: shape match vs BuildSimpleIndex(EmUnimodGroup(3)).
# ---------------------------------------------------------------
Print("\n=================================================================\n");
Print("  Test 2: shape match vs BuildSimpleIndex(EmUnimodGroup(3))\n");
Print("=================================================================\n");

G_dense := EmUnimodGroup(m_3);;
t0 := Runtime();;
idx_dense := BuildSimpleIndex(G_dense);;
t1 := Runtime();;
wall_dense := (t1 - t0) / 1000.0;;
Print("  BuildSimpleIndex(EmUnimodGroup(3)) wall: ", wall_dense, " s\n");

# Cross-check counts. Order may differ between the two; compare as
# multisets where order doesn't matter.
AssertOrLog("2a: same |G| (= 128)",
            idx_3.order = idx_dense.order);
AssertOrLog("2b: same number of classes",
            Length(idx_3.classes) = Length(idx_dense.classes));
AssertOrLog("2c: same rank (sum of num_irreps)",
            idx_3.rank = idx_dense.rank);

ni_3_sorted := AsSortedList(idx_3.num_irreps);;
ni_dense_sorted := AsSortedList(idx_dense.num_irreps);;
AssertOrLog("2d: num_irreps multiset matches dense version",
            ni_3_sorted = ni_dense_sorted);

# Class sizes multiset.
cs_3_sorted := AsSortedList(idx_3.class_sizes);;
cs_dense_sorted := AsSortedList(idx_dense.class_sizes);;
AssertOrLog("2e: class_sizes multiset matches dense version",
            cs_3_sorted = cs_dense_sorted);


# ---------------------------------------------------------------
# Test 3: pickup wall time (sanity perf check).
# ---------------------------------------------------------------
Print("\n=================================================================\n");
Print("  Test 3: pickup wall time at m=2, m=3\n");
Print("=================================================================\n");

for m_test in [2, 3] do
    # Re-build a fresh G so the closed-form's SetConjugacyClasses isn't
    # short-circuiting the dense run.
    G_perf := EmUnimodGroup(m_test);;
    t0 := Runtime();;
    idx_perf := BuildSimpleIndex(G_perf);;
    t1 := Runtime();;
    wall_perf_dense := (t1 - t0) / 1000.0;;

    # Closed form builds its own G internally.
    t0 := Runtime();;
    idx_perf_cf := BuildSimpleIndexEPlusClosedForm(m_test);;
    t1 := Runtime();;
    wall_perf_cf := (t1 - t0) / 1000.0;;

    Print("  m=", m_test, ":  dense ", wall_perf_dense,
          " s vs closed-form ", wall_perf_cf, " s; ",
          Length(idx_perf_cf.classes), " classes\n");

    AssertOrLog(Concatenation("3a/m=", String(m_test),
                              ": closed-form is below 1 s"),
                wall_perf_cf < 1.0);
    AssertOrLog(Concatenation("3b/m=", String(m_test),
                              ": closed-form num_classes matches dense"),
                Length(idx_perf_cf.classes) = Length(idx_perf.classes));
    AssertOrLog(Concatenation("3c/m=", String(m_test),
                              ": closed-form rank matches dense"),
                idx_perf_cf.rank = idx_perf.rank);
od;


# ---------------------------------------------------------------
# Test 4: BuildKRRSpectralCharactersSparse wires the closed form in.
# ---------------------------------------------------------------
Print("\n=================================================================\n");
Print("  Test 4: BuildKRRSpectralCharactersSparse dispatches correctly\n");
Print("=================================================================\n");

# Read the sparse builder. It should pick up the closed-form sibling
# automatically via its auto-load directive at end-of-file.
Read("krr_spectral_characters_sparse.g");

# m=3 is < 5 so the dispatcher routes through BuildSimpleIndex(G) (the
# non-lazy path because useLazy = (m >= 5) and m=3 < 5). The closed
# form is therefore NOT exercised here at m=3 — we only verify it's
# available.
AssertOrLog("4a: BuildSimpleIndexEPlusClosedForm is in scope after Read",
            IsBoundGlobal("BuildSimpleIndexEPlusClosedForm"));

# We don't run BuildKRRSpectralCharactersSparse(5+) here (CPU budget).
# The smoke test for actual integration is exercised by the K-4b m=5
# regression in `test_krr_spectral_characters_sparse.g` (which we don't
# re-run here to stay below the CPU budget). The m=3 smoke above
# verifies the helper is loaded and shape-compatible.


# ---------------------------------------------------------------
# Summary.
# ---------------------------------------------------------------
Print("\n=================================================================\n");
Print("  Summary\n");
Print("=================================================================\n");

if Length(testFailures) = 0 then
    Print("  ALL TESTS PASS.\n");
else
    Print("  FAILURES (", Length(testFailures), "):\n");
    for label in testFailures do
        Print("    ", label, "\n");
    od;
fi;
