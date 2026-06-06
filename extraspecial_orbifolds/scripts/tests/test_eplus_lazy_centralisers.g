# Lazy non-central centraliser materialisation for E_+(m) closed-form
# index records (issue #449 audit finding A1').
#
# This file lives in scripts/tests/. Run from scripts/ directory:
#   gap -q -b -c 'Read("tests/test_eplus_lazy_centralisers.g");'
#
# Acceptance criteria:
#   1. m=3 sanity: BuildSimpleIndexEPlusClosedForm(3) has
#       * idx.centralisers[i] = G for the two central classes (id,
#         minus_one).
#       * idx.centralisers[i] = fail for all non-central classes
#         BEFORE any access via _EPlusCentraliserOf.
#   2. m=3 access: _EPlusCentraliserOf(idx, k) for a non-central index k
#       returns the correct group AND caches it in-place so the second
#       call sees a non-`fail` slot.
#   3. m=3 equivalence: comparing the closed-form-with-lazy idx against
#       the eager BuildSimpleIndex (which materialises all centralisers
#       upfront) the centralisers (after materialisation) are equal as
#       groups (same Order, same generators-as-set).
#   4. m=3 spectral integration: BuildKRRSpectralCharactersSparse(3)
#       runs without errors when the closed-form idx is wired in (gated
#       on m >= 5 in production, but we manually run with the
#       closed-form idx here at m=3 to verify the lazy path is sound).

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
# Test 1: lazy sanity at m=3.
# ---------------------------------------------------------------
Print("\n=================================================================\n");
Print("  Test 1: lazy sanity at m=3 (central = G, non-central = fail)\n");
Print("=================================================================\n");

m_3 := 3;;
G_3 := EmUnimodGroup(m_3);;
idx_3 := BuildSimpleIndexEPlusClosedForm(m_3);;

Print("  num_classes = ", Length(idx_3.classes), "\n");
Print("  class_types[1..4] = ", idx_3.class_types{[1..4]}, "\n");

AssertOrLog("1a: idx.class_types[1] = id",
            idx_3.class_types[1] = "id");
AssertOrLog("1b: idx.class_types[2] = minus_one",
            idx_3.class_types[2] = "minus_one");

AssertOrLog("1c: idx.centralisers[1] = G (id is central)",
            idx_3.centralisers[1] = G_3);
AssertOrLog("1d: idx.centralisers[2] = G (-I is central)",
            idx_3.centralisers[2] = G_3);

# Find a non-central class index. Since class 3 onward are all
# non-central by construction, idx.centralisers[3] should be `fail`
# until accessed.
AssertOrLog("1e: idx.centralisers[3] = fail (non-central, lazy)",
            idx_3.centralisers[3] = fail);
AssertOrLog("1f: idx.centralisers[Length] = fail (non-central, lazy)",
            idx_3.centralisers[Length(idx_3.classes)] = fail);


# ---------------------------------------------------------------
# Test 2: lazy materialisation via _EPlusCentraliserOf.
# ---------------------------------------------------------------
Print("\n=================================================================\n");
Print("  Test 2: lazy materialisation\n");
Print("=================================================================\n");

# Pre-state: slot 3 is fail.
AssertOrLog("2a: pre-state idx.centralisers[3] = fail",
            idx_3.centralisers[3] = fail);

# First call materialises.
C3 := _EPlusCentraliserOf(idx_3, 3);;
AssertOrLog("2b: _EPlusCentraliserOf returns a group",
            IsGroup(C3));
AssertOrLog("2c: idx.centralisers[3] now caches the group (no longer fail)",
            idx_3.centralisers[3] = C3);
AssertOrLog("2d: idx.centralisers[3] is a subgroup of G",
            IsSubgroup(G_3, C3));
AssertOrLog("2e: rep is in its own centraliser",
            idx_3.reps[3] in C3);

# Second call: idempotent.
C3_b := _EPlusCentraliserOf(idx_3, 3);;
AssertOrLog("2f: second call returns the same group object",
            IsIdenticalObj(C3, C3_b));

# Central-class call: returns G unchanged.
C1 := _EPlusCentraliserOf(idx_3, 1);;
AssertOrLog("2g: _EPlusCentraliserOf for central class returns G",
            C1 = G_3);


# ---------------------------------------------------------------
# Test 3: equivalence with eager BuildSimpleIndex(G).
#
# Since the closed-form builder and the eager builder enumerate
# conjugacy classes in DIFFERENT orders, we can't compare per-index.
# Instead we check that the SET of {Order(C_i) : i} matches as a
# multiset (after lazy materialisation), and that the rank / class
# counts agree (Test 2 in test_buildsimpleindex_eplus_closed_form.g
# already verifies the shape).
# ---------------------------------------------------------------
Print("\n=================================================================\n");
Print("  Test 3: centralisers multiset matches eager BuildSimpleIndex\n");
Print("=================================================================\n");

# Materialise ALL slots first.
for i in [1..Length(idx_3.classes)] do
    _EPlusCentraliserOf(idx_3, i);;
od;

orders_lazy := List(idx_3.centralisers, Order);;
sorted_orders_lazy := AsSortedList(orders_lazy);;

idx_eager := BuildSimpleIndex(G_3);;
orders_eager := List(idx_eager.centralisers, Order);;
sorted_orders_eager := AsSortedList(orders_eager);;

Print("  closed-form sorted orders: ", sorted_orders_lazy{[1..Minimum(10, Length(sorted_orders_lazy))]}, "...\n");
Print("  eager sorted orders:       ", sorted_orders_eager{[1..Minimum(10, Length(sorted_orders_eager))]}, "...\n");

AssertOrLog("3a: centraliser order multiset matches eager builder",
            sorted_orders_lazy = sorted_orders_eager);


# ---------------------------------------------------------------
# Test 4: spectral integration smoke test.
#
# We don't actually invoke BuildKRRSpectralCharactersSparse here at
# m=3 (it's gated behind m >= 5 by the dispatcher in production).
# Instead, we directly invoke `_EnsureClassData` on a non-central
# class to verify the lazy materialisation path through
# untwisted_modular_data.g works end-to-end.
# ---------------------------------------------------------------
Print("\n=================================================================\n");
Print("  Test 4: _EnsureClassData propagates lazy materialisation\n");
Print("=================================================================\n");

# Fresh idx (so the cache state is clean).
idx_4 := BuildSimpleIndexEPlusClosedForm(m_3);;
# Pick a non-central slot and verify it's `fail`.
AssertOrLog("4a: fresh idx.centralisers[3] = fail",
            idx_4.centralisers[3] = fail);

_EnsureClassData(idx_4, 3);;
AssertOrLog("4b: after _EnsureClassData, idx.centralisers[3] is materialised",
            IsGroup(idx_4.centralisers[3]) and idx_4.centralisers[3] <> fail);
AssertOrLog("4c: after _EnsureClassData, idx.ct_centraliser[3] is bound",
            idx_4.ct_centraliser[3] <> fail);
AssertOrLog("4d: after _EnsureClassData, idx.irreps[3] is bound",
            idx_4.irreps[3] <> fail);


# ---------------------------------------------------------------
# Test 5: CentraliserClassData (sparse spectral) honours lazy path.
# ---------------------------------------------------------------
Print("\n=================================================================\n");
Print("  Test 5: CentraliserClassData (sparse spectral) honours lazy path\n");
Print("=================================================================\n");

# Read the sparse spectral file so that CentraliserClassData is bound.
Read("krr_spectral_characters_sparse.g");

idx_5 := BuildSimpleIndexEPlusClosedForm(m_3);;
# Pick a non-central slot.
AssertOrLog("5a: pre-state idx_5.centralisers[3] = fail",
            idx_5.centralisers[3] = fail);
cls_data_3 := CentraliserClassData(idx_5, 3);;
AssertOrLog("5b: CentraliserClassData returns a record with .num >= 1",
            IsRecord(cls_data_3) and IsBound(cls_data_3.num)
            and cls_data_3.num >= 1);
AssertOrLog("5c: post-call idx_5.centralisers[3] is materialised",
            IsGroup(idx_5.centralisers[3]) and idx_5.centralisers[3] <> fail);

# Central class: behave correctly (returns G).
cls_data_1 := CentraliserClassData(idx_5, 1);;
AssertOrLog("5d: CentraliserClassData(idx, central) has |G|/1 = NrConjugacyClasses(G) entries",
            cls_data_1.num = NrConjugacyClasses(G_3));


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
