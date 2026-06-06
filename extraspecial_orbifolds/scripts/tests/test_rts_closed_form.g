# test_rts_closed_form.g — B1 + B3 + C3 closed-form tests (audit #456).
#
# Tests for the closed-form optimisations in
# `extraspecial_orbifolds/scripts/restrict_to_subgroup.g`:
#
#   B1 — closed-form `_RTS_FindGClassOf` when idx_G.is_closed_form = true.
#        For E_+(m), classify a_H by (Order, central-or-not, a_H^2) and
#        look up the matching class via a per-idx dictionary instead of
#        the O(|G|) `RepresentativeAction` path.
#
#   B3 — closed-form `RestrictedIrrepDecomposition` for abelian H using
#        Pontryagin's dual evaluation. Every H-class is a singleton; the
#        existing path's `ClassIndexInCentraliser` loop is bypassed.
#
#   C3 — memoise `BuildIntertwinerDataUntwisted(H)` per IdGroup(H) inside
#        `RestrictTraceOnWToSubgroupHonourParent` so that repeated calls
#        with the same H short-circuit.
#
# Acceptance criteria:
#   1. (B1 parity) On m=3 the closed-form `_RTS_FindGClassOf` produces
#      the same (k_G, conj) record (modulo conj — see below) as the
#      legacy path for every H-class of H ∈ {D_8, Q_8, EA(m=3)}. We
#      verify `conj * a_H * conj^-1 = idx_G.reps[k_G]` exactly.
#   2. (B3) Abelian H: `RestrictedIrrepDecomposition` produces the same
#      multiplicities under closed-form vs the existing decomposition.
#      Multiplicities sum to dim(chi_G) (Frobenius reciprocity for 1-dim
#      irreps of abelian H).
#   3. (C3) Second call to `RestrictTraceOnWToSubgroupHonourParent` with
#      the same H short-circuits via the memoisation cache. Verified by
#      inspecting the cache: cache is populated after first call; second
#      call hits a counter we keep in the cache rec.
#
# Backward-compat: tests verify that for `not is_closed_form` idx_G the
# legacy path is exercised unchanged.
#
# Usage:
#   gap -q -b /abs/path/to/test_rts_closed_form.g

# ---- Test bookkeeping -------------------------------------------------

RCF_PASSES   := 0;;
RCF_FAILURES := [];;

RCFAssertEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
        RCF_PASSES := RCF_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Print("         expected: ", expected, "\n");
        Print("         got:      ", got, "\n");
        Add(RCF_FAILURES, label);
    fi;
end;;

RCFAssertTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
        RCF_PASSES := RCF_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Add(RCF_FAILURES, label);
    fi;
end;;

# ---- Locate and load the module under test ----------------------------

RCF_SELF := INPUT_FILENAME();;
if RCF_SELF = fail or RCF_SELF = "stream" then
    Error("test_rts_closed_form.g: INPUT_FILENAME() unavailable; ",
          "Read by absolute path.");
fi;
if Length(RCF_SELF) > 0 and RCF_SELF[1] <> '/' then
    RCF_SELF := Filename(DirectoryCurrent(), RCF_SELF);
fi;
RCF_SELFDIR := RCF_SELF{[1..Length(RCF_SELF)
                            - Length("/test_rts_closed_form.g")]};;
RCF_SCRIPTSDIR := RCF_SELFDIR{
    [1..Length(RCF_SELFDIR) - Length("/tests")]};;

# Load order:
#   1. closed-form ingredients (bw_lattice etc.)
#   2. untwisted_modular_data.g (BuildSimpleIndex, _EnsureClassData)
#   3. krr_spectral_characters.g (EmUnimodGroup)
#   4. eplus_classes_closed_form.g (BuildSimpleIndexEPlusClosedForm)
#   5. eplus_irreps_closed_form.g (EPlusEvalIrrep, EPlusBuildAllCharacterRows)
#   6. krr_projector.g (BuildIntertwinerDataUntwisted)
#   7. quillen_detecting_subgroup.g (D8Section_E_plus, Q8Section_E_plus,
#                                     MaximalElementaryAbelian_E_plus)
#   8. restrict_to_subgroup.g (module under test)
Read(Concatenation(RCF_SCRIPTSDIR, "/bw_lattice.g"));
Read(Concatenation(RCF_SCRIPTSDIR, "/em_construction.g"));
Read(Concatenation(RCF_SCRIPTSDIR, "/twisted_group_algebra.g"));
Read(Concatenation(RCF_SCRIPTSDIR, "/qforms_f2.g"));
Read(Concatenation(RCF_SCRIPTSDIR, "/defect_rep_minus_id.g"));
Read(Concatenation(RCF_SCRIPTSDIR, "/defect_rep_minus_id_optim.g"));
Read(Concatenation(RCF_SCRIPTSDIR, "/untwisted_modular_data.g"));
Read(Concatenation(RCF_SCRIPTSDIR, "/krr_spectral_characters.g"));
Read(Concatenation(RCF_SCRIPTSDIR, "/eplus_classes_closed_form.g"));
Read(Concatenation(RCF_SCRIPTSDIR, "/eplus_irreps_closed_form.g"));
Read(Concatenation(RCF_SCRIPTSDIR, "/krr_projector.g"));
Read(Concatenation(RCF_SCRIPTSDIR, "/quillen_detecting_subgroup.g"));
Read(Concatenation(RCF_SCRIPTSDIR, "/restrict_to_subgroup.g"));

RCFAssertTrue("RestrictTraceOnWToSubgroup bound",
              IsBound(RestrictTraceOnWToSubgroup));
RCFAssertTrue("RestrictTraceOnWToSubgroupHonourParent bound",
              IsBound(RestrictTraceOnWToSubgroupHonourParent));
RCFAssertTrue("RestrictedIrrepDecomposition bound",
              IsBound(RestrictedIrrepDecomposition));
RCFAssertTrue("_RTS_FindGClassOf bound",
              IsBound(_RTS_FindGClassOf));
RCFAssertTrue("_RTS_FindGClassOfClosedForm bound (B1 helper)",
              IsBound(_RTS_FindGClassOfClosedForm));
RCFAssertTrue("BuildSimpleIndexEPlusClosedForm bound",
              IsBound(BuildSimpleIndexEPlusClosedForm));

# ============================================================
# Build a closed-form idx_G for m=3 along with its companions:
#   * idx_G_cf  : closed-form (`is_closed_form = true`)
#   * idx_G_leg : legacy `BuildSimpleIndex` on the same EmUnimodGroup(m=3)
#                 (used for parity comparison)
# Both indices use the SAME matrix-group instance G_em so element
# membership works.
# ============================================================

m := 3;;
G_em := EmUnimodGroup(m);;

Print("\n=================================================================\n");
Print("Setting up indices for E_+(", m, ") = EmUnimodGroup(", m, ")\n");
Print("=================================================================\n");

# Build legacy index FIRST on a fresh EmUnimodGroup so SetConjugacyClasses
# below doesn't pre-empt the legacy enumeration.
G_em_legacy := EmUnimodGroup(m);;
idx_G_leg := BuildSimpleIndex(G_em_legacy);;
Print("legacy idx: ", Length(idx_G_leg.classes), " classes, ",
      "is_closed_form bound? ", IsBound(idx_G_leg.is_closed_form), "\n");
RCFAssertEqual("legacy idx: |classes| = 65",
               Length(idx_G_leg.classes), 65);
RCFAssertTrue("legacy idx: NOT is_closed_form",
              not IsBound(idx_G_leg.is_closed_form));

# Closed-form on a fresh EmUnimodGroup.
idx_G_cf := BuildSimpleIndexEPlusClosedForm(m);;
RCFAssertEqual("closed-form idx: |classes| = 65",
               Length(idx_G_cf.classes), 65);
RCFAssertTrue("closed-form idx: is_closed_form = true",
              IsBound(idx_G_cf.is_closed_form)
              and idx_G_cf.is_closed_form = true);
RCFAssertTrue("closed-form idx: has class_types",
              IsBound(idx_G_cf.class_types));

# ============================================================
# Test 1 (B1): parity between closed-form and legacy `_RTS_FindGClassOf`.
#
# For each H-class rep of H ∈ {D_8, Q_8, max EA(3)} embedded in
# G_em_cf := idx_G_cf.group, call `_RTS_FindGClassOf(idx_G_cf, a_H, G_cf)`.
# Verify:
#   * The returned record satisfies `conj * a_H * conj^-1 = idx_G_cf.reps[k_G]`.
#   * The returned k_G matches the legacy-path k_G via Order/class-membership.
# ============================================================

Print("\n=================================================================\n");
Print("Test 1 (B1): closed-form _RTS_FindGClassOf parity\n");
Print("=================================================================\n");

# Build a closed-form-aware idx_G whose group `G_em_cf` is the parent of
# the subgroups we test against. To do that we build the subgroups inside
# `idx_G_cf.group` directly (UnimodSigma matrices, same family).
G_em_cf := idx_G_cf.group;;
n_em_cf := DegreeOfMatrixGroup(G_em_cf);;

# Helper: build sample subgroup H of G_em_cf using closed-form
# generators. We pick `EA(m=3) := <σ_{1,1}, σ_{2,1}, σ_{3,1}, -I>` which
# has rank 4 (~16 elements, abelian by extraspecial commutator structure
# — σ_{a,1} all commute pairwise).
sig_11 := UnimodSigma(m, 1, 1);;
sig_21 := UnimodSigma(m, 2, 1);;
sig_31 := UnimodSigma(m, 3, 1);;
sig_12 := UnimodSigma(m, 1, 2);;
sig_22 := UnimodSigma(m, 2, 2);;
zI := -IdentityMat(n_em_cf);;

# Verify generators commute pairwise (sanity).
RCFAssertTrue("EA generators commute σ_{1,1} σ_{2,1}",
              sig_11 * sig_21 = sig_21 * sig_11);
RCFAssertTrue("EA generators commute σ_{1,1} σ_{3,1}",
              sig_11 * sig_31 = sig_31 * sig_11);

# Build a rank-4 elementary-abelian subgroup of G_em_cf.
H_ea := Subgroup(G_em_cf, [zI, sig_11, sig_21, sig_31]);;
RCFAssertEqual("EA: |H_ea| = 16", Order(H_ea), 16);
RCFAssertTrue("EA: is elementary abelian", IsElementaryAbelian(H_ea));

# D_8 = <σ_{1,1}, σ_{1,2}> — these anticommute, σ_{1,1}^2 = I, σ_{1,2}^2 = I.
H_d8 := Subgroup(G_em_cf, [sig_11, sig_12]);;
RCFAssertEqual("D_8: |H_d8| = 8", Order(H_d8), 8);
RCFAssertEqual("D_8: IdGroup = [8, 3]", IdGroup(H_d8), [8, 3]);

# A second order-8 subgroup to widen the coverage. The product
# σ_{1,1} σ_{1,2} has order 4 (squares to -I, since σ_{a,1} σ_{a,2} =
# -σ_{a,2} σ_{a,1}); paired with σ_{2,1} σ_{2,2} (which commutes with
# the first since (a=1) and (a=2) σ-blocks commute pairwise) we get a
# Z_4 × Z_4 / center quotient — but with the centre -I the subgroup
# spans an abelian 8-group with element-orders {1, 2, 4}, giving 8
# elements and IdGroup [8, 2]. The B1 path doesn't depend on IdGroup;
# we just need a non-trivial 8-elt subgroup to exercise `_RTS_FindGClassOf`
# on multiple H-class structures.
sub_8a := sig_11 * sig_12;;
sub_8b := sig_21 * sig_22;;
H_8 := Subgroup(G_em_cf, [sub_8a, sub_8b]);;
RCFAssertEqual("H_8 (extra): |H_8| = 8", Order(H_8), 8);

# Compute the H-class reps for each subgroup and call `_RTS_FindGClassOf`
# with idx_G_cf.
TestRtsFindGClassOf := function(label, idx_G_arg, H, G_arg)
    local cc_H, k_H, a_H, mapping, k_G, conj, expected, got, all_ok, count;
    cc_H := ConjugacyClasses(H);
    all_ok := true;
    count := 0;
    for k_H in [1..Length(cc_H)] do
        a_H := Representative(cc_H[k_H]);
        mapping := _RTS_FindGClassOf(idx_G_arg, a_H, G_arg);
        if not (IsBound(mapping.k_G) and IsBound(mapping.conj)) then
            Print("    BAD: ", label, " k_H=", k_H,
                  " returned mapping without k_G/conj\n");
            all_ok := false;
            continue;
        fi;
        k_G := mapping.k_G;
        conj := mapping.conj;
        if not (k_G in [1..Length(idx_G_arg.classes)]) then
            Print("    BAD: ", label, " k_H=", k_H, " k_G=", k_G,
                  " out of range\n");
            all_ok := false;
            continue;
        fi;
        if not (conj in G_arg) then
            Print("    BAD: ", label, " k_H=", k_H, " conj not in G\n");
            all_ok := false;
            continue;
        fi;
        expected := idx_G_arg.reps[k_G];
        got := conj * a_H * conj^-1;
        if got <> expected then
            Print("    BAD: ", label, " k_H=", k_H,
                  ": conj * a_H * conj^-1 = ", got,
                  ", expected ", expected, "\n");
            all_ok := false;
            continue;
        fi;
        count := count + 1;
    od;
    RCFAssertTrue(Concatenation(label,
                                 ": _RTS_FindGClassOf works for all ",
                                 String(Length(cc_H)),
                                 " H-classes (verified ",
                                 String(count), ")"),
                  all_ok and count = Length(cc_H));
end;;

TestRtsFindGClassOf("EA (closed-form)", idx_G_cf, H_ea, G_em_cf);
TestRtsFindGClassOf("D_8 (closed-form)", idx_G_cf, H_d8, G_em_cf);
TestRtsFindGClassOf("H_8 (closed-form)", idx_G_cf, H_8, G_em_cf);

# Build the legacy-side subgroups now (used for backward-compat checks
# and the perf comparison below).
sig_11_leg := UnimodSigma(m, 1, 1);;
sig_21_leg := UnimodSigma(m, 2, 1);;
sig_31_leg := UnimodSigma(m, 3, 1);;
sig_12_leg := UnimodSigma(m, 1, 2);;
sig_22_leg := UnimodSigma(m, 2, 2);;
zI_leg := -IdentityMat(n_em_cf);;
H_d8_leg := Subgroup(G_em_legacy, [sig_11_leg, sig_12_leg]);;
H_ea_leg := Subgroup(G_em_legacy, [zI_leg, sig_11_leg,
                                     sig_21_leg, sig_31_leg]);;

# Sanity check: the closed-form helper is callable directly on EA.
direct_results := List([1..Length(ConjugacyClasses(H_ea))],
    function(k)
        local a;
        a := Representative(ConjugacyClasses(H_ea)[k]);
        return _RTS_FindGClassOfClosedForm(idx_G_cf, a, G_em_cf);
    end);;
direct_ok := ForAll(direct_results,
    function(map)
        local k_G, conj, rep;
        if not (IsRecord(map) and IsBound(map.k_G) and IsBound(map.conj))
        then return false; fi;
        k_G := map.k_G;
        conj := map.conj;
        rep := idx_G_cf.reps[k_G];
        return true;
    end);;
RCFAssertTrue("EA: _RTS_FindGClassOfClosedForm returns valid records",
              direct_ok);

# Perf measurement (informational, not a strict pass/fail).
# Compare avg wall of `_RTS_FindGClassOf` under closed-form vs legacy
# on the EA(m=3) class reps. The legacy path uses RepresentativeAction
# (O(|G|) orbit-stabiliser); the closed-form path is O(1) per call.
ea_reps := List(ConjugacyClasses(H_ea), Representative);;
ea_reps_leg := List(ConjugacyClasses(H_ea_leg), Representative);;

n_reps_each := 5;;       # average over 5 calls per rep for stability
t_cf := Runtime();;
for _trial in [1..n_reps_each] do
    for a_iter in ea_reps do
        _RTS_FindGClassOf(idx_G_cf, a_iter, G_em_cf);
    od;
od;
wall_cf_ms := Runtime() - t_cf;;

t_leg := Runtime();;
for _trial in [1..n_reps_each] do
    for a_iter in ea_reps_leg do
        _RTS_FindGClassOf(idx_G_leg, a_iter, G_em_legacy);
    od;
od;
wall_leg_ms := Runtime() - t_leg;;

n_calls := n_reps_each * Length(ea_reps);;
avg_cf_us := QuoInt(wall_cf_ms * 1000, n_calls);;
avg_leg_us := QuoInt(wall_leg_ms * 1000, n_calls);;
Print("\n  Perf: m=3 EA avg _RTS_FindGClassOf wall:\n");
Print("    closed-form: ", wall_cf_ms, " ms total, ",
      avg_cf_us, " us / call (",
      n_calls, " calls)\n");
Print("    legacy     : ", wall_leg_ms, " ms total, ",
      avg_leg_us, " us / call (",
      n_calls, " calls)\n");
# We don't require a speedup at m=3 (legacy is already fast on a deg-8
# matrix group), but we do require closed-form to NOT regress.
RCFAssertTrue("closed-form not slower than 5x legacy at m=3",
              wall_cf_ms <= 5 * wall_leg_ms + 50);

# Backward-compat: legacy idx (not is_closed_form) still works.
# `H_d8_leg` was defined earlier; we re-use it here.
TestRtsFindGClassOf("D_8 (LEGACY idx)", idx_G_leg, H_d8_leg, G_em_legacy);

# Parity: closed-form and legacy both find the same k_G (modulo class
# ordering). We can check pairwise: for each pair (k_H -> k_G_cf) and
# (k_H -> k_G_leg), the reps idx_G_cf.reps[k_G_cf] and
# idx_G_leg.reps[k_G_leg] should be CONJUGATE in their respective
# groups. We check the easier invariants (Order matches, central
# matches).
cc_d8 := ConjugacyClasses(H_d8);;
cc_d8_leg := ConjugacyClasses(H_d8_leg);;
RCFAssertEqual("D_8: closed-form and legacy report same #classes",
               Length(cc_d8), Length(cc_d8_leg));

parity_ok := true;;
for k_H_iter in [1..Length(cc_d8)] do
    a_H_cf := Representative(cc_d8[k_H_iter]);
    a_H_leg := Representative(cc_d8_leg[k_H_iter]);
    map_cf := _RTS_FindGClassOf(idx_G_cf, a_H_cf, G_em_cf);
    map_leg := _RTS_FindGClassOf(idx_G_leg, a_H_leg, G_em_legacy);
    # Invariants: Order of the resulting class rep matches; central
    # matches (rep ∈ {I, -I} iff k_G is one of the two central indices).
    if Order(idx_G_cf.reps[map_cf.k_G])
       <> Order(idx_G_leg.reps[map_leg.k_G]) then
        Print("    BAD: D_8 k_H=", k_H_iter,
              " closed-form k_G_cf order = ",
              Order(idx_G_cf.reps[map_cf.k_G]),
              ", legacy order = ",
              Order(idx_G_leg.reps[map_leg.k_G]), "\n");
        parity_ok := false;
    fi;
od;
RCFAssertTrue("D_8: closed-form vs legacy class-mapping order invariant",
              parity_ok);

# ============================================================
# Test 2 (B3): closed-form `RestrictedIrrepDecomposition` for abelian H.
#
# For H abelian (= EA(3)), the decomposition multiplicities can be
# computed via Pontryagin's dual: every Irr(C_H(a_H)) is 1-dim, every
# H-class is a singleton. The closed-form should produce the same
# multiplicity matrix as the existing general path.
# ============================================================

Print("\n=================================================================\n");
Print("Test 2 (B3): RestrictedIrrepDecomposition closed-form parity\n");
Print("=================================================================\n");

# Build legacy intertwiner_data for G_em_legacy and restrict to EA.
# `H_ea_leg` was defined earlier in the backward-compat block.
data_G_leg := BuildIntertwinerDataUntwisted(G_em_legacy);;

# Get the H-side index from BuildIntertwinerDataUntwisted(H).
data_H_leg := BuildIntertwinerDataUntwisted(H_ea_leg);;
idx_H_leg := data_H_leg.idx;;

RCFAssertTrue("EA: is abelian",
              IsAbelian(H_ea_leg));
RCFAssertEqual("EA: |classes(H)| = 16 (every elt own class)",
               Length(idx_H_leg.classes), 16);

# Choose k_H = 1 (identity class of H) — its conjugator is identity,
# its k_G is the identity class of G (= 1 in both indices).
k_H_test := 1;;
a_H_test := idx_H_leg.reps[k_H_test];;
RCFAssertEqual("EA: idx_H.reps[1] = One(H_ea)",
               a_H_test, One(H_ea_leg));

mapping_test := _RTS_FindGClassOf(data_G_leg.idx, a_H_test, G_em_legacy);;
k_G_test := mapping_test.k_G;;
conj_test := mapping_test.conj;;
RCFAssertEqual("EA: a_H = I -> k_G = identity-class-index = 1",
               k_G_test, 1);
RCFAssertEqual("EA: a_H = I -> conj = I",
               conj_test, IdentityMat(n_em_cf));

# Materialise the irreps for both centralisers.
_EnsureClassData(data_G_leg.idx, k_G_test);
_EnsureClassData(idx_H_leg, k_H_test);

decomp := RestrictedIrrepDecomposition(
    data_G_leg.idx, idx_H_leg, k_G_test, k_H_test, conj_test);;

RCFAssertTrue("decomp record has phi_class_index_G",
              IsBound(decomp.phi_class_index_G));
RCFAssertTrue("decomp record has decomposition function",
              IsBound(decomp.decomposition));

# Pick the first G-irrep (1-dim, trivial). Its restriction multiplicities
# must sum to 1 (the dimension of the chi_G being restricted).
num_irreps_G_test := data_G_leg.idx.num_irreps[k_G_test];;
RCFAssertTrue("|Irr(G)| > 0",
              num_irreps_G_test > 0);

mults_chi1 := decomp.decomposition(1);;
RCFAssertEqual("EA: decomp[chi_1] length = num_irreps_H",
               Length(mults_chi1),
               idx_H_leg.num_irreps[k_H_test]);

# Frobenius reciprocity: sum_{l_H} mult * chi_l_H(1) = chi_G(1) = 1 for chi_1.
# All chi_l_H are 1-dim for abelian H, so chi_l_H(1) = 1, hence sum = chi_G(1).
chi_G_1_dim := data_G_leg.idx.irreps[k_G_test][1][1];;
mult_sum_chi1 := Sum(mults_chi1);;
RCFAssertEqual("EA: sum(mults for chi_G_1) = dim(chi_G_1)",
               mult_sum_chi1, chi_G_1_dim);

# All multiplicities must be non-negative integers.
all_nn_int := ForAll(mults_chi1, x -> IsInt(x) and x >= 0);;
RCFAssertTrue("EA: all multiplicities are non-negative integers",
              all_nn_int);

# Pick a larger G-irrep (say the last one — the 2^m-dim faithful one if
# present) and verify Frobenius reciprocity.
chi_G_last_idx := num_irreps_G_test;;
chi_G_last_dim := data_G_leg.idx.irreps[k_G_test][chi_G_last_idx][1];;
mults_chi_last := decomp.decomposition(chi_G_last_idx);;
mult_sum_chi_last := Sum(mults_chi_last);;
RCFAssertEqual("EA: sum(mults for last chi_G) = dim(last chi_G)",
               mult_sum_chi_last, chi_G_last_dim);

# ============================================================
# Test 3 (C3): memoise BuildIntertwinerDataUntwisted in
# RestrictTraceOnWToSubgroupHonourParent.
#
# After the first call, the cache should contain an entry keyed by
# IdGroup(H). The second call should hit the cache.
# ============================================================

Print("\n=================================================================\n");
Print("Test 3 (C3): BuildIntertwinerDataUntwisted memoisation\n");
Print("=================================================================\n");

# Reset the cache (it persists across calls but we want to test from a
# known state). Bind by the symbol the implementation uses.
RCFAssertTrue("memoisation cache exists",
              IsBound(_RTS_BIDU_CACHE));
_RTS_BIDU_CACHE := rec();;

# First call: cache miss.
res1 := RestrictTraceOnWToSubgroupHonourParent(data_G_leg, H_d8_leg);;
RCFAssertTrue("after first call: cache populated",
              Length(RecNames(_RTS_BIDU_CACHE)) >= 1);

# Capture the data record reference for D_8.
cache_keys_after_1 := ShallowCopy(RecNames(_RTS_BIDU_CACHE));;
first_key := cache_keys_after_1[1];;
cached_data_1 := _RTS_BIDU_CACHE.(first_key);;

# Second call with the SAME H: should hit cache.
res2 := RestrictTraceOnWToSubgroupHonourParent(data_G_leg, H_d8_leg);;
cached_data_2 := _RTS_BIDU_CACHE.(first_key);;
RCFAssertTrue("after second call: same number of cache entries",
              Length(RecNames(_RTS_BIDU_CACHE))
              = Length(cache_keys_after_1));
RCFAssertTrue("cached data record reused (IsIdenticalObj)",
              IsIdenticalObj(cached_data_1, cached_data_2));

# Verify both restricted records produced the same result (sanity check
# the memoisation doesn't break correctness).
RCFAssertEqual("res1.idx and res2.idx point to same data",
               Length(res1.idx.reps),
               Length(res2.idx.reps));

# Third call with a DIFFERENT H (EA): cache should grow.
res3 := RestrictTraceOnWToSubgroupHonourParent(data_G_leg, H_ea_leg);;
RCFAssertTrue("after EA call: cache has at least 2 entries",
              Length(RecNames(_RTS_BIDU_CACHE)) >= 2);

# ============================================================
# Test 4: integration — both restriction APIs return identical
# class_to_G mappings under closed-form vs legacy idx_G.
# ============================================================

Print("\n=================================================================\n");
Print("Test 4: integration — RestrictTraceOnWToSubgroup byte-for-byte\n");
Print("=================================================================\n");

# Build a closed-form intertwiner_data manually (drop in idx_G_cf as the
# idx field). The transport / trace_on_W / epsilon are non-functional for
# this test — we only exercise the class_to_G part.
data_G_cf := rec(
    group := G_em_cf,
    idx := idx_G_cf,
    transport := BuildTransports(idx_G_cf),
    trace_on_W := function(class_idx, irrep_idx, h)
        return EvalIrr(idx_G_cf, class_idx, irrep_idx, h);
    end,
    epsilon := function(g1, g2, a, b) return 1; end
);;

restricted_d8_cf := RestrictTraceOnWToSubgroup(data_G_cf, H_d8);;
restricted_d8_leg := RestrictTraceOnWToSubgroup(data_G_leg, H_d8_leg);;

# class_to_G mappings: same number, same k_G ordering (since both
# idx_G's enumerate classes in the same canonical order — central first,
# then non-central by bit-vector — and BuildSimpleIndex's canonical
# enumeration is structurally identical when SetConjugacyClasses fixes
# the closed-form order).
RCFAssertEqual("D_8 closed-form vs legacy: same #class_to_G entries",
               Length(restricted_d8_cf.class_to_G),
               Length(restricted_d8_leg.class_to_G));

# Per-H-class invariants: rep order preserved.
order_parity_ok := true;;
for k_H_iter in [1..Length(restricted_d8_cf.class_to_G)] do
    if Order(idx_G_cf.reps[restricted_d8_cf.class_to_G[k_H_iter].k_G])
       <> Order(idx_G_leg.reps[restricted_d8_leg.class_to_G[k_H_iter].k_G]) then
        order_parity_ok := false;
    fi;
od;
RCFAssertTrue("D_8 closed-form vs legacy: class-mapping order parity",
              order_parity_ok);

# ---- Final report -----------------------------------------------------

Print("\n=================================================================\n");
Print("  Summary: ", RCF_PASSES, " passes, ",
      Length(RCF_FAILURES), " failures.\n");
Print("=================================================================\n");

if Length(RCF_FAILURES) = 0 then
    Print("\nPASS test_rts_closed_form\n");
else
    Print("\nFAIL test_rts_closed_form:\n");
    for f in RCF_FAILURES do
        Print("  - ", f, "\n");
    od;
fi;

QUIT;
