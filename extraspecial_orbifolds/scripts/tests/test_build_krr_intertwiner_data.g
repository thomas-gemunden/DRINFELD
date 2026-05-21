# test_build_krr_intertwiner_data.g
#
# Tests for K-4a-T4b (issue #188):
#   `BuildKRRIntertwinerData(m, G [, opts])` produces an intertwiner_data
#   record consumable by K-1's `ProjectorFormula`, with lattice
#   provenance.
#
# Acceptance criteria (per #188):
#   1. m = 3: BuildKRRIntertwinerData(3, EmGroup(3)) -> ProjectorFormula
#      reproduces K-3's central-row anchor (matches §4.3 closed-form S^0
#      central row byte-for-byte / cyclotomic equality).
#   2. m = 5: callable returns valid data; falls through to the lite
#      mode (or sparse spectral when wired) and matches
#      BuildIntertwinerDataUntwisted on a sample.
#   3. m = 7: same as m = 5 — no degeneracies / errors at construction.
#
# This test runs the FULL m=3 acceptance via the existing K-3 closed-
# form harness from `closed_form_central.g`. For m = 5 / m = 7 we only
# smoke-test (construct + invoke once) because the full S central row
# at m ≥ 5 needs cache-build infrastructure that isn't in scope here.
#
# Invoke via absolute path (K-4a-T1 convention):
#   gap -q -b -c 'Read("/.../tests/test_build_krr_intertwiner_data.g");'
#
# IMPORTANT — file ordering. Several files in this codebase share
# function names (e.g. `_efPerH_keys`, `F2_Mul`, `MatOfBilForm` are
# overridden by `defect_rep_minus_id_optim.g`). The order below is the
# K-2 / K-4a canonical order; do not reshuffle without checking.

SetInfoLevel(InfoWarning, 0);
BreakOnError := false;

# Resolve absolute paths to siblings independent of CWD.
_SCRIPT_SELF := INPUT_FILENAME();;
if _SCRIPT_SELF = fail or _SCRIPT_SELF = "stream" then
    Error("test_build_krr_intertwiner_data.g: INPUT_FILENAME() unavailable; ",
          "invoke this test via an absolute Read(\"/.../tests/test_build_",
          "krr_intertwiner_data.g\").");
fi;
# Issue #325: when this file is Read via a relative path,
# INPUT_FILENAME() returns the relative path as-given and the slicing
# below would produce wrong/empty results. Promote to absolute first.
if Length(_SCRIPT_SELF) > 0 and _SCRIPT_SELF[1] <> '/' then
    _SCRIPT_SELF := Filename(DirectoryCurrent(), _SCRIPT_SELF);
fi;
_SELF_DIR := _SCRIPT_SELF{
    [1..Length(_SCRIPT_SELF)
       - Length("/test_build_krr_intertwiner_data.g")]};;
# Strip the trailing "/tests" to get the scripts dir.
_SCRIPTS_DIR := _SELF_DIR{[1..Length(_SELF_DIR) - Length("/tests")]};;
Print("Script dir resolved as: ", _SCRIPTS_DIR, "\n");

# Sanity-check: the resolved scripts dir must actually contain one of
# the dependencies we are about to Read. Bail out early with a clear
# message if path resolution is wrong (e.g. odd trailing characters in
# INPUT_FILENAME()).
if not IsExistingFile(Concatenation(_SCRIPTS_DIR, "/bw_lattice.g")) then
    Error("test_build_krr_intertwiner_data.g: resolved _SCRIPTS_DIR=\"",
          _SCRIPTS_DIR, "\" does not contain bw_lattice.g; ",
          "check INPUT_FILENAME() path resolution.");
fi;

# Historical note (issue #315 / #319): a previous version of this test
# included a `ChangeDirectoryCurrent(_SCRIPTS_DIR)` workaround because
# `twisted_group_algebra.g` did unconditional CWD-relative Reads of
# `bw_lattice.g` and `em_construction.g`. Those Reads have been removed
# in PR #321 (which fixes #319); this test now loads dependencies in
# the same order as before but no longer needs the chdir workaround.
# The Reads in this file are all done via `_T_Read` (absolute path), so
# CWD is irrelevant to the dependency-load phase.

# Helper to Read by absolute path.
_T_Read := function(rel)
    Read(Concatenation(_SCRIPTS_DIR, "/", rel));
end;;


# ------------------------------------------------------------------
# Test harness: simple pass/fail counters.
# ------------------------------------------------------------------

T_PASS := 0;;
T_FAILURES := [];;
TAssertTrue := function(label, cond)
    if cond then
        Print("  [ok]   ", label, "\n");
        T_PASS := T_PASS + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Add(T_FAILURES, label);
    fi;
end;;
TAssertEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok]   ", label, "\n");
        T_PASS := T_PASS + 1;
    else
        Print("  [FAIL] ", label, " (got=", got, ", expected=", expected, ")\n");
        Add(T_FAILURES, label);
    fi;
end;;


# ------------------------------------------------------------------
# Load dependencies.
# ------------------------------------------------------------------

_T_Read("bw_lattice.g");
_T_Read("em_construction.g");
_T_Read("twisted_group_algebra.g");
_T_Read("qforms_f2.g");
_T_Read("defect_rep_minus_id.g");
_T_Read("defect_rep_minus_id_optim.g");
_T_Read("untwisted_modular_data.g");
_T_Read("krr_projector.g");
_T_Read("closed_form_central.g");
# krr_spectral_characters.g is OPTIONAL — only needed for spectral_source
# = "dense_spectral" at m=3. We Read it so the m=3 dense_spectral mode
# path is exercised.
_T_Read("krr_spectral_characters.g");
_T_Read("build_krr_intertwiner_data.g");

# Verify that the critical globals are actually bound. If any are not,
# fail loudly here instead of letting Test 2 / Test 3 crash mid-run
# with a cryptic "Variable: must have an assigned value" error.
_REQUIRED_GLOBALS := [
    "UnimodSigma", "EmUnimodGroup", "EmGroup", "IsomorphismPcGroup",
    "BuildKRRIntertwinerData", "BuildIntertwinerDataUntwisted",
    "MakeWg", "ProjectorFormula", "ClosedFormCentralS",
    "BuildSimpleIndex", "_KRRI_BuildLiteCallables",
    "_KRRI_ResolveAutoSource"
];;
for _gl in _REQUIRED_GLOBALS do
    if not IsBoundGlobal(_gl) then
        Error("test_build_krr_intertwiner_data.g: required global \"",
              _gl, "\" is not bound after loading dependencies. ",
              "This usually indicates that one of the _T_Read calls ",
              "failed silently. Re-run with BreakOnError := true to ",
              "see the underlying error.");
    fi;
od;
Print("All required globals bound after dependency load (",
      Length(_REQUIRED_GLOBALS), " checked).\n");


# ==================================================================
# Test 1: m = 3 K-3 anchor — central row of S^Keller via
# BuildKRRIntertwinerData matches the §4.3 closed form byte-for-byte.
# ==================================================================
Print("\n=================================================================\n");
Print("  Test 1: m = 3 K-3 anchor (lite mode)\n");
Print("=================================================================\n");

T1_M := 3;;
# Per the issue body (#188) acceptance: BuildKRRIntertwinerData(3, EmGroup(3))
# (the matrix group) must reproduce the K-3 central-row anchor. We test this
# AND also a faster pc-group variant for use in driver code.
T1_G_MAT := EmGroup(T1_M);;
T1_ISO := IsomorphismPcGroup(T1_G_MAT);;
T1_G_PC := Image(T1_ISO);;

# Primary acceptance: matrix-group form, exactly as the issue body specifies.
T1_G := T1_G_MAT;;

Print("  Building intertwiner data via BuildKRRIntertwinerData(3, ",
      "EmGroup(3), opts=lite)...\n");
T1_T0 := Runtime();;
# Use "lite" mode explicitly: per the T4a research note (Section 3.2)
# and Section 4.1, at ω = 0 the spectral trace equals the centraliser-
# character trace, so the lite mode IS the lattice-derived answer for
# the K-4a CT case. This is the primary acceptance test for #188.
T1_DATA := BuildKRRIntertwinerData(T1_M, T1_G,
    rec(spectral_source := "lite", verbose := false));;
T1_T1 := Runtime();;
Print("  Build wall: ", T1_T1 - T1_T0, " ms\n");

TAssertTrue("T1: returned record has .group field",
            IsBound(T1_DATA.group));
TAssertTrue("T1: .group is the input G",
            T1_DATA.group = T1_G);
TAssertTrue("T1: returned record has .idx field",
            IsBound(T1_DATA.idx));
TAssertTrue("T1: returned record has .transport field",
            IsBound(T1_DATA.transport));
TAssertTrue("T1: returned record has .trace_on_W field (function)",
            IsBound(T1_DATA.trace_on_W) and IsFunction(T1_DATA.trace_on_W));
TAssertTrue("T1: returned record has .epsilon field (function)",
            IsBound(T1_DATA.epsilon) and IsFunction(T1_DATA.epsilon));
TAssertEqual("T1: .source = \"krr-lattice\"",
             T1_DATA.source, "krr-lattice");
TAssertEqual("T1: .omega_is_zero = true (omega_vec absent)",
             T1_DATA.omega_is_zero, true);
TAssertEqual("T1: .spectral_source_resolved = \"lite\"",
             T1_DATA.spectral_source_resolved, "lite");

# Sanity check: epsilon on arbitrary args returns 1.
TAssertEqual("T1: epsilon(arbitrary, ..., ...) = 1",
             T1_DATA.epsilon(One(T1_G), One(T1_G), One(T1_G), One(T1_G)), 1);

# Central-row acceptance: pick the central singleton classes of G
# (i.e. {1} and {z = -I}), then for every (ci, k1, tj, k2) compare
# ProjectorFormula(W_(ci,k1), W_(tj,k2), T1_DATA) vs §4.3 closed form.
T1_IDX := T1_DATA.idx;;
T1_CENTRAL := [];;
T1_GENS := GeneratorsOfGroup(T1_G);;
for i in [1..Length(T1_IDX.classes)] do
    if T1_IDX.class_sizes[i] <> 1 then continue; fi;
    g_c := T1_IDX.reps[i];;
    ok := true;;
    for h_gen in T1_GENS do
        if g_c * h_gen <> h_gen * g_c then ok := false; break; fi;
    od;
    if ok then Add(T1_CENTRAL, i); fi;
od;;
Print("  Central singleton class indices: ", T1_CENTRAL,
      "  (", Length(T1_CENTRAL), " classes)\n");

# Acceptance sweep.
Print("  Sweeping central rows (this is the K-3 anchor)...\n");
T1_TOTAL := 0;;
T1_MISMATCHES := 0;;
T1_FIRST_MISMATCH := fail;;
T1_T2 := Runtime();;
for ci in T1_CENTRAL do
    Ni := T1_IDX.num_irreps[ci];;
    for tj in [1..Length(T1_IDX.classes)] do
        Nj := T1_IDX.num_irreps[tj];;
        for k1 in [1..Ni] do
            W1 := MakeWg(T1_DATA, ci, k1);;
            for k2 in [1..Nj] do
                T1_TOTAL := T1_TOTAL + 1;
                W2 := MakeWg(T1_DATA, tj, k2);;
                vA := ProjectorFormula(W1, W2, T1_DATA);;
                vB := ClosedFormCentralS(T1_IDX, ci, k1, tj, k2);;
                if vA <> vB then
                    T1_MISMATCHES := T1_MISMATCHES + 1;
                    if T1_FIRST_MISMATCH = fail then
                        T1_FIRST_MISMATCH := rec(ci := ci, k1 := k1,
                                                  tj := tj, k2 := k2,
                                                  proj := vA, closed := vB);
                    fi;
                fi;
            od;
        od;
    od;
od;
T1_T3 := Runtime();;
Print("  Sweep total entries: ", T1_TOTAL,
      "  (", T1_T3 - T1_T2, " ms)\n");
Print("  Mismatches: ", T1_MISMATCHES, "\n");
if T1_FIRST_MISMATCH <> fail then
    Print("  First mismatch: ci=", T1_FIRST_MISMATCH.ci,
          " k1=", T1_FIRST_MISMATCH.k1,
          " tj=", T1_FIRST_MISMATCH.tj,
          " k2=", T1_FIRST_MISMATCH.k2, "\n");
    Print("    ProjectorFormula value: ", T1_FIRST_MISMATCH.proj, "\n");
    Print("    Closed-form value:      ", T1_FIRST_MISMATCH.closed, "\n");
fi;
TAssertEqual("T1: K-3 central-row anchor (lite mode) - 0 mismatches",
             T1_MISMATCHES, 0);


# ==================================================================
# Test 2: m = 3 dense_spectral mode -- DIAGNOSTIC ONLY, exercises the
# spectral build path but does not assert K-1 compatibility (the
# spectral irrep_idx convention differs from BuildSimpleIndex's; see
# the WARNING in build_krr_intertwiner_data.g's
# _KRRI_BuildDenseSpectralCallables comment).
# ==================================================================
Print("\n=================================================================\n");
Print("  Test 2: m = 3 dense_spectral mode (diagnostic)\n");
Print("=================================================================\n");

Print("  Building intertwiner data via BuildKRRIntertwinerData(3, ",
      "EmUnimodGroup(3), opts=dense_spectral)...\n");
T2_T0 := Runtime();;
T2_G := EmUnimodGroup(T1_M);;
T2_DATA := BuildKRRIntertwinerData(T1_M, T2_G,
    rec(spectral_source := "dense_spectral", verbose := false));;
T2_T1 := Runtime();;
Print("  Build wall: ", T2_T1 - T2_T0, " ms\n");
TAssertEqual("T2: .spectral_source_resolved = \"dense_spectral\"",
             T2_DATA.spectral_source_resolved, "dense_spectral");
TAssertTrue("T2: .spectral_data field is populated",
            IsBound(T2_DATA.spectral_data));

# Locate the -I class. T2_DATA.idx is over EmUnimodGroup(3), so -I is
# the matrix -IdentityMat(2^3).
T2_IDX := T2_DATA.idx;;
T2_CENTRAL_Z_CLASS := fail;;
for i_loop in [1..Length(T2_IDX.classes)] do
    if T2_IDX.class_sizes[i_loop] = 1
       and T2_IDX.reps[i_loop] = -IdentityMat(2^T1_M) then
        T2_CENTRAL_Z_CLASS := i_loop;
        break;
    fi;
od;;
TAssertTrue("T2: -I class located in EmUnimodGroup(3)",
            T2_CENTRAL_Z_CLASS <> fail);

# Verify the spectral builder identified some eigenspaces.
T2_EIGENSPACES_Z := T2_DATA.spectral_data.eigenspace_cache[T2_CENTRAL_Z_CLASS];;
TAssertTrue("T2: spectral builder found eigenspaces on the -I class",
            IsList(T2_EIGENSPACES_Z) and Length(T2_EIGENSPACES_Z) > 0);
Print("  Eigenspaces found on -I class: ", Length(T2_EIGENSPACES_Z),
      " (expected: 12, but basis-dependent — see krr_spectral_characters.g)\n");

# trace_on_W returns a cyclotomic for spectral irrep_idx in
# [1..Length(eigenspaces)].
T2_VAL_SPECTRAL := T2_DATA.trace_on_W(T2_CENTRAL_Z_CLASS, 1, One(T2_G));;
TAssertTrue("T2: spectral trace_on_W(z_class, 1, identity) is a cyclotomic",
            IsCyclotomic(T2_VAL_SPECTRAL));
Print("  Sample spectral trace on -I class, eigenspace 1, identity = ",
      T2_VAL_SPECTRAL, "\n");

# Non-central classes fall back to EvalIrr; should agree with lite on
# every (class, k, h).
T2_LITE_DATA := BuildKRRIntertwinerData(T1_M, T2_G,
    rec(spectral_source := "lite"));;
T2_NONCENTRAL_AGREE := true;;
T2_NONCENTRAL_FIRST_DIFF := fail;;
for i_loop in [1..Length(T2_IDX.classes)] do
    if i_loop = T2_CENTRAL_Z_CLASS then continue; fi;
    # Identity class is also "central" in a sense but spectral
    # treats it as non-(-I) (BuildTgens.is_minus_id = false), so
    # falls back to EvalIrr — should agree exactly with lite.
    Ni := T2_IDX.num_irreps[i_loop];;
    for k_loop in [1..Minimum(Ni, 3)] do
        # Sample h = identity and first generator.
        for h_samp in [One(T2_G), GeneratorsOfGroup(T2_G)[1]] do
            v_s := T2_DATA.trace_on_W(i_loop, k_loop, h_samp);
            v_l := T2_LITE_DATA.trace_on_W(i_loop, k_loop, h_samp);
            if v_s <> v_l then
                T2_NONCENTRAL_AGREE := false;
                if T2_NONCENTRAL_FIRST_DIFF = fail then
                    T2_NONCENTRAL_FIRST_DIFF :=
                        rec(class := i_loop, k := k_loop, h := h_samp,
                             spectral := v_s, lite := v_l);
                fi;
            fi;
        od;
    od;
od;
TAssertTrue("T2: non-central classes — spectral agrees with lite",
            T2_NONCENTRAL_AGREE);
if T2_NONCENTRAL_FIRST_DIFF <> fail then
    Print("  T2 first divergence: ", T2_NONCENTRAL_FIRST_DIFF, "\n");
fi;


# ==================================================================
# Test 3: m = 5 smoke test — BuildKRRIntertwinerData returns a record;
# trace_on_W and epsilon are invocable.
# ==================================================================
Print("\n=================================================================\n");
Print("  Test 3: m = 5 smoke test (auto -> lite, since sparse may be slow)\n");
Print("=================================================================\n");

T3_M := 5;;
T3_T0 := Runtime();;
T3_G_MAT := EmGroup(T3_M);;
T3_ISO := IsomorphismPcGroup(T3_G_MAT);;
T3_G := Image(T3_ISO);;
T3_T1 := Runtime();;
Print("  E_+(5) pc-group built in ", T3_T1 - T3_T0, " ms (|G| = ",
      Order(T3_G), ")\n");
T3_T2 := Runtime();;
T3_DATA := BuildKRRIntertwinerData(T3_M, T3_G,
    rec(spectral_source := "lite", verbose := false));;
T3_T3 := Runtime();;
Print("  BuildKRRIntertwinerData lite at m=5: ", T3_T3 - T3_T2, " ms\n");

TAssertEqual("T3: m=5 .source = \"krr-lattice\"",
             T3_DATA.source, "krr-lattice");
TAssertEqual("T3: m=5 .omega_is_zero = true",
             T3_DATA.omega_is_zero, true);
TAssertEqual("T3: m=5 .spectral_source_resolved = \"lite\"",
             T3_DATA.spectral_source_resolved, "lite");
TAssertTrue("T3: m=5 .trace_on_W is a function",
            IsFunction(T3_DATA.trace_on_W));
TAssertTrue("T3: m=5 .epsilon is a function",
            IsFunction(T3_DATA.epsilon));

# Invoke trace_on_W on a few sample arguments to check no error.
T3_OK := true;;
for i in [1..Minimum(Length(T3_DATA.idx.classes), 4)] do
    for k_local in [1..Minimum(T3_DATA.idx.num_irreps[i], 2)] do
        val := T3_DATA.trace_on_W(i, k_local, One(T3_G));
        if not IsCyclotomic(val) then
            T3_OK := false;
            Print("  T3 fail at i=", i, " k=", k_local, ": got ", val, "\n");
        fi;
    od;
od;
TAssertTrue("T3: m=5 trace_on_W returns cyclotomics on sample",
            T3_OK);
TAssertEqual("T3: m=5 epsilon(1,1,1,1) = 1",
             T3_DATA.epsilon(One(T3_G), One(T3_G), One(T3_G), One(T3_G)), 1);

# Sanity: at omega = 0, lite-mode BuildKRRIntertwinerData should be
# numerically equivalent to BuildIntertwinerDataUntwisted on the
# SAME idx (same class enumeration). Build both and compare a sample.
T3_BASELINE := BuildIntertwinerDataUntwisted(T3_G);;
T3_NUM_DIFF := 0;;
T3_GENS := GeneratorsOfGroup(T3_G);;
for i in [1..Minimum(Length(T3_DATA.idx.classes), 5)] do
    for k_local in [1..Minimum(T3_DATA.idx.num_irreps[i], 3)] do
        for h_samp in [One(T3_G), T3_GENS[1], T3_GENS[2]] do
            v_new := T3_DATA.trace_on_W(i, k_local, h_samp);
            v_old := T3_BASELINE.trace_on_W(i, k_local, h_samp);
            if v_new <> v_old then
                T3_NUM_DIFF := T3_NUM_DIFF + 1;
            fi;
        od;
    od;
od;
TAssertEqual("T3: m=5 lite trace agrees with BuildIntertwinerDataUntwisted",
             T3_NUM_DIFF, 0);
# Same for epsilon.
TAssertEqual("T3: m=5 lite epsilon agrees with baseline (both = 1)",
             T3_DATA.epsilon(T3_GENS[1], T3_GENS[2], T3_GENS[1], T3_GENS[2]),
             T3_BASELINE.epsilon(T3_GENS[1], T3_GENS[2], T3_GENS[1], T3_GENS[2]));


# ==================================================================
# Test 4: m = 7 smoke test — same as m = 5, but at the (much larger)
# m = 7 group. Use spectral_source = "lite" explicitly since both
# dense and sparse spectral are infeasible at m = 7 without the
# Gauss-sum path.
# ==================================================================
Print("\n=================================================================\n");
Print("  Test 4: m = 7 smoke test (lite mode)\n");
Print("=================================================================\n");

T4_M := 7;;
# Check auto-resolution at m = 7 first (cheap; no group build).
TAssertEqual("T4: m=7 auto-resolve = \"lite\" (no sparse Gauss-sum path)",
             _KRRI_ResolveAutoSource(7), "lite");

# Smoke-test on a small group first (sanity check the helper).
T4_SMALL_G := SymmetricGroup(3);;       # smallest non-abelian; cheap.
T4_SMALL_IDX := BuildSimpleIndex(T4_SMALL_G);;
T4_LITE_CALLS := _KRRI_BuildLiteCallables(T4_SMALL_IDX);;
TAssertTrue("T4: _KRRI_BuildLiteCallables returns a trace_on_W function",
            IsFunction(T4_LITE_CALLS.trace_on_W));
val_T4 := T4_LITE_CALLS.trace_on_W(1, 1, One(T4_SMALL_G));;
TAssertTrue("T4: lite trace_on_W returns a cyclotomic on S_3",
            IsCyclotomic(val_T4));

# Optionally run BuildKRRIntertwinerData at m = 7 with lazy = true.
# This is what K-4c-style callers do. The lazy pipeline avoids the
# eager CharacterTable build over all ~16K classes; but materialising
# even one class's CT at m=7 takes a few minutes (|G| = 32K).
# Gate by env: K4A_T4B_RUN_M7 = "1" enables; default skip (CI-friendly).
if not IsBound(K4A_T4B_RUN_M7) then
    K4A_T4B_RUN_M7 := "0";
fi;
if K4A_T4B_RUN_M7 = "1" then
    Print("  T4 m=7 enabled via K4A_T4B_RUN_M7=1.\n");
    Print("  Building E_+(7) pc-group (this can take ~30 s)...\n");
    T4_T0 := Runtime();
    T4_G_MAT := EmGroup(T4_M);
    T4_ISO := IsomorphismPcGroup(T4_G_MAT);
    T4_G := Image(T4_ISO);
    T4_T1 := Runtime();
    Print("  E_+(7) pc-group built in ", T4_T1 - T4_T0, " ms (|G| = ",
          Order(T4_G), ")\n");

    Print("  Building BuildKRRIntertwinerData(7, E_+(7), lazy=true, lite)...\n");
    T4_T2 := Runtime();
    T4_DATA := BuildKRRIntertwinerData(T4_M, T4_G,
        rec(spectral_source := "lite", lazy := true, verbose := false));
    T4_T3 := Runtime();
    Print("  Built in ", T4_T3 - T4_T2, " ms.\n");

    TAssertEqual("T4: m=7 .source = \"krr-lattice\"",
                 T4_DATA.source, "krr-lattice");
    TAssertEqual("T4: m=7 .omega_is_zero = true",
                 T4_DATA.omega_is_zero, true);
    TAssertEqual("T4: m=7 .spectral_source_resolved = \"lite\"",
                 T4_DATA.spectral_source_resolved, "lite");
    TAssertTrue("T4: m=7 .idx.is_lazy = true (lazy path active)",
                IsBound(T4_DATA.idx.is_lazy) and T4_DATA.idx.is_lazy = true);
    TAssertTrue("T4: m=7 .trace_on_W is a function",
                IsFunction(T4_DATA.trace_on_W));

    # Query trace_on_W(1, 1, identity) — materialises class 1's CT only.
    T4_T4 := Runtime();
    T4_VAL := T4_DATA.trace_on_W(1, 1, One(T4_G));
    T4_T5 := Runtime();
    Print("  T4 trace_on_W(1, 1, 1) at m=7: ", T4_VAL,
          "  (", T4_T5 - T4_T4, " ms — materialised one CT lazily)\n");
    TAssertTrue("T4: m=7 lazy trace_on_W returns a cyclotomic",
                IsCyclotomic(T4_VAL));
    TAssertEqual("T4: m=7 epsilon(1,1,1,1) = 1",
                 T4_DATA.epsilon(One(T4_G), One(T4_G), One(T4_G), One(T4_G)),
                 1);
else
    Print("  T4 m=7 single-query skipped (gate K4A_T4B_RUN_M7 not set).\n");
    Print("    To run, prefix the GAP invocation with: K4A_T4B_RUN_M7 := \"1\";;\n");
    # We at least verify that BuildKRRIntertwinerData with lazy = true
    # is invokable on a SMALL group (the lazy-mode contract).
    T4_SMALL_G2 := EmGroup(2);;
    T4_SMALL_LAZY := BuildKRRIntertwinerData(2, T4_SMALL_G2,
        rec(spectral_source := "lite", lazy := true));
    TAssertTrue("T4: lazy mode at m=2 returns a record with is_lazy",
                IsBound(T4_SMALL_LAZY.idx.is_lazy)
                and T4_SMALL_LAZY.idx.is_lazy = true);
    T4_LAZY_VAL := T4_SMALL_LAZY.trace_on_W(1, 1, One(T4_SMALL_G2));
    TAssertTrue("T4: lazy mode at m=2 trace_on_W returns a cyclotomic",
                IsCyclotomic(T4_LAZY_VAL));
fi;


# ==================================================================
# Test 5: opts validation — bad inputs raise Errors (best-effort).
# ==================================================================
Print("\n=================================================================\n");
Print("  Test 5: opts validation\n");
Print("=================================================================\n");

# Use CALL_WITH_CATCH if available; otherwise skip the negative-path
# tests. The positive-path tests above are the real acceptance gate.
T5_M := 3;;
T5_G := Image(IsomorphismPcGroup(EmGroup(T5_M)));;

if IsBoundGlobal("CALL_WITH_CATCH") then
    T5_R1 := CALL_WITH_CATCH(function()
        return BuildKRRIntertwinerData(T5_M, T5_G,
            rec(spectral_source := "nonsense_value"));
    end, []);
    TAssertTrue("T5: BuildKRRIntertwinerData rejects bad spectral_source",
                T5_R1[1] = false);
    T5_R2 := CALL_WITH_CATCH(function()
        return BuildKRRIntertwinerData(0, T5_G);
    end, []);
    TAssertTrue("T5: BuildKRRIntertwinerData rejects non-positive m",
                T5_R2[1] = false);
else
    Print("  CALL_WITH_CATCH unavailable; skipping bad-input checks.\n");
fi;


# ==================================================================
# Summary
# ==================================================================
Print("\n=================================================================\n");
Print("  Summary\n");
Print("=================================================================\n");
Print("Passes:   ", T_PASS, "\n");
Print("Failures: ", Length(T_FAILURES), "\n");
if Length(T_FAILURES) > 0 then
    Print("Failure labels:\n");
    for lbl in T_FAILURES do
        Print("  - ", lbl, "\n");
    od;
fi;
Print("\nALL TESTS PASS: ", Length(T_FAILURES) = 0, "\n");

QUIT;
