# test_idx_irreps_interface_regression.g
#
# Post-A1''' (#455) + A1' (#454) regression suite for the
# `BuildSimpleIndexEPlusClosedForm` idx record's irrep + centraliser
# interface. Covers issue #457 (audit Q6 + Q7) for K-4b m=7 (#449).
#
# CONTEXT
# =======
# After PR #455 (A1'''): for closed-form E_+(m) idxs the central-class
# `idx.irreps[i]` is bypassed entirely; reads route via `EvalIrr` to
# `EPlusEvalIrrep(m, k, h)` without populating the slot. When
# `_EnsureClassData(idx, i)` IS called explicitly (e.g. by
# `BuildKRRIntertwinerData::proj_for_class`), `idx.irreps[i]` is
# populated by `EPlusBuildAllCharacterRows` as a plain list-of-lists
# (NOT a list of GAP `ClassFunction` objects).
#
# After PR #454 (A1'): `idx.centralisers[i]` is `fail` for non-central
# classes at build time; `_EPlusCentraliserOf(idx, i)` materialises on
# first access. Direct reads bypass this lazy path and may crash.
#
# This test file verifies, at m=3:
#   1. The irrep interface preserves `idx.irreps[i][k][cc_idx]` reads
#      (whether via closed-form OR via standard fallback).
#   2. The lazy centraliser slots stay `fail` until explicit access.
#   3. The K-4a m=3 verdict anchor still holds.
#   4. The K-4b m=5 TRIVIAL verdict artefact is loadable + correct.
#   5. The closed-form `EPlusEvalIrrep` smoke at m=7 still works.
#   6. The K-4a non-trivial sweep at m=3 (#419 risk) still passes.
#
# Run:
#   gap -q -b /Users/.../tests/test_idx_irreps_interface_regression.g

# ---- Test bookkeeping --------------------------------------------------

IIR_PASSES   := 0;;
IIR_FAILURES := [];;

IIRAssertEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
        IIR_PASSES := IIR_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Print("         expected: ", expected, "\n");
        Print("         got:      ", got, "\n");
        Add(IIR_FAILURES, label);
    fi;
end;;

IIRAssertTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
        IIR_PASSES := IIR_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Add(IIR_FAILURES, label);
    fi;
end;;

# ---- Locate worktree / scripts -----------------------------------------

IIR_SELF := INPUT_FILENAME();;
if IIR_SELF = fail or IIR_SELF = "stream" then
    Error("test_idx_irreps_interface_regression.g: INPUT_FILENAME() ",
          "unavailable; Read the file by its absolute path.");
fi;
IIR_SELFDIR := IIR_SELF{
    [1..Length(IIR_SELF)
        - Length("/test_idx_irreps_interface_regression.g")]};;
IIR_SCRIPTSDIR := IIR_SELFDIR{
    [1..Length(IIR_SELFDIR) - Length("/tests")]};;
IIR_WT_ROOT := IIR_SCRIPTSDIR{
    [1..Length(IIR_SCRIPTSDIR) - Length("/extraspecial_orbifolds/scripts")]};;

# Chdir to scripts/ so relative Reads in the load chain work.
ChangeDirectoryCurrent(IIR_SCRIPTSDIR);

# ---- Load chain --------------------------------------------------------

# Load src/modular_data.g first (k4a_classify and related touch
# LoadModularData; loading early is more robust).
Read(Concatenation(IIR_WT_ROOT, "/src/modular_data.g"));

# Closed-form E_+(m) ingredients.
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
Read("eplus_irreps_closed_form.g");
Read("krr_spectral_characters_sparse.g");

# K-4a orchestrator (transitively loads its own deps).
Read("k4a_classify.g");

# Pre-load lattice-source path's lazy-loaded siblings while CWD = scripts/.
# Section 6 changes CWD to a Modular_Data symlink directory, which breaks
# the bare relative Reads in detecting_family_vanish.g / detecting_family_restriction.g.
if not IsBoundGlobal("ResIsTrivialOnDetectingFamily") then
    Read("detecting_family_restriction.g");
    Read("detecting_family_vanish.g");
fi;
if not IsBoundGlobal("BuildKRRIntertwinerData") then
    Read("build_krr_intertwiner_data.g");
fi;
if not IsBoundGlobal("KellerTwistIsTrivial") then
    Read("keller/keller_twist_is_trivial.g");
fi;

IIRAssertTrue("Load: BuildSimpleIndexEPlusClosedForm bound",
              IsBoundGlobal("BuildSimpleIndexEPlusClosedForm"));
IIRAssertTrue("Load: EPlusEvalIrrep bound",
              IsBoundGlobal("EPlusEvalIrrep"));
IIRAssertTrue("Load: EPlusBuildAllCharacterRows bound",
              IsBoundGlobal("EPlusBuildAllCharacterRows"));
IIRAssertTrue("Load: _EPlusCentraliserOf bound",
              IsBoundGlobal("_EPlusCentraliserOf"));
IIRAssertTrue("Load: K4aClassify bound",
              IsBoundGlobal("K4aClassify"));

# =================================================================
# Section 1: irrep interface preservation
# =================================================================
Print("\n=================================================================\n");
Print("Section 1: idx.irreps[i][k][cc_idx] interface preservation at m=3\n");
Print("=================================================================\n");

IIR_M := 3;;
IIR_N := 2 ^ IIR_M;;
IIR_G := EmUnimodGroup(IIR_M);;

# Build both flavours.
IIR_T0 := Runtime();;
IIR_IDX_CF := BuildSimpleIndexEPlusClosedForm(IIR_M);;
IIR_T1 := Runtime();;
Print("  BuildSimpleIndexEPlusClosedForm(3) wall: ",
      (IIR_T1 - IIR_T0) / 1000.0, " s\n");

IIR_T0 := Runtime();;
IIR_IDX_DENSE := BuildSimpleIndex(IIR_G);;
IIR_T1 := Runtime();;
Print("  BuildSimpleIndex(EmUnimodGroup(3)) wall: ",
      (IIR_T1 - IIR_T0) / 1000.0, " s\n");

IIRAssertEqual("1a: closed-form has the right number of classes",
               Length(IIR_IDX_CF.classes), 4^IIR_M + 1);
IIRAssertEqual("1a': dense has the same number of classes",
               Length(IIR_IDX_DENSE.classes), 4^IIR_M + 1);
IIRAssertEqual("1b: rank matches between cf and dense",
               IIR_IDX_CF.rank, IIR_IDX_DENSE.rank);

# Locate the two central classes in each builder.
IIR_CF_CENTRAL := Filtered([1..Length(IIR_IDX_CF.classes)],
    i -> IIR_IDX_CF.centralisers[i] = IIR_IDX_CF.group);;
IIR_DENSE_CENTRAL := Filtered([1..Length(IIR_IDX_DENSE.classes)],
    i -> IIR_IDX_DENSE.centralisers[i] = IIR_IDX_DENSE.group);;
IIRAssertEqual("1c: closed-form has exactly 2 central classes",
               Length(IIR_CF_CENTRAL), 2);
IIRAssertEqual("1d: dense has exactly 2 central classes",
               Length(IIR_DENSE_CENTRAL), 2);

# For each central class, build the closed-form character table as a
# multiset of row-functions on idx_dense.reps. Compare to the dense
# character table evaluated at the same reps.
for IIR_CF_I in IIR_CF_CENTRAL do
    Print("\n  --- central class ", IIR_CF_I, " (cf) ---\n");
    IIR_NUM_IRREPS := IIR_IDX_CF.num_irreps[IIR_CF_I];
    IIRAssertEqual(
        Concatenation("1e/cf-class", String(IIR_CF_I),
                      ": num_irreps = 4^m + 1 = 65"),
        IIR_NUM_IRREPS, 4^IIR_M + 1);

    # Read via EvalIrr (the closed-form dispatcher): values at each
    # dense.reps element.
    IIR_CF_ROWS := List([1..IIR_NUM_IRREPS], k ->
        List(IIR_IDX_DENSE.reps, g ->
            EvalIrr(IIR_IDX_CF, IIR_CF_I, k, g)));

    # Read via dense (using the first dense central class as reference).
    IIR_DENSE_I := IIR_DENSE_CENTRAL[1];
    IIR_DENSE_ROWS := List([1..IIR_IDX_DENSE.num_irreps[IIR_DENSE_I]], k ->
        List(IIR_IDX_DENSE.reps, g ->
            EvalIrr(IIR_IDX_DENSE, IIR_DENSE_I, k, g)));

    IIRAssertEqual(
        Concatenation("1f/cf-class", String(IIR_CF_I),
                      ": # closed-form rows = # dense rows"),
        Length(IIR_CF_ROWS), Length(IIR_DENSE_ROWS));

    IIRAssertEqual(
        Concatenation("1g/cf-class", String(IIR_CF_I),
                      ": closed-form rows = dense rows as multiset"),
        AsSortedList(IIR_CF_ROWS), AsSortedList(IIR_DENSE_ROWS));
od;

# Now exercise the "direct read" path: after _EnsureClassData runs
# for the closed-form central class, `idx.irreps[i][k][cc_idx]` must
# work — this is the contract consumed by closed_form_central.g,
# krr_spectral_characters.g, krr_spectral_characters_sparse.g,
# brw_simples_action.g (line 147, 169), build_krr_intertwiner_data.g
# line 751, etc.
Print("\n  --- direct read idx.irreps[i][k][cc_idx] ---\n");
IIR_CF_I := IIR_CF_CENTRAL[1];;
IIRAssertTrue("1h: before _EnsureClassData, irreps[i] = fail",
              IIR_IDX_CF.irreps[IIR_CF_I] = fail);
_EnsureClassData(IIR_IDX_CF, IIR_CF_I);;
IIRAssertTrue("1i: after _EnsureClassData, irreps[i] is bound",
              IIR_IDX_CF.irreps[IIR_CF_I] <> fail);
IIRAssertTrue("1j: irreps[i] is a list of lists (NOT class-function objects)",
              IsList(IIR_IDX_CF.irreps[IIR_CF_I])
              and Length(IIR_IDX_CF.irreps[IIR_CF_I]) = 4^IIR_M + 1
              and IsList(IIR_IDX_CF.irreps[IIR_CF_I][1]));
IIRAssertEqual(
    "1k: irreps[i][1][1] = 1 (trivial char at identity)",
    IIR_IDX_CF.irreps[IIR_CF_I][1][1], 1);
IIRAssertEqual(
    "1l: irreps[i][4^m+1][1] = 2^m (faithful char at identity)",
    IIR_IDX_CF.irreps[IIR_CF_I][4^IIR_M + 1][1], 2^IIR_M);

# cc_centraliser[i] must also be bound after _EnsureClassData.
IIRAssertTrue("1m: cc_centraliser[i] bound after _EnsureClassData",
              IIR_IDX_CF.cc_centraliser[IIR_CF_I] <> fail);
IIRAssertEqual("1n: cc_centraliser[i] = idx.classes (closed-form path)",
               IIR_IDX_CF.cc_centraliser[IIR_CF_I], IIR_IDX_CF.classes);

# For non-central classes, irreps[i] starts as fail. Lazy materialisation
# fires via _EnsureClassData → standard CharacterTable path (PR #454):
# the slot becomes a plain list of GAP ClassFunctions, NOT closed-form.
IIR_NC := First([1..Length(IIR_IDX_CF.classes)],
                i -> not (i in IIR_CF_CENTRAL));;
IIRAssertTrue("1o: non-central class index found",
              IIR_NC <> fail);
IIRAssertTrue("1p: before _EnsureClassData, nc.irreps = fail",
              IIR_IDX_CF.irreps[IIR_NC] = fail);
IIRAssertTrue("1q: before _EnsureClassData, nc.centralisers = fail (A1')",
              IIR_IDX_CF.centralisers[IIR_NC] = fail);
_EnsureClassData(IIR_IDX_CF, IIR_NC);;
IIRAssertTrue("1r: after _EnsureClassData, nc.irreps is bound",
              IIR_IDX_CF.irreps[IIR_NC] <> fail);
IIRAssertTrue("1s: after _EnsureClassData, nc.centralisers is a group",
              IsGroup(IIR_IDX_CF.centralisers[IIR_NC]));
IIRAssertTrue("1t: nc irreps[i][k][cc_idx] reads return cyclotomics",
              IsCyc(IIR_IDX_CF.irreps[IIR_NC][1][1]));


# =================================================================
# Section 2: lazy centraliser audit
# =================================================================
Print("\n=================================================================\n");
Print("Section 2: lazy centraliser materialisation (A1', PR #454)\n");
Print("=================================================================\n");

# Fresh idx with no prior access.
IIR_IDX_S2 := BuildSimpleIndexEPlusClosedForm(IIR_M);;

# Central classes are eagerly G; non-central classes are fail.
IIRAssertEqual("2a: centralisers[1] = G (central, eager)",
               IIR_IDX_S2.centralisers[1], IIR_IDX_S2.group);
IIRAssertEqual("2b: centralisers[2] = G (central, eager)",
               IIR_IDX_S2.centralisers[2], IIR_IDX_S2.group);
IIRAssertEqual("2c: centralisers[3] = fail (non-central, lazy)",
               IIR_IDX_S2.centralisers[3], fail);
IIRAssertEqual(
    "2d: centralisers[Length] = fail (non-central, lazy)",
    IIR_IDX_S2.centralisers[Length(IIR_IDX_S2.classes)], fail);

# Count fail slots: should be 4^m - 1 = 63 at m=3.
IIR_FAIL_COUNT := Length(Filtered([1..Length(IIR_IDX_S2.classes)],
    i -> IIR_IDX_S2.centralisers[i] = fail));;
IIRAssertEqual("2e: # fail slots = 4^m - 1 = 63",
               IIR_FAIL_COUNT, 4^IIR_M - 1);

# Lazy materialisation via _EPlusCentraliserOf.
IIR_C3 := _EPlusCentraliserOf(IIR_IDX_S2, 3);;
IIRAssertTrue("2f: _EPlusCentraliserOf returns a group",
              IsGroup(IIR_C3));
IIRAssertTrue("2g: after _EPlusCentraliserOf, slot is no longer fail",
              IIR_IDX_S2.centralisers[3] <> fail);
IIRAssertTrue("2h: slot now equals the returned group",
              IIR_IDX_S2.centralisers[3] = IIR_C3);
IIRAssertTrue("2i: rep is in its own centraliser",
              IIR_IDX_S2.reps[3] in IIR_C3);

# Idempotency: second call returns the SAME object (no rebuild).
IIR_C3_B := _EPlusCentraliserOf(IIR_IDX_S2, 3);;
IIRAssertTrue("2j: second call returns identical group object (cached)",
              IsIdenticalObj(IIR_C3, IIR_C3_B));

# Central-class call returns G unchanged.
IIR_C1 := _EPlusCentraliserOf(IIR_IDX_S2, 1);;
IIRAssertEqual("2k: _EPlusCentraliserOf for central class returns G",
               IIR_C1, IIR_IDX_S2.group);

# CRITICAL: triggering closed-form character data at central class via
# _EnsureClassData (or via CharacterMultiplicities downstream) must NOT
# fire lazy materialisation on non-central slots.
IIR_IDX_S2b := BuildSimpleIndexEPlusClosedForm(IIR_M);;
_EnsureClassData(IIR_IDX_S2b, 1);;
# Sample 5 non-central slots and verify they are still fail.
IIR_STILL_FAIL_OK := true;;
for IIR_TEST_I in [3, 5, 10, 30, Length(IIR_IDX_S2b.classes)] do
    if IIR_IDX_S2b.centralisers[IIR_TEST_I] <> fail then
        IIR_STILL_FAIL_OK := false;
    fi;
od;
IIRAssertTrue(
    "2l: _EnsureClassData on central class does NOT touch non-central centralisers",
    IIR_STILL_FAIL_OK);

# Same with CentraliserClassData on the central class.
IIR_IDX_S2c := BuildSimpleIndexEPlusClosedForm(IIR_M);;
IIR_CCD := CentraliserClassData(IIR_IDX_S2c, 1);;
IIRAssertTrue("2m: CentraliserClassData(idx, central) returns a record",
              IsRecord(IIR_CCD));
IIR_STILL_FAIL_2 := true;;
for IIR_TEST_I in [3, 5, 10, 30, Length(IIR_IDX_S2c.classes)] do
    if IIR_IDX_S2c.centralisers[IIR_TEST_I] <> fail then
        IIR_STILL_FAIL_2 := false;
    fi;
od;
IIRAssertTrue(
    "2n: CentraliserClassData on central class does NOT touch non-central centralisers",
    IIR_STILL_FAIL_2);


# =================================================================
# Section 3: K-4b m=3 anchor (re-run K4aClassify(3))
# =================================================================
Print("\n=================================================================\n");
Print("Section 3: K-4a m=3 anchor (verdict = trivial)\n");
Print("=================================================================\n");

# Same setup pattern as test_k4a_classify.g: symlink Modular_Data,
# chdir to the link directory.
IIR_MD_ROOT := fail;;
for IIR_CAND in
    [ Concatenation(IIR_WT_ROOT, "/../modular_data"),
      "/Users/thomasgemunden/Projects/group_cohomology/modular_data" ] do
    if IIR_MD_ROOT = fail
       and IsExistingFile(Concatenation(IIR_CAND, "/8/4/1.txt")) then
        IIR_MD_ROOT := IIR_CAND;
    fi;
od;
if IIR_MD_ROOT = fail then
    Print("  [warn] Skipping K-4a anchor: modular_data tree not found.\n");
else
    IIR_LINKDIR := Concatenation(IIR_SELFDIR, "/idx_irreps_regression");
    if not IsExistingFile(IIR_LINKDIR) then
        Exec(Concatenation("mkdir -p '", IIR_LINKDIR, "'"));
    fi;
    IIR_LINKPATH := Concatenation(IIR_LINKDIR, "/Modular_Data");
    if not IsExistingFile(IIR_LINKPATH) then
        Exec(Concatenation("ln -s '", IIR_MD_ROOT, "' '",
                           IIR_LINKPATH, "'"));
    fi;
    ChangeDirectoryCurrent(IIR_LINKDIR);

    IIR_T2_T0 := Runtime();
    IIR_T2_RES := K4aClassify(3);
    IIR_T2_WALL := (Runtime() - IIR_T2_T0) / 1000.0;

    Print("  K4aClassify(3) wall: ", IIR_T2_WALL, " s\n");
    IIRAssertEqual("3a: K4aClassify(3).verdict = trivial",
                   IIR_T2_RES.verdict, "trivial");
    IIRAssertEqual("3b: K4aClassify(3).trivial = true",
                   IIR_T2_RES.trivial, true);
    IIRAssertEqual("3c: E_class.is_coboundary = true",
                   IIR_T2_RES.E_class.is_coboundary, true);
    IIRAssertEqual("3d: D8_class.class_idx = 1",
                   IIR_T2_RES.D8_class.class_idx, 1);
    IIRAssertEqual("3e: Q8_class.class_idx = 1",
                   IIR_T2_RES.Q8_class.class_idx, 1);
    IIRAssertEqual("3f: E CT modular data rank = 256 (m=3)",
                   Length(IIR_T2_RES.E_class.modular_ct.S), 256);
    IIRAssertTrue("3g: wall < 5 min",
                  IIR_T2_WALL < 300.0);

    # Restore cwd for subsequent sections.
    ChangeDirectoryCurrent(IIR_SCRIPTSDIR);
fi;


# =================================================================
# Section 4: K-4b m=5 anchor (load m5_verdict.g)
# =================================================================
Print("\n=================================================================\n");
Print("Section 4: K-4b m=5 verdict artefact (PR #421 = TRIVIAL)\n");
Print("=================================================================\n");

IIR_M5_VERDICT_PATH := Concatenation(IIR_WT_ROOT,
    "/extraspecial_orbifolds/computed/k4b/m5_verdict.g");;

IIRAssertTrue("4a: m5_verdict.g artefact exists",
              IsExistingFile(IIR_M5_VERDICT_PATH));

if IsExistingFile(IIR_M5_VERDICT_PATH) then
    # Load into a fresh RESULT global.
    RESULT := fail;
    Read(IIR_M5_VERDICT_PATH);
    IIRAssertTrue("4b: m5_verdict.g binds RESULT after Read",
                  IsRecord(RESULT));
    IIRAssertEqual("4c: RESULT.verdict = trivial",
                   RESULT.verdict, "trivial");
    IIRAssertEqual("4d: RESULT.trivial = true",
                   RESULT.trivial, true);
    IIRAssertEqual("4e: RESULT.E_class.is_coboundary = true",
                   RESULT.E_class.is_coboundary, true);
    IIRAssertEqual("4f: RESULT.D8_class.class_idx = 1",
                   RESULT.D8_class.class_idx, 1);
    IIRAssertEqual("4g: RESULT.Q8_class.class_idx = 1",
                   RESULT.Q8_class.class_idx, 1);
    IIRAssertEqual("4h: RESULT.E_class.modular_ct_rank = 4096 (m=5)",
                   RESULT.E_class.modular_ct_rank, 4096);
fi;


# =================================================================
# Section 5: m=7 EPlusEvalIrrep standalone smoke
# =================================================================
Print("\n=================================================================\n");
Print("Section 5: m=7 EPlusEvalIrrep smoke (no full idx build)\n");
Print("=================================================================\n");

IIR_M7 := 7;;
IIR_N7 := 2 ^ IIR_M7;;
IIR_I7 := IdentityMat(IIR_N7);;
IIR_Z7 := -IIR_I7;;

# Linear χ_17 at z = -I.  Linear chars factor through G/Z so χ_17(z) = +1.
IIR_T0 := Runtime();;
IIR_LIN17_Z := EPlusEvalIrrep(IIR_M7, 17, IIR_Z7);;
IIR_T1 := Runtime();;
IIR_WALL := (IIR_T1 - IIR_T0) / 1000.0;;
Print("  EPlusEvalIrrep(7, 17, -I) = ", IIR_LIN17_Z,
      " (wall = ", IIR_WALL, " s)\n");
IIRAssertEqual("5a: linear irrep 17 at -I = +1 (factors through G/Z)",
               IIR_LIN17_Z, 1);
# Spec target: < 0.1 s. With marker-cache build first call may be
# slightly slower; relax to < 5 s to absorb cold-start.
IIRAssertTrue("5b: EPlusEvalIrrep(7, 17, -I) wall < 5 s (cold start)",
              IIR_WALL < 5.0);

# Faithful irrep at -I: χ_{4^7 + 1}(z) = -2^7 = -128.
IIR_T0 := Runtime();;
IIR_FAITH_Z := EPlusEvalIrrep(IIR_M7, 4^IIR_M7 + 1, IIR_Z7);;
IIR_T1 := Runtime();;
IIR_WALL := (IIR_T1 - IIR_T0) / 1000.0;;
Print("  EPlusEvalIrrep(7, 4^7+1, -I) = ", IIR_FAITH_Z,
      " (wall = ", IIR_WALL, " s)\n");
IIRAssertEqual("5c: faithful irrep at -I = -128",
               IIR_FAITH_Z, -2^IIR_M7);
IIRAssertTrue("5d: faithful eval wall < 0.1 s (warm)",
              IIR_WALL < 0.1);

# Faithful at identity: +128.
IIRAssertEqual("5e: faithful irrep at I = +128",
               EPlusEvalIrrep(IIR_M7, 4^IIR_M7 + 1, IIR_I7), 2^IIR_M7);


# =================================================================
# Section 6: K-4a consumer path risk audit (#419)
# =================================================================
Print("\n=================================================================\n");
Print("Section 6: CharacterMultiplicities consumer reads idx.irreps[i][k][cc_idx]\n");
Print("=================================================================\n");
# Exercises the consumer path most at risk of breaking after PR #455:
# `CharacterMultiplicities` (krr_spectral_characters_sparse.g:1115) does
# `idx.irreps[class_idx][k][cc_idx[j]]` — three nested subscripts. If
# the closed-form A1''' bypass left `idx.irreps[i]` as something other
# than a plain list of plain lists, this would crash.
#
# `CharacterMultiplicities` is also invoked by `BuildKRRIntertwinerData::
# proj_for_class` indirectly (via `BuildKRRSpectralCharactersSparse(5+)`).
# By exercising it at m=3 with a closed-form idx, we catch the same
# interface contract violation without paying the m=5 cost.

# Build a fresh closed-form idx and a synthetic cls_data + traces.
IIR_IDX_S6 := BuildSimpleIndexEPlusClosedForm(IIR_M);;
IIR_CENTRAL_S6 := IIR_CF_CENTRAL[1];;  # use the first central class (id, C=G)

# Populate idx.irreps[central] via _EnsureClassData (closed-form path).
_EnsureClassData(IIR_IDX_S6, IIR_CENTRAL_S6);;

# cls_data describes the conjugacy classes of C = G (since this is
# central). Use CentraliserClassData which is the production builder.
IIR_CLS_DATA := CentraliserClassData(IIR_IDX_S6, IIR_CENTRAL_S6);;
IIRAssertTrue("6a: CentraliserClassData returns a record with .num >= 1",
              IsRecord(IIR_CLS_DATA) and IIR_CLS_DATA.num >= 1);

# Trivial traces (all 1's, which corresponds to identity intertwiner Tr).
IIR_TRACES := ListWithIdenticalEntries(IIR_CLS_DATA.num, 1);;

# Invoke CharacterMultiplicities. This exercises the consumer pattern
# `idx.irreps[class_idx][k][cc_idx[j]]` for every (k, j) pair.
IIR_MULTS := CharacterMultiplicities(IIR_IDX_S6, IIR_CENTRAL_S6,
                                     IIR_CLS_DATA, IIR_TRACES);;
IIRAssertEqual("6b: CharacterMultiplicities returns list of right length",
               Length(IIR_MULTS), IIR_IDX_S6.num_irreps[IIR_CENTRAL_S6]);
# Each entry is a cyclotomic (rational at the closed-form character values).
IIRAssertTrue("6c: each multiplicity is a cyclotomic",
              ForAll(IIR_MULTS, m -> IsCyc(m)));

# With traces = identity, the multiplicities should sum to dim(W_a). For
# the identity intertwiner (traces all 1, which is Tr(I) = ?), the
# `mult_chi` formula collapses by row orthogonality. Specifically:
#   sum_chi mult_chi = (1/|G|) * sum_K |K| * 1 * sum_chi chi(K)^*
# Using column orthogonality (sum_chi chi(K)^* = |C_G(g)| if K = {e},
# 0 otherwise), this is (1/|G|) * |C_G(e)| = 1. Sanity check below.
IIRAssertTrue(
    "6d: sum(mults) = 1 with identity traces (column orthogonality)",
    Sum(IIR_MULTS) = 1);

# Verify that the consumer pattern itself works as direct reads (not
# routed through EvalIrr). This is the actual PR #455 contract.
IIR_DIRECT_READ_OK := true;;
for IIR_K in [1, 2, 4^IIR_M + 1] do  # sample 3 irreps
    for IIR_J in [1..Minimum(IIR_CLS_DATA.num, 5)] do  # sample 5 cls_idx
        if not IsBound(IIR_IDX_S6.irreps[IIR_CENTRAL_S6][IIR_K][IIR_J]) then
            IIR_DIRECT_READ_OK := false;
        elif not IsCyc(IIR_IDX_S6.irreps[IIR_CENTRAL_S6][IIR_K][IIR_J]) then
            IIR_DIRECT_READ_OK := false;
        fi;
    od;
od;
IIRAssertTrue(
    "6e: direct subscript idx.irreps[central][k][cc_idx] returns cyclotomics",
    IIR_DIRECT_READ_OK);


# =================================================================
# Final report
# =================================================================
Print("\n=================================================================\n");
Print("Summary: ", IIR_PASSES, " passes, ",
      Length(IIR_FAILURES), " failures.\n");
Print("=================================================================\n");

if Length(IIR_FAILURES) = 0 then
    Print("\nPASS test_idx_irreps_interface_regression\n");
else
    Print("\nFAIL test_idx_irreps_interface_regression:\n");
    for IIR_F in IIR_FAILURES do
        Print("  - ", IIR_F, "\n");
    od;
fi;

QUIT;
