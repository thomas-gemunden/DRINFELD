# test_gauge_invariants.g
#
# Smoke test for gauge_invariants_wrapper.g (V-4 #16, task #52).
#
# Acceptance criteria (issue #16):
#   1. `GaugeInvariants(Q_8)` runs without error and returns a record with the
#      documented shape.
#   2. Output for the trivial cocycle agrees with element-wise invocation of
#      `FSIforDoubles` on a sample of simples.
#
# Mathematical caveat (issue #81): HAP's `StandardCocycle` does not satisfy the
# bar 3-cocycle equation for non-trivial omega on Q_8.  We therefore restrict
# correctness tests to omega = 0.  The wrapper still runs end-to-end at omega != 0
# for completeness, but we only spot-check that it doesn't crash; we don't
# pin numerical values.

# --- locate gauge_invariants_wrapper.g (no chdir) -------------------------
gaugeWrapper := fail;;
for gaugeCand in [".", "..", "../..", "../../..", "../../../..",
                  "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-v4"] do
    if IsExistingFile(Concatenation(gaugeCand, "/extraspecial_orbifolds/scripts/gauge_invariants_wrapper.g")) then
        gaugeWrapper := Concatenation(gaugeCand, "/extraspecial_orbifolds/scripts/gauge_invariants_wrapper.g");
        break;
    fi;
od;;
if gaugeWrapper = fail then
    Error("test_gauge_invariants.g: could not locate gauge_invariants_wrapper.g");
fi;
Read(gaugeWrapper);;


# --- helpers --------------------------------------------------------------
giPass := 0;;
giFail := 0;;
giAssertEqual := function(label, actual, expected)
    if actual = expected then
        Print("  OK   ", label, "  =  ", actual, "\n");
        giPass := giPass + 1;
        return true;
    else
        Print("  FAIL ", label, "  actual=", actual, "  expected=", expected, "\n");
        giFail := giFail + 1;
        return false;
    fi;
end;;
giAssertTrue := function(label, cond)
    if cond then
        Print("  OK   ", label, "\n");
        giPass := giPass + 1;
        return true;
    else
        Print("  FAIL ", label, "\n");
        giFail := giFail + 1;
        return false;
    fi;
end;;


# --- Stage 1: Q_8 = SmallGroup(8, 4) --------------------------------------
Print("\n=== Stage 1: Q_8 = SmallGroup(8,4) ===\n");
giQ8 := SmallGroup(8, 4);;
giAssertEqual("Q_8 is the quaternion group", StructureDescription(giQ8), "Q8");


# --- Stage 2: GaugeInvariants(Q_8) end-to-end -----------------------------
#
# Acceptance #1: runs without error, returns a record with the documented
# shape.  We measure time too; this is a moderately heavy computation but
# expected to complete in well under a minute on Q_8.
Print("\n=== Stage 2: GaugeInvariants(Q_8) runs end-to-end ===\n");
giT0 := Runtime();;
giRes := GaugeInvariants(giQ8);;
giT1 := Runtime();;
Print("  GaugeInvariants(Q_8) elapsed (ms): ", giT1 - giT0, "\n");

# Shape checks.
giAssertTrue("result is a record", IsRecord(giRes));
giAssertTrue("result has UCT field", IsBound(giRes.UCT));
giAssertTrue("result has orbits field", IsBound(giRes.orbits));
giAssertTrue("result has representatives field", IsBound(giRes.representatives));
giAssertTrue("result has Table field", IsBound(giRes.Table));
giAssertTrue("orbits is a list", IsList(giRes.orbits));
giAssertTrue("representatives is a list", IsList(giRes.representatives));
giAssertTrue("Table is a list", IsList(giRes.Table));
giAssertEqual("len(orbits) = len(representatives)",
              Size(giRes.orbits), Size(giRes.representatives));
giAssertEqual("len(Table) = len(orbits)",
              Size(giRes.Table), Size(giRes.orbits));

# Each Table entry is [rep, FSlist, Collected[...]] -- check first one.
giE1 := giRes.Table[1];;
giAssertTrue("Table[1] has 3 entries", Size(giE1) = 3);
giAssertTrue("Table[1][1] is a list (cocycle rep)", IsList(giE1[1]));
giAssertTrue("Table[1][2] is a list (FSlist starting with 0)",
             IsList(giE1[2]) and giE1[2][1] = 0);
giAssertTrue("Table[1][3] is a list (Collected)", IsList(giE1[3]));

Print("  H^3(Q_8) orbit count under Aut(Q_8): ", Size(giRes.orbits), "\n");
Print("  representatives: ", giRes.representatives, "\n");
for giIdx in [1..Size(giRes.Table)] do
    Print("  orbit ", giIdx, ": rep=", giRes.Table[giIdx][1],
          ", FSlist=", giRes.Table[giIdx][2],
          ", #distinct invariant-tuples=", Size(giRes.Table[giIdx][3]), "\n");
od;


# --- Stage 3: cross-check trivial cocycle against direct FSIforDoubles ----
#
# Acceptance #2: GaugeInvariants(Q_8) at the trivial (omega = 0) orbit agrees
# with element-wise invocation of FSIforDoubles on a sample of simples.
#
# The trivial orbit is the one whose representative is the zero hom-vector.
Print("\n=== Stage 3: trivial-cocycle agreement vs FSIforDoubles ===\n");

# Locate the trivial orbit by finding the all-zero representative.
giTrivIdx := fail;;
for giIdx in [1..Size(giRes.representatives)] do
    if ForAll(giRes.representatives[giIdx], x -> x = 0) then
        giTrivIdx := giIdx;
        break;
    fi;
od;;
giAssertTrue("trivial orbit located", giTrivIdx <> fail);

# Build the corresponding hom-vector (also all zero).
giUCT := giRes.UCT;;
giTrivHom := List(giRes.UCT!.hombasis, x -> 0);;

# Build the un-aggregated table for comparison.
giRaw := GaugeInvariantsRaw(giQ8, giTrivHom);;
Print("  raw #classes: ", Size(giRaw.classes), "\n");
Print("  raw FSlist:   ", giRaw.FSlist, "\n");

# Sanity: should be 5 classes (Q_8 has 5 conjugacy classes).
giAssertEqual("Q_8 has 5 conjugacy classes", Size(giRaw.classes), 5);

# Compare GaugeInvariantsRaw against direct element-wise FSIforDoubles on a
# *sample* of (class, chi, m) triples.  We do this via the V-3 wrapper's
# FSIAllAtClass and via the raw FSIforDoubles call too.
#
# Sample selection: for each conjugacy class, take chi_index = 1
# (first projective character) and m = 2 (classical Frobenius-Schur).
Print("  --- sample cross-check (chi_index=1, m=2, all classes) ---\n");

giCtxTriv := giRaw.ctx;;
giFSm := 2;;
for giClassIdx in [1..Size(giRaw.classes)] do
    giClass := giRaw.classes[giClassIdx];;
    # Pull the GaugeInvariants result for (this class, chi=1, m=2).
    # Need the m=2 column in FSlist.
    giMIdx := Position(giRaw.FSlist, giFSm);;
    if giMIdx = fail then
        Print("    skipping class ", giClassIdx, " (m=2 not in FSlist=",
              giRaw.FSlist, ")\n");
        continue;
    fi;
    giNuFromGauge := giRaw.indicators[giClassIdx][1][giMIdx];;
    # Direct call to FSIforDoubles.
    giProjDirect := giRaw.PC[giClassIdx];;
    giNuDirect := FSIforDoubles(
        giCtxTriv.G, giCtxTriv.f, giClass, giProjDirect, 1, giCtxTriv.exp,
        giCtxTriv.listG, List(giCtxTriv.listG, x ->
            ValuesOfPiSymbols(giCtxTriv.G, giCtxTriv.R, giCtxTriv.K,
                              giCtxTriv.UCT, x, giCtxTriv.f)),
        giFSm);;
    giAssertEqual(Concatenation("class ", String(giClassIdx),
                                ", chi=1, m=2 (GaugeInvariants vs FSIforDoubles)"),
                  giNuFromGauge, giNuDirect);
od;

# Stronger check: at omega = 0 the identity class g=1 should give the classical
# FS indicators of Q_8, namely the multiset [+1,+1,+1,+1,-1] (four 1-dim real
# reps + one quaternionic 2-dim rep), at m=2.
Print("  --- classical FS indicators at g=1, m=2 ---\n");
giOneIdx := fail;;
for giClassIdx in [1..Size(giRaw.classes)] do
    if Order(giRaw.classes[giClassIdx]) = 1 then
        giOneIdx := giClassIdx;
        break;
    fi;
od;;
giAssertTrue("identity class located", giOneIdx <> fail);

giMIdx2 := Position(giRaw.FSlist, 2);;
giNuAtId := List(giRaw.indicators[giOneIdx], xs -> xs[giMIdx2]);;
Print("  nu_2 at g=1 (per chi): ", giNuAtId, "\n");
giAssertEqual("nu_2 at g=1 multiset (Q_8, omega=0)",
              Collected(giNuAtId), Collected([1, 1, 1, 1, -1]));


# --- Stage 4: Collected aggregation parity --------------------------------
#
# The aggregated `Table[trivIdx][3]` should be the Collected of the
# concatenated indicators+twist rows across all classes.  Verify this matches
# what we'd build from `giRaw`.
Print("\n=== Stage 4: Collected aggregation parity (trivial cocycle) ===\n");
giFSlist := giRaw.FSlist;;
giCols := Size(giFSlist);;
giRowsFromRaw := [];;
for giClassIdx in [1..Size(giRaw.classes)] do
    for giChiIdx in [1..Size(giRaw.PC[giClassIdx]!.table)] do
        giRow := Concatenation(
            giRaw.indicators[giClassIdx][giChiIdx],
            [giRaw.twist[giClassIdx][giChiIdx]]);;
        Add(giRowsFromRaw, giRow);
    od;
od;;

# GaugeInvariants does SortParallel(indicators, twist) before concatenating.
# Replicate: sort indicators with twist in parallel, then concatenate per-row.
giIndicatorsFlat := [];;
giTwistFlat := [];;
for giClassIdx in [1..Size(giRaw.classes)] do
    for giChiIdx in [1..Size(giRaw.PC[giClassIdx]!.table)] do
        Add(giIndicatorsFlat, giRaw.indicators[giClassIdx][giChiIdx]);
        Add(giTwistFlat, giRaw.twist[giClassIdx][giChiIdx]);
    od;
od;;
SortParallel(giIndicatorsFlat, giTwistFlat);;
giRowsSorted := List([1..Size(giIndicatorsFlat)], i ->
    Concatenation(giIndicatorsFlat[i], [giTwistFlat[i]]));;
giCollectedExpected := Collected(giRowsSorted);;
giCollectedActual := giRes.Table[giTrivIdx][3];;
giAssertEqual("Collected aggregation matches",
              giCollectedActual, giCollectedExpected);


# --- Stage 5: cross-check with V-3 wrapper's FSIAllAtClass ---------------
#
# This is a third independent route to nu values: the V-3 wrapper's
# FSIAllAtClass uses its own (correct) FSIContext.  Compare to giRaw.
Print("\n=== Stage 5: cross-check vs V-3 FSIAllAtClass ===\n");
giMIdx3 := Position(giRaw.FSlist, 2);;
for giClassIdx in [1..Size(giRaw.classes)] do
    giClass := giRaw.classes[giClassIdx];;
    giV3 := FSIAllAtClass(giCtxTriv, giClass, 2);;
    giFromRaw := List([1..Size(giRaw.PC[giClassIdx]!.table)],
                     j -> giRaw.indicators[giClassIdx][j][giMIdx3]);;
    giAssertEqual(Concatenation("class ", String(giClassIdx),
                                " nu_2 vector vs FSIAllAtClass"),
                  giFromRaw, giV3.nu);
od;


# --- summary --------------------------------------------------------------
Print("\n=== summary ===\n");
Print("  passed: ", giPass, "    failed: ", giFail, "\n");
if giFail > 0 then
    Print("  STATUS: FAIL\n");
    QUIT_GAP(1);
else
    Print("  STATUS: PASS\n");
fi;
