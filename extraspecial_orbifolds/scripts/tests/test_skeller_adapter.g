# K-2 verification driver for `skeller_adapter.g`.
#
# Acceptance criteria (from issue #39):
#   - For m = 3 on central-row entries: agrees with V-2's S^omega for
#     omega = 0 within numerical tolerance (1e-12).
#   - For m = 7: completes a query in <= 5 minutes.
#
# V-2 dependency note: V-2 is not implemented yet. At omega = 0 the V-2
# closed form for central rows reduces to the standard untwisted S-matrix
# entry, so we use the dense untwisted S (via `ComputeSBlock` from
# `untwisted_modular_data.g`) as the V-2 stand-in. This is the same
# ground truth K-1's tests validated.
#
# Tolerance note: SKeller and ComputeSBlock both produce cyclotomic
# numbers (no float roundoff), so the comparison `a = b` is exact when
# the two sides agree. The "<= 1e-12" criterion is therefore satisfied
# trivially whenever the equality test passes. We report the mismatch
# count as the primary metric; when 0 the numerical deviation is
# identically 0 by construction.
#
# Run from the scripts/ directory:
#   gap -q -b -A tests/test_skeller_adapter.g

BreakOnError := false;
SetInfoLevel(InfoWarning, 0);

# ----- load all dependencies, in order -----
Read("em_construction.g");
Read("untwisted_modular_data.g");
Read("krr_projector.g");
Read("skeller_adapter.g");


# ---------------------------------------------------------------
# Test A: sanity — index decode round-trip on E_+(3)
# ---------------------------------------------------------------
Print("\n=================================================================\n");
Print("  Test A: index decode / encode round-trip (E_+(3))\n");
Print("=================================================================\n");

t0 := Runtime();;
rank3 := SKellerRank(3);;
Print("rank(Z(Vec_{E_+(3)})) = ", rank3, "  (cache build ",
      Runtime() - t0, " ms)\n");

testA_ok := true;;
for i in [1, 2, 17, 100, 500, 1000, rank3 - 1, rank3] do
    pair := SKellerDecodeIndex(3, i);;
    iback := SKellerEncodeIndex(3, pair[1], pair[2]);;
    if iback <> i then
        Print("  FAIL: i = ", i, " -> ", pair, " -> ", iback, "\n");
        testA_ok := false;
    fi;
od;
Print("Decode/encode round-trip on 8 indices: ", testA_ok, "\n");

# Range guard: SKellerDecodeIndex must error on i = 0 and i = rank+1.
errLow := CALL_WITH_CATCH(SKellerDecodeIndex, [3, 0]);;
errHigh := CALL_WITH_CATCH(SKellerDecodeIndex, [3, rank3 + 1]);;
Print("Out-of-range guard (low):  ", not errLow[1], "\n");
Print("Out-of-range guard (high): ", not errHigh[1], "\n");
testA_ok := testA_ok and (not errLow[1]) and (not errHigh[1]);;


# ---------------------------------------------------------------
# Test B: m = 3 central-row agreement vs dense untwisted S
#         (V-2 stand-in: ComputeSBlock from untwisted_modular_data.g)
#
# We compute each (class_i, class_j) block of the untwisted S via
# ComputeSBlock, then for every entry of that block ask the adapter
# SKeller(3, gi, gj) for the same value via global indices. Exact
# (cyclotomic) equality is the pass condition. This both:
#   - validates the index-decoding logic of the adapter, and
#   - confirms the agreement with the V-2 stand-in.
# ---------------------------------------------------------------
Print("\n=================================================================\n");
Print("  Test B: m = 3 central-row agreement (acceptance criterion)\n");
Print("=================================================================\n");

entry3 := SKellerGetCache(3);;
data3 := entry3.data;;
idx3 := data3.idx;;
Print("E_+(3): order ", Order(entry3.group),
      ", classes ", Length(idx3.classes),
      ", rank ", idx3.rank, "\n");

# Recover the list of central class indices.
central3 := SKellerCentralRowIndices(3);;
# `SKellerCentralRowIndices` returns *global* indices; we also need
# the underlying class indices. Use the index decode.
central3_classes := [];;
for i in [1..Length(idx3.classes)] do
    if idx3.class_sizes[i] <> 1 then continue; fi;
    g := idx3.reps[i];;
    ok := true;;
    for h in GeneratorsOfGroup(idx3.group) do
        if g * h <> h * g then ok := false; break; fi;
    od;
    if ok then Add(central3_classes, i); fi;
od;
Print("Central class indices: ", central3_classes, "  (",
      Length(central3_classes), " central singletons)\n");
Print("Central-row global indices: ", Length(central3),
      " in total\n");

t0 := Runtime();;
totalMismatch := 0;;
totalEntries := 0;;
maxDelta := "0 (cyclotomic equality)";;

for ci in central3_classes do
    Print("  Central class ", ci, ": sweeping ", Length(idx3.classes),
          " right classes...\n");
    for cj in [1..Length(idx3.classes)] do
        blockS := ComputeSBlock(idx3, data3.transport, ci, cj);;
        Ni := idx3.num_irreps[ci];;
        Nj := idx3.num_irreps[cj];;
        totalEntries := totalEntries + Ni * Nj;
        for k1 in [1..Ni] do
            for k2 in [1..Nj] do
                gi := SKellerEncodeIndex(3, ci, k1);;
                gj := SKellerEncodeIndex(3, cj, k2);;
                vK := SKeller(3, gi, gj);;
                vS := blockS[k1][k2];;
                if vK <> vS then
                    totalMismatch := totalMismatch + 1;
                    if totalMismatch <= 3 then
                        Print("    MISMATCH at i=", gi, ", j=", gj,
                              " ((", ci, ",", k1, "),(", cj, ",", k2,
                              ")): SKeller=", vK, ", S^0=", vS, "\n");
                    fi;
                fi;
            od;
        od;
    od;
od;
t1 := Runtime();;
Print("Central-row entries checked: ", totalEntries,
      ", mismatches: ", totalMismatch,
      "  (", t1 - t0, " ms = ", (t1 - t0) / 1000., " s)\n");
Print("Max numerical deviation (cyclotomic): ", maxDelta, "\n");
testB_ok := totalMismatch = 0;;
Print("Test B PASS: ", testB_ok, "\n");


# ---------------------------------------------------------------
# Test C: m = 7 single-query timing (best effort, stretch goal).
#
# m = 7 has |E_+(7)| = 2^15 = 32768. Building intertwiner data alone is
# potentially very expensive: transports call RepresentativeAction for
# every element of every class (and the inner sum of the projector
# formula iterates over commuting pairs of class elements, which can be
# enormous for large centralisers).
#
# Per the K-2 issue body: "the 5-minute budget for m=7 may require
# optimization — for now, just verify it works at m=3 in tolerance, and
# let m=7 be a stretch goal." We make a guarded attempt.
# ---------------------------------------------------------------
Print("\n=================================================================\n");
Print("  Test C: m = 7 single-query timing (stretch goal)\n");
Print("=================================================================\n");

# Budget for the cache build + single-entry query, in ms.
BUDGET_MS := 5 * 60 * 1000;;   # 5 minutes

m7Attempted := false;;
m7Built := false;;
m7Query := fail;;
m7BuildMs := fail;;
m7QueryMs := fail;;

if not IsBoundGlobal("SKELLER_SKIP_M7") then
    BindGlobal("SKELLER_SKIP_M7", false);
fi;

if SKELLER_SKIP_M7 then
    Print("Skipping m=7 by SKELLER_SKIP_M7=true.\n");
else
    Print("Attempting m=7. Building cache (this may take a while)...\n");
    m7Attempted := true;
    t0 := Runtime();;
    catch := CALL_WITH_CATCH(SKellerGetCache, [7]);;
    t1 := Runtime();;
    m7BuildMs := t1 - t0;;
    if not catch[1] then
        Print("  Cache build FAILED with error: ", catch[2], "\n");
        Print("  Build time before failure: ", m7BuildMs, " ms\n");
    else
        m7Built := true;
        Print("  Cache build: ", m7BuildMs, " ms (",
              m7BuildMs / 1000., " s)\n");
        Print("  rank = ", catch[2].rank, "\n");
        Print("Querying SKeller(7, 1, 1) ...\n");
        t0 := Runtime();;
        catch2 := CALL_WITH_CATCH(SKeller, [7, 1, 1]);;
        t1 := Runtime();;
        m7QueryMs := t1 - t0;;
        if not catch2[1] then
            Print("  Query FAILED with error: ", catch2[2], "\n");
        else
            m7Query := catch2[2];
            Print("  SKeller(7, 1, 1) = ", m7Query, "\n");
            Print("  Query time: ", m7QueryMs, " ms (",
                  m7QueryMs / 1000., " s)\n");
        fi;
    fi;
fi;

testC_ok := m7Attempted and m7Built and (m7Query <> fail)
            and (m7QueryMs <> fail) and (m7QueryMs <= BUDGET_MS);;
Print("Test C result (m=7 query within ", BUDGET_MS / 1000.,
      " s budget): ", testC_ok, "\n");
if m7Attempted and m7Built and m7Query <> fail and not testC_ok then
    Print("  (m=7 succeeded but exceeded the 5-min budget. ",
          "Optimisation deferred — see issue body 'm = 7 is a ",
          "stretch goal'.)\n");
fi;


# ---------------------------------------------------------------
# Summary
# ---------------------------------------------------------------
Print("\n=================================================================\n");
Print("  Summary\n");
Print("=================================================================\n");
Print("Test A (decode/encode round-trip):                  ", testA_ok, "\n");
Print("Test B (m=3 central-row agreement, acceptance):     ", testB_ok, "\n");
Print("Test C (m=7 single-query <= 5 min, stretch goal):   ", testC_ok, "\n");

acceptancePass := testA_ok and testB_ok;;
Print("\nK-2 acceptance criteria (omega=0 m=3 central rows): ",
      acceptancePass, "\n");
if testC_ok then
    Print("K-2 stretch goal (m=7 within 5 min): PASS\n");
else
    Print("K-2 stretch goal (m=7 within 5 min): not met (see above)\n");
fi;

if acceptancePass then
    Print("\nK-2 ADAPTER: index decoding works and m=3 central rows ",
          "match S^0 exactly (V-2 stand-in).\n");
else
    Print("\nK-2 FAILURE: see mismatches above.\n");
fi;

QUIT;
