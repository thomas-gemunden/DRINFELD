# K-1 verification driver for `krr_projector.g`.
#
# Acceptance criterion (from issue #20):
#   For omega = 0 at m = 3: ProjectorFormula entries on central-row index
#   pairs agree with the dense untwisted S exactly.
#
# Strategy:
#   - We test on E_+(3) = SmallGroup(128, 2326). For m = 3 the dense
#     untwisted S is rank 2272 and computing it row-by-row would take
#     significant time, so we use the per-block helper `ComputeSBlock`
#     from `untwisted_modular_data.g` to compute the *(class_1, class_2)*
#     blocks we sample, and check ProjectorFormula matches every entry
#     of those blocks.
#   - Central rows in E_+(m) are indexed by g_1 in {1, -1}. Both are
#     singleton conjugacy classes, so for any class j we sample both the
#     (1, j) and (-1, j) blocks (where 1, -1 means central reps).
#   - For belt-and-braces coverage we also run the same comparison on
#     E_+(2) where the full dense S is cheap.
#
# Run from the scripts/ directory:
#   gap -q -b -c 'Read("tests/test_krr_projector.g");'

SetInfoLevel(InfoWarning, 0);

Read("untwisted_modular_data.g");
Read("krr_projector.g");

# ---------------------------------------------------------------
# Helper: identify the "central" classes (singletons in conjugacy)
# whose representative is central in G.
# Returns list of class indices i such that idx.class_sizes[i] = 1
# and idx.reps[i] is central (i.e. commutes with all of G).
# ---------------------------------------------------------------
CentralClassIndices := function(idx)
    local out, i, g, gens, ok, h;
    out := [];
    gens := GeneratorsOfGroup(idx.group);
    for i in [1..Length(idx.classes)] do
        if idx.class_sizes[i] <> 1 then continue; fi;
        g := idx.reps[i];
        ok := true;
        for h in gens do
            if g * h <> h * g then ok := false; break; fi;
        od;
        if ok then Add(out, i); fi;
    od;
    return out;
end;;

# ---------------------------------------------------------------
# Single block check: ProjectorFormula vs ComputeSBlock for class
# pair (i, j). Returns the number of mismatched entries.
# ---------------------------------------------------------------
CheckBlock := function(intertwiner_data, i, j)
    local idx, blockS, mismatches, k1, k2, vP, vS;
    idx := intertwiner_data.idx;
    blockS := ComputeSBlock(idx, intertwiner_data.transport, i, j);
    mismatches := 0;
    for k1 in [1..idx.num_irreps[i]] do
        for k2 in [1..idx.num_irreps[j]] do
            vP := ProjectorFormulaByIndex(i, k1, j, k2, intertwiner_data);
            vS := blockS[k1][k2];
            if vP <> vS then
                mismatches := mismatches + 1;
                if mismatches <= 3 then
                    Print("    MISMATCH at (i=", i, ", k1=", k1,
                          ", j=", j, ", k2=", k2, "): projector = ",
                          vP, ", block = ", vS, "\n");
                fi;
            fi;
        od;
    od;
    return mismatches;
end;;

# ---------------------------------------------------------------
# Test 0: E_+(2) — full grid sanity check
# ---------------------------------------------------------------
Print("\n=================================================================\n");
Print("  Test 0: E_+(2) full-grid sanity check (rank 184)\n");
Print("=================================================================\n");

G2 := SmallGroup(32, 49);;
data2 := BuildIntertwinerDataUntwisted(G2);;
Print("E_+(2): order ", Order(G2),
      ", classes ", Length(data2.idx.classes),
      ", rank ", data2.idx.rank, "\n");
central2 := CentralClassIndices(data2.idx);;
Print("Central class indices: ", central2, "  (",
      Length(central2), " central singletons)\n");

t0 := Runtime();;
totalMismatch2 := 0;;
totalEntries2 := 0;;
for i in central2 do
    for j in [1..Length(data2.idx.classes)] do
        totalEntries2 := totalEntries2 +
            data2.idx.num_irreps[i] * data2.idx.num_irreps[j];
        totalMismatch2 := totalMismatch2 + CheckBlock(data2, i, j);
    od;
od;
t1 := Runtime();;
Print("Central-row entries checked: ", totalEntries2,
      ", mismatches: ", totalMismatch2,
      "  (", t1 - t0, " ms)\n");

test0Pass := totalMismatch2 = 0;;
Print("Test 0 PASS: ", test0Pass, "\n");

# ---------------------------------------------------------------
# Test 1: E_+(3) — central-row entries against ComputeSBlock
#         (this is the issue's headline acceptance test)
# ---------------------------------------------------------------
Print("\n=================================================================\n");
Print("  Test 1: E_+(3) central-row entries (acceptance criterion)\n");
Print("=================================================================\n");

G3 := SmallGroup(128, 2326);;
data3 := BuildIntertwinerDataUntwisted(G3);;
Print("E_+(3): order ", Order(G3),
      ", classes ", Length(data3.idx.classes),
      ", rank ", data3.idx.rank, "\n");
central3 := CentralClassIndices(data3.idx);;
Print("Central class indices: ", central3, "  (",
      Length(central3), " central singletons)\n");

t0 := Runtime();;
totalMismatch3 := 0;;
totalEntries3 := 0;;
for i in central3 do
    Print("  Central class ", i, ": checking blocks vs each of ",
          Length(data3.idx.classes), " right classes...\n");
    for j in [1..Length(data3.idx.classes)] do
        totalEntries3 := totalEntries3 +
            data3.idx.num_irreps[i] * data3.idx.num_irreps[j];
        totalMismatch3 := totalMismatch3 + CheckBlock(data3, i, j);
    od;
od;
t1 := Runtime();;
Print("Central-row entries checked: ", totalEntries3,
      ", mismatches: ", totalMismatch3,
      "  (", t1 - t0, " ms = ", (t1 - t0) / 1000., " s)\n");

test1Pass := totalMismatch3 = 0;;
Print("Test 1 PASS: ", test1Pass, "\n");

# ---------------------------------------------------------------
# Test 2: E_+(3) — sanity-check non-central row triples to confirm
#         the formula is generally correct, not just on central rows.
# ---------------------------------------------------------------
Print("\n=================================================================\n");
Print("  Test 2: E_+(3) sample non-central-row blocks (sanity)\n");
Print("=================================================================\n");

# Sample a few non-central classes; compare each against a few right
# classes only (don't sweep the whole grid).
nonCentral := Filtered([1..Length(data3.idx.classes)],
                        i -> not (i in central3));;
sample_i := nonCentral{[1, QuoInt(Length(nonCentral), 2),
                        Length(nonCentral)]};;
sample_j := [1, central3[2], nonCentral[1],
             nonCentral[QuoInt(Length(nonCentral), 2)]];;
Print("Sampling i in ", sample_i, "  x  j in ", sample_j, "\n");
t0 := Runtime();;
totalMismatch4 := 0;;
totalEntries4 := 0;;
for i in sample_i do
    for j in sample_j do
        totalEntries4 := totalEntries4 +
            data3.idx.num_irreps[i] * data3.idx.num_irreps[j];
        totalMismatch4 := totalMismatch4 + CheckBlock(data3, i, j);
    od;
od;
t1 := Runtime();;
Print("Sampled entries checked: ", totalEntries4,
      ", mismatches: ", totalMismatch4,
      "  (", t1 - t0, " ms)\n");

test2Pass := totalMismatch4 = 0;;
Print("Test 2 PASS: ", test2Pass, "\n");

# ---------------------------------------------------------------
# Summary
# ---------------------------------------------------------------
Print("\n=================================================================\n");
Print("  Summary\n");
Print("=================================================================\n");
Print("Test 0 (E_+(2) central rows full-grid):  ", test0Pass, "\n");
Print("Test 1 (E_+(3) central rows full-grid):  ", test1Pass, "\n");
Print("Test 2 (E_+(3) non-central sample):      ", test2Pass, "\n");

allPass := test0Pass and test1Pass and test2Pass;;
Print("\nAll tests pass: ", allPass, "\n");

if allPass then
    Print("\nK-1 ACCEPTANCE: PROJECTOR FORMULA IS CORRECT FOR omega = 0.\n");
else
    Print("\nK-1 FAILURE: see mismatches above.\n");
fi;

QUIT;
