# test_quillen_h3_structure.g — Stage A acceptance for Quillen integration.
#
# Verifies that `QuillenH3Structure(m)` for m in {1, 2, 3} matches the
# HAP `SetupCohomology3` torsion exactly. The HAP value is the
# established ground truth (verified by the D_8 and E_+(2) anchors).
#
# Run from extraspecial_orbifolds/scripts/:
#   gap -q -b -c 'Read("tests/test_quillen_h3_structure.g");'

BreakOnError := false;;
SetInfoLevel(InfoWarning, 0);

Read("transgression_kernel.g");
Read("quillen_h3_structure.g");

Print("\n=== test_quillen_h3_structure.g (Quillen integration Stage A) ===\n");

testFailures := [];;

# Local ternary helper (matches the idiom in other scripts).
If_ := function(c, a, b) if c then return a; else return b; fi; end;;

AssertOrLog := function(label, cond)
    Print("  ", label, ": ", If_(cond, "PASS", "FAIL"), "\n");
    if not cond then Add(testFailures, label); fi;
end;;

# --------------------------------------------------------------------
# Helper: group constructor for E_+(m) at m = 1, 2, 3.
# --------------------------------------------------------------------

EPlus_SmallGroup := function(m)
    if m = 1 then return SmallGroup(8, 3); fi;
    if m = 2 then return SmallGroup(32, 49); fi;
    if m = 3 then return SmallGroup(128, 2326); fi;
    Error("EPlus_SmallGroup: m must be in {1, 2, 3} for HAP cross-check");
end;;

# --------------------------------------------------------------------
# For each m in {1, 2, 3}:
#   - Build the HAP setup, extract torsion + sort canonically.
#   - Compare against QuillenH3Structure(m).torsion (canonically sorted).
# --------------------------------------------------------------------

for m_iter in [1, 2, 3] do
    Print("\n--- m = ", m_iter, " ---\n");
    G := EPlus_SmallGroup(m_iter);
    setup := SetupCohomology3(G);;
    hap_torsion := ShallowCopy(setup.torsion);;
    Sort(hap_torsion);

    qstruct := QuillenH3Structure(m_iter);;
    quillen_torsion := ShallowCopy(qstruct.torsion);;
    Sort(quillen_torsion);

    Print("  HAP torsion (sorted):     ", hap_torsion, "\n");
    Print("  Quillen torsion (sorted): ", quillen_torsion, "\n");
    AssertOrLog(
        Concatenation("torsion m=", String(m_iter)),
        hap_torsion = quillen_torsion);
    AssertOrLog(
        Concatenation("exponent m=", String(m_iter)),
        qstruct.exponent = setup.exponent);
    AssertOrLog(
        Concatenation("num_generators m=", String(m_iter)),
        qstruct.num_generators = setup.num_generators);
od;

# --------------------------------------------------------------------
# Q-int A2 (#136): m = 5, 7 now derived analytically via Harada-Kono
# 1987 Thm 1.1 + Bockstein on the Q-2a canonical presentation.
# Expected shape: [(Z/2)^r, Z/4] with r determined by dim ker β_4 - 1.
# --------------------------------------------------------------------

Print("\n--- m = 3 derived path matches hardcoded ---\n");

if not IsBoundGlobal("QuillenH4TorsionFromBockstein") then
    Read("quillen_h4_torsion.g");
fi;
derived_m3 := QuillenH4TorsionFromBockstein(3);;
hardcoded_m3 := Concatenation(ListWithIdenticalEntries(34, 2), [4]);;
AssertOrLog("m=3 Bockstein-derived torsion matches hardcoded",
            derived_m3 = hardcoded_m3);

Print("\n--- m = 5 (Bockstein-derived) ---\n");
qstruct_m5 := QuillenH3Structure(5);;
Print("  torsion length: ", qstruct_m5.num_generators, "\n");
Print("  exponent:       ", qstruct_m5.exponent, "\n");
Print("  source:         ", qstruct_m5.source, "\n");
AssertOrLog("m=5 returns a record (no longer raises)",
            IsRecord(qstruct_m5));
AssertOrLog("m=5 source = bockstein-derived",
            qstruct_m5.source = "bockstein-derived");
AssertOrLog("m=5 num_generators = 165 (matches A-5b empirical k)",
            qstruct_m5.num_generators = 165);
AssertOrLog("m=5 exponent = 4 (Harada-Kono A(4) = Z/4 for m >= 3)",
            qstruct_m5.exponent = 4);
AssertOrLog("m=5 last torsion entry = 4 (cyclic Z/4 summand)",
            qstruct_m5.torsion[Length(qstruct_m5.torsion)] = 4);
AssertOrLog("m=5 all-but-last torsion entries = 2 (Z/2 summands)",
            ForAll([1..Length(qstruct_m5.torsion)-1],
                   i -> qstruct_m5.torsion[i] = 2));
AssertOrLog("m=5 available-predicate is true",
            QuillenH3StructureAvailable(5));

Print("\n--- m = 7 (Bockstein-derived) ---\n");
qstruct_m7 := QuillenH3Structure(7);;
Print("  torsion length: ", qstruct_m7.num_generators, "\n");
Print("  exponent:       ", qstruct_m7.exponent, "\n");
Print("  source:         ", qstruct_m7.source, "\n");
AssertOrLog("m=7 returns a record (no longer raises)",
            IsRecord(qstruct_m7));
AssertOrLog("m=7 source = bockstein-derived",
            qstruct_m7.source = "bockstein-derived");
AssertOrLog("m=7 num_generators = 455",
            qstruct_m7.num_generators = 455);
AssertOrLog("m=7 exponent = 4 (Harada-Kono A(4) = Z/4 for m >= 3)",
            qstruct_m7.exponent = 4);
AssertOrLog("m=7 last torsion entry = 4 (cyclic Z/4 summand)",
            qstruct_m7.torsion[Length(qstruct_m7.torsion)] = 4);
AssertOrLog("m=7 all-but-last torsion entries = 2 (Z/2 summands)",
            ForAll([1..Length(qstruct_m7.torsion)-1],
                   i -> qstruct_m7.torsion[i] = 2));
AssertOrLog("m=7 available-predicate is true",
            QuillenH3StructureAvailable(7));

AssertOrLog("m=2 available-predicate is true", QuillenH3StructureAvailable(2));
AssertOrLog("m=4 available-predicate is true (m>=3 covered)",
            QuillenH3StructureAvailable(4));

# --------------------------------------------------------------------
# Summary.
# --------------------------------------------------------------------

Print("\n=== Summary ===\n");
if IsEmpty(testFailures) then
    Print("test_quillen_h3_structure: ALL PASS\n");
else
    Print("test_quillen_h3_structure: FAIL (",
          Length(testFailures), " failures)\n");
    for f in testFailures do Print("  - ", f, "\n"); od;
fi;
