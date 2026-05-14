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
# Negative test: m = 5, 7 not yet supported -> raises informative error.
# --------------------------------------------------------------------

Print("\n--- m = 5, 7 (not yet derived; expect raise) ---\n");
for m_iter in [5, 7] do
    catch_result := CALL_WITH_CATCH(QuillenH3Structure, [m_iter]);
    AssertOrLog(
        Concatenation("m=", String(m_iter), " raises (TODO)"),
        not catch_result[1]);
    AssertOrLog(
        Concatenation("m=", String(m_iter), " available-predicate is false"),
        not QuillenH3StructureAvailable(m_iter));
od;

AssertOrLog("m=2 available-predicate is true", QuillenH3StructureAvailable(2));

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
