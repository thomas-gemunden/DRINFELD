# Tests for D-VAN-2: BuildRestrictionMatrices(m, source).
# Run from extraspecial_orbifolds/scripts/:
#   gap -q -b -c 'Read("tests/test_detecting_family_restriction.g"); QUIT;'

BreakOnError := false;;

Read("detecting_family_restriction.g");

Print("\n=== test_detecting_family_restriction.g ===\n");

testFailures := [];;
If_ := function(c, a, b) if c then return a; else return b; fi; end;;
AssertOrLog := function(label, cond)
    Print("  ", label, ": ", If_(cond, "PASS", "FAIL"), "\n");
    if not cond then Add(testFailures, label); fi;
end;;

Print("\n--- Task 1.1: file scaffold ---\n");
AssertOrLog("BuildRestrictionMatrices is bound",
            IsBoundGlobal("BuildRestrictionMatrices"));
AssertOrLog("_DETF_CACHE is bound (module-level cache)",
            IsBoundGlobal("_DETF_CACHE"));
AssertOrLog("_DETF_CACHE is a record",
            IsRecord(ValueGlobal("_DETF_CACHE")));

Print("\n--- Task 1.2: SubgroupCohomologyContext ---\n");

# Build the context for D_8 (smallest case) and check the returned rec
# has the right fields. SubgroupCohomologyContext takes a GAP group
# and returns a rec with R, K, UCT, exponent, num_generators, torsion.
D8 := SmallGroup(8, 3);;
ctx_d8 := SubgroupCohomologyContext(D8);;

AssertOrLog("SubgroupCohomologyContext returns a record",
            IsRecord(ctx_d8));
AssertOrLog("ctx_d8.R is bound", IsBound(ctx_d8.R));
AssertOrLog("ctx_d8.K is bound", IsBound(ctx_d8.K));
AssertOrLog("ctx_d8.UCT is bound", IsBound(ctx_d8.UCT));
AssertOrLog("ctx_d8.exponent = 4 (D_8 H^3 exp)",
            ctx_d8.exponent = 4);
AssertOrLog("ctx_d8.num_generators = 3 (D_8 H^3 rank)",
            ctx_d8.num_generators = 3);
AssertOrLog("ctx_d8.torsion = [2, 2, 4] (sorted)",
            SortedList(ctx_d8.torsion) = [2, 2, 4]);

if IsEmpty(testFailures) then
    Print("\n=== test_detecting_family_restriction: PASS ===\n");
else
    Print("\n=== test_detecting_family_restriction: FAIL ===\n");
    for f in testFailures do Print("  - ", f, "\n"); od;
fi;
