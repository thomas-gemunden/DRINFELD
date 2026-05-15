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

Print("\n--- Task 1.3: SubgroupInclusion ---\n");

# Each call to EPlusGroup(m) builds a fresh GAP group (no caching),
# so H_d8_rec.parent and an independent EPlusGroup(2) call produce
# DIFFERENT groups with non-overlapping element families. The plan's
# original test used a separate EPlusGroup(2); we use H_d8_rec.parent
# here to keep H and G in the same family, which is what GAP's
# GroupHomomorphismByImages actually needs. Plan deviation: docs only.
H_d8_rec := D8Section_E_plus(2);;
G_22 := H_d8_rec.parent;;   # E_+(2), order 32, same family as H_d8
H_d8 := H_d8_rec.subgroup;;

phi := SubgroupInclusion(H_d8, G_22);;
AssertOrLog("SubgroupInclusion returns a homomorphism",
            IsGroupHomomorphism(phi));
AssertOrLog("Source(phi) = H",
            Source(phi) = H_d8);
AssertOrLog("Range(phi) = G",
            Range(phi) = G_22);
AssertOrLog("phi is injective",
            IsInjective(phi));
AssertOrLog("phi(h) = h for the first generator of H",
            Image(phi, GeneratorsOfGroup(H_d8)[1])
                = GeneratorsOfGroup(H_d8)[1]);

if IsEmpty(testFailures) then
    Print("\n=== test_detecting_family_restriction: PASS ===\n");
else
    Print("\n=== test_detecting_family_restriction: FAIL ===\n");
    for f in testFailures do Print("  - ", f, "\n"); od;
fi;
