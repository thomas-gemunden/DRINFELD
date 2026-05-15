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

Print("\n--- Task 1.4: RestrictionMatrixViaHAP ---\n");

setup_G_22 := SetupCohomology3(G_22);;
ctx_H_d8 := SubgroupCohomologyContext(H_d8);;
phi_d8 := SubgroupInclusion(H_d8, G_22);;

# Build the restriction matrix H^3(G) -> H^3(D_8) for G = E_+(2).
res_mat := RestrictionMatrixViaHAP(setup_G_22, ctx_H_d8, phi_d8);;

AssertOrLog("RestrictionMatrixViaHAP returns a matrix",
            IsMatrix(res_mat));
AssertOrLog("matrix has k_G = 10 rows (E_+(2) H^3 rank)",
            Length(res_mat) = 10);
AssertOrLog("matrix has k_H = 3 columns (D_8 H^3 rank)",
            Length(res_mat[1]) = 3);

# Entries should be reduced mod the H-side torsion. torsion_H = [2, 2, 4]
# in some order; every entry must be in [0..3].
all_reduced := ForAll(res_mat, row -> ForAll(row, x -> x >= 0 and x <= 3));
AssertOrLog("all entries reduced mod max(torsion_H) = 4",
            all_reduced);

Print("\n--- Task 1.5: BuildRestrictionMatrices public API ---\n");

# Plan correction (per the first dispatched agent's diagnostic): the
# plan's original assertions for `res_E` dimensions (10 x 3 at m=2,
# 35 x 4 at m=3) conflated the rank of the elementary abelian E with
# the rank of H^3(E; U(1)). The latter comes from the full UCT and is
# LARGER: 7 at m=2 (k=3 EA), 14 at m=3 (k=4 EA). Empirically verified
# via SetupCohomology3 on each EA before writing this test.
rec_m2 := BuildRestrictionMatrices(2, "hap");;

AssertOrLog("rec.m = 2", rec_m2.m = 2);
AssertOrLog("rec.source = hap", rec_m2.source = "hap");
AssertOrLog("rec.res_E is a 10 x 7 matrix (m=2 EA H^3 has 7 invariant factors)",
            Length(rec_m2.res_E) = 10
            and Length(rec_m2.res_E[1]) = 7);
AssertOrLog("rec.res_D8 is a 10 x 3 matrix (D_8 H^3 has 3 invariant factors)",
            Length(rec_m2.res_D8) = 10
            and Length(rec_m2.res_D8[1]) = 3);
AssertOrLog("rec.torsion_G = E_+(2) torsion ([(Z/2)^9, Z/8])",
            SortedList(rec_m2.torsion_G)
                = Concatenation(List([1..9], i -> 2), [8]));
AssertOrLog("rec.torsion_E sorted = [2,2,2,2,2,2,2] (m=2 EA = (Z/2)^3)",
            SortedList(rec_m2.torsion_E)
                = ListWithIdenticalEntries(7, 2));
AssertOrLog("rec.torsion_D8 sorted = [2,2,4]",
            SortedList(rec_m2.torsion_D8) = [2, 2, 4]);
AssertOrLog("rec.exp_E = 2",  rec_m2.exp_E = 2);
AssertOrLog("rec.exp_D8 = 4", rec_m2.exp_D8 = 4);
AssertOrLog("rec.H_E is a GAP group of order 8 (rank 3 EA)",
            IsGroup(rec_m2.H_E) and Order(rec_m2.H_E) = 8);
AssertOrLog("rec.H_D8 is a GAP group of order 8 (D_8 section)",
            IsGroup(rec_m2.H_D8) and Order(rec_m2.H_D8) = 8);
AssertOrLog("rec.G is the pinned parent E_+(2) of order 32",
            IsGroup(rec_m2.G) and Order(rec_m2.G) = 32);

# Entries reduced mod torsion_H[j].
all_res_E_reduced := ForAll([1..Length(rec_m2.res_E)], i ->
    ForAll([1..Length(rec_m2.res_E[i])], j ->
        rec_m2.res_E[i][j] >= 0
        and rec_m2.res_E[i][j] < rec_m2.torsion_E[j]));
AssertOrLog("res_E entries reduced mod per-column torsion_E",
            all_res_E_reduced);

all_res_D8_reduced := ForAll([1..Length(rec_m2.res_D8)], i ->
    ForAll([1..Length(rec_m2.res_D8[i])], j ->
        rec_m2.res_D8[i][j] >= 0
        and rec_m2.res_D8[i][j] < rec_m2.torsion_D8[j]));
AssertOrLog("res_D8 entries reduced mod per-column torsion_D8",
            all_res_D8_reduced);

# Caching: second call returns identical-reference rec.
rec_m2_again := BuildRestrictionMatrices(2, "hap");;
AssertOrLog("second call returns cached rec (identical reference)",
            IsIdenticalObj(rec_m2, rec_m2_again));

# source=quillen errors (Phase 2 not yet shipped).
err := CALL_WITH_CATCH(BuildRestrictionMatrices, [2, "quillen"]);;
AssertOrLog("source=quillen at m=2 errors (Phase 2 not implemented)",
            not err[1]);

# m=7 with source=hap errors (would invoke the OOM trap).
err := CALL_WITH_CATCH(BuildRestrictionMatrices, [7, "hap"]);;
AssertOrLog("source=hap at m=7 errors (m > 5 not supported in hap path)",
            not err[1]);

# Bad m and bad source.
err := CALL_WITH_CATCH(BuildRestrictionMatrices, [0, "hap"]);;
AssertOrLog("m = 0 errors", not err[1]);
err := CALL_WITH_CATCH(BuildRestrictionMatrices, [2, "garbage"]);;
AssertOrLog("unknown source errors", not err[1]);

Print("\n--- Task 1.6: m=3 smoke ---\n");

# Larger group: E_+(3) = order 128, k_G = 35, EA at m=3 has rank 4
# (gives k_E = 14 invariant factors per UCT), D_8 unchanged (k_D8 = 3).
# This call exercises HAP resolution on E_+(3) (~10 s) plus two
# EquivariantChainMap builds (E -> G and D_8 -> G); total ~30-60 s wall.
rec_m3 := BuildRestrictionMatrices(3, "hap");;
AssertOrLog("rec_m3.m = 3", rec_m3.m = 3);
AssertOrLog("res_E is 35 x 14 (m=3 EA k=4 -> H^3 has 14 invariant factors)",
            Length(rec_m3.res_E) = 35
            and Length(rec_m3.res_E[1]) = 14);
AssertOrLog("res_D8 is 35 x 3",
            Length(rec_m3.res_D8) = 35
            and Length(rec_m3.res_D8[1]) = 3);
AssertOrLog("torsion_E sorted = [2,2,2,2,2,2,2,2,2,2,2,2,2,2]",
            SortedList(rec_m3.torsion_E)
                = ListWithIdenticalEntries(14, 2));
AssertOrLog("torsion_D8 sorted = [2,2,4]",
            SortedList(rec_m3.torsion_D8) = [2, 2, 4]);
AssertOrLog("torsion_G sorted = (Z/2)^34 + Z/4 (per A-3a kernel.g)",
            SortedList(rec_m3.torsion_G)
                = Concatenation(ListWithIdenticalEntries(34, 2), [4]));

if IsEmpty(testFailures) then
    Print("\n=== test_detecting_family_restriction: PASS ===\n");
else
    Print("\n=== test_detecting_family_restriction: FAIL (",
          Length(testFailures), ") ===\n");
    for f in testFailures do Print("  - ", f, "\n"); od;
fi;
