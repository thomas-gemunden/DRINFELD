# Tests for D-VAN-5 / D-VAN-6: Keller-namespace wrapper + S-entry dispatcher.
# Run from extraspecial_orbifolds/scripts/:
#   gap -q -b -c 'Read("tests/test_keller_s_entry.g"); QUIT;'

BreakOnError := false;;

Read("keller/keller_twist_is_trivial.g");

Print("\n=== test_keller_s_entry.g ===\n");

testFailures := [];;
If_ := function(c, a, b) if c then return a; else return b; fi; end;;
AssertOrLog := function(label, cond)
    Print("  ", label, ": ", If_(cond, "PASS", "FAIL"), "\n");
    if not cond then Add(testFailures, label); fi;
end;;

Print("\n--- Task 4.1: KellerTwistIsTrivial smoke ---\n");
AssertOrLog("KellerTwistIsTrivial is bound",
            IsBoundGlobal("KellerTwistIsTrivial"));

# Zero omega is trivial.
zero_m2 := List([1..10], i -> 0);;
AssertOrLog("KellerTwistIsTrivial(2, zero) = true",
            KellerTwistIsTrivial(2, zero_m2) = true);

# Z/8 generator (the unique torsion-8 H^3 generator at m=2) is not
# trivial — D-VAN's Gate 1B witness re-checked through the Keller
# wrapper.
rec_m2 := BuildRestrictionMatrices(2, "hap");;
exp_idx := Position(rec_m2.torsion_G, 8);;
e_z8 := List([1..10], i -> If_(i = exp_idx, 1, 0));;
AssertOrLog("KellerTwistIsTrivial(2, Z/8 gen) = false",
            KellerTwistIsTrivial(2, e_z8) = false);

Print("\n--- Task 5.2: KellerSEntry dispatcher ---\n");

Read("keller/keller_s_entry.g");

AssertOrLog("KellerSEntry is bound",
            IsBoundGlobal("KellerSEntry"));

# Gate 1C: at omega = 0 (trivial twist), KellerSEntry should match
# SKeller(m, i, j) for every (i, j). We sweep a small grid at m=2;
# the SKeller cache is built once.
rank_m2 := SKellerRank(2);;
Print("  SKellerRank(2) = ", rank_m2, "\n");
mismatches_1c := 0;;
for i in [1..rank_m2] do
    for j in [1..rank_m2] do
        keller_dvan := KellerSEntry(2, zero_m2, i, j);
        skeller_only := SKeller(2, i, j);
        if keller_dvan <> skeller_only then
            mismatches_1c := mismatches_1c + 1;
        fi;
    od;
od;
AssertOrLog("Gate 1C: trivial-twist S = SKeller at omega=0 for all (i,j) at m=2",
            mismatches_1c = 0);

# Gate 1D: dispatcher correctly handles a non-trivial omega at m=3.
# Every unit generator e_i is a non-zero class in H^3(E_+(m); U(1)),
# so D-VAN flags it as non-trivial. (At m=3, A-3a in fact found
# ker(Tr) = full H^3, so in_kernel_gens = [1..35] and every e_i is
# BOTH in ker(Tr) AND a non-zero cohomology class. D-VAN tests the
# latter — see PR #155 / #156 for the reframing rationale.)
omega_nontrivial_m3 := List([1..35], j -> If_(j = 1, 1, 0));;
AssertOrLog("D-VAN flags e_1 (m=3) as non-trivial",
            KellerTwistIsTrivial(3, omega_nontrivial_m3) = false);
# For (i, j) = (1, 1) the value should equal SKeller(3, 1, 1) (the
# K-2 backend is unconditional on omega in this Phase 1 scope; D-VAN
# only flips the dispatch path, both branches call SKeller).
val_dvan := KellerSEntry(3, omega_nontrivial_m3, 1, 1);;
val_skeller := SKeller(3, 1, 1);;
AssertOrLog("Gate 1D: non-trivial dispatch matches SKeller at (1,1)",
            val_dvan = val_skeller);

if IsEmpty(testFailures) then
    Print("\n=== test_keller_s_entry: PASS ===\n");
else
    Print("\n=== test_keller_s_entry: FAIL (",
          Length(testFailures), ") ===\n");
    for f in testFailures do Print("  - ", f, "\n"); od;
fi;
