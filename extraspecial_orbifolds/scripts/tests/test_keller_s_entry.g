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

if IsEmpty(testFailures) then
    Print("\n=== test_keller_s_entry: PASS ===\n");
else
    Print("\n=== test_keller_s_entry: FAIL (",
          Length(testFailures), ") ===\n");
    for f in testFailures do Print("  - ", f, "\n"); od;
fi;
