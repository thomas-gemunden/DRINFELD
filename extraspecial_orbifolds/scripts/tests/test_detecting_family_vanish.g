# Tests for D-VAN-3: ResIsTrivialOnDetectingFamily(m, omega_vec).
# Run from extraspecial_orbifolds/scripts/:
#   gap -q -b -c 'Read("tests/test_detecting_family_vanish.g"); QUIT;'

BreakOnError := false;;

Read("detecting_family_vanish.g");

Print("\n=== test_detecting_family_vanish.g ===\n");

testFailures := [];;
If_ := function(c, a, b) if c then return a; else return b; fi; end;;
AssertOrLog := function(label, cond)
    Print("  ", label, ": ", If_(cond, "PASS", "FAIL"), "\n");
    if not cond then Add(testFailures, label); fi;
end;;

Print("\n--- Task 2.1: scaffold ---\n");
AssertOrLog("ResIsTrivialOnDetectingFamily is bound",
            IsBoundGlobal("ResIsTrivialOnDetectingFamily"));
