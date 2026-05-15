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

Print("\n--- Task 2.2: NormaliseOmegaToHomBasis ---\n");

rec_m2 := BuildRestrictionMatrices(2, "hap");;

# Hom-basis input (length 10 for E_+(2)). Should pass through unchanged.
hom_vec_id := List([1..10], i -> If_(i = 1, 1, 0));;
normalised := NormaliseOmegaToHomBasis(rec_m2, hom_vec_id);;
AssertOrLog("hom-basis input passes through",
            normalised = hom_vec_id);

# Cocycle-form input (length K_G!.dimension(3)) is recognised and
# rejected in Phase 1. (Full cocycle-form path needs a UCT.cyclebasis
# pairing step that's deferred to a follow-up.)
cocycle_vec_id := ListWithIdenticalEntries(
    rec_m2.setup_G.K!.dimension(3), 0);;
err := CALL_WITH_CATCH(NormaliseOmegaToHomBasis,
                       [rec_m2, cocycle_vec_id]);;
AssertOrLog("cocycle-form input errors (Phase 1 deferred)",
            not err[1]);

# Bad length input.
err := CALL_WITH_CATCH(NormaliseOmegaToHomBasis, [rec_m2, [1, 2, 3]]);;
AssertOrLog("bad-length input errors", not err[1]);

Print("\n--- Task 2.3: ResIsTrivialOnDetectingFamily basic API ---\n");

# Zero omega: trivially in the kernel.
omega_zero := List([1..10], i -> 0);;
r_zero := ResIsTrivialOnDetectingFamily(2, omega_zero);;
AssertOrLog("omega=0 is trivial", r_zero.trivial = true);
AssertOrLog("res_E_vec is zero (length k_E = 7)",
            r_zero.res_E_vec = ListWithIdenticalEntries(7, 0));
AssertOrLog("res_D8_vec is zero (length k_D8 = 3)",
            r_zero.res_D8_vec = [0, 0, 0]);
AssertOrLog("f_E is a function", IsFunction(r_zero.f_E));
AssertOrLog("f_D8 is a function", IsFunction(r_zero.f_D8));
AssertOrLog("source = hap", r_zero.source = "hap");

Print("\n--- Task 2.4: Gate 1A m=2 (10 generators vs HAP) ---\n");

# Load the HAP-computed kernel of Tr for E_+(2): 2048 vectors of length
# 10 in Z/2^9 (+) Z/8.
ker_data := ReadAsFunction(
    "../../computed/transgression/2/kernel.g")();;
ker_vecs := ker_data.kernel_vecs;;
AssertOrLog("loaded 2048 HAP kernel vectors",
            Length(ker_vecs) = 2048);

# For each of the 10 unit generators, check whether D-VAN's verdict
# matches "is e_i in HAP's kernel?". If any mismatch, the AM04
# detecting-family injectivity is violated empirically — STOP.
mismatches := [];;
for i in [1..10] do
    e_i := List([1..10], j -> If_(j = i, 1, 0));
    in_hap_ker := e_i in ker_vecs;
    r := ResIsTrivialOnDetectingFamily(2, e_i);
    if r.trivial <> in_hap_ker then
        Add(mismatches, rec(i := i, dvan := r.trivial,
                             hap := in_hap_ker));
    fi;
od;
AssertOrLog("Gate 1A: D-VAN matches HAP on all 10 m=2 generators",
            IsEmpty(mismatches));
if not IsEmpty(mismatches) then
    Print("    mismatches: ", mismatches, "\n");
fi;

if IsEmpty(testFailures) then
    Print("\n=== test_detecting_family_vanish: PASS ===\n");
else
    Print("\n=== test_detecting_family_vanish: FAIL (",
          Length(testFailures), ") ===\n");
    for f in testFailures do Print("  - ", f, "\n"); od;
fi;
