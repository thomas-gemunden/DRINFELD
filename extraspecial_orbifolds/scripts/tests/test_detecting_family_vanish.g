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

Print("\n--- Task 2.5: Gate 1B m=2 (Z/8 witness) ---\n");

# The order-8 generator is the unique generator with torsion[i] = 8.
exp_index_m2 := Position(rec_m2.torsion_G, 8);;
AssertOrLog("found unique torsion-8 generator at index",
            exp_index_m2 <> fail);

# e_{exp_index_m2} is the Z/8 generator. Verify it is NOT in the HAP
# kernel (Tr is non-trivial on it).
e_z8 := List([1..10], j -> If_(j = exp_index_m2, 1, 0));;
AssertOrLog("Z/8 generator is NOT in HAP kernel",
            not (e_z8 in ker_vecs));

# D-VAN must report it as NOT trivial.
r_z8 := ResIsTrivialOnDetectingFamily(2, e_z8);;
AssertOrLog("Gate 1B: D-VAN reports Z/8 generator as non-trivial",
            r_z8.trivial = false);

# The D_8-side restriction is THE witness — single elementary abelian
# alone (which has only 2-torsion in H^3) would miss this generator.
AssertOrLog("Gate 1B witness: res_D8_vec is non-zero on Z/8 generator",
            not ForAll(r_z8.res_D8_vec, x -> x = 0));

# 2 * e_{Z/8} = order-2 element inside the Z/8 factor. D-VAN's verdict
# must match HAP's verdict on this half-vector.
e_z8_half := List([1..10], j -> If_(j = exp_index_m2, 2, 0));;
in_hap_half := e_z8_half in ker_vecs;;
r_z8_half := ResIsTrivialOnDetectingFamily(2, e_z8_half);;
AssertOrLog("2*e_{Z/8} verdict matches HAP",
            r_z8_half.trivial = in_hap_half);

Print("\n--- Task 2.6: f_D8 satisfies bar 3-cocycle equation ---\n");

# Pick a non-trivial omega (the Z/8 generator from Task 2.5) and verify
# f_D8 satisfies the bar 3-cocycle equation on D_8.
r_z8_check := ResIsTrivialOnDetectingFamily(2, e_z8);;
D8_grp := rec_m2.H_D8;;
elts_D8 := AsList(D8_grp);;
n_viol_D8 := 0;;
for g0 in elts_D8 do for g1 in elts_D8 do
    for g2 in elts_D8 do for g3 in elts_D8 do
        val := (r_z8_check.f_D8(g1, g2, g3)
                - r_z8_check.f_D8(g0*g1, g2, g3)
                + r_z8_check.f_D8(g0, g1*g2, g3)
                - r_z8_check.f_D8(g0, g1, g2*g3)
                + r_z8_check.f_D8(g0, g1, g2)) mod rec_m2.exp_D8;
        if val <> 0 then n_viol_D8 := n_viol_D8 + 1; fi;
    od; od;
od; od;;
AssertOrLog("f_D8 is a strict bar 3-cocycle on D_8 (0 violations)",
            n_viol_D8 = 0);
Print("    f_D8 violations: ", n_viol_D8, " / ",
      Length(elts_D8)^4, "\n");

Print("\n--- Task 2.7: D_8-section choice invariance smoke ---\n");

# Choose two distinct D_8 sections of E_+(2) and verify D-VAN's
# `trivial` verdict is identical on the 10 unit generators (the
# witness vectors differ but the trivial bit is class-invariant).
# Re-use rec_m2.G — the SAME EPlusGroup(2) instance the cached
# restriction matrices were built against.
all_subs := List(ConjugacyClassesSubgroups(rec_m2.G), Representative);;
d8_candidates := Filtered(all_subs,
                          S -> Order(S) = 8
                              and not IsAbelian(S)
                              and IdGroup(S) = [8, 3]);;
AssertOrLog("E_+(2) has at least 2 distinct D_8-section conjugacy classes",
            Length(d8_candidates) >= 2);

if Length(d8_candidates) >= 2 then
    H_d8_alt := d8_candidates[2];
    ctx_d8_alt := SubgroupCohomologyContext(H_d8_alt);
    phi_d8_alt := SubgroupInclusion(H_d8_alt, rec_m2.G);
    res_D8_alt := RestrictionMatrixViaHAP(rec_m2.setup_G,
                                            ctx_d8_alt, phi_d8_alt);
    mismatch_count := 0;
    for i in [1..10] do
        e_i := List([1..10], j -> If_(j = i, 1, 0));
        primary := ResIsTrivialOnDetectingFamily(2, e_i).trivial;
        # alt verdict: re-use rec_m2's E-side, swap in alt D_8-side.
        primary_E_vec := List([1..7], j ->
            Sum([1..10], k -> e_i[k] * rec_m2.res_E[k][j]) mod 2);
        alt_D8_int := List([1..Length(ctx_d8_alt.torsion)], j ->
            Sum([1..10], k -> e_i[k] * res_D8_alt[k][j]));
        alt_D8_vec := List([1..Length(alt_D8_int)], j ->
            alt_D8_int[j] mod ctx_d8_alt.torsion[j]);
        alt_trivial := ForAll(primary_E_vec, x -> x = 0)
                       and ForAll(alt_D8_vec, x -> x = 0);
        if alt_trivial <> primary then
            mismatch_count := mismatch_count + 1;
        fi;
    od;
    AssertOrLog("trivial verdict is invariant under D_8-section choice",
                mismatch_count = 0);
fi;

if IsEmpty(testFailures) then
    Print("\n=== test_detecting_family_vanish: PASS ===\n");
else
    Print("\n=== test_detecting_family_vanish: FAIL (",
          Length(testFailures), ") ===\n");
    for f in testFailures do Print("  - ", f, "\n"); od;
fi;
