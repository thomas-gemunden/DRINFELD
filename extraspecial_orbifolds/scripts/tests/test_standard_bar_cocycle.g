# test_standard_bar_cocycle.g
#
# V-4a / issue #81 verification.  Outcome: HAP's StandardCocycle is correct;
# the previously-observed "1105 / 4096 violations" came from feeding a
# non-cocycle vector into StandardCocycle, not from a HAP bug.
#
# This test demonstrates:
#
#   (1) BUG REPRODUCTION:
#       The original buggy callsite (effectively `UCT.lift * e_i` with
#       e_i of length |hombasis|) produces a vector that fails the
#       projective-resolution cocycle equation (vec . d^* != 0 mod m).
#       Consequently HAP's StandardCocycle on this junk vector fails the
#       inhomogeneous bar 3-cocycle equation.
#
#   (2) FIX VERIFICATION:
#       Using the genuine hom vector `UCT.hombasis[i]` (length |cyclebasis|)
#       lifted via UCT.lift produces a cocycle vector that
#       (a) satisfies the projective-resolution cocycle equation,
#       (b) gives a HAP StandardCocycle that satisfies the bar 3-cocycle
#           equation (0 / 4096 violations),
#       (c) makes `alpha_g(omega)` a 2-cocycle on every centraliser.
#
#       The wrapper `StandardBarCocycleFromHom(R, UCT, hom_vec, n, m)`
#       provides a type-safe entry that catches the original mistake.
#
# Verified on Q_8 (SmallGroup(8, 4)) where H^3 = Z/8, both for the order-8
# generator and the order-2 generator.

# --- locate sibling files (no chdir) -------------------------------------
sbcAdapter := fail;;
sbcUCTSrc := fail;;
for sbcCand in [".", "..", "../..", "../../..", "../../../..",
                "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-v4a",
                "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-v3"] do
    if sbcAdapter = fail
       and IsExistingFile(Concatenation(sbcCand, "/extraspecial_orbifolds/scripts/standard_bar_cocycle.g")) then
        sbcAdapter := Concatenation(sbcCand, "/extraspecial_orbifolds/scripts/standard_bar_cocycle.g");
    fi;
    if sbcUCTSrc = fail
       and IsExistingFile(Concatenation(sbcCand, "/src/universal_coefficients.g")) then
        sbcUCTSrc := Concatenation(sbcCand, "/src/universal_coefficients.g");
    fi;
od;;
if sbcAdapter = fail then
    Error("test_standard_bar_cocycle.g: could not locate standard_bar_cocycle.g");
fi;
if sbcUCTSrc = fail then
    Error("test_standard_bar_cocycle.g: could not locate src/universal_coefficients.g");
fi;
LoadPackage("hap");;
LoadPackage("io");;
LoadPackage("hapco", false);;
Read(sbcUCTSrc);;
Read(sbcAdapter);;


# --- helpers --------------------------------------------------------------
sbcPass := 0;;
sbcFail := 0;;
sbcAssert := function(label, cond)
    if cond then
        Print("  OK   ", label, "\n");
        sbcPass := sbcPass + 1;
    else
        Print("  FAIL ", label, "\n");
        sbcFail := sbcFail + 1;
    fi;
end;;


# Brute-force check: does the projective-resolution cochain `vec` (a
# length-`R!.dimension(n)` vector) satisfy the resolution cocycle equation
# `vec . d_{n+1}(k) = 0 mod m` for all k?
sbcCheckRCocycle := function(R, vec, n, m)
    local violations, k, b, term, val;
    violations := 0;
    for k in [1..R!.dimension(n+1)] do
        b := List([1..R!.dimension(n)], i -> 0);
        for term in R!.boundary(n+1, k) do
            if term[1] > 0 then b[term[1]]   := b[term[1]]   + 1;
            else                b[-term[1]]  := b[-term[1]]  - 1;
            fi;
        od;
        val := (vec * b) mod m;
        if val <> 0 then violations := violations + 1; fi;
    od;
    return rec(checked := R!.dimension(n+1), violations := violations);
end;;


# --- build context: Q_8, R, K, UCT --------------------------------------
Print("\n=== Q_8 set-up ===\n");
Q8 := SmallGroup(8, 4);;
Print("  StructureDescription = ", StructureDescription(Q8), "\n");
RQ8 := ResolutionFiniteGroup(Q8, 4);;
KQ8 := TensorWithIntegers(RQ8);;
UCTQ8 := UniversalCoefficientsTheorem(KQ8, 3);;
mQ8 := UCTQ8!.exponent;;
Print("  H^3 = Z/", mQ8, "\n");
Print("  |hombasis|   = ", Size(UCTQ8!.hombasis),
      "   (number of cyclic Z/D[i] generators)\n");
Print("  |cyclebasis| = ", Size(UCTQ8!.cyclebasis),
      "   (rank of Z_3, dimension UCT.lift expects)\n");
Print("  UCT.lift shape: ", Length(UCTQ8!.lift), " x ",
      Length(UCTQ8!.lift[1]), "\n");
Print("  UCT.hombasis[1] = ", UCTQ8!.hombasis[1], "\n");


# --- (1) BUG REPRODUCTION ------------------------------------------------
# We synthesise the original mistake: pass a unit vector e_i of length
# |cyclebasis| (which is what UCT.lift expects dimensionally) but which is
# NOT in the integer span of UCT.hombasis modulo m.  The lift produces a
# length-R.dim(3) vector that is NOT a cocycle (vec . d^* != 0 mod m), and
# HAP's StandardCocycle on this junk vector then fails the bar 3-cocycle
# equation -- exactly what was observed as "1105/4096 violations".
#
# (We also show the analogous failure when feeding GAP's matrix-vector
# multiplication a wrong-length input that silently zero-pads.)
Print("\n=== (1) Bug reproduction: feeding non-hom vectors to UCT.lift ===\n");
sbcCycDim := Size(UCTQ8!.cyclebasis);;
sbcUnitCycVectors := List([1..sbcCycDim], i ->
    List([1..sbcCycDim], j -> 0));;
for i in [1..sbcCycDim] do
    sbcUnitCycVectors[i][i] := 1;
od;;
sbcAnyBarViolation := false;;
for i in [1..sbcCycDim] do
    sbc_hom_i := sbcUnitCycVectors[i];
    sbc_vec_i := (UCTQ8!.lift * sbc_hom_i) mod mQ8;
    sbc_rcheck := sbcCheckRCocycle(RQ8, sbc_vec_i, 3, mQ8);
    sbc_f_hap := StandardCocycle(RQ8, sbc_vec_i, 3, mQ8);
    sbc_res := CheckBar3CocycleEquation(Q8, sbc_f_hap, mQ8);
    Print("  e_", i, " in Z^|cyclebasis|: vec = ", sbc_vec_i,
          "; R-cocycle violations = ", sbc_rcheck.violations, " / ",
          sbc_rcheck.checked,
          "; bar 3-cocycle violations = ", sbc_res.violations, " / ",
          sbc_res.checked, "\n");
    if sbc_res.violations > 0 then sbcAnyBarViolation := true; fi;
od;;
# At least one of the standard-basis vectors should hit the original
# failure mode (a non-cocycle lift, leading to bar violations).
sbcAssert("bug repro: at least one e_i in Z^|cyclebasis| lifts to a non-cocycle, causing bar violations",
          sbcAnyBarViolation);

# Bonus: demonstrate the exact original-bug input on Q_8 -- the unit vector
# of length |hombasis|=1.  GAP's matrix*vec with mismatched length silently
# zero-pads, producing the same buggy [1, 0, 0] reported as the original
# 1105/4096 failure.
sbc_buggy_vec := (UCTQ8!.lift * [1]) mod mQ8;;
sbc_buggy_rcheck := sbcCheckRCocycle(RQ8, sbc_buggy_vec, 3, mQ8);;
sbc_buggy_f := StandardCocycle(RQ8, sbc_buggy_vec, 3, mQ8);;
sbc_buggy_res := CheckBar3CocycleEquation(Q8, sbc_buggy_f, mQ8);;
Print("  ORIGINAL BUG INPUT ([1] of length |hombasis|=1):\n");
Print("    UCT.lift * [1] (GAP zero-pads silently) = ", sbc_buggy_vec, "\n");
Print("    R-cocycle violations    = ", sbc_buggy_rcheck.violations,
      " / ", sbc_buggy_rcheck.checked, "\n");
Print("    bar 3-cocycle violations = ", sbc_buggy_res.violations,
      " / ", sbc_buggy_res.checked,
      "    (the historic 1105/4096 number)\n");
sbcAssert("bug repro: original [1] input reproduces non-zero bar violations",
          sbc_buggy_res.violations > 0);


# --- (2) FIX VERIFICATION ------------------------------------------------
# The CORRECT API is to feed `UCT.hombasis[i]` directly (length |cyclebasis|)
# into UCT.lift.  We test all hombasis elements; we also test scalar multiples
# (the order-mQ8/k generator for each divisor k of mQ8).
Print("\n=== (2) Fix verification: using UCT.hombasis[i] correctly ===\n");
for i in [1..Size(UCTQ8!.hombasis)] do
    sbc_hom_i := UCTQ8!.hombasis[i];
    sbc_vec_i := (UCTQ8!.lift * sbc_hom_i) mod mQ8;
    sbc_rcheck := sbcCheckRCocycle(RQ8, sbc_vec_i, 3, mQ8);
    sbcAssert(Concatenation("UCT.hombasis[", String(i),
                            "] lifts to an R-cocycle"),
              sbc_rcheck.violations = 0);
    sbc_f_bar := StandardCocycle(RQ8, sbc_vec_i, 3, mQ8);
    sbc_res := CheckBar3CocycleEquation(Q8, sbc_f_bar, mQ8);
    Print("  hombasis[", i, "]: vec = ", sbc_vec_i,
          "; bar 3-cocycle violations = ", sbc_res.violations, " / ",
          sbc_res.checked, "\n");
    sbcAssert(Concatenation("HAP StandardCocycle on hombasis[", String(i),
                            "] passes bar 3-cocycle equation"),
              sbc_res.violations = 0);
od;;

# Also test the order-2 sub-generator (the one Mignard-Schauenburg's nu_2
# computations care most about): (mQ8 / 2) * UCT.hombasis[1].
Print("\n  --- order-2 generator: (mQ8 / 2) * hombasis[1] ---\n");
sbc_hom_o2 := (mQ8 / 2) * UCTQ8!.hombasis[1];;
sbc_vec_o2 := (UCTQ8!.lift * sbc_hom_o2) mod mQ8;;
sbc_rcheck := sbcCheckRCocycle(RQ8, sbc_vec_o2, 3, mQ8);;
sbcAssert("order-2 hom lifts to an R-cocycle", sbc_rcheck.violations = 0);
sbc_f_o2 := StandardCocycle(RQ8, sbc_vec_o2, 3, mQ8);;
sbc_res := CheckBar3CocycleEquation(Q8, sbc_f_o2, mQ8);;
Print("  order-2 generator: bar 3-cocycle violations = ",
      sbc_res.violations, " / ", sbc_res.checked, "\n");
sbcAssert("order-2 generator: bar 3-cocycle equation holds",
          sbc_res.violations = 0);


# --- (3) WRAPPER VERIFICATION --------------------------------------------
# StandardBarCocycleFromHom should give the same answers, and should ERROR
# loudly if fed a wrong-length input.
Print("\n=== (3) StandardBarCocycleFromHom wrapper ===\n");
sbc_f_via_wrapper := StandardBarCocycleFromHom(RQ8, UCTQ8,
                                                UCTQ8!.hombasis[1], 3, mQ8);;
sbc_res := CheckBar3CocycleEquation(Q8, sbc_f_via_wrapper, mQ8);;
Print("  wrapper, hombasis[1]: bar 3-cocycle violations = ",
      sbc_res.violations, " / ", sbc_res.checked, "\n");
sbcAssert("StandardBarCocycleFromHom(hombasis[1]) gives a bar 3-cocycle",
          sbc_res.violations = 0);

# Confirm wrapper errors out on a wrong-length input (the original bug).
# We catch the error via CALL_WITH_CATCH.
sbc_caught := CALL_WITH_CATCH(StandardBarCocycleFromHom,
                              [RQ8, UCTQ8, [1], 3, mQ8]);;
sbcAssert("StandardBarCocycleFromHom errors on length-1 vector (|hombasis|)",
          sbc_caught[1] = false);


# --- (4) DOWNSTREAM: alpha_g is a 2-cocycle on C_G(g) -------------------
Print("\n=== (4) Downstream: alpha_g is a 2-cocycle on C_G(g) ===\n");
classesQ8 := List(ConjugacyClasses(Q8), Representative);;

# Use the order-mQ8 generator (hombasis[1]).
sbc_f_top := StandardBarCocycleFromHom(RQ8, UCTQ8,
                                        UCTQ8!.hombasis[1], 3, mQ8);;
for g in classesQ8 do
    sbc_res := CheckAlphaIs2Cocycle(Q8, g, sbc_f_top, mQ8);
    Print("  hombasis[1] gen: class order ", Order(g),
          ": alpha 2-cocycle violations = ",
          sbc_res.violations, " / ", sbc_res.checked, "\n");
    sbcAssert(Concatenation("alpha is 2-cocycle at class order ",
                            String(Order(g)), " (hombasis[1] gen)"),
              sbc_res.violations = 0);
od;;

# Also check the order-2 generator.
sbc_f_o2_w := StandardBarCocycleFromHom(RQ8, UCTQ8,
                                         sbc_hom_o2, 3, mQ8);;
Print("\n  --- order-2 generator ---\n");
for g in classesQ8 do
    sbc_res := CheckAlphaIs2Cocycle(Q8, g, sbc_f_o2_w, mQ8);
    Print("  order-2 gen: class order ", Order(g),
          ": alpha 2-cocycle violations = ",
          sbc_res.violations, " / ", sbc_res.checked, "\n");
    sbcAssert(Concatenation("alpha is 2-cocycle at class order ",
                            String(Order(g)), " (order-2 gen)"),
              sbc_res.violations = 0);
od;;


# --- summary -------------------------------------------------------------
Print("\n=== summary ===\n");
Print("  passed: ", sbcPass, "    failed: ", sbcFail, "\n");
if sbcFail > 0 then
    Print("  STATUS: FAIL\n");
    QUIT_GAP(1);
else
    Print("  STATUS: PASS\n");
fi;
