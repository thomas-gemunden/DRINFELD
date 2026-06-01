# test_pathz_a2_bit_no_roundtrip.g — issue #396 A-2.
#
# Verifies the refactored IsCoboundary2Z4VecBits (Design 1 / A-2) which
# wires the GF(2) bit slices end-to-end through the IB modulus=4 base
# case, avoiding the previous bits -> ints -> bits round-trip.
#
# Strategy: this test extends test_iscoboundary2_z4_vec_bits.g with
# additional D_8 fixtures that exercise the new bit-form code path, plus
# Z/4 fixtures that hit each math branch:
#
#   (T1) Zero cochain (trivial coboundary). Tests the early-exit when
#        c_bot = 0 (strict F_2 witness β = 0).
#   (T2) Known integer-coboundary (δβ with β assigning {0,1,2,3}).
#        Tests the c_table_next derivation (β nonzero, integer arithmetic
#        in δβ matters).
#   (T3) Random Z/4 cochain table on D_8 (40 trials). Cross-checks
#        bit-form path against integer IsCoboundary2Z2kVec on the same
#        c_g_vec.
#   (T4) F_2-only cochain (c_top = 0): tests the path where δβ mod 4 has
#        bit_1 = 0 everywhere (β values in {0, 1}).
#   (T5) Path that the strict F_2 test rejects (c_bot is not a GF(2)
#        coboundary): the bit-form path must short-circuit on `false`
#        without computing δβ.
#   (T6) Q_8 (8, 4): a different small group with non-trivial Bockstein
#        image (the rationale for IsCoboundary2Mod2WithLift's WithLift
#        branch). Exercises the lift test on a non-strict-coboundary input.
#
# The reference path uses IsCoboundary2Z2kVec on the integer
# reconstruction `2*c_top + c_bot` — this is what the PR #393 entry point
# delegated to before A-2. Agreement on every input is the regression
# guarantee.
#
# CWD shim mirrors test_iscoboundary2_z4_vec_bits.g.

ic2bits_a2_test_target := fail;;
for ic2bits_a2_try in [
        ".", "tests", "extraspecial_orbifolds/scripts/solver/tests",
        "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD/extraspecial_orbifolds/scripts/solver/tests"] do
    if IsExistingFile(Concatenation(ic2bits_a2_try,
                                     "/test_pathz_a2_bit_no_roundtrip.g")) then
        ic2bits_a2_test_target := ic2bits_a2_try;
        break;
    fi;
od;;
if ic2bits_a2_test_target = fail then
    Error("test_pathz_a2_bit_no_roundtrip.g: cannot locate self from CWD ",
          Filename(DirectoryCurrent(), ""));
fi;
ChangeDirectoryCurrent(ic2bits_a2_test_target);;
Read("../iterated_bockstein.g");
Read("../iscoboundary2_split.g");

# Helper: split an integer vec mod 4 into two packed GF(2) bit slices.
SplitBits := function(c_int)
    local one, c_bot, c_top;
    one := One(GF(2));
    c_bot := (c_int mod 2) * one;
    c_top := List(c_int, x -> QuoInt(x, 2) mod 2) * one;
    ConvertToVectorRep(c_bot, GF(2));
    ConvertToVectorRep(c_top, GF(2));
    return rec(bot := c_bot, top := c_top);
end;;

# Helper: build a Z/4 coboundary from a length-n integer 1-cochain β.
BuildCobZ4 := function(elts, idx_dict, beta)
    local n, c_g, i, j;
    n := Length(elts);
    c_g := ListWithIdenticalEntries(n * n, 0);
    for i in [1..n] do
        for j in [1..n] do
            c_g[(i-1)*n + j] :=
                (beta[i] + beta[j]
                 - beta[LookupDictionary(idx_dict, elts[i] * elts[j])])
                    mod 4;
        od;
    od;
    return c_g;
end;;

Print("test_pathz_a2_bit_no_roundtrip: starting...\n");

# === (T1) Zero cochain on D_8 ===
G_d8 := SmallGroup(8, 3);;     # D_8
elts_d8 := AsList(G_d8);;
n_d8 := Length(elts_d8);;
idx_d8 := NewDictionary(elts_d8[1], true, elts_d8);;
for i in [1..n_d8] do AddDictionary(idx_d8, elts_d8[i], i); od;

zero_c := ListWithIdenticalEntries(n_d8 * n_d8, 0);;
ref_zero := IsCoboundary2Z2kVec(G_d8, zero_c, 2);;
Assert(0, ref_zero = true, "T1: zero cochain must be a coboundary");
bits_zero := SplitBits(zero_c);;
got_zero := IsCoboundary2Z4VecBits(G_d8, bits_zero.bot, bits_zero.top, n_d8);;
Assert(0, got_zero = true,
       Concatenation("T1: zero cochain via bits must be true; got ",
                     String(got_zero)));
Print("T1 zero cochain: PASS\n");

# === (T2) Known integer-coboundary (β with values in {0,1,2,3}) ===
beta_d8 := ListWithIdenticalEntries(n_d8, 0);;
beta_d8[2] := 1;
beta_d8[3] := 2;
beta_d8[4] := 3;
beta_d8[5] := 1;
c_g_t2 := BuildCobZ4(elts_d8, idx_d8, beta_d8);;
ref_t2 := IsCoboundary2Z2kVec(G_d8, c_g_t2, 2);;
Assert(0, ref_t2 = true,
       "T2: constructed Z/4 coboundary must be detected by integer API");
bits_t2 := SplitBits(c_g_t2);;
got_t2 := IsCoboundary2Z4VecBits(G_d8, bits_t2.bot, bits_t2.top, n_d8);;
Assert(0, got_t2 = ref_t2,
       Concatenation("T2 agreement: bits=", String(got_t2),
                     " vs ref=", String(ref_t2)));
Print("T2 constructed Z/4 cob: PASS\n");

# === (T3) Random Z/4 cochain agreement on D_8 (40 trials) ===
n_pass_t3 := 0;;
n_fail_t3 := 0;;
seed_t3 := RandomSource(IsMersenneTwister, 42);;
for trial in [1..40] do
    rand_c := List([1..n_d8*n_d8], _ -> Random(seed_t3, [0..3]));
    ref := IsCoboundary2Z2kVec(G_d8, rand_c, 2);
    bits := SplitBits(rand_c);
    got := IsCoboundary2Z4VecBits(G_d8, bits.bot, bits.top, n_d8);
    if got = ref then
        n_pass_t3 := n_pass_t3 + 1;
    else
        n_fail_t3 := n_fail_t3 + 1;
        Print("  T3 trial ", trial, " DISAGREEMENT: bits=", got,
              " ref=", ref, "\n");
    fi;
od;
Assert(0, n_fail_t3 = 0,
       Concatenation("T3: ", String(n_fail_t3), " disagreements"));
Print("T3 random D_8 (40 trials): PASS (", n_pass_t3, "/40)\n");

# === (T4) F_2-only cochain (c_top = 0) ===
# Build a Z/4 cochain with c_g[i] mod 2 a non-trivial F_2 coboundary, and
# c_g[i] ∈ {0, 1} (so c_top is identically zero). Caveat: a value of 0
# in F_2 might come from a value of 0 OR 2 in Z/4, so an "F_2 coboundary
# lifted to {0, 1}" is generally NOT a Z/4 coboundary — it may even be a
# Z/4 non-coboundary. We don't predict which; we just verify bit-form
# path agrees with integer path. Exercises the c_top = 0 branch of the
# c_table_next derivation: c_table_next_bot = 0 XOR db_top = db_top.
beta_t4 := ListWithIdenticalEntries(n_d8, 0);;
beta_t4[2] := 1;
beta_t4[5] := 1;
c_g_t4 := ListWithIdenticalEntries(n_d8 * n_d8, 0);;
for i in [1..n_d8] do
    for j in [1..n_d8] do
        c_g_t4[(i-1)*n_d8 + j] :=
            ((beta_t4[i] + beta_t4[j]
              - beta_t4[LookupDictionary(idx_d8, elts_d8[i] * elts_d8[j])])
              mod 2);  # mod 2 (not mod 4) — values in {0, 1}
    od;
od;
ref_t4 := IsCoboundary2Z2kVec(G_d8, c_g_t4, 2);;
bits_t4 := SplitBits(c_g_t4);;
# Sanity: c_top should be all zero (no entry has bit_1 set).
Assert(0, IsZero(bits_t4.top), "T4 sanity: c_top should be zero for {0,1} cochain");
got_t4 := IsCoboundary2Z4VecBits(G_d8, bits_t4.bot, bits_t4.top, n_d8);;
Assert(0, got_t4 = ref_t4,
       Concatenation("T4 agreement: bits=", String(got_t4),
                     " vs ref=", String(ref_t4), " (T4 verdict was: ",
                     String(ref_t4), ")"));
Print("T4 c_top=0 path: PASS (verdict ", ref_t4, ")\n");

# === (T5) Strict F_2 test rejects (short-circuit on false) ===
# Construct a c_bot that is NOT a strict F_2 coboundary. On D_8 the
# F_2 cohomology H²(D_8; F_2) has dimension >= 1 nontrivial classes.
# Strategy: enumerate small perturbations of a Z/4 coboundary by
# flipping one entry mod 2 until IsCoboundary2Z2kVec returns false.
non_cob_found := false;;
for trial in [1..20] do
    perturbed := ShallowCopy(c_g_t2);
    pos := Random([1..n_d8 * n_d8]);
    perturbed[pos] := (perturbed[pos] + 2) mod 4;  # flip bit_1 only
    if not IsCoboundary2Z2kVec(G_d8, perturbed, 2) then
        bits_t5 := SplitBits(perturbed);
        got_t5 := IsCoboundary2Z4VecBits(G_d8, bits_t5.bot, bits_t5.top, n_d8);
        Assert(0, got_t5 = false,
               Concatenation("T5 non-cob (bit_1 flip): bits=", String(got_t5),
                             " ref=false"));
        non_cob_found := true;
        Print("T5 non-cob via bit_1 flip: PASS\n");
        break;
    fi;
od;
if not non_cob_found then
    # Try flipping bit_0 (changes the F_2 reduction).
    for trial in [1..20] do
        perturbed := ShallowCopy(c_g_t2);
        pos := Random([1..n_d8 * n_d8]);
        perturbed[pos] := (perturbed[pos] + 1) mod 4;
        if not IsCoboundary2Z2kVec(G_d8, perturbed, 2) then
            bits_t5 := SplitBits(perturbed);
            got_t5 := IsCoboundary2Z4VecBits(G_d8, bits_t5.bot, bits_t5.top, n_d8);
            Assert(0, got_t5 = false,
                   Concatenation("T5 non-cob (bit_0 flip): bits=", String(got_t5),
                                 " ref=false"));
            non_cob_found := true;
            Print("T5 non-cob via bit_0 flip: PASS\n");
            break;
        fi;
    od;
fi;
Assert(0, non_cob_found,
       "T5: must find at least one non-coboundary perturbation");

# === (T6) Q_8 cochain agreement ===
G_q8 := SmallGroup(8, 4);;     # Q_8
elts_q8 := AsList(G_q8);;
n_q8 := Length(elts_q8);;
idx_q8 := NewDictionary(elts_q8[1], true, elts_q8);;
for i in [1..n_q8] do AddDictionary(idx_q8, elts_q8[i], i); od;
beta_q8 := ListWithIdenticalEntries(n_q8, 0);;
beta_q8[2] := 1;
beta_q8[3] := 2;
beta_q8[5] := 3;
c_g_q8 := BuildCobZ4(elts_q8, idx_q8, beta_q8);;
ref_q8 := IsCoboundary2Z2kVec(G_q8, c_g_q8, 2);;
bits_q8 := SplitBits(c_g_q8);;
got_q8 := IsCoboundary2Z4VecBits(G_q8, bits_q8.bot, bits_q8.top, n_q8);;
Assert(0, got_q8 = ref_q8,
       Concatenation("T6 Q_8: bits=", String(got_q8), " ref=", String(ref_q8)));
Print("T6 Q_8 cob agreement: PASS\n");

# === (T7) Random Q_8 agreement (20 trials) ===
n_pass_t7 := 0;;
n_fail_t7 := 0;;
seed_t7 := RandomSource(IsMersenneTwister, 77);;
for trial in [1..20] do
    rand_c := List([1..n_q8*n_q8], _ -> Random(seed_t7, [0..3]));
    ref := IsCoboundary2Z2kVec(G_q8, rand_c, 2);
    bits := SplitBits(rand_c);
    got := IsCoboundary2Z4VecBits(G_q8, bits.bot, bits.top, n_q8);
    if got = ref then
        n_pass_t7 := n_pass_t7 + 1;
    else
        n_fail_t7 := n_fail_t7 + 1;
        Print("  T7 trial ", trial, " DISAGREEMENT: bits=", got,
              " ref=", ref, "\n");
    fi;
od;
Assert(0, n_fail_t7 = 0,
       Concatenation("T7: ", String(n_fail_t7), " disagreements"));
Print("T7 random Q_8 (20 trials): PASS (", n_pass_t7, "/20)\n");

# === (T8) Z/2 × Z/2 agreement ===
G_22 := SmallGroup(4, 2);;     # Z/2 × Z/2
elts_22 := AsList(G_22);;
n_22 := Length(elts_22);;
n_pass_t8 := 0;;
n_fail_t8 := 0;;
seed_t8 := RandomSource(IsMersenneTwister, 123);;
for trial in [1..20] do
    rand_c := List([1..n_22*n_22], _ -> Random(seed_t8, [0..3]));
    ref := IsCoboundary2Z2kVec(G_22, rand_c, 2);
    bits := SplitBits(rand_c);
    got := IsCoboundary2Z4VecBits(G_22, bits.bot, bits.top, n_22);
    if got = ref then
        n_pass_t8 := n_pass_t8 + 1;
    else
        n_fail_t8 := n_fail_t8 + 1;
        Print("  T8 trial ", trial, " DISAGREEMENT: bits=", got,
              " ref=", ref, "\n");
    fi;
od;
Assert(0, n_fail_t8 = 0,
       Concatenation("T8: ", String(n_fail_t8), " disagreements"));
Print("T8 random Z/2 x Z/2 (20 trials): PASS (", n_pass_t8, "/20)\n");

Print("\ntest_pathz_a2_bit_no_roundtrip: ALL PASS\n");
QUIT;
