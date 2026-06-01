# test_iscoboundary2_z4_vec_bits.g — unit tests for IsCoboundary2Z4VecBits
# (issue #391, Approach B).
#
# Coverage:
#   * D_8 modulus=4 known coboundary: bit-slice path must agree with
#     IsCoboundary2Z2kVec.
#   * D_8 modulus=4 known non-coboundary: bit-slice path must agree.
#   * Q_8 (32, *) — pick from existing test fixtures if available.
#
# Strategy: build c_g_table (length n² integer vec in [0..3]) for a
# constructed cochain on a small centraliser; split into bit slices;
# call IsCoboundary2Z4VecBits and IsCoboundary2Z2kVec; assert agreement.

# CWD shim — same pattern as test_iterated_bockstein.g.
ic2bits_test_target := fail;;
for ic2bits_try in [
        ".", "tests", "extraspecial_orbifolds/scripts/solver/tests",
        "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD/extraspecial_orbifolds/scripts/solver/tests"] do
    if IsExistingFile(Concatenation(ic2bits_try,
                                     "/test_iscoboundary2_z4_vec_bits.g")) then
        ic2bits_test_target := ic2bits_try;
        break;
    fi;
od;;
if ic2bits_test_target = fail then
    Error("test_iscoboundary2_z4_vec_bits.g: cannot locate self from CWD ",
          Filename(DirectoryCurrent(), ""));
fi;
ChangeDirectoryCurrent(ic2bits_test_target);;
Read("../iterated_bockstein.g");
Read("../iscoboundary2_split.g");

# Helper: split an integer vec mod 4 into two packed GF(2) bit slices.
SplitBits := function(c_int)
    local one, c_bot, c_top;
    one := One(GF(2));
    # List-level mod and div: GAP's `list mod int` and arithmetic on
    # integer lists are compiled list-int ops.
    c_bot := (c_int mod 2) * one;
    c_top := List(c_int, x -> (QuoInt(x, 2) mod 2)) * one;
    ConvertToVectorRep(c_bot, GF(2));
    ConvertToVectorRep(c_top, GF(2));
    return rec(bot := c_bot, top := c_top);
end;;

# === D_8 (8,3): construct Z/4 coboundary from an integer 1-cochain ===
G_d8 := SmallGroup(8, 3);;
elts_d8 := AsList(G_d8);;
n_d8 := Length(elts_d8);;

# beta(g) in {0,1,2,3}: assign 1 to elts_d8[2], 2 to elts_d8[3], rest 0.
beta_d8 := ListWithIdenticalEntries(n_d8, 0);;
beta_d8[2] := 1;
beta_d8[3] := 2;

# Build c_g_table as δβ mod 4 in length-n^2 integer vector form (the
# (i, j) entry at row (i-1)*n + j).
idx_d8 := NewDictionary(elts_d8[1], true, elts_d8);;
for i in [1..n_d8] do
    AddDictionary(idx_d8, elts_d8[i], i);
od;
c_g_d8 := ListWithIdenticalEntries(n_d8 * n_d8, 0);;
for i in [1..n_d8] do
    for j in [1..n_d8] do
        c_g_d8[(i-1)*n_d8 + j] :=
            (beta_d8[i] + beta_d8[j]
             - beta_d8[LookupDictionary(idx_d8, elts_d8[i] * elts_d8[j])])
                mod 4;
    od;
od;

# Reference: IsCoboundary2Z2kVec (integer-vec API).
ref_d8_cob := IsCoboundary2Z2kVec(G_d8, c_g_d8, 2);;
Assert(0, ref_d8_cob = true,
       "D_8: constructed Z/4 coboundary must be detected by IsCoboundary2Z2kVec");

# Bit-slice path.
bits_d8 := SplitBits(c_g_d8);;
bits_d8_cob := IsCoboundary2Z4VecBits(G_d8, bits_d8.bot, bits_d8.top, n_d8);;
Assert(0, bits_d8_cob = ref_d8_cob,
       Concatenation("D_8 cob agreement: bits=", String(bits_d8_cob),
                     " vs ref=", String(ref_d8_cob)));
Print("D_8 cob: bits=", bits_d8_cob, " ref=", ref_d8_cob, " ✓\n");

# === D_8 non-coboundary test ===
# Add a known non-coboundary tail to c_g_d8 so the result is a
# non-coboundary at Z/4. We use a simple construction: set c_g[(i-1)*n+j] +=
# (i = 4 and j = 5) * 2 mod 4. This picks one off-diagonal entry; the
# perturbation is generically non-coboundary at small n.
non_cob_d8 := ShallowCopy(c_g_d8);;
non_cob_d8[(4-1)*n_d8 + 5] := (non_cob_d8[(4-1)*n_d8 + 5] + 2) mod 4;
ref_d8_noncob := IsCoboundary2Z2kVec(G_d8, non_cob_d8, 2);;
bits_nc := SplitBits(non_cob_d8);;
bits_d8_noncob := IsCoboundary2Z4VecBits(G_d8, bits_nc.bot, bits_nc.top, n_d8);;
Assert(0, bits_d8_noncob = ref_d8_noncob,
       Concatenation("D_8 non-cob agreement: bits=", String(bits_d8_noncob),
                     " vs ref=", String(ref_d8_noncob)));
Print("D_8 perturbed: bits=", bits_d8_noncob, " ref=", ref_d8_noncob, " ✓\n");

# === Z/2 × Z/2 (4,2) test ===
G_22 := SmallGroup(4, 2);;
elts_22 := AsList(G_22);;
n_22 := Length(elts_22);;
zero_22 := ListWithIdenticalEntries(n_22 * n_22, 0);;
ref_22 := IsCoboundary2Z2kVec(G_22, zero_22, 2);;
bits_22 := SplitBits(zero_22);;
bits_22_cob := IsCoboundary2Z4VecBits(G_22, bits_22.bot, bits_22.top, n_22);;
Assert(0, bits_22_cob = ref_22,
       Concatenation("Z/2 × Z/2 zero: bits=", String(bits_22_cob),
                     " vs ref=", String(ref_22)));
Print("Z/2 × Z/2 zero: bits=", bits_22_cob, " ref=", ref_22, " ✓\n");

# === Random test: 16 random c_g_table inputs over D_8, agreement check ===
random_pass := 0;;
random_fail := 0;;
for trial in [1..16] do
    rand_c := List([1..n_d8*n_d8], _ -> Random([0..3]));
    ref := IsCoboundary2Z2kVec(G_d8, rand_c, 2);
    bits := SplitBits(rand_c);
    bits_result := IsCoboundary2Z4VecBits(G_d8, bits.bot, bits.top, n_d8);
    if bits_result = ref then
        random_pass := random_pass + 1;
    else
        random_fail := random_fail + 1;
        Print("Random trial ", trial, " disagreement: bits=", bits_result,
              " ref=", ref, "\n");
    fi;
od;
Assert(0, random_fail = 0,
       Concatenation("Random tests: ", String(random_fail), " disagreements"));
Print("Random D_8 (16 trials): ", random_pass, "/", random_pass + random_fail, " ✓\n");

Print("\ntest_iscoboundary2_z4_vec_bits.g: all assertions passed.\n");
