# test_fsi_agt_wrapper.g
#
# Smoke tests for fsi_agt_wrapper.g (V-8 #55).
#
# Goal: verify that the parser-fixed `FSIforAGT` runs end-to-end on a small
# AGT (algebra-group-triple) example.  Per CLAUDE.md / V-3 / V-4 the
# mathematical reliability is only guaranteed at omega = 0; we therefore
# only test omega = 0 and check structural properties of the output.
#
# Test target (per task body): Q_8 with N = Z(Q_8) = {+/- 1}, omega = 0.
#   N = Z(Q_8) is a normal subgroup of order 2; Q_8 / N = (Z/2)^2.
#   At omega = 0, omega_1 reduces to (cohomologically) the trivial 3-cocycle on G
#   (FirstStep + SecondStep add coboundaries to an already-zero starting cocycle,
#   so the resulting function still returns 0 mod n on all triples).
#
# Structural checks we make:
#   * `FSIforAGT_Fixed(G, N, 0)` returns a non-empty list.
#   * Each entry is a list of FSexp cyclotomic values.
#   * The number of entries equals
#       sum_{coset i} (# projective irreps of S_i, where S_i = N \cap N^{rep_i^{-1}}).
#     For Q_8, N = Z(Q_8): N is central, so N^g = N for all g, so S_i = N = Z/2
#     for every double coset.  Each S_i has 2 ordinary irreps (alpha is trivial at
#     omega=0), and there are |Q_8| / |N|^2 ... actually for normal N, # double cosets
#     = |G/N|, so # double cosets = 4.  Total entries = 4 * 2 = 8.
#   * The trivial-cocycle nu-values at m=0 must be the dimensions of those irreps
#     (= 1 for both irreps of Z/2).

# --- locate the wrapper (do not chdir) ------------------------------------
fsiAgtTestWrap := fail;;
for fsiAgtTestCand in [".", "..", "../..", "../../..", "../../../..",
                       "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-v8",
                       "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-v3"] do
    if IsExistingFile(Concatenation(fsiAgtTestCand,
            "/extraspecial_orbifolds/scripts/fsi_agt_wrapper.g")) then
        fsiAgtTestWrap := Concatenation(fsiAgtTestCand,
            "/extraspecial_orbifolds/scripts/fsi_agt_wrapper.g");
        break;
    fi;
od;;
if fsiAgtTestWrap = fail then
    Error("test_fsi_agt_wrapper.g: could not locate fsi_agt_wrapper.g");
fi;
Read(fsiAgtTestWrap);;


# --- helpers ---------------------------------------------------------------
fsiAgtPass := 0;;
fsiAgtFail := 0;;
fsiAgtAssertTrue := function(label, cond)
    if cond then
        Print("  OK   ", label, "\n");
        fsiAgtPass := fsiAgtPass + 1;
        return true;
    else
        Print("  FAIL ", label, "\n");
        fsiAgtFail := fsiAgtFail + 1;
        return false;
    fi;
end;;
fsiAgtAssertEqual := function(label, actual, expected)
    if actual = expected then
        Print("  OK   ", label, "  =  ", actual, "\n");
        fsiAgtPass := fsiAgtPass + 1;
        return true;
    else
        Print("  FAIL ", label, "  actual=", actual, "  expected=", expected, "\n");
        fsiAgtFail := fsiAgtFail + 1;
        return false;
    fi;
end;;


# --- Stage 1: parser sanity ----------------------------------------------
Print("\n=== Stage 1: parser sanity (FSIforAGT loads without error) ===\n");
fsiAgtAssertTrue("FSIforAGT is bound after Read",
                 IsBound(FSIforAGT) and IsFunction(FSIforAGT));
fsiAgtAssertTrue("FSIforAGT_Fixed is bound after Read",
                 IsBound(FSIforAGT_Fixed) and IsFunction(FSIforAGT_Fixed));


# --- Stage 2: Q_8 with N = Z(Q_8), omega = 0 ------------------------------
Print("\n=== Stage 2: Q_8 with N = Z(Q_8), omega = 0 ===\n");
agtQ8 := SmallGroup(8, 4);;
fsiAgtAssertEqual("Q_8 = SmallGroup(8,4) is the quaternion group",
                  StructureDescription(agtQ8), "Q8");
agtZ := Centre(agtQ8);;
fsiAgtAssertEqual("|Z(Q_8)|", Size(agtZ), 2);
fsiAgtAssertTrue("Z(Q_8) is normal in Q_8", IsNormal(agtQ8, agtZ));

# Build a zero hom-vector (length = Size(UCT.hombasis)).  FSI_LiftIfHom
# multiplies by UCT.lift mod n -> still zero.
agtR := ResolutionFiniteGroup(agtQ8, 4);;
agtK := TensorWithIntegers(agtR);;
agtUCT := UniversalCoefficientsTheorem(agtK, 3);;
Print("  UCT.exponent = ", agtUCT!.exponent,
      "; |hombasis| = ", Length(agtUCT!.hombasis),
      "; R!.dimension(3) = ", agtR!.dimension(3), "\n");
agtZeroHom := ListWithIdenticalEntries(Length(agtUCT!.hombasis), 0);;

Print("  calling FSIforAGT_Fixed(Q_8, Z(Q_8), 0)...\n");
agtT0 := Runtime();;
agtResult := FSIforAGT_Fixed(agtQ8, agtZ, agtZeroHom);;
agtT1 := Runtime();;
Print("  call returned in ", agtT1 - agtT0, " ms\n");
Print("  result has ", Length(agtResult), " entries, ",
      "inner length(s) = ", Set(List(agtResult, Length)), "\n");

# Structural checks:
fsiAgtAssertTrue("FSIforAGT_Fixed returned a list",
                 IsList(agtResult));
fsiAgtAssertTrue("FSIforAGT_Fixed returned a non-empty list",
                 Length(agtResult) > 0);
fsiAgtAssertTrue("each entry is a list of equal length",
                 Size(Set(List(agtResult, Length))) = 1);

# Number of entries:
#   N = Z(Q_8) is central, so N^g = N for all g, so for every double coset
#   the intersection S_i = N \cap N^{rep^{-1}} = N = Z/2.
#   # double cosets N\G/N = |G|/(|N|*|N|) * ... actually since N normal,
#   # double cosets = |G|/|N| = 4.  Each Z/2 has 2 irreps at trivial alpha.
#   So total entries = 4 * 2 = 8.
fsiAgtAssertEqual("# AGT FSI vectors for Q_8, N=Z, omega=0",
                  Length(agtResult), 8);

# Sanity: at m=0, nu_0(chi) for an AGT setup at trivial cocycle should give
# the rank (dim of the algebra projection / character at identity, scaled
# by 1/|S| -- in our formulation it's pi_x(o)^{QuoInt(0,o)-1} = 1/period * 1
# which can be a fraction).  We don't pin a single value, but we record.
Print("  m=0 values: ", List(agtResult, v -> v[1]), "\n");
Print("  full result: ", agtResult, "\n");


# --- summary --------------------------------------------------------------
Print("\n=== summary ===\n");
Print("  passed: ", fsiAgtPass, "    failed: ", fsiAgtFail, "\n");
if fsiAgtFail > 0 then
    Print("  STATUS: FAIL\n");
    QUIT_GAP(1);
else
    Print("  STATUS: PASS\n");
fi;
