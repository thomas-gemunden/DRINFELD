# test_uc_sequence.g — acceptance for `IntegerCohomologyViaUC` (Q-5).
#
# Run from `extraspecial_orbifolds/scripts/`:
#   gap -q -b tests/test_uc_sequence.g
#
# Set the global Q5_INCLUDE_E_PLUS_3 := true before reading this file to
# also run the E_+(3) check (still <1 s with HAP's direct method, but
# kept gated for parity with the existing test_integral_cohomology.g).
#
# Acceptance cases (per Q-5 brief + issue #25):
#   1. D_8        (SmallGroup(8, 3)):     full n=0..4 table
#   2. Q_8        (SmallGroup(8, 4)):     H^4 = Z/8  (equivalently
#                                         H^3(Q_8; U(1)) = Z/8, matching
#                                         the 8 cocycle classes in
#                                         q8_extension_type/Modular_Data/8/4/)
#   3. E_+(2)     (SmallGroup(32, 49)):   H^4 = (Z/2)^9 + Z/8
#   4. E_+(3)     (SmallGroup(128, 2326)): H^4 = (Z/2)^34 + Z/4    [gated]
#   5. Z_2 x Z_4  (cross-check vs hand-computed UCT)

BreakOnError := false;;

Read("uc_sequence.g");

Print("\n=== test_uc_sequence.g ===\n");

testFailures := [];;
If_ := function(c, a, b) if c then return a; else return b; fi; end;;
AssertOrLog := function(label, cond)
    Print("  ", label, ": ", If_(cond, "PASS", "FAIL"), "\n");
    if not cond then Add(testFailures, label); fi;
end;;

SortedCopy := function(v) local w; w := ShallowCopy(v); Sort(w); return w; end;;
SameMultiset := function(a, b)
    return SortedCopy(a) = SortedCopy(b);
end;;

# ---------------------------------------------------------------------
# Test 1: D_8 = SmallGroup(8, 3), full n=0..4 table.
#
# Expected (cross-checked against Adem-Milgram / HAP):
#   H^0 = Z          free_rank = 1, torsion = []
#   H^1 = 0          free_rank = 0, torsion = []
#   H^2 = (Z/2)^2    torsion = [2, 2]
#   H^3 = Z/2        torsion = [2]
#   H^4 = (Z/2)^2 + Z/4   torsion = [2, 2, 4]
# ---------------------------------------------------------------------
Print("\n--- Test 1: D_8 = SmallGroup(8, 3), full table n=0..4 ---\n");
D8 := SmallGroup(8, 3);
r_d8 := IntegerCohomologyViaUC(D8, 4);;
IntegerCohomologyPrint(r_d8);

AssertOrLog("D_8 result length = 5", Length(r_d8) = 5);
AssertOrLog("D_8 degrees [0..4]",
            List(r_d8, x -> x.degree) = [0,1,2,3,4]);
AssertOrLog("D_8 every record uses hap-direct source",
            ForAll(r_d8, x -> x.source = "hap-direct"));

AssertOrLog("D_8 H^0: free_rank = 1, torsion = []",
            r_d8[1].free_rank = 1 and r_d8[1].torsion = []);
AssertOrLog("D_8 H^1: free_rank = 0, torsion = []  (no Z-quotient)",
            r_d8[2].free_rank = 0 and r_d8[2].torsion = []);
AssertOrLog("D_8 H^2 torsion = [2, 2]",
            r_d8[3].free_rank = 0
            and SameMultiset(r_d8[3].torsion, [2, 2]));
AssertOrLog("D_8 H^3 torsion = [2]",
            r_d8[4].free_rank = 0
            and SameMultiset(r_d8[4].torsion, [2]));
AssertOrLog("D_8 H^4 torsion = [2, 2, 4]",
            r_d8[5].free_rank = 0
            and SameMultiset(r_d8[5].torsion, [2, 2, 4]));

# ---------------------------------------------------------------------
# Test 2: Q_8 = SmallGroup(8, 4), H^4 = Z/8.
# This matches the 8 cocycle classes in q8_extension_type/Modular_Data/8/4/
# via H^3(Q_8; U(1)) ~= H^4(Q_8; Z) (Bockstein for 0 -> Z -> R -> U(1) -> 0).
# ---------------------------------------------------------------------
Print("\n--- Test 2: Q_8 = SmallGroup(8, 4), n=0..4 ---\n");
Q8 := SmallGroup(8, 4);
r_q8 := IntegerCohomologyViaUC(Q8, 4);;
IntegerCohomologyPrint(r_q8);

AssertOrLog("Q_8 H^0: free_rank = 1",
            r_q8[1].free_rank = 1 and r_q8[1].torsion = []);
AssertOrLog("Q_8 H^1: trivial",
            r_q8[2].free_rank = 0 and r_q8[2].torsion = []);
AssertOrLog("Q_8 H^2 torsion = [2, 2]   (Q_8^ab = Z/2 x Z/2 via UCT)",
            SameMultiset(r_q8[3].torsion, [2, 2]));
AssertOrLog("Q_8 H^3: trivial   (H_2(Q_8;Z) = 0; Schur multiplier=0)",
            r_q8[4].free_rank = 0 and r_q8[4].torsion = []);
AssertOrLog("Q_8 H^4 torsion = [8]   (matches |H^3(Q_8; U(1))| = 8)",
            SameMultiset(r_q8[5].torsion, [8]));

# ---------------------------------------------------------------------
# Test 3: E_+(2) = SmallGroup(32, 49), H^4 = (Z/2)^9 + Z/8.
# ---------------------------------------------------------------------
Print("\n--- Test 3: E_+(2) = SmallGroup(32, 49), H^4 ---\n");
Ep2 := SmallGroup(32, 49);
r_ep2 := IntegerCohomologyViaUC(Ep2, 4);;
Print("  H^4 torsion (sorted) = ", SortedCopy(r_ep2[5].torsion), "\n");
Print("  H^4 #invariant factors = ", Length(r_ep2[5].torsion), "\n");

AssertOrLog("E_+(2) H^4: 10 invariant factors",
            Length(r_ep2[5].torsion) = 10);
AssertOrLog("E_+(2) H^4 torsion = [2^9, 8]",
            SameMultiset(r_ep2[5].torsion,
                         Concatenation(ListWithIdenticalEntries(9, 2),
                                       [8])));

# ---------------------------------------------------------------------
# Test 5: Z_2 x Z_4 cross-check vs HAP direct (UCT pipeline validation).
# Expected H^n(Z_2 x Z_4; Z) for n=0..4:
#   n=0: Z          (rank 1, no torsion)
#   n=1: 0
#   n=2: Z/2 + Z/4
#   n=3: Z/2
#   n=4: Z/2 + Z/2 + Z/4
# (Verified via Künneth on Z_2 and Z_4 separately, or direct HAP query.)
# ---------------------------------------------------------------------
Print("\n--- Test 5: Z_2 x Z_4 cross-check vs HAP direct ---\n");
G_ab := AbelianGroup([2, 4]);
r_ab := IntegerCohomologyViaUC(G_ab, 4);;
IntegerCohomologyPrint(r_ab);

# Direct HAP query for every n -- the wrapper should be a perfect mirror
# (modulo the (free_rank, torsion) split).
for n in [0..4] do
    raw := GroupCohomology(G_ab, n);
    parsed := _UC_ParseHAPCohomology(raw);
    AssertOrLog(Concatenation("Z_2 x Z_4 H^", String(n),
                              " mirrors HAP direct"),
                r_ab[n + 1].free_rank = parsed.free_rank
                and SameMultiset(r_ab[n + 1].torsion, parsed.torsion));
od;

# Explicit numeric anchors (independently verified).
AssertOrLog("Z_2 x Z_4 H^0 = Z",
            r_ab[1].free_rank = 1 and r_ab[1].torsion = []);
AssertOrLog("Z_2 x Z_4 H^1 = 0",
            r_ab[2].free_rank = 0 and r_ab[2].torsion = []);
AssertOrLog("Z_2 x Z_4 H^2 torsion = [2, 4]",
            SameMultiset(r_ab[3].torsion, [2, 4]));
AssertOrLog("Z_2 x Z_4 H^3 torsion = [2]",
            SameMultiset(r_ab[4].torsion, [2]));
AssertOrLog("Z_2 x Z_4 H^4 torsion = [2, 2, 4]",
            SameMultiset(r_ab[5].torsion, [2, 2, 4]));

# ---------------------------------------------------------------------
# Format helper sanity.
# ---------------------------------------------------------------------
Print("\n--- Format-helper sanity ---\n");
AssertOrLog("Format(H^0(D_8)) = \"Z\"",
            IntegerCohomologyFormat(r_d8[1]) = "Z");
AssertOrLog("Format(H^1(D_8)) = \"0\"",
            IntegerCohomologyFormat(r_d8[2]) = "0");
AssertOrLog("Format(H^4(D_8)) collapses pairs to (Z/2)^2 + Z/4",
            IntegerCohomologyFormat(r_d8[5]) = "(Z/2)^2 + Z/4");
AssertOrLog("Format(H^4(Q_8)) = \"Z/8\"",
            IntegerCohomologyFormat(r_q8[5]) = "Z/8");
AssertOrLog("Format(H^4(E_+(2))) = \"(Z/2)^9 + Z/8\"",
            IntegerCohomologyFormat(r_ep2[5]) = "(Z/2)^9 + Z/8");

# ---------------------------------------------------------------------
# Test 4 (gated): E_+(3) = SmallGroup(128, 2326), H^4 = (Z/2)^34 + Z/4.
# ---------------------------------------------------------------------
include_e3 := false;
if IsBoundGlobal("Q5_INCLUDE_E_PLUS_3")
   and ValueGlobal("Q5_INCLUDE_E_PLUS_3") = true then
    include_e3 := true;
fi;
if include_e3 then
    Print("\n--- Test 4: E_+(3) = SmallGroup(128, 2326), H^4 ---\n");
    Ep3 := SmallGroup(128, 2326);
    t0 := Runtime();
    r_ep3 := IntegerCohomologyViaUC(Ep3, 4);;
    t1 := Runtime();
    Print("  E_+(3) IntegerCohomologyViaUC(., 4) wall = ",
          t1 - t0, " ms\n");
    Print("  H^4 #invariant factors = ", Length(r_ep3[5].torsion), "\n");
    AssertOrLog("E_+(3) H^4: 35 invariant factors",
                Length(r_ep3[5].torsion) = 35);
    AssertOrLog("E_+(3) H^4 torsion = [2^34, 4]",
                SameMultiset(r_ep3[5].torsion,
                             Concatenation(ListWithIdenticalEntries(34, 2),
                                           [4])));
else
    Print("\n--- Test 4: E_+(3) SKIPPED ",
          "(set Q5_INCLUDE_E_PLUS_3 := true to run) ---\n");
fi;

# ---------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------
Print("\n=== Summary ===\n");
if IsEmpty(testFailures) then
    Print("test_uc_sequence: ALL PASS\n");
    QUIT_GAP(0);
else
    Print("test_uc_sequence: FAIL (", Length(testFailures), " failures)\n");
    for f in testFailures do Print("  - ", f, "\n"); od;
    QUIT_GAP(1);
fi;
