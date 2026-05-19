# test_d8_classifier.g
#
# K-4a-T2 (issue #194): tests for ClassifyOnD8 (in `d8_classifier.g`).
#
# Acceptance criteria (per issue body):
#
#   (C1)  Self-classify: for each k in {1, ..., 12},
#             ClassifyOnD8(LoadModularData(8, 3, k).S,
#                          LoadModularData(8, 3, k).T)
#         returns class_idx = k. All 12 stored classes are pairwise
#         inequivalent (per Mignard-Schauenburg + the explicit storage
#         convention used in modular_data/8/3/), so the answer is unique.
#
#   (C2)  Corrupted-input fail: feed (S1, T1) with one T-entry tweaked
#         so no stored class matches; assert class_idx = fail.
#
#   (C3)  Cross-class inequivalence at the matcher level: spot-check
#         several inter-class pairs and confirm JointPermutationMatcher
#         returns ok = false for each.
#
#   (C4)  Permuted-input round-trip: apply a random permutation to
#         class-1's (S, T) and confirm ClassifyOnD8 still returns 1.

# ---- Test bookkeeping --------------------------------------------------
D8C_PASSES   := 0;;
D8C_FAILURES := [];;

D8CAssertEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
        D8C_PASSES := D8C_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Print("         expected: ", expected, "\n");
        Print("         got:      ", got, "\n");
        Add(D8C_FAILURES, label);
    fi;
end;;

D8CAssertTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
        D8C_PASSES := D8C_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Add(D8C_FAILURES, label);
    fi;
end;;

# ---- Locate the worktree and dependencies ------------------------------
D8C_SELF := INPUT_FILENAME();;
if D8C_SELF = fail or D8C_SELF = "stream" then
    Error("test_d8_classifier.g: INPUT_FILENAME() unavailable; ",
          "Read the file by its absolute path.");
fi;
D8C_SELFDIR := D8C_SELF{[1..Length(D8C_SELF)
                          - Length("/test_d8_classifier.g")]};;
D8C_SCRIPTSDIR := D8C_SELFDIR{
    [1..Length(D8C_SELFDIR) - Length("/tests")]};;
D8C_WT_ROOT := D8C_SCRIPTSDIR{
    [1..Length(D8C_SCRIPTSDIR) - Length("/extraspecial_orbifolds/scripts")]};;

# Load src/modular_data.g first so LoadModularData is bound before
# d8_classifier.g asserts on its presence.
Read(Concatenation(D8C_WT_ROOT, "/src/modular_data.g"));
D8CAssertTrue("LoadModularData bound (from src/modular_data.g)",
              IsBound(LoadModularData));

# Load the module under test. d8_classifier.g auto-loads the matcher
# sibling, so we should not Read joint_permutation_matcher.g explicitly.
Read(Concatenation(D8C_SCRIPTSDIR, "/d8_classifier.g"));
D8CAssertTrue("ClassifyOnD8 bound", IsBound(ClassifyOnD8));
D8CAssertTrue("JointPermutationMatcher bound (transitively)",
              IsBound(JointPermutationMatcher));

# ---- Locate the modular_data tree --------------------------------------
D8C_MD_ROOT := fail;;
for D8C_CAND in
    [ Concatenation(D8C_WT_ROOT, "/../modular_data"),
      "/Users/thomasgemunden/Projects/group_cohomology/modular_data" ] do
    if D8C_MD_ROOT = fail
       and IsExistingFile(Concatenation(D8C_CAND, "/8/3/1.txt")) then
        D8C_MD_ROOT := D8C_CAND;
    fi;
od;
if D8C_MD_ROOT = fail then
    Error("test_d8_classifier.g: cannot locate modular_data tree.");
fi;
Print("modular_data root: ", D8C_MD_ROOT, "\n");

# ---- Prepare Modular_Data symlink and chdir there ----------------------
D8C_LINKDIR := Concatenation(D8C_SELFDIR, "/k4a/d8");;
if not IsExistingFile(D8C_LINKDIR) then
    Exec(Concatenation("mkdir -p '", D8C_LINKDIR, "'"));
fi;
D8C_LINKPATH := Concatenation(D8C_LINKDIR, "/Modular_Data");;
if not IsExistingFile(D8C_LINKPATH) then
    Exec(Concatenation("ln -s '", D8C_MD_ROOT, "' '",
                       D8C_LINKPATH, "'"));
fi;
if not IsExistingFile(Concatenation(D8C_LINKPATH, "/8/3/1.txt")) then
    Error("test_d8_classifier.g: Modular_Data symlink at ",
          D8C_LINKPATH, " does not resolve to a tree containing ",
          "8/3/1.txt.");
fi;
ChangeDirectoryCurrent(D8C_LINKDIR);

# ---- Test C1: self-classify for each k in {1..12} ----------------------
Print("\nTest C1: self-classify for each k in {1, ..., 12}.\n");
D8C_RESULTS := [];;
for D8C_K in [1..12] do
    D8C_T0 := Runtime();
    D8C_DATA := LoadModularData(8, 3, D8C_K);
    D8C_RES  := ClassifyOnD8(D8C_DATA.S, D8C_DATA.T);
    D8C_DT   := Runtime() - D8C_T0;
    Print("  k = ", D8C_K, ": class_idx = ", D8C_RES.class_idx,
          ", all_matches = ", D8C_RES.all_matches,
          " (", D8C_DT, "ms)\n");
    Add(D8C_RESULTS, D8C_RES);
    D8CAssertEqual(Concatenation("class ", String(D8C_K),
                                 ": class_idx = ", String(D8C_K)),
                   D8C_RES.class_idx, D8C_K);
    D8CAssertEqual(Concatenation("class ", String(D8C_K),
                                 ": all_matches = [", String(D8C_K), "]"),
                   D8C_RES.all_matches, [D8C_K]);
    D8CAssertTrue(Concatenation("class ", String(D8C_K),
                                ": pi is a permutation of [1..22]"),
                  IsList(D8C_RES.pi)
                  and Length(D8C_RES.pi) = 22
                  and SortedList(D8C_RES.pi) = [1..22]);
od;

# ---- Test C2: corrupted-input fail via the public API ------------------
# We feed class-1's (S, T) but corrupt T at one entry so the call hits
# no stored class. This is a clean way to exercise the "fail" branch of
# ClassifyOnD8 without smuggling in non-D_8 data.
Print("\nTest C2: corrupted input / no-match case via the public API.\n");
D8C_DATA1 := LoadModularData(8, 3, 1);;
D8C_S1 := D8C_DATA1.S;;
D8C_T1V := DiagonalOfMat(D8C_DATA1.T);;
D8C_T1V_BAD := ShallowCopy(D8C_T1V);;
# Bump one T-eigenvalue to a value that cannot occur in any stored class.
D8C_T1V_BAD[1] := D8C_T1V_BAD[1] * E(99) + 1;;
D8C_RES_BAD := ClassifyOnD8(D8C_S1, D8C_T1V_BAD);;
Print("  corrupted input: class_idx = ", D8C_RES_BAD.class_idx,
      ", all_matches = ", D8C_RES_BAD.all_matches, "\n");
D8CAssertEqual("corrupted input: class_idx = fail",
               D8C_RES_BAD.class_idx, fail);
D8CAssertEqual("corrupted input: all_matches = []",
               D8C_RES_BAD.all_matches, []);
D8CAssertEqual("corrupted input: pi = fail", D8C_RES_BAD.pi, fail);

# ---- Test C3: cross-class fail at the matcher level --------------------
# Directly assert that two distinct stored D_8 classes fail to match
# under the underlying matcher. This is the explicit cross-class
# inequivalence guaranteed by Mignard-Schauenburg + the convention that
# modular_data/8/3/{1..12}.txt stores Aut(D_8)-orbit reps.
Print("\nTest C3: cross-class inequivalence at matcher level.\n");
D8C_INEQUIV_HITS := 0;;
D8C_INEQUIV_PAIRS := [];;
# Spot-check a handful of pairs spanning the index range.
for D8C_PAIR in [ [1, 2], [1, 3], [2, 5], [4, 7], [5, 9], [8, 12], [10, 11] ] do
    D8C_DATA_A := LoadModularData(8, 3, D8C_PAIR[1]);
    D8C_DATA_B := LoadModularData(8, 3, D8C_PAIR[2]);
    D8C_MATCH := JointPermutationMatcher(
        D8C_DATA_A.S, D8C_DATA_A.T,
        D8C_DATA_B.S, D8C_DATA_B.T);
    Print("  pair ", D8C_PAIR, ": ok = ", D8C_MATCH.ok, "\n");
    if not D8C_MATCH.ok then
        D8C_INEQUIV_HITS := D8C_INEQUIV_HITS + 1;
    else
        Add(D8C_INEQUIV_PAIRS, D8C_PAIR);
    fi;
od;
D8CAssertTrue("at least one inter-class pair is inequivalent",
              D8C_INEQUIV_HITS >= 1);
# Strong form: ALL the spot-checked pairs are inequivalent. If this
# fails, two of the stored D_8 cocycle files actually agree up to row
# permutation — surprising and worth investigating.
D8CAssertEqual("all 7 spot-checked inter-class pairs inequivalent",
               D8C_INEQUIV_HITS, 7);
if D8C_INEQUIV_PAIRS <> [] then
    Print("  pairs that DID match (unexpected): ",
          D8C_INEQUIV_PAIRS, "\n");
fi;

# ---- Test C4: permuted-input round trip through ClassifyOnD8 -----------
# Feed a randomly-permuted version of class-1's data and check it still
# classifies to class 1.
Print("\nTest C4: permuted class-1 input still classifies to k = 1.\n");
Reset(GlobalMersenneTwister, 194);;
D8C_PI_RAND := List([1..22], i -> i);;
for D8C_I in Reversed([2..22]) do
    D8C_J := Random(GlobalMersenneTwister, [1..D8C_I]);
    D8C_TMP := D8C_PI_RAND[D8C_I];
    D8C_PI_RAND[D8C_I] := D8C_PI_RAND[D8C_J];
    D8C_PI_RAND[D8C_J] := D8C_TMP;
od;
D8C_S1P := List([1..22],
    i -> List([1..22],
              j -> D8C_S1[D8C_PI_RAND[i]][D8C_PI_RAND[j]]));;
D8C_T1P := List([1..22], i -> D8C_T1V[D8C_PI_RAND[i]]);;
D8C_T0 := Runtime();;
D8C_RES_PERM := ClassifyOnD8(D8C_S1P, D8C_T1P);;
Print("  permuted class-1: class_idx = ", D8C_RES_PERM.class_idx,
      " (", Runtime() - D8C_T0, "ms)\n");
D8CAssertEqual("permuted class-1: class_idx = 1",
               D8C_RES_PERM.class_idx, 1);
D8CAssertEqual("permuted class-1: all_matches = [1]",
               D8C_RES_PERM.all_matches, [1]);

# ---- Final summary -----------------------------------------------------
Print("\n=== Final summary ===\n");
Print("  passes:   ", D8C_PASSES, "\n");
Print("  failures: ", Length(D8C_FAILURES), "\n");
if Length(D8C_FAILURES) = 0 then
    Print("\ntest_d8_classifier: PASS\n");
else
    Print("\ntest_d8_classifier: FAIL (",
          Length(D8C_FAILURES), "):\n");
    for D8C_F in D8C_FAILURES do
        Print("  - ", D8C_F, "\n");
    od;
fi;

QUIT;
