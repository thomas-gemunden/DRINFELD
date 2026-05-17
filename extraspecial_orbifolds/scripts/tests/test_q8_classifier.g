# test_q8_classifier.g
#
# K-4a-T1 (issue #192): tests for ClassifyOnQ8 (in `q8_classifier.g`).
#
# Acceptance criteria (per issue body):
#
#   (C1)  Self-classify: for each k in {1, ..., 8},
#             ClassifyOnQ8(LoadModularData(8, 4, k).S,
#                          LoadModularData(8, 4, k).T)
#         returns class_idx = k. All 8 stored classes are pairwise
#         inequivalent (per Mignard-Schauenburg + the explicit search in
#         q8_extension_type/), so the answer is unique.
#
#   (C2)  Cross-class fail: confirm at least one inter-class pair feeds
#         through the underlying matcher with pi = fail. (Implicit in
#         the construction: class_idx in {1, ..., 8} for class-i stored
#         input ensures matches against classes != i return fail.) We
#         also exercise an explicit cross-class call.
#
# Plus a coarse rank check and a self-classify check that uses a
# permuted (S, T) input to exercise the matcher path (rather than the
# trivial identity match).

# ---- Test bookkeeping --------------------------------------------------
Q8C_PASSES   := 0;;
Q8C_FAILURES := [];;

Q8CAssertEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
        Q8C_PASSES := Q8C_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Print("         expected: ", expected, "\n");
        Print("         got:      ", got, "\n");
        Add(Q8C_FAILURES, label);
    fi;
end;;

Q8CAssertTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
        Q8C_PASSES := Q8C_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Add(Q8C_FAILURES, label);
    fi;
end;;

# ---- Locate the worktree and dependencies ------------------------------
Q8C_SELF := INPUT_FILENAME();;
if Q8C_SELF = fail or Q8C_SELF = "stream" then
    Error("test_q8_classifier.g: INPUT_FILENAME() unavailable; ",
          "Read the file by its absolute path.");
fi;
Q8C_SELFDIR := Q8C_SELF{[1..Length(Q8C_SELF)
                          - Length("/test_q8_classifier.g")]};;
Q8C_SCRIPTSDIR := Q8C_SELFDIR{
    [1..Length(Q8C_SELFDIR) - Length("/tests")]};;
Q8C_WT_ROOT := Q8C_SCRIPTSDIR{
    [1..Length(Q8C_SCRIPTSDIR) - Length("/extraspecial_orbifolds/scripts")]};;

# Load src/modular_data.g first so LoadModularData is bound before
# q8_classifier.g asserts on its presence.
Read(Concatenation(Q8C_WT_ROOT, "/src/modular_data.g"));
Q8CAssertTrue("LoadModularData bound (from src/modular_data.g)",
              IsBound(LoadModularData));

# Load the module under test. q8_classifier.g auto-loads the matcher
# sibling, so we should not Read joint_permutation_matcher.g explicitly.
Read(Concatenation(Q8C_SCRIPTSDIR, "/q8_classifier.g"));
Q8CAssertTrue("ClassifyOnQ8 bound", IsBound(ClassifyOnQ8));
Q8CAssertTrue("JointPermutationMatcher bound (transitively)",
              IsBound(JointPermutationMatcher));

# ---- Locate the modular_data tree --------------------------------------
Q8C_MD_ROOT := fail;;
for Q8C_CAND in
    [ Concatenation(Q8C_WT_ROOT, "/../modular_data"),
      "/Users/thomasgemunden/Projects/group_cohomology/modular_data" ] do
    if Q8C_MD_ROOT = fail
       and IsExistingFile(Concatenation(Q8C_CAND, "/8/4/1.txt")) then
        Q8C_MD_ROOT := Q8C_CAND;
    fi;
od;
if Q8C_MD_ROOT = fail then
    Error("test_q8_classifier.g: cannot locate modular_data tree.");
fi;
Print("modular_data root: ", Q8C_MD_ROOT, "\n");

# ---- Prepare Modular_Data symlink and chdir there ----------------------
Q8C_LINKDIR := Concatenation(Q8C_SELFDIR, "/k4a/q8");;
if not IsExistingFile(Q8C_LINKDIR) then
    Exec(Concatenation("mkdir -p '", Q8C_LINKDIR, "'"));
fi;
Q8C_LINKPATH := Concatenation(Q8C_LINKDIR, "/Modular_Data");;
if not IsExistingFile(Q8C_LINKPATH) then
    Exec(Concatenation("ln -s '", Q8C_MD_ROOT, "' '",
                       Q8C_LINKPATH, "'"));
fi;
if not IsExistingFile(Concatenation(Q8C_LINKPATH, "/8/4/1.txt")) then
    Error("test_q8_classifier.g: Modular_Data symlink at ",
          Q8C_LINKPATH, " does not resolve to a tree containing ",
          "8/4/1.txt.");
fi;
ChangeDirectoryCurrent(Q8C_LINKDIR);

# ---- Test C1: self-classify for each k in {1..8} -----------------------
Print("\nTest C1: self-classify for each k in {1, ..., 8}.\n");
Q8C_RESULTS := [];;
for Q8C_K in [1..8] do
    Q8C_T0 := Runtime();
    Q8C_DATA := LoadModularData(8, 4, Q8C_K);
    Q8C_RES  := ClassifyOnQ8(Q8C_DATA.S, Q8C_DATA.T);
    Q8C_DT   := Runtime() - Q8C_T0;
    Print("  k = ", Q8C_K, ": class_idx = ", Q8C_RES.class_idx,
          ", all_matches = ", Q8C_RES.all_matches,
          " (", Q8C_DT, "ms)\n");
    Add(Q8C_RESULTS, Q8C_RES);
    Q8CAssertEqual(Concatenation("class ", String(Q8C_K),
                                 ": class_idx = ", String(Q8C_K)),
                   Q8C_RES.class_idx, Q8C_K);
    Q8CAssertEqual(Concatenation("class ", String(Q8C_K),
                                 ": all_matches = [", String(Q8C_K), "]"),
                   Q8C_RES.all_matches, [Q8C_K]);
    Q8CAssertTrue(Concatenation("class ", String(Q8C_K),
                                ": pi is a permutation of [1..22]"),
                  IsList(Q8C_RES.pi)
                  and Length(Q8C_RES.pi) = 22
                  and SortedList(Q8C_RES.pi) = [1..22]);
od;

# ---- Test C2: cross-class fail via the public API ---------------------
# We feed class-1's (S, T) but corrupt T at one entry so the call hits
# no stored class. This is a clean way to exercise the "fail" branch of
# ClassifyOnQ8 without smuggling in non-Q_8 data.
Print("\nTest C2: cross-class / no-match case via the public API.\n");
Q8C_DATA1 := LoadModularData(8, 4, 1);;
Q8C_S1 := Q8C_DATA1.S;;
Q8C_T1V := DiagonalOfMat(Q8C_DATA1.T);;
Q8C_T1V_BAD := ShallowCopy(Q8C_T1V);;
# Bump one T-eigenvalue to a value that cannot occur in any stored class.
Q8C_T1V_BAD[1] := Q8C_T1V_BAD[1] * E(99) + 1;;
Q8C_RES_BAD := ClassifyOnQ8(Q8C_S1, Q8C_T1V_BAD);;
Print("  corrupted input: class_idx = ", Q8C_RES_BAD.class_idx,
      ", all_matches = ", Q8C_RES_BAD.all_matches, "\n");
Q8CAssertEqual("corrupted input: class_idx = fail",
               Q8C_RES_BAD.class_idx, fail);
Q8CAssertEqual("corrupted input: all_matches = []",
               Q8C_RES_BAD.all_matches, []);
Q8CAssertEqual("corrupted input: pi = fail", Q8C_RES_BAD.pi, fail);

# ---- Test C3: cross-class fail at the matcher level -------------------
# Directly assert that two distinct stored Q_8 classes fail to match
# under the underlying matcher. This is the explicit cross-class
# inequivalence guaranteed by Mignard-Schauenburg + writeup.md.
Print("\nTest C3: cross-class inequivalence at matcher level.\n");
Q8C_INEQUIV_HITS := 0;;
Q8C_INEQUIV_PAIRS := [];;
# Spot-check the diagonally-easiest pair first (class 1 vs 2 is the
# Mignard-Schauenburg poster pair), then a few more for breadth.
for Q8C_PAIR in [ [1, 2], [1, 3], [2, 5], [4, 7], [5, 6] ] do
    Q8C_DATA_A := LoadModularData(8, 4, Q8C_PAIR[1]);
    Q8C_DATA_B := LoadModularData(8, 4, Q8C_PAIR[2]);
    Q8C_MATCH := JointPermutationMatcher(
        Q8C_DATA_A.S, Q8C_DATA_A.T,
        Q8C_DATA_B.S, Q8C_DATA_B.T);
    Print("  pair ", Q8C_PAIR, ": ok = ", Q8C_MATCH.ok, "\n");
    if not Q8C_MATCH.ok then
        Q8C_INEQUIV_HITS := Q8C_INEQUIV_HITS + 1;
    else
        Add(Q8C_INEQUIV_PAIRS, Q8C_PAIR);
    fi;
od;
Q8CAssertTrue("at least one inter-class pair is inequivalent",
              Q8C_INEQUIV_HITS >= 1);
# Strong form: ALL the spot-checked pairs are inequivalent. If this
# fails, two of the stored Q_8 cocycle files actually agree up to row
# permutation — surprising and worth investigating.
Q8CAssertEqual("all 5 spot-checked inter-class pairs inequivalent",
               Q8C_INEQUIV_HITS, 5);
if Q8C_INEQUIV_PAIRS <> [] then
    Print("  pairs that DID match (unexpected): ",
          Q8C_INEQUIV_PAIRS, "\n");
fi;

# ---- Test C4: permuted-input round trip through ClassifyOnQ8 ----------
# Feed a randomly-permuted version of class-1's data and check it still
# classifies to class 1.
Print("\nTest C4: permuted class-1 input still classifies to k = 1.\n");
Reset(GlobalMersenneTwister, 192);;
Q8C_PI_RAND := List([1..22], i -> i);;
for Q8C_I in Reversed([2..22]) do
    Q8C_J := Random(GlobalMersenneTwister, [1..Q8C_I]);
    Q8C_TMP := Q8C_PI_RAND[Q8C_I];
    Q8C_PI_RAND[Q8C_I] := Q8C_PI_RAND[Q8C_J];
    Q8C_PI_RAND[Q8C_J] := Q8C_TMP;
od;
Q8C_S1P := List([1..22],
    i -> List([1..22],
              j -> Q8C_S1[Q8C_PI_RAND[i]][Q8C_PI_RAND[j]]));;
Q8C_T1P := List([1..22], i -> Q8C_T1V[Q8C_PI_RAND[i]]);;
Q8C_T0 := Runtime();;
Q8C_RES_PERM := ClassifyOnQ8(Q8C_S1P, Q8C_T1P);;
Print("  permuted class-1: class_idx = ", Q8C_RES_PERM.class_idx,
      " (", Runtime() - Q8C_T0, "ms)\n");
Q8CAssertEqual("permuted class-1: class_idx = 1",
               Q8C_RES_PERM.class_idx, 1);
Q8CAssertEqual("permuted class-1: all_matches = [1]",
               Q8C_RES_PERM.all_matches, [1]);

# ---- Final summary -----------------------------------------------------
Print("\n=== Final summary ===\n");
Print("  passes:   ", Q8C_PASSES, "\n");
Print("  failures: ", Length(Q8C_FAILURES), "\n");
if Length(Q8C_FAILURES) = 0 then
    Print("\ntest_q8_classifier: PASS\n");
else
    Print("\ntest_q8_classifier: FAIL (",
          Length(Q8C_FAILURES), "):\n");
    for Q8C_F in Q8C_FAILURES do
        Print("  - ", Q8C_F, "\n");
    od;
fi;

QUIT;
