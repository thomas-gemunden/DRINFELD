# test_joint_permutation_matcher.g
#
# K-4a-T1 (issue #192): tests for JointPermutationMatcher (in
# `joint_permutation_matcher.g`).
#
# Acceptance criteria (per issue body):
#
#   (T1)  Self-match: feed (S, T, S, T) from LoadModularData(8, 4, 1) and
#         verify the matcher returns a valid pi (need not be identity —
#         re-verify S/T equations under whatever pi it returns).
#
#   (T2)  Random permutation round-trip: pick a random pi_rand of length
#         22 (the Q_8 rank), construct
#             S' := pi_rand . S . pi_rand^{-1},
#             T' := pi_rand . T,
#         and run the matcher on (S, T, S', T'). Should succeed; the
#         recovered pi need not equal pi_rand, just satisfy the equations.
#
#   (T3)  Mignard-Schauenburg negative: run matcher on
#             LoadModularData(8, 4, 1) vs LoadModularData(8, 4, 2).
#         Per `q8_extension_type/writeup.md` these are inequivalent MTCs.
#         Expect pi = fail.
#
# Plus a couple of cheap shape-and-error-path checks.
#
# Modular data tree resolution.
# -----------------------------
# Following the pattern in `tests/test_aut_nt.g`, we locate the
# precomputed modular_data tree by trying a list of candidate paths
# (relative + absolute). For LoadModularData proper we use
# ChangeDirectoryCurrent into a dir containing a `Modular_Data` symlink;
# if no such symlink is present we synthesise it via Exec("ln -s ...").
#
# Run from anywhere:
#     /opt/homebrew/bin/gap -q -b -c 'Read("ABS/PATH/test_joint_permutation_matcher.g");'

# ---- Test bookkeeping --------------------------------------------------
JPM_PASSES   := 0;;
JPM_FAILURES := [];;

JPMAssertEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
        JPM_PASSES := JPM_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Print("         expected: ", expected, "\n");
        Print("         got:      ", got, "\n");
        Add(JPM_FAILURES, label);
    fi;
end;;

JPMAssertTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
        JPM_PASSES := JPM_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Add(JPM_FAILURES, label);
    fi;
end;;

# ---- Locate ourselves and the module under test ------------------------
JPM_SELF := INPUT_FILENAME();;
if JPM_SELF = fail or JPM_SELF = "stream" then
    Error("test_joint_permutation_matcher.g: INPUT_FILENAME() ",
          "unavailable; Read the file by its absolute path.");
fi;
JPM_SELFDIR := JPM_SELF{[1..Length(JPM_SELF)
                          - Length("/test_joint_permutation_matcher.g")]};;
# tests/test_joint_permutation_matcher.g
# -> .../extraspecial_orbifolds/scripts/tests/
# parent: .../extraspecial_orbifolds/scripts/
JPM_SCRIPTSDIR := JPM_SELFDIR{[1..Length(JPM_SELFDIR) - Length("/tests")]};;
# Look further up to find the repo root (the worktree top).
JPM_WT_ROOT := JPM_SCRIPTSDIR{
    [1..Length(JPM_SCRIPTSDIR) - Length("/extraspecial_orbifolds/scripts")]};;

# Load the module under test.
Read(Concatenation(JPM_SCRIPTSDIR, "/joint_permutation_matcher.g"));
JPMAssertTrue("JointPermutationMatcher bound",
              IsBound(JointPermutationMatcher));

# We also need LoadModularData for tests T1 and T3.
Read(Concatenation(JPM_WT_ROOT, "/src/modular_data.g"));
JPMAssertTrue("LoadModularData bound", IsBound(LoadModularData));

# ---- Locate the modular_data tree --------------------------------------
JPM_MD_ROOT := fail;;
for JPM_CAND in
    [ Concatenation(JPM_WT_ROOT, "/../modular_data"),
      "/Users/thomasgemunden/Projects/group_cohomology/modular_data" ] do
    if JPM_MD_ROOT = fail
       and IsExistingFile(Concatenation(JPM_CAND, "/8/4/1.txt")) then
        JPM_MD_ROOT := JPM_CAND;
    fi;
od;
if JPM_MD_ROOT = fail then
    Error("test_joint_permutation_matcher.g: cannot locate modular_data ",
          "tree containing 8/4/1.txt. Tried sibling of worktree and ",
          "/Users/thomasgemunden/Projects/group_cohomology/modular_data.");
fi;
Print("modular_data root: ", JPM_MD_ROOT, "\n");

# ---- Prepare a Modular_Data symlink for LoadModularData ----------------
# LoadModularData looks for "Modular_Data/<n>/<m>/<i>.txt" relative to
# GAP's cwd. We chdir (GAP-internal) into a stable test-side directory
# and synthesise the symlink there if it is missing.
JPM_LINKDIR := Concatenation(JPM_SELFDIR, "/k4a/q8");;
if not IsExistingFile(JPM_LINKDIR) then
    Exec(Concatenation("mkdir -p '", JPM_LINKDIR, "'"));
fi;
JPM_LINKPATH := Concatenation(JPM_LINKDIR, "/Modular_Data");;
if not IsExistingFile(JPM_LINKPATH) then
    Exec(Concatenation("ln -s '", JPM_MD_ROOT, "' '",
                       JPM_LINKPATH, "'"));
fi;
if not IsExistingFile(Concatenation(JPM_LINKPATH, "/8/4/1.txt")) then
    Error("test_joint_permutation_matcher.g: Modular_Data symlink at ",
          JPM_LINKPATH, " does not resolve to a tree containing ",
          "8/4/1.txt.");
fi;
ChangeDirectoryCurrent(JPM_LINKDIR);

# ---- Helpers -----------------------------------------------------------
# Verify a candidate pi against (S1, T1, S2, T2) directly (do not trust
# matcher's internal verifier; the tests are the trusted reference).
JPMVerifyEquations := function(pi, S1, T1vec, S2, T2vec)
    local n, i, j;
    n := Length(T2vec);
    if pi = fail or not IsList(pi) or Length(pi) <> n then
        return false;
    fi;
    for i in [1..n] do
        if T2vec[i] <> T1vec[pi[i]] then
            return false;
        fi;
    od;
    for i in [1..n] do
        for j in [1..n] do
            if S2[i][j] <> S1[pi[i]][pi[j]] then
                return false;
            fi;
        od;
    od;
    return true;
end;;

# ---- Test T1: self-match -----------------------------------------------
Print("\nTest T1: self-match on LoadModularData(8, 4, 1).\n");
JPM_T0 := Runtime();;
JPM_DATA1 := LoadModularData(8, 4, 1);;
JPM_S1 := JPM_DATA1.S;;
JPM_T1V := DiagonalOfMat(JPM_DATA1.T);;
JPMAssertEqual("rank from LoadModularData(8,4,1) is 22",
               Length(JPM_T1V), 22);

JPM_M11 := JointPermutationMatcher(JPM_S1, JPM_T1V, JPM_S1, JPM_T1V);;
Print("  matcher ok = ", JPM_M11.ok, ", elapsed ms = ",
      Runtime() - JPM_T0, "\n");
JPMAssertTrue("self-match: ok = true", JPM_M11.ok);
JPMAssertTrue("self-match: pi is a list of length 22",
              IsList(JPM_M11.pi) and Length(JPM_M11.pi) = 22);
# Re-verify equations independently.
JPMAssertTrue("self-match: returned pi satisfies S/T equations",
              JPMVerifyEquations(JPM_M11.pi,
                                 JPM_S1, JPM_T1V,
                                 JPM_S1, JPM_T1V));
# Note: pi need not be the identity (Aut(N, T) has order 6 for class 1 —
# any of its 6 elements is a valid answer). We document that here.
Print("  identity? pi = [1..22]: ", JPM_M11.pi = [1..22], "\n");

# Accept either vector or DiagonalMat input — the matcher normalises.
JPM_M11D := JointPermutationMatcher(JPM_S1, JPM_DATA1.T,
                                    JPM_S1, JPM_DATA1.T);;
JPMAssertTrue("self-match: accepts DiagonalMat input for T", JPM_M11D.ok);

# ---- Test T2: random permutation round-trip ---------------------------
Print("\nTest T2: random permutation round-trip (rank 22).\n");
# Seed for reproducibility (GAP's Random() takes (state, range) but the
# default global generator is deterministic when re-seeded via Reset).
Reset(GlobalMersenneTwister, 192);;
JPM_PI_RAND := List([1..22], i -> i);;
# Knuth-shuffle.
for JPM_I in Reversed([2..22]) do
    JPM_J := Random(GlobalMersenneTwister, [1..JPM_I]);
    JPM_TMP := JPM_PI_RAND[JPM_I];
    JPM_PI_RAND[JPM_I] := JPM_PI_RAND[JPM_J];
    JPM_PI_RAND[JPM_J] := JPM_TMP;
od;
Print("  pi_rand = ", JPM_PI_RAND, "\n");
JPMAssertEqual("pi_rand is a permutation of [1..22]",
               SortedList(JPM_PI_RAND), [1..22]);

# Build (S', T') as the pi_rand-shuffle of (S, T):
#     S'[i][j] = S[pi_rand[i]][pi_rand[j]],   T'[i] = T[pi_rand[i]].
JPM_S_PRIME := List([1..22],
    i -> List([1..22], j -> JPM_S1[JPM_PI_RAND[i]][JPM_PI_RAND[j]]));;
JPM_T_PRIME := List([1..22], i -> JPM_T1V[JPM_PI_RAND[i]]);;

# Sanity: the constructed (S', T') is itself a valid alignment of
# (S, T) under pi_rand.
JPMAssertTrue("constructed (S', T') round-trips pi_rand",
              JPMVerifyEquations(JPM_PI_RAND, JPM_S1, JPM_T1V,
                                 JPM_S_PRIME, JPM_T_PRIME));

# Run matcher and check (need not equal pi_rand — Aut may permit
# alternatives).
JPM_T0 := Runtime();;
JPM_M_RT := JointPermutationMatcher(JPM_S1, JPM_T1V,
                                    JPM_S_PRIME, JPM_T_PRIME);;
Print("  matcher ok = ", JPM_M_RT.ok, ", elapsed ms = ",
      Runtime() - JPM_T0, "\n");
JPMAssertTrue("round-trip: ok = true", JPM_M_RT.ok);
JPMAssertTrue("round-trip: pi is a permutation of [1..22]",
              IsList(JPM_M_RT.pi)
              and SortedList(JPM_M_RT.pi) = [1..22]);
JPMAssertTrue("round-trip: recovered pi satisfies S/T equations",
              JPMVerifyEquations(JPM_M_RT.pi,
                                 JPM_S1, JPM_T1V,
                                 JPM_S_PRIME, JPM_T_PRIME));
Print("  recovered pi = pi_rand? ", JPM_M_RT.pi = JPM_PI_RAND, "\n");

# ---- Test T3: Mignard-Schauenburg negative -----------------------------
Print("\nTest T3: class 1 vs class 2 (Mignard-Schauenburg inequivalence).\n");
JPM_DATA2 := LoadModularData(8, 4, 2);;
JPM_S2 := JPM_DATA2.S;;
JPM_T2V := DiagonalOfMat(JPM_DATA2.T);;
JPM_T0 := Runtime();;
JPM_M12 := JointPermutationMatcher(JPM_S1, JPM_T1V, JPM_S2, JPM_T2V);;
Print("  matcher ok = ", JPM_M12.ok, ", elapsed ms = ",
      Runtime() - JPM_T0, "\n");
JPMAssertEqual("class 1 vs class 2: pi = fail", JPM_M12.pi, fail);
JPMAssertEqual("class 1 vs class 2: ok = false", JPM_M12.ok, false);
JPMAssertTrue("class 1 vs class 2: reason is a non-empty string",
              IsString(JPM_M12.reason) and Length(JPM_M12.reason) > 0);
Print("  reason: ", JPM_M12.reason, "\n");

# ---- Test T4: shape mismatch detection (cheap) -------------------------
Print("\nTest T4: shape-mismatch error paths.\n");
JPM_S_SMALL := [[1, 2], [3, 4]];;
JPM_T_SMALL := [1, 1];;
JPM_M_SHAPE := JointPermutationMatcher(JPM_S1, JPM_T1V,
                                       JPM_S_SMALL, JPM_T_SMALL);;
JPMAssertEqual("rank-mismatch: pi = fail", JPM_M_SHAPE.pi, fail);
JPMAssertEqual("rank-mismatch: ok = false", JPM_M_SHAPE.ok, false);

# Vacuous case.
JPM_M_EMPTY := JointPermutationMatcher([], [], [], []);;
JPMAssertEqual("empty inputs: pi = []", JPM_M_EMPTY.pi, []);
JPMAssertEqual("empty inputs: ok = true", JPM_M_EMPTY.ok, true);

# T-multiset disagreement (very cheap reject).
JPM_T_DIFFMS := ShallowCopy(JPM_T1V);;
JPM_T_DIFFMS[1] := JPM_T_DIFFMS[1] + 1;;  # corrupt one entry
JPM_M_TMS := JointPermutationMatcher(JPM_S1, JPM_T1V,
                                     JPM_S1, JPM_T_DIFFMS);;
JPMAssertEqual("T-multiset-mismatch: pi = fail", JPM_M_TMS.pi, fail);

# ---- Final summary -----------------------------------------------------
Print("\n=== Final summary ===\n");
Print("  passes:   ", JPM_PASSES, "\n");
Print("  failures: ", Length(JPM_FAILURES), "\n");
if Length(JPM_FAILURES) = 0 then
    Print("\ntest_joint_permutation_matcher: PASS\n");
else
    Print("\ntest_joint_permutation_matcher: FAIL (",
          Length(JPM_FAILURES), "):\n");
    for JPM_F in JPM_FAILURES do
        Print("  - ", JPM_F, "\n");
    od;
fi;

QUIT;
