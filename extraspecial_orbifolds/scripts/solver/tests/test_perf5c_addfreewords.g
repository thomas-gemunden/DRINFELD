# test_perf5c_addfreewords.g
# ---------------------------
# Per-call correctness check for A-7 perf-5c's _AddFreeWordsFast (#282).
# Asserts that _AddFreeWordsFast(w1, w2) produces output bit-identical to
# HAP's AddFreeWords(w1, w2) for a wide sample of inputs.
#
# Coverage:
#   (1) Curated edge cases: empty inputs, length-1 inputs, all-cancel,
#       no-cancel, repeated identical entries with partial cancellation,
#       same-cell-different-sign in same word.
#   (2) Random synthetic word pairs over small (c, g) alphabets, where
#       collisions and cancellations are common.
#   (3) Real intermediate states from Syzygy(R, [a, b, c]) evaluation at
#       m=2 (E_+(2)) -- captures the actual operand shapes seen during
#       _Homotopy2's accumulator loop.
#
# Read this from solver/ or solver/tests/; CWD shim mirrors the pattern
# in snf_wrapper.g.

test_perf5c_orig_dir := DirectoryCurrent();;
test_perf5c_target := fail;;
for test_perf5c_try in [".", "..", "../.."] do
    if IsExistingFile(Concatenation(test_perf5c_try, "/snf_wrapper.g")) then
        test_perf5c_target := test_perf5c_try;
        break;
    fi;
od;;
if test_perf5c_target = fail then
    Error("test_perf5c_addfreewords.g: cannot locate snf_wrapper.g from CWD ",
          Filename(test_perf5c_orig_dir, ""));
fi;
ChangeDirectoryCurrent(test_perf5c_target);;
Read("snf_wrapper.g");
ChangeDirectoryCurrent(Filename(test_perf5c_orig_dir, ""));;

Print("\n=== test_perf5c_addfreewords: per-call correctness of _AddFreeWordsFast ===\n");

mismatches := 0;;
checks := 0;;

CheckPair := function(w1, w2, label)
    local got, expected;
    got := _AddFreeWordsFast(w1, w2);
    expected := AddFreeWords(w1, w2);
    checks := checks + 1;
    if got <> expected then
        mismatches := mismatches + 1;
        Print("MISMATCH ", label, "\n");
        Print("  w1 = ", w1, "\n");
        Print("  w2 = ", w2, "\n");
        Print("  expected = ", expected, "\n");
        Print("  got      = ", got, "\n");
    fi;
end;;

# (1) Curated edge cases.
Print("\n--- (1) Curated edge cases ---\n");

CheckPair([], [], "empty + empty");
CheckPair([], [[1, 3]], "empty + singleton");
CheckPair([[1, 3]], [], "singleton + empty");
CheckPair([[1, 3]], [[-1, 3]], "singleton cancel");
CheckPair([[1, 3]], [[1, 3]], "singleton same-sign (no cancel)");
CheckPair([[1, 3]], [[-1, 4]], "singleton different g (no cancel)");
CheckPair([[1, 3]], [[2, 3]], "singleton different |c| (no cancel)");

# Repeated entries: w has duplicates, v cancels some.
CheckPair([[1, 1], [1, 1], [1, 1]], [[-1, 1]],
          "w has 3 copies of [1,1], v cancels one");
CheckPair([[1, 1], [1, 1], [1, 1]], [[-1, 1], [-1, 1]],
          "w has 3 copies, v cancels two");
CheckPair([[1, 1], [1, 1]], [[-1, 1], [-1, 1], [-1, 1]],
          "w has 2 copies, v has 3 anti-copies (one leftover)");

# Same word in both arguments (everything cancels).
CheckPair([[1, 1], [2, 5], [-3, 7]], [[-1, 1], [-2, 5], [3, 7]],
          "all cancel");

# w longer than v (default branch).
CheckPair([[1, 1], [1, 2], [1, 3], [1, 4], [1, 5]], [[-1, 3]],
          "long w + short v with cancel in middle");

# v longer than w (other branch).
CheckPair([[-1, 3]], [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5]],
          "short w + long v (branch flip)");

# Mixed signs in same word -- with [c,g] and [-c,g] both present.
CheckPair([[1, 1], [-1, 1], [2, 2]], [[-1, 1]],
          "w has both [1,1] and [-1,1]; v has [-1,1] -- cancels first [1,1]");
CheckPair([[1, 1], [-1, 1], [2, 2]], [[1, 1]],
          "w has both [1,1] and [-1,1]; v has [1,1] -- cancels [-1,1]");

# Length 0 / 0 ordering edge: ensure shallow-copy semantics on the
# pass-through (mutating result must not mutate input).
test_w_copy := [[1, 1], [2, 2]];;
test_v_copy := [];;
test_result := _AddFreeWordsFast(test_w_copy, test_v_copy);;
test_result[1] := [99, 99];;
if test_w_copy[1] = [99, 99] then
    Print("MISMATCH: pass-through aliased input (length-0 v case)\n");
    mismatches := mismatches + 1;
fi;
checks := checks + 1;

# Below-threshold path: with length 1+1, _AddFreeWordsFast falls through to HAP.
# This is implicitly tested by the singletons above.

# Above-threshold path: build a 30-entry input to force dict path.
big_w := List([1..30], i -> [i, 1]);;
big_v := [[-15, 1], [-25, 1], [-7, 1]];;
CheckPair(big_w, big_v, "30 entries + 3 cancellations (dict path)");

Print("Curated edge cases: ", checks, " checks, ", mismatches, " mismatches so far.\n");

# (2) Random synthetic pairs.
Print("\n--- (2) Random synthetic pairs (1000 each, small + large) ---\n");

RandomWord := function(max_len, max_c, max_g)
    local len, w, i;
    len := Random([0..max_len]);
    w := [];
    for i in [1..len] do
        Add(w, [(2 * Random([0..1]) - 1) * Random([1..max_c]),
                Random([1..max_g])]);
    od;
    return w;
end;;

for trial in [1..500] do
    CheckPair(RandomWord(10, 5, 5), RandomWord(10, 5, 5),
              Concatenation("random small #", String(trial)));
od;

for trial in [1..500] do
    CheckPair(RandomWord(50, 8, 8), RandomWord(50, 8, 8),
              Concatenation("random medium #", String(trial)));
od;

# Force-large to hit the dict path on both sides.
for trial in [1..200] do
    CheckPair(RandomWord(80, 12, 12), RandomWord(80, 12, 12),
              Concatenation("random large #", String(trial)));
od;

Print("Random sample: ", checks, " checks, ", mismatches, " mismatches so far.\n");

# (3) Real intermediate states from Syzygy(R, [a, b, c]) evaluation at m=2.
Print("\n--- (3) Real Syzygy intermediate states (E_+(2)) ---\n");

G := SmallGroup(32, 49);;     # E_+(2)
setup := SetupCohomology3(G);;
R := setup.R;;

# Pick a non-trivial gRep and its centraliser.
classes := ConjugacyClasses(G);;
non_trivial_idx := First([1..Length(classes)],
                         j -> Order(Representative(classes[j])) > 1);;
gRep := Representative(classes[non_trivial_idx]);;
C := Centralizer(G, gRep);;
elts := AsList(C);;
n := Length(elts);;
Print("Group: E_+(2); gRep order = ", Order(gRep), ", |C| = ", n, "\n");

# For 50 random (a, b) pairs, sample the intermediate AddFreeWords operand
# pairs that appear inside the Syzygy + _Homotopy2 chain.
# Cleanest sample: capture (Syz, S_g1_g2g3) and similar pairs by recomputing.
syz_checks := 0;;
syz_mismatches := 0;;
for trial in [1..50] do
    a := Random([1..n]);
    b := Random([1..n]);
    a_elt := elts[a];
    b_elt := elts[b];
    ab_elt := a_elt * b_elt;
    gRep_a := gRep * a_elt;
    a_gRep := a_elt * gRep;
    b_gRep := b_elt * gRep;
    gRep_b := gRep * b_elt;

    # Capture Syzygy([gRep, a, b]) intermediate words: w = Mult(gRep, Syz([a, b]))
    # paired with Syz([gRep, ab]), then with -Syz([gRep_a, b]) and -Syz([gRep, a]).
    S_a_b := Syzygy(R, [a_elt, b_elt]);
    S_gRep_ab := Syzygy(R, [gRep, ab_elt]);
    S_gRep_a_b := Syzygy(R, [gRep_a, b_elt]);
    S_gRep_a := Syzygy(R, [gRep, a_elt]);

    # Walk through the AddFreeWords sequence in _Syzygy3FromParts for Triple #1.
    Syz1 := List(S_a_b, y -> [y[1], Position(R!.elts,
                                              gRep * R!.elts[y[2]])]);
    # Stage 1: Syz1 + S_gRep_ab
    CheckPair(Syz1, S_gRep_ab,
              Concatenation("syz1+S_gRep_ab trial ", String(trial)));
    Syz1 := AddFreeWords(Syz1, S_gRep_ab);
    # Stage 2: Syz1 + NegateWord(S_gRep_a_b)
    CheckPair(Syz1, NegateWord(S_gRep_a_b),
              Concatenation("syz1+neg trial ", String(trial)));
    Syz1 := AddFreeWords(Syz1, NegateWord(S_gRep_a_b));
    # Stage 3: Syz1 + NegateWord(S_gRep_a)
    CheckPair(Syz1, NegateWord(S_gRep_a),
              Concatenation("syz1+neg2 trial ", String(trial)));
    Syz1 := AddFreeWords(Syz1, NegateWord(S_gRep_a));
    # Stage 4: _Homotopy2's accumulator. For x in Syz1, accumulate
    # AddFreeWords(ans, R!.homotopy(2, x)).
    ans := [];
    for x in Syz1 do
        h := R!.homotopy(2, x);
        CheckPair(ans, h,
                  Concatenation("homotopy2 accum trial ", String(trial)));
        ans := AddFreeWords(ans, h);
    od;
od;

Print("\n=== TOTAL ", checks, " checks, ", mismatches, " mismatches. ===\n");
Assert(0, mismatches = 0,
       Concatenation(String(mismatches), " mismatches found in ",
                     String(checks), " checks"));

Print("\ntest_perf5c_addfreewords: PASS\n");
QUIT;
