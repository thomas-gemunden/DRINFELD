# test_perf5e_hap_addfreewords.g — verify hot-patched HAP AddFreeWords
# is bit-identical to HAP's original on random + curated + Syzygy inputs.
#
# Usage:
#   gap -q -b /tmp/run_test.g
# where run_test.g contains:
#   LoadPackage("hap");
#   Read("<absolute path to this file>");
#
# The test (a) captures HAP's original AddFreeWords BEFORE installing
# the patch, (b) installs the patch, (c) runs both versions on the same
# inputs and asserts output equality.

# Capture HAP's original AddFreeWords by reading it BEFORE patching.
# At this point AddFreeWords should be HAP's untouched function.
if not IsBoundGlobal("AddFreeWords") then
    Error("test_perf5e_hap_addfreewords: AddFreeWords not bound; ",
          "did you LoadPackage(\"hap\") first?");
fi;

# Save reference to HAP's original.
HAP_AFW5e_RefOriginal := ValueGlobal("AddFreeWords");;

# Install the patch.
patch_dir := DirectoryCurrent();;
patch_file := Filename(DirectoryCurrent(), "install_addfreewords_patch.g");;
if not IsExistingFile(patch_file) then
    # Try sibling lookup if CWD isn't the patch dir.
    patch_file := "install_addfreewords_patch.g";
fi;
Read(patch_file);

# Sanity: patched version should be installed now.
if not IsBoundGlobal("HAP_AFW5e_state") then
    Error("test_perf5e_hap_addfreewords: install_addfreewords_patch did ",
          "not run (HAP_AFW5e_state not bound)");
fi;
HAP_AFW5e_RefPatched := ValueGlobal("AddFreeWords");;

Print("\n=== test_perf5e_hap_addfreewords: bit-identity check vs original ===\n");

mismatches := 0;;
checks := 0;;

CheckPair := function(w1, w2, label)
    local got, expected, w1_copy, w2_copy;
    # Fresh copies for both branches since HAP's original may mutate
    # inputs in some edge cases.
    w1_copy := List(w1, Immutable);
    w2_copy := List(w2, Immutable);
    expected := HAP_AFW5e_RefOriginal(w1_copy, w2_copy);
    w1_copy := List(w1, Immutable);
    w2_copy := List(w2, Immutable);
    got := HAP_AFW5e_RefPatched(w1_copy, w2_copy);
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

CheckPair([[1, 1], [1, 1], [1, 1]], [[-1, 1]],
          "w has 3 copies of [1,1], v cancels one");
CheckPair([[1, 1], [1, 1], [1, 1]], [[-1, 1], [-1, 1]],
          "w has 3 copies, v cancels two");
CheckPair([[1, 1], [1, 1]], [[-1, 1], [-1, 1], [-1, 1]],
          "w has 2 copies, v has 3 anti-copies (one leftover)");

CheckPair([[1, 1], [2, 5], [-3, 7]], [[-1, 1], [-2, 5], [3, 7]],
          "all cancel");

CheckPair([[1, 1], [1, 2], [1, 3], [1, 4], [1, 5]], [[-1, 3]],
          "long w + short v with cancel in middle");

CheckPair([[-1, 3]], [[1, 1], [1, 2], [1, 3], [1, 4], [1, 5]],
          "short w + long v (branch flip)");

CheckPair([[1, 1], [-1, 1], [2, 2]], [[-1, 1]],
          "w has both [1,1] and [-1,1]; v has [-1,1] -- cancels first [1,1]");
CheckPair([[1, 1], [-1, 1], [2, 2]], [[1, 1]],
          "w has both [1,1] and [-1,1]; v has [1,1] -- cancels [-1,1]");

# 30-entry input to force dict path.
big_w := List([1..30], i -> [i, 1]);;
big_v := [[-15, 1], [-25, 1], [-7, 1]];;
CheckPair(big_w, big_v, "30 entries + 3 cancellations (dict path)");

Print("Curated edge cases: ", checks, " checks, ", mismatches, " mismatches so far.\n");

# (2) Random synthetic pairs.
Print("\n--- (2) Random synthetic pairs (1200 trials, small + medium + large) ---\n");

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
for trial in [1..200] do
    CheckPair(RandomWord(80, 12, 12), RandomWord(80, 12, 12),
              Concatenation("random large #", String(trial)));
od;

Print("Random sample: ", checks, " checks, ", mismatches, " mismatches so far.\n");

# (3) Real intermediate states from Syzygy(R, [a, b, c]) evaluation at m=2.
Print("\n--- (3) Real Syzygy intermediate states (E_+(2)) ---\n");

# Note: at this point the patched AddFreeWords has replaced HAP's. So
# direct calls to AddFreeWords go through the patched version. That's
# the actual production path; HAP's Syzygy uses it internally.

G := SmallGroup(32, 49);;
R := ResolutionFiniteGroup(G, 4);;

classes := ConjugacyClasses(G);;
non_trivial_idx := First([1..Length(classes)],
                         j -> Order(Representative(classes[j])) > 1);;
gRep := Representative(classes[non_trivial_idx]);;
C := Centralizer(G, gRep);;
elts := AsList(C);;
n := Length(elts);;
Print("Group: E_+(2); gRep order = ", Order(gRep), ", |C| = ", n, "\n");

syz_checks := 0;;
syz_mismatches := 0;;
for trial in [1..30] do
    a := Random([1..n]);
    b := Random([1..n]);
    a_elt := elts[a];
    b_elt := elts[b];
    ab_elt := a_elt * b_elt;
    gRep_a := gRep * a_elt;
    a_gRep := a_elt * gRep;

    S_a_b := Syzygy(R, [a_elt, b_elt]);
    S_gRep_ab := Syzygy(R, [gRep, ab_elt]);
    S_gRep_a_b := Syzygy(R, [gRep_a, b_elt]);
    S_gRep_a := Syzygy(R, [gRep, a_elt]);

    # Recreate the Mult step manually (matches HAP's Syzygy chain).
    Syz1 := List(S_a_b, y -> [y[1], Position(R!.elts,
                                              gRep * R!.elts[y[2]])]);
    # Stage 1.
    CheckPair(Syz1, S_gRep_ab,
              Concatenation("syz1+S_gRep_ab trial ", String(trial)));
    Syz1 := HAP_AFW5e_RefOriginal(Syz1, S_gRep_ab);
    # Stage 2.
    CheckPair(Syz1, NegateWord(S_gRep_a_b),
              Concatenation("syz1+neg trial ", String(trial)));
    Syz1 := HAP_AFW5e_RefOriginal(Syz1, NegateWord(S_gRep_a_b));
    # Stage 3.
    CheckPair(Syz1, NegateWord(S_gRep_a),
              Concatenation("syz1+neg2 trial ", String(trial)));
    Syz1 := HAP_AFW5e_RefOriginal(Syz1, NegateWord(S_gRep_a));
    # Stage 4: _Homotopy2's accumulator.
    ans := [];
    for x in Syz1 do
        h := R!.homotopy(2, x);
        CheckPair(ans, h,
                  Concatenation("homotopy2 accum trial ", String(trial)));
        ans := HAP_AFW5e_RefOriginal(ans, h);
    od;
od;

Print("\n=== TOTAL ", checks, " checks, ", mismatches, " mismatches. ===\n");
Assert(0, mismatches = 0,
       Concatenation(String(mismatches), " mismatches found in ",
                     String(checks), " checks"));

Print("\ntest_perf5e_hap_addfreewords: PASS\n");
QUIT;
