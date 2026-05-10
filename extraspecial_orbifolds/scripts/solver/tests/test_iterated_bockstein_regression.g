# test_iterated_bockstein_regression.g — 200/200 regression gate.
#
# Sweep 200 (vec, class) pairs on E_+(2). For each:
#   * compute c_g for the class
#   * baseline := IsCoboundary2(C, c_g, 8)            (slow Z/8 augmented-Z)
#   * iter     := IsCoboundary2Z2k(C, c_g, 3)         (iterated Bockstein)
# Both MUST agree on every pair. Even one disagreement is a math bug and
# we abort with the failing case printed.
#
# CWD shim: this test can be invoked from any CWD (e.g. running
#     gap -q -b /abs/path/to/test_iterated_bockstein_regression.g
# from a different worktree). Try a list of CWD candidates.
itbr_test_target := fail;;
for itbr_test_try in [
        ".", "tests", "extraspecial_orbifolds/scripts/solver/tests",
        "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-t1d/extraspecial_orbifolds/scripts/solver/tests",
        "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD/extraspecial_orbifolds/scripts/solver/tests"] do
    if IsExistingFile(Concatenation(itbr_test_try, "/test_iterated_bockstein_regression.g")) then
        itbr_test_target := itbr_test_try;
        break;
    fi;
od;;
if itbr_test_target = fail then
    Error("test_iterated_bockstein_regression.g: cannot locate self from CWD ",
          Filename(DirectoryCurrent(), ""));
fi;
ChangeDirectoryCurrent(itbr_test_target);;
Read("../iterated_bockstein.g");
Read("../iscoboundary2_split.g");

G := SmallGroup(32, 49);;          # E_+(2)
setup := SetupCohomology3(G);;
classes := ConjugacyClasses(G);;
n_classes := Length(classes);;

# Pre-compute centralisers; reused across vecs.
class_data := List([1..n_classes], j ->
    rec(gRep := Representative(classes[j]),
        C := Centralizer(G, Representative(classes[j]))));;

Print("E_+(2) torsion = ", setup.torsion, ", exp = ", setup.exponent, "\n");
Print("# classes = ", n_classes, "\n");
Print("Sweeping 200 (vec, class) pairs...\n\n");

# Deterministic seed for reproducibility.
seed := RandomSource(IsMersenneTwister, 12345);;

n_checks := 200;;
n_agree := 0;;
mismatches := [];;
n_torsion := Length(setup.torsion);;
exp_index := Position(setup.torsion, setup.exponent);;

for trial in [1..n_checks] do
    # Build a Path-Z-routable vec: vec[exp_index] in [1..7], other coords
    # random in [0..1]. (This is what the diagnostic agent's spike used —
    # so we exercise the full Z/8 path.)
    vec := List([1..n_torsion], i -> Random(seed, [0..1]));
    vec[exp_index] := Random(seed, [1..7]);
    omega := StandardCocycleOf(setup, vec);

    j := Random(seed, [1..n_classes]);
    cd := class_data[j];
    c_g := CGCocycleFunc(omega, cd.gRep);

    base := IsCoboundary2(cd.C, c_g, setup.exponent);
    iter := IsCoboundary2Z2k(cd.C, c_g, LogInt(setup.exponent, 2));

    if iter = base then
        n_agree := n_agree + 1;
    else
        # Snapshot a small portion of c_g for debugging.
        Add(mismatches, rec(trial := trial, vec := vec, class := j,
                            iter := iter, base := base));
        Print("  MISMATCH trial=", trial, " vec=", vec,
              " class=", j, " iter=", iter, " base=", base, "\n");
    fi;

    if (trial mod 50) = 0 then
        Print("  after ", trial, "/", n_checks, " trials: ", n_agree, " agree\n");
    fi;
od;

Print("\n=== Regression: ", n_agree, "/", n_checks, " agreements ===\n");
if Length(mismatches) > 0 then
    Print("MISMATCHES (", Length(mismatches), "):\n");
    for m in mismatches do
        Print("  trial=", m.trial, " vec=", m.vec, " class=", m.class,
              " iter=", m.iter, " base=", m.base, "\n");
    od;
fi;

Assert(0, n_agree = n_checks,
       Concatenation("Regression FAILED: ", String(n_agree), "/",
                     String(n_checks), " — ", String(Length(mismatches)),
                     " mismatches"));

Print("test_iterated_bockstein_regression: PASS (", n_agree, "/", n_checks, ")\n");
QUIT;
