# Test the BRW-amortised per-generator transgression on E_+(2).
#
# Parity check: pick one (or a small set of) H^3 generators i for m=2 and
# compare PerGeneratorTransgressionBRW(G, i).per_class against the baseline
# TestGenerator(setup, i, classes).per_class from
# transgression_per_generator.g.
#
# Tier-1 acceptance (Stage 1, single-generator check):
#   - per_class lists agree, entry-by-entry, for at least one generator
#     at m=2. (Either both lists are all true, or both flag the same
#     witness classes.)
#
# Tier-2 (Stage 2, all generators): same parity over all k generators of
# H^3(E_+(2); U(1)).
#
# Logged output: /tmp/test_transgression_per_generator_brw.log.

ChangeDirectoryCurrent(
    "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-t3d/extraspecial_orbifolds/scripts");

# Pull in both implementations.
Read("transgression_per_generator.g");
Read("transgression_per_generator_brw.g");

LogPath := "/tmp/test_transgression_per_generator_brw.log";;
PrintTo(LogPath, "=== test_transgression_per_generator_brw.g ===\n");

# Use EmGroup(m) directly (the BRW-amortised path requires it).
m := 2;;
G := EmGroup(m);;
AppendTo(LogPath, "G = EmGroup(", m, "), |G| = ", Order(G), "\n");

setup := SetupCohomology3(G);;
classes := ConjugacyClasses(G);;
n_classes := Length(classes);;
k := setup.num_generators;;

AppendTo(LogPath, "n_classes = ", n_classes, ", k = ", k, "\n");
AppendTo(LogPath, "torsion = ", setup.torsion, "\n");

# Stage-1 parity check: pick i = 1, run both paths, compare per_class.
ParityCheckOneGenerator := function(i)
    local t_b, r_baseline, t_o, r_orbit, baseline_class, agree, mismatches, j;
    AppendTo(LogPath, "\n--- Generator i = ", i, " ---\n");

    t_b := Runtime();
    r_baseline := TestGenerator(setup, i, classes);
    t_b := (Runtime() - t_b) / 1000.;
    AppendTo(LogPath, "Baseline (transgression_per_generator.g): ", t_b,
             " s; all_in_kernel = ", r_baseline.all_in_kernel, "\n");

    t_o := Runtime();
    r_orbit := PerGeneratorTransgressionBRW(G, i);
    t_o := (Runtime() - t_o) / 1000.;
    AppendTo(LogPath, "Orbit-aware (BRW):                          ", t_o,
             " s; all_in_kernel = ", r_orbit.all_in_kernel, "\n");

    # Compare per-class: baseline stores [j, |C_g|, isCob] tuples,
    # orbit-aware stores just true/false per class index.
    mismatches := [];
    for j in [1..n_classes] do
        baseline_class := r_baseline.per_class[j];
        # baseline_class[3] is the boolean isCob.
        if baseline_class[3] <> r_orbit.per_class[j] then
            Add(mismatches, rec(j := j,
                                baseline := baseline_class[3],
                                orbit := r_orbit.per_class[j]));
        fi;
    od;
    agree := IsEmpty(mismatches);
    AppendTo(LogPath, "Per-class parity: ", agree, " (",
             Length(mismatches), " mismatches)\n");
    if not agree then
        AppendTo(LogPath, "Mismatches: ", mismatches, "\n");
    fi;
    return rec(i := i, agree := agree, mismatches := mismatches,
               t_baseline := t_b, t_orbit := t_o,
               r_baseline := r_baseline, r_orbit := r_orbit);
end;;

# Stage-1: run on i = 1, log result.
r1 := ParityCheckOneGenerator(1);;
Print("\nGenerator 1: agree = ", r1.agree, "\n");

# Stage-2 (if no failures so far): run on all k generators.
all_results := [];;
Add(all_results, r1);
if r1.agree then
    AppendTo(LogPath, "\n=== Stage-2: all generators ===\n");
    for i in [2..k] do
        ri := ParityCheckOneGenerator(i);
        Add(all_results, ri);
        Print("  gen ", i, ": agree = ", ri.agree, "\n");
        if not ri.agree then
            Print("  MISMATCH at gen ", i, "; halting Stage-2.\n");
            break;
        fi;
    od;
fi;

# Final summary.
agreed := Length(Filtered(all_results, r -> r.agree));;
total := Length(all_results);;
AppendTo(LogPath, "\n=== Summary ===\n");
AppendTo(LogPath, "Tested ", total, " of ", k, " generators; ", agreed,
         " in parity with baseline.\n");
Print("\n=== Test summary ===\n");
Print("Tested ", total, " generators; ", agreed, " match baseline.\n");
Print("Log: ", LogPath, "\n");
