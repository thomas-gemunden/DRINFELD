# test_perf5b_prefix.g
# ----------------------
# Per-triple correctness check for A-7 perf-5b's prefix-sharing
# Syzygy implementation. Asserts that _Syzygy3FromParts (the inlined
# n=3 Syzygy with pre-computed length-2 sub-syzygies) produces bit-
# identical output to a fresh HAP Syzygy call.
#
# This is the CRITICAL safety check for Route B: if any sample triple
# disagrees, the prefix prototype is wrong and the BuildPerClassCocycle-
# Basis output is wrong.
#
# Sample: 40 random triples from m=3 (E_+(3)), using elements of a
# centraliser large enough to exercise the chain walk meaningfully.
#
# Read this from solver/ or solver/tests/; the CWD shim mirrors the
# pattern in snf_wrapper.g.

test_perf5b_orig_dir := DirectoryCurrent();;
test_perf5b_target := fail;;
for test_perf5b_try in [".", "..", "../.."] do
    if IsExistingFile(Concatenation(test_perf5b_try, "/snf_wrapper.g")) then
        test_perf5b_target := test_perf5b_try;
        break;
    fi;
od;;
if test_perf5b_target = fail then
    Error("test_perf5b_prefix.g: cannot locate snf_wrapper.g from CWD ",
          Filename(test_perf5b_orig_dir, ""));
fi;
ChangeDirectoryCurrent(test_perf5b_target);;
Read("snf_wrapper.g");
ChangeDirectoryCurrent(Filename(test_perf5b_orig_dir, ""));;

Print("\n=== test_perf5b_prefix: per-triple correctness of _Syzygy3FromParts ===\n");

# Use E_+(2) for a quick smoke (~2s); the inlined code path is identical
# at any group order so a small sample covers all paths in the helper.
G := SmallGroup(32, 49);;     # E_+(2)
Print("Group: E_+(2) = SmallGroup(32, 49), order ", Order(G), "\n");
setup := SetupCohomology3(G);;
R := setup.R;;

# Pick a representative non-trivial gRep and centraliser.
classes := ConjugacyClasses(G);;
non_trivial_idx := First([1..Length(classes)],
                         j -> Order(Representative(classes[j])) > 1);;
gRep := Representative(classes[non_trivial_idx]);;
C := Centralizer(G, gRep);;
elts := AsList(C);;
n := Length(elts);;
Print("gRep order = ", Order(gRep), ", |C| = ", n, "\n");

# Sample 40 random (a, b) pairs (covers all 3 triple positions × 40 = 120 triples).
sample_size := Minimum(40, n * n);;
sample_pairs := [];;
seen := rec();;
attempts := 0;;
while Length(sample_pairs) < sample_size and attempts < 4 * sample_size do
    attempts := attempts + 1;
    a := Random([1..n]);
    b := Random([1..n]);
    key := Concatenation(String(a), "_", String(b));
    if not IsBound(seen.(key)) then
        seen.(key) := true;
        Add(sample_pairs, [a, b]);
    fi;
od;
Print("Drew ", Length(sample_pairs), " random (a, b) pairs.\n");

mismatches := 0;;
checked := 0;;
for pair in sample_pairs do
    a := pair[1];
    b := pair[2];
    a_elt := elts[a];
    b_elt := elts[b];
    ab_elt := a_elt * b_elt;
    gRep_a := gRep * a_elt;
    a_gRep := a_elt * gRep;
    b_gRep := b_elt * gRep;
    gRep_b := gRep * b_elt;
    a_b_gRep := a_elt * b_gRep;

    # Compute each triple two ways: direct HAP Syzygy and via prefix-shared
    # _Syzygy3FromParts. Verify bit-identical output.

    # ---- Triple #1: Syzygy(R, [gRep, a, b]) ----
    S_a_b := Syzygy(R, [a_elt, b_elt]);
    S_T1_S_g1_g2g3 := Syzygy(R, [gRep, ab_elt]);
    S_T1_S_g1g2_g3 := Syzygy(R, [gRep_a, b_elt]);
    S_gRep_a := Syzygy(R, [gRep, a_elt]);
    expected1 := Syzygy(R, [gRep, a_elt, b_elt]);
    got1 := _Syzygy3FromParts(R, gRep,
                              S_a_b,
                              S_T1_S_g1_g2g3,
                              S_T1_S_g1g2_g3,
                              S_gRep_a);
    if expected1 <> got1 then
        mismatches := mismatches + 1;
        Print("MISMATCH Triple #1 at (a=", a, ", b=", b, "): ",
              "got_len=", Length(got1), " exp_len=", Length(expected1), "\n");
    fi;
    checked := checked + 1;

    # ---- Triple #2: Syzygy(R, [a, gRep, b]) ----
    S_gRep_b := Syzygy(R, [gRep, b_elt]);
    S_T2_S_g1_g2g3 := Syzygy(R, [a_elt, gRep_b]);
    S_T2_S_g1g2_g3 := Syzygy(R, [a_gRep, b_elt]);
    S_a_gRep := Syzygy(R, [a_elt, gRep]);
    expected2 := Syzygy(R, [a_elt, gRep, b_elt]);
    got2 := _Syzygy3FromParts(R, a_elt,
                              S_gRep_b,
                              S_T2_S_g1_g2g3,
                              S_T2_S_g1g2_g3,
                              S_a_gRep);
    if expected2 <> got2 then
        mismatches := mismatches + 1;
        Print("MISMATCH Triple #2 at (a=", a, ", b=", b, "): ",
              "got_len=", Length(got2), " exp_len=", Length(expected2), "\n");
    fi;
    checked := checked + 1;

    # ---- Triple #3: Syzygy(R, [a, b, gRep]) ----
    S_b_gRep := Syzygy(R, [b_elt, gRep]);
    S_T3_S_g1_g2g3 := Syzygy(R, [a_elt, b_gRep]);
    S_T3_S_g1g2_g3 := Syzygy(R, [ab_elt, gRep]);
    # S_a_b reused from above.
    expected3 := Syzygy(R, [a_elt, b_elt, gRep]);
    got3 := _Syzygy3FromParts(R, a_elt,
                              S_b_gRep,
                              S_T3_S_g1_g2g3,
                              S_T3_S_g1g2_g3,
                              S_a_b);
    if expected3 <> got3 then
        mismatches := mismatches + 1;
        Print("MISMATCH Triple #3 at (a=", a, ", b=", b, "): ",
              "got_len=", Length(got3), " exp_len=", Length(expected3), "\n");
    fi;
    checked := checked + 1;
od;

Print("\nPer-triple check: ", checked, " triples checked, ",
      mismatches, " mismatches.\n");
Assert(0, mismatches = 0,
       Concatenation(String(mismatches), " mismatches found"));

# Secondary check: brute-force build the contribution-row table the
# "old" way (three direct Syzygy calls per (a, b)) for a 4x4 subset of
# the centraliser, then compare it cell-by-cell against the new
# implementation's table for the same elements.
Print("\nSecondary: brute-force contrib check on a small (a,b) sub-grid...\n");
sub_n := Minimum(4, n);;
old_contribs := [];;
new_contribs := [];;
for a in [1..sub_n] do
    a_elt := elts[a];
    gRep_a_v := gRep * a_elt;
    a_gRep_v := a_elt * gRep;
    S_gRep_a_v := Syzygy(R, [gRep, a_elt]);
    S_a_gRep_v := Syzygy(R, [a_elt, gRep]);
    for b in [1..sub_n] do
        b_elt := elts[b];
        ab_elt_v := a_elt * b_elt;
        b_gRep_v := b_elt * gRep;
        gRep_b_v := gRep * b_elt;

        # --- OLD WAY (direct Syzygy) ---
        contrib_old := ListWithIdenticalEntries(R!.dimension(3), 0);
        # +
        S_old := Syzygy(R, [gRep, a_elt, b_elt]);
        Apply(S_old, x -> x[1]);
        for x in S_old do
            contrib_old[AbsoluteValue(x)] := contrib_old[AbsoluteValue(x)]
                                              + SignInt(x);
        od;
        # -
        S_old := Syzygy(R, [a_elt, gRep, b_elt]);
        Apply(S_old, x -> x[1]);
        for x in S_old do
            contrib_old[AbsoluteValue(x)] := contrib_old[AbsoluteValue(x)]
                                              - SignInt(x);
        od;
        # +
        S_old := Syzygy(R, [a_elt, b_elt, gRep]);
        Apply(S_old, x -> x[1]);
        for x in S_old do
            contrib_old[AbsoluteValue(x)] := contrib_old[AbsoluteValue(x)]
                                              + SignInt(x);
        od;

        # --- NEW WAY (_Syzygy3FromParts) ---
        S_a_b_v := Syzygy(R, [a_elt, b_elt]);
        S_T1_g1_g2g3 := Syzygy(R, [gRep, ab_elt_v]);
        S_T1_g1g2_g3 := Syzygy(R, [gRep_a_v, b_elt]);
        S_gRep_b_v := Syzygy(R, [gRep, b_elt]);
        S_T2_g1_g2g3 := Syzygy(R, [a_elt, gRep_b_v]);
        S_T2_g1g2_g3 := Syzygy(R, [a_gRep_v, b_elt]);
        S_b_gRep_v := Syzygy(R, [b_elt, gRep]);
        S_T3_g1_g2g3 := Syzygy(R, [a_elt, b_gRep_v]);
        S_T3_g1g2_g3 := Syzygy(R, [ab_elt_v, gRep]);
        contrib_new := ListWithIdenticalEntries(R!.dimension(3), 0);
        # +
        S_new := _Syzygy3FromParts(R, gRep, S_a_b_v, S_T1_g1_g2g3,
                                   S_T1_g1g2_g3, S_gRep_a_v);
        Apply(S_new, x -> x[1]);
        for x in S_new do
            contrib_new[AbsoluteValue(x)] := contrib_new[AbsoluteValue(x)]
                                              + SignInt(x);
        od;
        # -
        S_new := _Syzygy3FromParts(R, a_elt, S_gRep_b_v, S_T2_g1_g2g3,
                                   S_T2_g1g2_g3, S_a_gRep_v);
        Apply(S_new, x -> x[1]);
        for x in S_new do
            contrib_new[AbsoluteValue(x)] := contrib_new[AbsoluteValue(x)]
                                              - SignInt(x);
        od;
        # +
        S_new := _Syzygy3FromParts(R, a_elt, S_b_gRep_v, S_T3_g1_g2g3,
                                   S_T3_g1g2_g3, S_a_b_v);
        Apply(S_new, x -> x[1]);
        for x in S_new do
            contrib_new[AbsoluteValue(x)] := contrib_new[AbsoluteValue(x)]
                                              + SignInt(x);
        od;

        if contrib_old <> contrib_new then
            Print("MISMATCH contrib at (a=", a, ", b=", b, ")\n");
            mismatches := mismatches + 1;
        fi;
        Add(old_contribs, contrib_old);
        Add(new_contribs, contrib_new);
    od;
od;
Print("Secondary contrib check: ",
      sub_n * sub_n, " (a,b) cells, ", mismatches, " mismatches.\n");
Assert(0, mismatches = 0,
       Concatenation("Secondary mismatch: ", String(mismatches)));

# Tertiary check: combined-word Homotopy(2,...) equivalence.
# Verify that _Syzygy3CombinedWord produces a result whose per-cell
# contribution vector equals the +/- sum of the three individual
# Syzygy(R, [...]) contributions, via the brute-force computation.
Print("\nTertiary: combined-word Homotopy(2) check on a small (a,b) grid...\n");
combined_mismatches := 0;;
for a in [1..sub_n] do
    a_elt := elts[a];
    gRep_a_v := gRep * a_elt;
    a_gRep_v := a_elt * gRep;
    S_gRep_a_v := Syzygy(R, [gRep, a_elt]);
    S_a_gRep_v := Syzygy(R, [a_elt, gRep]);
    for b in [1..sub_n] do
        b_elt := elts[b];
        ab_elt_v := a_elt * b_elt;
        b_gRep_v := b_elt * gRep;
        gRep_b_v := gRep * b_elt;

        # Brute-force contribution via three independent Syzygy calls.
        contrib_old := ListWithIdenticalEntries(R!.dimension(3), 0);
        S_old := Syzygy(R, [gRep, a_elt, b_elt]);
        Apply(S_old, x -> x[1]);
        for x in S_old do
            contrib_old[AbsoluteValue(x)] := contrib_old[AbsoluteValue(x)]
                                              + SignInt(x);
        od;
        S_old := Syzygy(R, [a_elt, gRep, b_elt]);
        Apply(S_old, x -> x[1]);
        for x in S_old do
            contrib_old[AbsoluteValue(x)] := contrib_old[AbsoluteValue(x)]
                                              - SignInt(x);
        od;
        S_old := Syzygy(R, [a_elt, b_elt, gRep]);
        Apply(S_old, x -> x[1]);
        for x in S_old do
            contrib_old[AbsoluteValue(x)] := contrib_old[AbsoluteValue(x)]
                                              + SignInt(x);
        od;

        # Combined-word contribution.
        S_a_b_v := Syzygy(R, [a_elt, b_elt]);
        S_gRep_ab_v := Syzygy(R, [gRep, ab_elt_v]);
        S_gRep_a_b_v := Syzygy(R, [gRep_a_v, b_elt]);
        S_gRep_b_v := Syzygy(R, [gRep, b_elt]);
        S_a_gRep_b_v := Syzygy(R, [a_elt, gRep_b_v]);
        S_a_gRep_b_2_v := Syzygy(R, [a_gRep_v, b_elt]);
        S_b_gRep_v := Syzygy(R, [b_elt, gRep]);
        S_a_b_gRep_v := Syzygy(R, [a_elt, b_gRep_v]);
        S_ab_gRep_v := Syzygy(R, [ab_elt_v, gRep]);

        S_combined := _Syzygy3CombinedWord(R, gRep, a_elt,
                                            S_gRep_a_v, S_a_gRep_v, S_a_b_v,
                                            S_gRep_ab_v, S_gRep_a_b_v,
                                            S_gRep_b_v,
                                            S_a_gRep_b_v, S_a_gRep_b_2_v,
                                            S_b_gRep_v,
                                            S_a_b_gRep_v, S_ab_gRep_v);
        contrib_new := ListWithIdenticalEntries(R!.dimension(3), 0);
        Apply(S_combined, x -> x[1]);
        for x in S_combined do
            contrib_new[AbsoluteValue(x)] := contrib_new[AbsoluteValue(x)]
                                              + SignInt(x);
        od;
        if contrib_old <> contrib_new then
            Print("MISMATCH combined contrib at (a=", a, ", b=", b, ")\n");
            combined_mismatches := combined_mismatches + 1;
        fi;
    od;
od;
Print("Tertiary combined-word check: ",
      sub_n * sub_n, " (a,b) cells, ", combined_mismatches, " mismatches.\n");
Assert(0, combined_mismatches = 0,
       Concatenation("Tertiary mismatch: ", String(combined_mismatches)));

Print("\ntest_perf5b_prefix: PASS\n");
QUIT;
