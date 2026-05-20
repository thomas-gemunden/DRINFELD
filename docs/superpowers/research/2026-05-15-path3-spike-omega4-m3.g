# Path 3 spike (#137): empirical fingerprint of HAP's Z/4 bar 3-cocycle
# for the order-4 generator of H^3(E_+(3); U(1)) ≅ H^4(E_+(3); Z).
#
# Goal: get a tabulated function f: G^3 → Z/4 representing the Z/4
# generator, plus enough metadata to compare with candidate cochain-
# level formulas (IntegralBockstein, Pontryagin variants).
#
# Run from extraspecial_orbifolds/scripts/:
#   gap -q -b /tmp/path3_spike_m3.g

LoadPackage("hap");

Read("em_construction.g");
Read("transgression_kernel.g");   # SetupCohomology3, StandardCocycleOf
Read("bar_cocycle.g");
Read("integral_bockstein.g");

Print("\n=== Path 3 spike: HAP's Z/4 3-cocycle at m=3 ===\n");

G := EmGroup(3);;
Print("  |G| = ", Order(G), "\n");
t0 := Runtime();;
setup := SetupCohomology3(G);;
Print("  SetupCohomology3 wall: ", (Runtime() - t0) / 1000.0, " s\n");
Print("  setup.exponent = ", setup.exponent, "\n");
Print("  setup.torsion (sorted) = ", AsSortedList(setup.torsion), "\n");
Print("  num H^3 generators = ", setup.num_generators, "\n");

exp_idx := Position(setup.torsion, setup.exponent);;
Print("  exp_index = ", exp_idx, " (the Z/4 generator)\n");

# Build the Z/4 generator's bar 3-cocycle via HAP's StandardCocycleOf.
e_exp := List([1..setup.num_generators], i -> If_(i = exp_idx, 1, 0));;
omega4 := StandardCocycleOf(setup, e_exp);;
Print("  omega4 = StandardCocycleOf(setup, e_", exp_idx, ") -> Z/4 function\n");

# Tabulate distinct values over many triples.
elts := Elements(G);;
n := Length(elts);;
Print("  |G| = ", n, ", G^3 has ", n^3, " triples\n");

# Sample triples deterministically: first 100 (g, h, k) in Elements order.
sample := [];;
counter := 0;
for i in [1..Minimum(5, n)] do
    for j in [1..Minimum(5, n)] do
        for k in [1..Minimum(5, n)] do
            Add(sample, [elts[i], elts[j], elts[k]]);
            counter := counter + 1;
        od;
    od;
od;
Print("  sample size: ", Length(sample), "\n");

# Tabulate omega4 on the sample.
vals := [];;
distinct := [];;
for t in sample do
    v := omega4(t[1], t[2], t[3]) mod 4;
    Add(vals, v);
    if not v in distinct then Add(distinct, v); fi;
od;
Print("  values seen (sample): ", AsSortedList(distinct), "\n");
Print("  first 20 (g_i, g_j, g_k, omega4): \n");
for i in [1..Minimum(20, Length(sample))] do
    Print("    [", i, "] = ", vals[i], "\n");
od;

# Verify it satisfies the bar 3-cocycle equation mod 4 on a sample.
n_viol := 0;;
for i in [1..Length(elts)] do
    for j in [1..Length(elts)] do
        for k in [1..Length(elts)] do
            for l in [1..Length(elts)] do
                if i > 3 or j > 3 or k > 3 or l > 3 then continue; fi;
                val := (omega4(elts[j], elts[k], elts[l])
                        - omega4(elts[i] * elts[j], elts[k], elts[l])
                        + omega4(elts[i], elts[j] * elts[k], elts[l])
                        - omega4(elts[i], elts[j], elts[k] * elts[l])
                        + omega4(elts[i], elts[j], elts[k])) mod 4;
                if val <> 0 then n_viol := n_viol + 1; fi;
            od;
        od;
    od;
od;
Print("  bar 3-cocycle equation violations on 3^4 = 81 sample: ",
      n_viol, "\n");

# Check 2 * omega4 is a non-trivial Z/4 class. If 2 * omega4 is a
# Z/4 coboundary, then omega4 has order dividing 2 (contradiction
# since omega4 is the Z/4 generator). So 2 * omega4 should NOT be a
# Z/4 coboundary. We test in two ways:
# - 2 * omega4 evaluated on the sample is not identically zero
two_omega4_vals := List(vals, v -> (2 * v) mod 4);;
two_omega4_distinct := [];;
for v in two_omega4_vals do
    if not v in two_omega4_distinct then Add(two_omega4_distinct, v); fi;
od;
Print("  2 * omega4 distinct values on sample: ", AsSortedList(two_omega4_distinct), "\n");

# Check the F_2 reduction.
f2_vals := List(vals, v -> v mod 2);;
n_zero_f2 := Length(Filtered(f2_vals, v -> v = 0));;
n_one_f2 := Length(Filtered(f2_vals, v -> v = 1));;
Print("  F_2 reduction of omega4: ", n_zero_f2, " zeros, ", n_one_f2,
      " ones (out of ", Length(vals), ")\n");

QUIT;
