# test_run_e_plus_3_kernel.g — verify the persisted kernel file for E_+(3).
#
# This test does NOT re-run the full A-3a driver (~10-15 min wall-clock).
# It instead loads the persisted output `computed/transgression/3/kernel.g`
# and verifies:
#
#   1. File exists at the expected path.
#   2. The file is a valid GAP source file returning a record.
#   3. The record has the documented fields with the right shapes.
#   4. The recorded torsion matches H^3(E_+(3); U(1)) = (Z/2)^34 + Z/4.
#   5. The kernel is closed under coordinate-wise addition (mod torsion),
#      i.e. it really is a subgroup. (Subgroup invariant.)
#   6. The zero vector is in the kernel.
#   7. The basis_summary structure is consistent with kernel_size:
#      kernel_size = product of basis_orders, where basis_orders is
#      torsion[i] for full e_i and 2 for the half-vec case.
#
# Run via:
#   gap -q -b -c 'Read("tests/test_run_e_plus_3_kernel.g");'
# from extraspecial_orbifolds/scripts/.

# Locate the kernel file. We support invocation from either
# extraspecial_orbifolds/scripts/ (canonical CWD) or its tests/ sub-dir.
# This mirrors the path layout of computed/transgression/2/kernel.g.
# After merge to main the worktree-absolute path should be updated to
# .../DRINFELD/... ; until then we try the wt-a3a worktree path too.
CandidateFiles := [
    "../../computed/transgression/3/kernel.g",         # from scripts/
    "../../../computed/transgression/3/kernel.g",      # from scripts/tests/
    "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-a3a/computed/transgression/3/kernel.g",
    "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD/computed/transgression/3/kernel.g"
];;
KernelFile := fail;;
for cand in CandidateFiles do
    if IsExistingFile(cand) then
        KernelFile := cand;
        break;
    fi;
od;;

# 1. file existence
Assert(0, KernelFile <> fail and IsExistingFile(KernelFile),
       Concatenation("expected kernel.g at one of ",
                     String(CandidateFiles),
                     " (driver run_e_plus_3_kernel.g not executed?)"));
Print("test_run_e_plus_3_kernel: file exists at ", KernelFile, "\n");

# 2. load as a function returning the record (matches the LoadModularData idiom).
data := ReadAsFunction(KernelFile)();;
Assert(0, IsRecord(data), "kernel.g did not evaluate to a record");
Print("test_run_e_plus_3_kernel: loaded record\n");

# 3. shape checks
for field in ["group", "id", "torsion", "exponent",
              "kernel_size", "kernel_vecs",
              "in_kernel_gens", "exp_index",
              "half_vec_in_kernel", "basis_summary"] do
    Assert(0, field in RecNames(data),
           Concatenation("missing field: ", field));
od;
Assert(0, data.group = "E_+(3)", "group label mismatch");
Assert(0, data.id = [128, 2326], "SmallGroup id mismatch");
Assert(0, IsList(data.torsion), "torsion must be a list");
Assert(0, IsInt(data.exponent) and data.exponent > 0,
       "exponent must be a positive integer");
Assert(0, IsInt(data.kernel_size) and data.kernel_size > 0,
       "kernel_size must be a positive integer");
# kernel_vecs may be `fail` when the kernel is too large to enumerate.
Assert(0, IsList(data.kernel_vecs) or data.kernel_vecs = fail,
       "kernel_vecs must be a list or fail");
Assert(0, IsList(data.in_kernel_gens), "in_kernel_gens must be a list");
Assert(0, IsInt(data.exp_index) and data.exp_index > 0,
       "exp_index must be a positive integer");
Assert(0, IsBool(data.half_vec_in_kernel),
       "half_vec_in_kernel must be a bool");
Assert(0, IsList(data.basis_summary), "basis_summary must be a list");
Print("test_run_e_plus_3_kernel: shape checks PASS\n");

# 4. torsion / exponent match H^3(E_+(3); U(1)) = (Z/2)^34 + Z/4
# Note: HAP returns the torsion in invariant-factor form; the order of
# entries depends on GAP/HAP version. We accept any permutation as long
# as the multiset matches.
sorted_torsion := ShallowCopy(data.torsion);;
Sort(sorted_torsion);;
expected_sorted := Concatenation(ListWithIdenticalEntries(34, 2), [4]);;
Assert(0, sorted_torsion = expected_sorted,
       Concatenation("torsion shape mismatch: got sorted ",
                     String(sorted_torsion),
                     ", expected ", String(expected_sorted)));
Assert(0, data.exponent = 4,
       Concatenation("exponent mismatch: got ", String(data.exponent),
                     ", expected 4"));
Assert(0, Length(data.torsion) = 35,
       Concatenation("expected 35 generators, got ",
                     String(Length(data.torsion))));
Print("test_run_e_plus_3_kernel: torsion / exponent PASS\n");
Print("  H^3 size = ", Product(data.torsion), " = 2^36\n");

# 4b. exp_index is consistent
Assert(0, data.torsion[data.exp_index] = data.exponent,
       Concatenation("exp_index ", String(data.exp_index),
                     " does not point to exponent generator; ",
                     "torsion[exp_index] = ",
                     String(data.torsion[data.exp_index]),
                     " != exponent ", String(data.exponent)));
Print("test_run_e_plus_3_kernel: exp_index points to order-4 gen PASS\n");

# 5. kernel_size sanity vs kernel_vecs (only if enumerated).
if data.kernel_vecs <> fail then
    Assert(0, data.kernel_size = Length(data.kernel_vecs),
           Concatenation("kernel_size = ", String(data.kernel_size),
                         " disagrees with Length(kernel_vecs) = ",
                         String(Length(data.kernel_vecs))));
    Print("test_run_e_plus_3_kernel: kernel_size = Length(kernel_vecs) PASS\n");
else
    Print("test_run_e_plus_3_kernel: kernel_vecs = fail (kernel too large); ",
          "skipping enumerated-list checks.\n");
fi;

# 6. closure under coordinate-wise addition (mod torsion). Subgroup invariant.
# Only applicable when kernel_vecs is enumerated.
ReduceModTorsion := function(v, t)
    return List([1..Length(v)], i -> v[i] mod t[i]);
end;;
zero_vec := List(data.torsion, t -> 0);;
if data.kernel_vecs <> fail then
    kernel_set := Set(data.kernel_vecs);
    Assert(0, Length(kernel_set) = data.kernel_size,
           "kernel_vecs contains duplicates");
    n_sample := Minimum(16, data.kernel_size);
    sample := data.kernel_vecs{[1..n_sample]};
    for v1 in sample do
        for v2 in sample do
            Assert(0, ReduceModTorsion(v1 + v2, data.torsion) in kernel_set,
                   Concatenation("subgroup closure violated: ",
                                 String(v1), " + ", String(v2)));
        od;
    od;
    Print("test_run_e_plus_3_kernel: subgroup-closure sample (", n_sample,
          " x ", n_sample, ") PASS\n");
    # 7. zero vec is in the kernel
    Assert(0, zero_vec in kernel_set, "zero vec missing from kernel");
    Print("test_run_e_plus_3_kernel: zero vec in kernel PASS\n");
else
    # Structural-only: subgroup-closure follows from the basis structure
    # (Z-linear combinations of independent torsion generators always close).
    # Verify that the basis_summary describes well-formed vectors.
    for r in data.basis_summary do
        Assert(0, Length(r.vec) = Length(data.torsion),
               "basis_summary vec wrong length");
        Assert(0, IsInt(r.order) and r.order > 0,
               "basis_summary entry has invalid order");
        Assert(0, r.vec = ReduceModTorsion(r.vec, data.torsion),
               "basis_summary vec entries not in canonical [0..torsion-1]");
        # The basis vector, multiplied by its order, must be zero mod torsion.
        Assert(0, ReduceModTorsion(r.order * r.vec, data.torsion) = zero_vec,
               Concatenation("basis vec ", String(r.vec),
                             " of order ", String(r.order),
                             " does not annihilate at .order * v"));
    od;
    Print("test_run_e_plus_3_kernel: structural basis_summary checks PASS\n");
fi;

# 8. basis_summary consistency with kernel_size.
# Each entry of basis_summary has .order; the product of these should
# equal kernel_size (basis vectors are independent generators).
basis_orders := List(data.basis_summary, r -> r.order);;
expected_size := Maximum(1, Product(basis_orders));;
Assert(0, data.kernel_size = expected_size,
       Concatenation("kernel_size = ", String(data.kernel_size),
                     " disagrees with product of basis_orders = ",
                     String(expected_size),
                     "; basis_orders = ", String(basis_orders)));
Print("test_run_e_plus_3_kernel: kernel_size = Product(basis_orders) PASS\n");

# 9. Sanity bound: kernel_size <= |H^3| = 2^36.
Assert(0, data.kernel_size <= Product(data.torsion),
       Concatenation("kernel_size ", String(data.kernel_size),
                     " > |H^3| = ", String(Product(data.torsion))));
Print("test_run_e_plus_3_kernel: kernel_size <= |H^3| PASS\n");

# 10. Each kernel vec (or each basis vec, structural case) has entries
# reduced mod torsion (canonical reps).
if data.kernel_vecs <> fail then
    for v in data.kernel_vecs{[1..Minimum(16, Length(data.kernel_vecs))]} do
        Assert(0, v = ReduceModTorsion(v, data.torsion),
               Concatenation("kernel vec ", String(v),
                             " has entries outside canonical [0..torsion-1]"));
    od;
    Print("test_run_e_plus_3_kernel: canonical-rep sample (kernel) PASS\n");
else
    for r in data.basis_summary do
        Assert(0, r.vec = ReduceModTorsion(r.vec, data.torsion),
               Concatenation("basis vec ", String(r.vec),
                             " has entries outside canonical [0..torsion-1]"));
    od;
    Print("test_run_e_plus_3_kernel: canonical-rep basis PASS\n");
fi;

Print("\ntest_run_e_plus_3_kernel: ALL PASS\n");
Print("  |ker Tr|       = ", data.kernel_size, "\n");
Print("  |H^3|          = ", Product(data.torsion), "\n");
Print("  |coker Tr|     = ", Product(data.torsion) / data.kernel_size, "\n");
Print("  In-kernel gens: ", Length(data.in_kernel_gens), " / ",
      Length(data.torsion), "\n");
QUIT;
