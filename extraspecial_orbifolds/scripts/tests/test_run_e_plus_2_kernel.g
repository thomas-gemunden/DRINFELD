# test_run_e_plus_2_kernel.g — verify the persisted kernel file for E_+(2).
#
# This test does NOT re-run the full A-2 driver (~minutes wall-clock).
# It instead loads the persisted output `computed/transgression/2/kernel.g`
# and verifies:
#
#   1. File exists at the expected path.
#   2. The file is a valid GAP source file returning a record.
#   3. The record has the documented fields with the right shapes.
#   4. The recorded |ker Tr| matches the anchor 2048.
#   5. The recorded torsion / exponent matches H^3(E_+(2); U(1)).
#   6. The kernel is closed under coordinate-wise addition (mod torsion),
#      i.e. it really is a subgroup. (This is a structural invariant that
#      catches accidental persistence corruption.)
#   7. The zero vector is in the kernel.
#
# These tests run in well under a second once the file exists.
# The math anchor (kernel_size = 2048) is verified independently by
# solver/tests/test_rung3_e_plus_2_kernel.g, which actually invokes
# TransgressionKernelExact.
#
# Run via:
#   gap -q -b -c 'Read("tests/test_run_e_plus_2_kernel.g");'
# from extraspecial_orbifolds/scripts/.

ChangeDirectoryCurrent(
    "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-a2/extraspecial_orbifolds/scripts");

KernelFile := "../../computed/transgression/2/kernel.g";;

# 1. file existence
Assert(0, IsExistingFile(KernelFile),
       Concatenation("expected file at ", KernelFile,
                     " (driver run_e_plus_2_kernel.g not executed?)"));
Print("test_run_e_plus_2_kernel: file exists at ", KernelFile, "\n");

# 2. load as a function returning the record (matches the LoadModularData idiom).
data := ReadAsFunction(KernelFile)();;
Assert(0, IsRecord(data), "kernel.g did not evaluate to a record");
Print("test_run_e_plus_2_kernel: loaded record\n");

# 3. shape checks
for field in ["group", "id", "torsion", "exponent",
              "kernel_size", "kernel_vecs"] do
    Assert(0, field in RecNames(data),
           Concatenation("missing field: ", field));
od;
Assert(0, data.group = "E_+(2)", "group label mismatch");
Assert(0, data.id = [32, 49], "SmallGroup id mismatch");
Assert(0, IsList(data.torsion), "torsion must be a list");
Assert(0, IsInt(data.exponent) and data.exponent > 0,
       "exponent must be a positive integer");
Assert(0, IsInt(data.kernel_size) and data.kernel_size > 0,
       "kernel_size must be a positive integer");
Assert(0, IsList(data.kernel_vecs), "kernel_vecs must be a list");
Print("test_run_e_plus_2_kernel: shape checks PASS\n");

# 4. math anchor: |ker Tr| = 2048
Assert(0, data.kernel_size = 2048,
       Concatenation("kernel_size anchor mismatch: got ",
                     String(data.kernel_size), ", expected 2048"));
Assert(0, Length(data.kernel_vecs) = 2048,
       Concatenation("Length(kernel_vecs) anchor mismatch: got ",
                     String(Length(data.kernel_vecs)), ", expected 2048"));
Print("test_run_e_plus_2_kernel: kernel_size = 2048 PASS\n");

# 5. torsion / exponent match H^3(E_+(2); U(1)) = (Z/2)^9 (+) Z/8
expected_torsion := [2,2,2,2,2,2,2,2,2,8];;
Assert(0, data.torsion = expected_torsion,
       Concatenation("torsion mismatch: got ", String(data.torsion),
                     ", expected ", String(expected_torsion)));
Assert(0, data.exponent = 8,
       Concatenation("exponent mismatch: got ", String(data.exponent),
                     ", expected 8"));
Print("test_run_e_plus_2_kernel: torsion / exponent PASS\n");

# 6. closure under coordinate-wise addition (mod torsion). Subgroup invariant.
ReduceModTorsion := function(v, t)
    return List([1..Length(v)], i -> v[i] mod t[i]);
end;;
kernel_set := Set(data.kernel_vecs);;
Assert(0, Length(kernel_set) = data.kernel_size,
       "kernel_vecs contains duplicates");
# Sample-check closure: take the first 16 vecs and verify all 16*16 sums
# remain in the set. Full closure check is O(N^2) ≈ 4M ops; the sample
# is enough to catch any wholesale corruption.
sample := data.kernel_vecs{[1..16]};;
for v1 in sample do
    for v2 in sample do
        Assert(0, ReduceModTorsion(v1 + v2, data.torsion) in kernel_set,
               Concatenation("subgroup closure violated: ",
                             String(v1), " + ", String(v2)));
    od;
od;
Print("test_run_e_plus_2_kernel: subgroup-closure sample PASS\n");

# 7. zero vec is in the kernel
zero_vec := List(data.torsion, t -> 0);;
Assert(0, zero_vec in kernel_set, "zero vec missing from kernel");
Print("test_run_e_plus_2_kernel: zero vec in kernel PASS\n");

Print("\ntest_run_e_plus_2_kernel: ALL PASS\n");
QUIT;
