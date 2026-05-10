# test_snf_wrapper.g — sanity-check the SNF wrapper on D_8.
#
# The plan's draft asserted "D_8 trivial transgression kernel"
# (Length(result.kernel) = 0). That was incorrect. Verified empirically
# against the existing baseline TransgressionKernel in
# extraspecial_orbifolds/scripts/transgression_kernel.g: D_8 has a
# 4-element kernel containing
#   [0,0,0], [0,1,2], [1,0,0], [1,1,2]
# (a Z/2 x Z/2 subgroup of H^3(D_8; U(1)) = Z/2 x Z/2 x Z/4). This test
# pins the brute-force wrapper to that empirical anchor.
Read("../snf_wrapper.g");

G := SmallGroup(8, 3);;
result := TransgressionKernelExact(G);;

Assert(0, result.kernel_size = 4,
       Concatenation("D_8 transgression kernel size must be 4; got ",
                     String(result.kernel_size)));

# The non-zero kernel elements should be a 3-element list (excluding zero vec).
Assert(0, IsList(result.kernel) and Length(result.kernel) = 3,
       "D_8 non-zero kernel must have exactly 3 elements");

# Pin the actual non-zero kernel content (matches baseline).
expected := [[0, 1, 2], [1, 0, 0], [1, 1, 2]];;
Assert(0, Set(result.kernel) = Set(expected),
       Concatenation("D_8 kernel content mismatch; got ",
                     String(result.kernel)));

Print("test_snf_wrapper: PASS (D_8 kernel = ", result.kernel_size,
      " elements, matches baseline)\n");
QUIT;
