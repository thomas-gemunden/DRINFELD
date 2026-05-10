# test_rung3_e_plus_2_kernel.g — full ker Tr(E_+(2)) must equal 2048.
# Ground truth: commit 9bffebb.

Read("../snf_wrapper.g");

G := SmallGroup(32, 49);;     # E_+(2)
result := TransgressionKernelExact(G);;

# Source group H^3(E_+(2); U(1)) = (Z/2)^9 + Z/8, total |H^3| = 2^9 * 8 = 4096.
# Verified ker Tr = 2048 (commit 9bffebb).
Print("E_+(2) computed |ker Tr| = ", result.kernel_size, "\n");
Print("Expected |ker Tr| = 2048 (commit 9bffebb)\n");
Assert(0, result.kernel_size = 2048,
       Concatenation("ker Tr size mismatch: got ", String(result.kernel_size),
                     ", expected 2048"));
Print("\ntest_rung3_e_plus_2_kernel: PASS — math anchor confirmed\n");
QUIT;
