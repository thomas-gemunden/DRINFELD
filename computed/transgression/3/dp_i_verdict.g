# DP-I verdict from scripts/dp_i_dispatch.g (issue #43 A-3b).
# Source kernel: ../../computed/transgression/3/kernel.g
# Verdict: DP-I: |ker Tr| = 68719476736. Next: candidate-elimination
return rec(
    kernel_size       := 68719476736,
    kernel_trivial    := false,
    branch_label      := "candidate-elimination",
    issues_to_unblock := [ "A-3c", "A-3d", "A-5a" ],
    verdict           := "DP-I: |ker Tr| = 68719476736. Next: candidate-elimination"
);;
