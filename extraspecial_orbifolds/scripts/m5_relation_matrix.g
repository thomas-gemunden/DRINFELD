# Verify the m=5 relation matrix from equation (4.4.9) of Keller-Roberts-Roberts
# (arXiv:2411.13646).
#
# The matrix records, for each pair (T_ar, T_bs) of generator products, the
# value of one specific entry. Equation (4.4.1) is established by the
# diagonal being 1; equation (4.4.2) by the matrix being symmetric.
#
# We just transcribe the matrix (as printed in the paper), check symmetry
# and diagonal, and report.

# Read off from (4.4.9) of the paper.
# The matrix is 10x10 because there are 10 generators T_ar with a in 1..5, r in 1..2.
# Order: (a=1,r=1), (1,2), (2,1), (2,2), (3,1), (3,2), (4,1), (4,2), (5,1), (5,2).

M := [
    [1, 1/4, 1, 1/8, 1/4, 1/2, 1/2, 1/2, 1/2, 1/2],
    [1/4, 1, 1/4, 1/4, 1/8, 1/4, 1/8, 1/4, 1/4, 1/4],
    [1, 1/4, 1, 1/8, 1/4, 1/2, 1/2, 1/2, 1/2, 1/2],
    [1/8, 1/4, 1/8, 1, 1/16, 1/8, 1/8, 1/8, 1/8, 1/8],
    [1/4, 1/8, 1/4, 1/16, 1, 1/8, 1/4, 1/4, 1/4, 1/4],
    [1/2, 1/4, 1/2, 1/8, 1/8, 1, 1/2, 1/2, 1/2, 1/2],
    [1/2, 1/8, 1/2, 1/8, 1/4, 1/2, 1, 1/4, 1/4, 1/2],
    [1/2, 1/4, 1/2, 1/8, 1/4, 1/2, 1/4, 1, 1/2, 1/4],
    [1/2, 1/4, 1/2, 1/8, 1/4, 1/2, 1/4, 1/2, 1, 1/4],
    [1/2, 1/4, 1/2, 1/8, 1/4, 1/2, 1/2, 1/4, 1/4, 1]
];;

Print("=== m=5 relation matrix (eq 4.4.9 of Keller-Roberts-Roberts) ===\n");
Print("Size: ", Length(M), " x ", Length(M[1]), "\n");

# Check diagonal entries are 1 (so T_ar^2 = identity)
diag := List([1..Length(M)], i -> M[i][i]);;
Print("Diagonal: ", diag, "\n");
Print("Diagonal all 1 (so T_ar^2 = 1): ", ForAll(diag, x -> x = 1), "\n");

# Check the matrix is symmetric (so T_ar T_bs = T_bs T_ar)
Print("Symmetric (so [T_ar, T_bs] = 0): ", M = TransposedMat(M), "\n");

# If both true, then c_g = 1 (the 2-cocycle of the projective rep is trivial).

QUIT;
