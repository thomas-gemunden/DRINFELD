# Inspect the precomputed Z(Vec_{E_+(2)}) untwisted modular data
# (cocycle 1, trivial). E_+(2) = SmallGroup(32, 49), |G|=32, rank 184.
# Verify the T-eigenvalue multiset against our prediction from the
# extraspecial structure.

Read("../../src/modular_data.g");

data := LoadModularData(32, 49, 1);;
Tdiag := DiagonalOfMat(data.T);;
n := Length(Tdiag);;
Print("Rank: ", n, "  (predicted 184)\n");

# T-eigenvalue multiset
Print("\n--- T-eigenvalue multiset ---\n");
Tcollect := Collected(Tdiag);;
for pair in Tcollect do
    Print("  T = ", pair[1], "  multiplicity ", pair[2], "\n");
od;

# Predicted breakdown for E_+(2):
# - 17 simples in {1} sector, T = 1 for all      (17 × 1)
# - 17 simples in {-1} sector, T = ±1            (16 × 1, 1 × -1)
# - 9 order-2 non-central classes, each contributes 10 simples (90 simples).
# - 6 order-4 non-central classes, each contributes 10 simples (60 simples).
# Total 184.
#
# The order-2 sectors give T ∈ {±1} (centralizer order-2 element evaluations).
# The order-4 sectors give T ∈ {1, i, -1, -i} (centralizer order-4 evaluations).

# Quick sanity: total number of distinct T values
Print("\nDistinct T values: ", Length(Tcollect), "\n");

# Distribution by type
nReals := Sum(Tcollect, p -> p[2]) - Sum(Filtered(Tcollect, p -> not IsRat(p[1])), p -> p[2]);;
nReals := Sum(Filtered(Tcollect, p -> IsRat(p[1])), p -> p[2]);;
Print("Real T values count: ", nReals, "  (predicted 17 + 17 + 90 = 124)\n");
nNonReal := n - nReals;;
Print("Non-real T values count: ", nNonReal, "  (predicted 60 from order-4 sectors)\n");

QUIT;
