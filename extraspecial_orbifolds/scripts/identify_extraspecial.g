# Identify extraspecial 2-groups E_+(m) and E_-(m) in GAP's SmallGroup library.
#
# E_+(m) = (D_8)^{*m}                 (central product of m copies of D_8)
#        = "ExtraspecialGroup(2^{2m+1}, '+')"
# E_-(m) = Q_8 * (D_8)^{*(m-1)}       (one Q_8 and m-1 D_8's)
#        = "ExtraspecialGroup(2^{2m+1}, '-')"
#
# GAP's library function ExtraspecialGroup(p^{2m+1}, sign) constructs them
# as PC groups; we then translate to a SmallGroup ID via IdGroup.

for m in [1, 2, 3] do
    Print("\n=== m = ", m, ", |G| = 2^{", 2*m+1, "} = ", 2^(2*m+1), " ===\n");
    for sign in ["+", "-"] do
        G := ExtraspecialGroup(2^(2*m+1), sign);
        id := IdGroup(G);
        Print("  E_", sign, "(", m, ") = SmallGroup", id,
              "  StructureDescription = ", StructureDescription(G), "\n");
    od;
od;

# Also: compute the predicted rank of Z(Vec_{E_+(m)}) untwisted.
# Rank = 2*(4^m + 1) + (4^m - 1) * (2*4^{m-1} + 2)
Print("\n--- Predicted rank of Z(Vec_{E_+(m)}) untwisted ---\n");
for m in [1, 2, 3, 4, 5, 7] do
    rk := 2*(4^m + 1) + (4^m - 1) * (2*4^(m-1) + 2);
    Print("  m=", m, ", |G|=", 2^(2*m+1), ", rank=", rk, "\n");
od;

QUIT;
