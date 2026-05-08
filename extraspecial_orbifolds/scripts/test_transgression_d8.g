# Sanity-check the transgression kernel computation on D_8 = E_+(1).

Read("transgression_kernel.g");

G := SmallGroup(8, 3);;       # D_8
result := TransgressionKernel(G);;

if result.kernel_vecs <> fail then
    Print("\n--- Kernel vectors ---\n");
    for vec in result.kernel_vecs do
        Print("  ", vec, "\n");
    od;
fi;

QUIT;
