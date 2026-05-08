# Run the transgression kernel test on E_+(2) and E_+(3).

Read("transgression_kernel.g");

# E_+(2)
Print("\n############### E_+(2) ###############\n");
G2 := SmallGroup(32, 49);;
r2 := TransgressionKernel(G2);;
if r2.kernel_vecs <> fail then
    Print("\nKernel of size ", r2.kernel_size, " out of ",
          r2.total_classes, " classes\n");
    if r2.kernel_size <= 32 then
        for vec in r2.kernel_vecs do Print("  ", vec, "\n"); od;
    fi;
fi;

# E_+(3)
Print("\n############### E_+(3) ###############\n");
G3 := SmallGroup(128, 2326);;
r3 := TransgressionKernel(G3);;
if r3.kernel_vecs <> fail then
    Print("\nKernel of size ", r3.kernel_size, " out of ",
          r3.total_classes, " classes\n");
    if r3.kernel_size <= 32 then
        for vec in r3.kernel_vecs do Print("  ", vec, "\n"); od;
    fi;
fi;

QUIT;
