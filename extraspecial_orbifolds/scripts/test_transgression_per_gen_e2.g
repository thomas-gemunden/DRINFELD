Read("transgression_per_generator.g");

# Use Print + a manual flush via PrintTo to a temporary file we tail.
# Simpler: just trust GAP's Print with `--output-buffer-size 0` is
# usually unbuffered to terminal; redirect via tee.

Print("\n##### D_8 #####\n");
TestAllGenerators(SmallGroup(8, 3));;

Print("\n##### E_+(2) #####\n");
TestAllGenerators(SmallGroup(32, 49));;

QUIT;
