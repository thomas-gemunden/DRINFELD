Read("transgression_per_generator.g");

# E_+(1) = D_8 sanity (already know kernel = {0} from earlier)
Print("\n############### E_+(1) = D_8 ###############\n");
TestAllGenerators(SmallGroup(8, 3));;

# E_+(2)
Print("\n############### E_+(2) ###############\n");
TestAllGenerators(SmallGroup(32, 49));;

# E_+(3)
Print("\n############### E_+(3) ###############\n");
TestAllGenerators(SmallGroup(128, 2326));;

QUIT;
