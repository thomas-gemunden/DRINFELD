Read("transgression_per_generator.g");

# IO_stderr for unbuffered progress
LoadPackage("IO");
ProgressMsg := function(msg) IO_Write(IO_stderr, msg); IO_Flush(IO_stderr); end;;

ProgressMsg("Starting E_+(1) D_8 sanity...\n");
TestAllGenerators(SmallGroup(8, 3));;
ProgressMsg("D_8 done.\n");

ProgressMsg("Starting E_+(2)...\n");
TestAllGenerators(SmallGroup(32, 49));;
ProgressMsg("E_+(2) done.\n");

QUIT;
