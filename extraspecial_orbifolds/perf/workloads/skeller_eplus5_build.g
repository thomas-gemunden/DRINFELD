# Workload: time BuildIntertwinerDataUntwisted on E_+(5).
# K-2a (#70) target: get m=7 query < 5 min; profile m=5 first to
# extrapolate. m=5: |G| = 2^11 = 2048.

ChangeDirectoryCurrent(
    "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-k2a/extraspecial_orbifolds/scripts");

Read("em_construction.g");
Read("untwisted_modular_data.g");
Read("krr_projector.g");
Read("skeller_adapter.g");

LoadPackage("hap");

Print("\n=== workload: BuildIntertwinerDataUntwisted on E_+(5) ===\n");
t0 := Runtime();;

# Build E_+(5) and the intertwiner data.
Gbuilt := SKellerBuildEmAsPcOrPerm(5);;
Print("E_+(5) built (|G| = ", Size(Gbuilt.group), ")\n");

t_idx := Runtime();;
idx := BuildSimpleIndex(Gbuilt.group);;
Print("BuildSimpleIndex wall: ", (Runtime() - t_idx) / 1000., " s\n");
Print("  num classes: ", Length(idx.classes), "\n");

t_tr := Runtime();;
transport := BuildTransports(idx);;
Print("BuildTransports wall: ", (Runtime() - t_tr) / 1000., " s\n");

Print("workload total wall: ", (Runtime() - t0) / 1000., " s\n");
Print("DONE\n");
QUIT;
