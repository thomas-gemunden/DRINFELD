# Workload: time FusionCoefficientsFromS on the E_+(2) rank-184 S matrix.
# Per V-5c history, this is where the agent stalled before completing.

ChangeDirectoryCurrent(
    "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-p4/extraspecial_orbifolds/scripts");

Read("aut_nt_refine.g");

LoadPackage("hap");

Print("\n=== workload: FusionCoefficientsFromS on D^0(E_+(2)) ===\n");

# Load the modular data for E_+(2) at the trivial cocycle.
md_path := "/Users/thomasgemunden/Projects/group_cohomology/modular_data/32/49/1.txt";;
data := ReadAsFunction(md_path)();;
S := data.S;;
r := Length(S);;
Print("rank r = ", r, "\n");

# Tally sparsity (count nonzero entries).
nz := 0;;
for i in [1..r] do
    for j in [1..r] do
        if S[i][j] <> 0 then
            nz := nz + 1;
        fi;
    od;
od;
Print("S matrix nonzero entries: ", nz, " / ", r*r,
      " (", Float(100. * nz / (r*r)), "%)\n");

# Time it.
Print("\nCalling FusionCoefficientsFromS ...\n");
t0 := Runtime();;
N := FusionCoefficientsFromS(S);;
wall := (Runtime() - t0) / 1000.;;
Print("wall: ", wall, " s\n");

# Sanity: count nonzero fusion coefficients.
total_nz := 0;;
total := 0;;
for i in [1..r] do for j in [1..r] do for k in [1..r] do
    total := total + 1;
    if N[i][j][k] <> 0 then total_nz := total_nz + 1; fi;
od; od; od;
Print("N tensor: ", total_nz, " / ", total,
      " nonzero (", Float(100. * total_nz / total), "%)\n");

Print("DONE\n");
QUIT;
