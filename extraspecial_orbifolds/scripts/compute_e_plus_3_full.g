# Phase B: full S, T for Mod(D^1(E_+(3))).  Uses the direct
# untwisted-D(G) library that bypasses Gruen.

Read("untwisted_modular_data.g");
Read("predict_e_plus_m.g");

G := SmallGroup(128, 2326);;     # E_+(3)
Print("|G| = ", Order(G), "  StructureDescription: ",
      StructureDescription(G), "\n");

# Build index
Print("\nBuilding simple-object index...");
tic := Runtime();;
idx := BuildSimpleIndex(G);;
toc := Runtime() - tic;;
Print("  done in ", toc / 1000., " s\n");
Print("  rank = ", idx.rank, "  (predicted 2272)\n");
Print("  number of conjugacy classes = ", Length(idx.classes), "  (predicted 65)\n");

# T
Print("\nComputing T...");
tic := Runtime();;
T := ComputeUntwistedT(idx);;
toc := Runtime() - tic;;
Print("  done in ", toc / 1000., " s\n");

Tcollect := Collected(T);;
Print("\nT-multiset (computed):\n");
for pair in Tcollect do
    Print("  T = ", pair[1], "  multiplicity ", pair[2], "\n");
od;

pred := PredictE_plus_m(3);;
Print("\nAnalytical prediction (m=3):\n");
Print("  T = 1     : ", pred.TMultiset.one, "\n");
Print("  T = -1    : ", pred.TMultiset.minus_one, "\n");
Print("  T = i     : ", pred.TMultiset.i, "\n");
Print("  T = -i    : ", pred.TMultiset.minus_i, "\n");

# T-prediction match check
tCount := function(val) local p; p := First(Tcollect, q -> q[1] = val);
    if p = fail then return 0; else return p[2]; fi; end;;
Tmatch := tCount(1)     = pred.TMultiset.one
      and tCount(-1)    = pred.TMultiset.minus_one
      and tCount(E(4))  = pred.TMultiset.i
      and tCount(-E(4)) = pred.TMultiset.minus_i;;
Print("\nT-multiset matches prediction: ", Tmatch, "\n");

# S
Print("\nComputing S (this is the substantive work)...");
tic := Runtime();;
S := ComputeUntwistedS(idx);;
toc := Runtime() - tic;;
Print("  done in ", toc / 1000., " s\n");

# Modularity
Print("\nModularity check S^2 = (ST)^3:\n");
tic := Runtime();;
LHS := S^2;;
RHS := (S * DiagonalMat(T))^3;;
toc := Runtime() - tic;;
modOK := LHS = RHS;;
Print("  S^2 = (ST)^3: ", modOK, "  (took ", toc / 1000., " s)\n");

# Unitarity sample
Print("\nUnitarity samples:\n");
for sampleRow in [1, 2, 100, 1000, 2272] do
    norm := Sum(S[sampleRow], x -> x * ComplexConjugate(x));
    Print("  Sum |S[", sampleRow, "][a]|^2 = ", norm, " (expect 1)\n");
od;

# Persist results
outdir := "../computed/E_plus_3";;
Exec(Concatenation("mkdir -p ", outdir));;

PrintTo(Concatenation(outdir, "/T.g"),
    "# Mod(D^1(E_+(3))) untwisted: T-vector\n",
    "# rank = ", idx.rank, "\n",
    "T := ", T, ";;\n");
Print("\nWrote ", outdir, "/T.g\n");

PrintTo(Concatenation(outdir, "/S.g"),
    "# Mod(D^1(E_+(3))) untwisted: S-matrix\n",
    "# rank = ", idx.rank, "\n",
    "S := ", S, ";;\n");
Print("Wrote ", outdir, "/S.g\n");

PrintTo(Concatenation(outdir, "/manifest.g"),
    "# Mod(D^1(E_+(3))) untwisted, computed with untwisted_modular_data.g\n",
    "manifest := rec(\n",
    "    smallgroup := [128, 2326],\n",
    "    structure_desc := \"", StructureDescription(G), "\",\n",
    "    rank := ", idx.rank, ",\n",
    "    cocycle := \"trivial\",\n",
    "    num_classes := ", Length(idx.classes), ",\n",
    "    class_sizes := ", idx.class_sizes, ",\n",
    "    num_irreps_per_class := ", idx.num_irreps, ",\n",
    "    irrep_dims := ", idx.irrep_dims, ",\n",
    "    modularity_passed := ", modOK, ",\n",
    "    T_match_predicted := ", Tmatch, "\n",
    ");;\n");
Print("Wrote ", outdir, "/manifest.g\n");

QUIT;
