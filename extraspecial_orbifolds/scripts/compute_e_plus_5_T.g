# Phase C: T-vector of Mod(D^1(E_+(5))).
#
# E_+(5) = SmallGroup(2048, ?), |G| = 2^11 = 2048.
# Predicted rank: 527872. T-multiset {1^264464, -1^262416, i^496, -i^496}.
#
# T is much cheaper than S — per simple it is a single character-value
# lookup. We can do the whole rank-528K vector in a few minutes.

Read("untwisted_modular_data.g");
Read("predict_e_plus_m.g");

# GAP's SmallGroup library doesn't go up to 2048; we use the PC-group
# directly from ExtraspecialGroup.
G := ExtraspecialGroup(2048, "+");;
Print("|G| = ", Order(G), "  (SmallGroup library not available at order 2048)\n");
Print("Exponent: ", Exponent(G), "  Center order: ", Order(Center(G)), "\n");
# We won't compute StructureDescription either — it can be slow on PC groups
# of this size.  The presentation is sufficient.

# Build index — this is the bottleneck.
Print("\nBuilding simple-object index (|G| = 2048, 1025 classes)...\n");
tic := Runtime();;
idx := BuildSimpleIndex(G);;
toc := Runtime() - tic;;
Print("  done in ", toc / 1000., " s\n");
Print("  rank = ", idx.rank, "  (predicted 527872)\n");
Print("  num classes = ", Length(idx.classes), "  (predicted 1025)\n");

# Compute T.
Print("\nComputing T...\n");
tic := Runtime();;
T := ComputeUntwistedT(idx);;
toc := Runtime() - tic;;
Print("  done in ", toc / 1000., " s\n");

# Cross-check against analytical predictor.
Tcollect := Collected(T);;
Print("\nT-multiset:\n");
for pair in Tcollect do
    Print("  T = ", pair[1], "  multiplicity ", pair[2], "\n");
od;

pred := PredictE_plus_m(5);;
Print("\nAnalytical prediction:\n");
Print("  T = 1   : ", pred.TMultiset.one, "\n");
Print("  T = -1  : ", pred.TMultiset.minus_one, "\n");
Print("  T = i   : ", pred.TMultiset.i, "\n");
Print("  T = -i  : ", pred.TMultiset.minus_i, "\n");

tCount := function(val)
    local p; p := First(Tcollect, q -> q[1] = val);
    if p = fail then return 0; else return p[2]; fi;
end;;
Tmatch := tCount(1)     = pred.TMultiset.one
      and tCount(-1)    = pred.TMultiset.minus_one
      and tCount(E(4))  = pred.TMultiset.i
      and tCount(-E(4)) = pred.TMultiset.minus_i;;
Print("\nT-multiset matches analytical prediction: ", Tmatch, "\n");

# Save per-sector chunks under computed/E_plus_5/T/.
outdir := "../computed/E_plus_5/T";;
Exec(Concatenation("mkdir -p ", outdir));;
Print("\nWriting per-sector chunks to ", outdir, "/sector_<i>.g ...\n");

for i in [1..Length(idx.classes)] do
    local_T := List([1..idx.num_irreps[i]],
        k -> T[idx.global_offset[i] + k]);
    # Issue #449 A1': lazy centraliser materialisation (no-op for
    # eager idxs).
    if IsBoundGlobal("_EPlusCentraliserOf") then
        cen_i := _EPlusCentraliserOf(idx, i);
    else
        cen_i := idx.centralisers[i];
    fi;
    PrintTo(Concatenation(outdir, "/sector_", String(i), ".g"),
        "# Mod(D^1(E_+(5))) T, sector ", i, "\n",
        "# class size: ", idx.class_sizes[i], "\n",
        "# centraliser order: ", Order(cen_i), "\n",
        "# # irreps: ", idx.num_irreps[i], "\n",
        "# global index range: ", idx.global_offset[i] + 1, "..",
            idx.global_offset[i] + idx.num_irreps[i], "\n",
        "T_sector_", i, " := ", local_T, ";;\n",
        "irrep_dims_sector_", i, " := ", idx.irrep_dims[i], ";;\n");
od;
Print("  wrote ", Length(idx.classes), " sector chunks\n");

# Manifest
PrintTo(Concatenation(outdir, "/../manifest.g"),
    "# Mod(D^1(E_+(5))) untwisted, T-vector only\n",
    "# Group constructed via ExtraspecialGroup(2048, \"+\")\n",
    "manifest := rec(\n",
    "    group_construction := \"ExtraspecialGroup(2048, +)\",\n",
    "    group_order := ", Order(G), ",\n",
    "    rank := ", idx.rank, ",\n",
    "    cocycle := \"trivial\",\n",
    "    num_classes := ", Length(idx.classes), ",\n",
    "    class_sizes := ", idx.class_sizes, ",\n",
    "    num_irreps_per_class := ", idx.num_irreps, ",\n",
    "    T_match_predicted := ", Tmatch, "\n",
    ");;\n");
Print("Wrote ", outdir, "/../manifest.g\n");

QUIT;
