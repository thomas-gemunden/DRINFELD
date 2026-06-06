# Phase F: T-vector of Mod(D^1(E_+(7))).
#
# E_+(7) constructed via ExtraspecialGroup(32768, "+").  |G| = 2^15.
# Predicted rank: 134,275,072 ≈ 1.34 × 10^8.
# T-multiset: {1^67145792, -1^67113024, i^8128, -i^8128}.
#
# Bottleneck is the index build: 16384 + 1 = 16385 conjugacy classes,
# each requiring a Centralizer() and a CharacterTable() call.  At ~200 ms
# per centraliser (extrapolating from E_+(5) which took ~95 ms over
# 1024 centralisers), we expect ~55 minutes wall time for the index.
# The T extraction itself is negligible (~tens of seconds).

Read("untwisted_modular_data.g");
Read("predict_e_plus_m.g");

G := ExtraspecialGroup(32768, "+");;
Print("|G| = ", Order(G), "\n");
Print("Exponent: ", Exponent(G), "  Center order: ", Order(Center(G)), "\n");

Print("\nBuilding simple-object index (this is the bottleneck — many minutes)...\n");
tic := Runtime();;
idx := BuildSimpleIndex(G);;
toc := Runtime() - tic;;
Print("  done in ", toc / 1000., " s\n");
Print("  rank = ", idx.rank, "  (predicted 134275072)\n");
Print("  num classes = ", Length(idx.classes), "  (predicted 16385)\n");

Print("\nComputing T...\n");
tic := Runtime();;
T := ComputeUntwistedT(idx);;
toc := Runtime() - tic;;
Print("  done in ", toc / 1000., " s\n");

Tcollect := Collected(T);;
Print("\nT-multiset:\n");
for pair in Tcollect do
    Print("  T = ", pair[1], "  multiplicity ", pair[2], "\n");
od;

pred := PredictE_plus_m(7);;
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

# Save per-sector chunks.
outdir := "../computed/E_plus_7/T";;
Exec(Concatenation("mkdir -p ", outdir));;
Print("\nWriting per-sector chunks to ", outdir, "/sector_<i>.g ...\n");

tic := Runtime();;
for i in [1..Length(idx.classes)] do
    local_T := List([1..idx.num_irreps[i]],
        k -> T[idx.global_offset[i] + k]);
    # Issue #449 A1': lazy centraliser materialisation. For closed-form
    # E_+(m) idxs this materialises non-central centralisers on demand
    # (acceptable here — this driver writes the full T vector). No-op
    # for eager idxs.
    if IsBoundGlobal("_EPlusCentraliserOf") then
        cen_i := _EPlusCentraliserOf(idx, i);
    else
        cen_i := idx.centralisers[i];
    fi;
    PrintTo(Concatenation(outdir, "/sector_", String(i), ".g"),
        "# Mod(D^1(E_+(7))) T, sector ", i, "\n",
        "# class size: ", idx.class_sizes[i], "\n",
        "# centraliser order: ", Order(cen_i), "\n",
        "# # irreps: ", idx.num_irreps[i], "\n",
        "# global index range: ", idx.global_offset[i] + 1, "..",
            idx.global_offset[i] + idx.num_irreps[i], "\n",
        "T_sector_", i, " := ", local_T, ";;\n",
        "irrep_dims_sector_", i, " := ", idx.irrep_dims[i], ";;\n");
od;
toc := Runtime() - tic;;
Print("  wrote ", Length(idx.classes), " sector chunks in ", toc / 1000., " s\n");

PrintTo(Concatenation(outdir, "/../manifest.g"),
    "# Mod(D^1(E_+(7))) untwisted, T-vector only\n",
    "# Group constructed via ExtraspecialGroup(32768, \"+\")\n",
    "manifest := rec(\n",
    "    group_construction := \"ExtraspecialGroup(32768, +)\",\n",
    "    group_order := ", Order(G), ",\n",
    "    rank := ", idx.rank, ",\n",
    "    cocycle := \"trivial\",\n",
    "    num_classes := ", Length(idx.classes), ",\n",
    "    T_match_predicted := ", Tmatch, "\n",
    ");;\n");
Print("Wrote ", outdir, "/../manifest.g\n");

QUIT;
