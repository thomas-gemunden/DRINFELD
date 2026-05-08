# Phase F' — Structural T-vector for Mod(D^1(E_+(m))).
#
# Insight (Keller-Roberts-Roberts Prop 3.1):  the conjugacy classes of
# E_+(m) under E_+(m)-conjugation come in just FOUR centraliser types
# (under the larger BRW(m)-conjugation, only 4 BRW-classes; each
# splits into BRW-class-size / 2 many E_+(m)-classes).  Two simples
# (g, ρ) and (g', ρ) with g, g' in the same BRW-orbit have the same
# centraliser structure and the same character ρ (up to BRW-conjugation),
# so T_{(g, ρ)} = T_{(g', ρ)} up to relabelling.
#
# Concretely, the four types and per-type T-values:
#
#   1. {1}:          C = E_+(m).  Irreps:  4^m of dim 1 + 1 of dim 2^m.
#                     T-values:  ALL equal to 1.  Total simples: 4^m + 1.
#
#   2. {-1}:         C = E_+(m).  Irreps as above.
#                     T-values:  4^m × 1   (the 1-dim irreps factor through
#                                            E/Z and send -1 → 1)
#                                1 × -1     (the faithful 2^m-dim irrep
#                                            sends -1 → -2^m, so T = -1)
#                     Total simples: 4^m + 1.
#
#   3. σ_2-type non-central g (order 2):
#                     C = Z_2 × E_+(m-1).
#                     Irreps:  pairs (χ_a, ρ_b) with χ_a ∈ Irr(Z_2),
#                              ρ_b ∈ Irr(E_+(m-1)).
#                     dim((χ_a, ρ_b)) = dim(ρ_b).
#                     T_{((g, ρ_b)} = χ_a(g) · ρ_b(e) / dim(ρ_b)
#                                  = χ_a(g) ∈ {1, -1}.
#                     Per sector: (4^{m-1} + 1) × T=1   (χ trivial)
#                                 (4^{m-1} + 1) × T=-1  (χ sign)
#                     Total simples per sector: 2 · (4^{m-1} + 1).
#                     Number of sectors: 2^{2m-1} + 2^{m-1} - 1.
#
#   4. σ_1 σ_2-type non-central g (order 4):
#                     C = Z_4 ∘ E_+(m-1)  (central product over <z>).
#                     Irreps from compatible pairs (χ_a of Z_4, ρ_b of
#                     E_+(m-1)) with χ_a(g²) = ρ_b(z):
#                       (χ_0, 1-dim ρ_b) → 4^{m-1} pairs, T = 1
#                       (χ_2, 1-dim ρ_b) → 4^{m-1} pairs, T = -1
#                       (χ_1, faithful ρ_b) → 1 pair, T = i
#                       (χ_3, faithful ρ_b) → 1 pair, T = -i
#                     Per-sector total: 2 · 4^{m-1} + 2.
#                     Number of sectors: 2^{2m-1} - 2^{m-1}.
#
# This gives the entire T-multiset analytically.  No call to
# ConjugacyClasses(E_+(m)) needed; no character-table computation
# on E_+(m) needed.

# ---------------------------------------------------------------
# Per-sector T-data, keyed by sector type
# ---------------------------------------------------------------

EplusType_TPerSector := function(m)
    return rec(
        # Per sector of each type, list of [count, T-value]:
        identity_sector := [
            [4^m + 1, 1]
        ],
        minus_one_sector := [
            [4^m, 1],
            [1, -1]
        ],
        order2_sector := [
            [4^(m-1) + 1, 1],
            [4^(m-1) + 1, -1]
        ],
        order4_sector := [
            [4^(m-1), 1],
            [4^(m-1), -1],
            [1, E(4)],
            [1, -E(4)]
        ]
    );
end;;

# Number of sectors of each type for E_+(m)
SectorCounts := function(m)
    return rec(
        identity := 1,
        minus_one := 1,
        order2 := 2^(2*m - 1) + 2^(m - 1) - 1,
        order4 := 2^(2*m - 1) - 2^(m - 1)
    );
end;;

# Aggregate T-multiset
AggregateTMultiset := function(m)
    local T_per, counts, mult, t, count_secs, key;
    T_per := EplusType_TPerSector(m);
    counts := SectorCounts(m);
    mult := rec(one := 0, minus_one := 0, i_val := 0, minus_i := 0);

    AddTo := function(per_sector_data, num_sectors)
        local entry;
        for entry in per_sector_data do
            if entry[2] = 1 then mult.one := mult.one + entry[1] * num_sectors;
            elif entry[2] = -1 then mult.minus_one := mult.minus_one + entry[1] * num_sectors;
            elif entry[2] = E(4) then mult.i_val := mult.i_val + entry[1] * num_sectors;
            elif entry[2] = -E(4) then mult.minus_i := mult.minus_i + entry[1] * num_sectors;
            fi;
        od;
    end;

    AddTo(T_per.identity_sector, counts.identity);
    AddTo(T_per.minus_one_sector, counts.minus_one);
    AddTo(T_per.order2_sector, counts.order2);
    AddTo(T_per.order4_sector, counts.order4);

    return rec(m := m,
               group_order := 2^(2*m + 1),
               sector_counts := counts,
               T_per_sector := T_per,
               TMultiset := mult,
               total_rank := mult.one + mult.minus_one + mult.i_val + mult.minus_i);
end;;

# Sanity: cross-check against predict_e_plus_m.g

Read("predict_e_plus_m.g");

CheckAgainstPredictor := function(m)
    local agg, pred, ok;
    agg := AggregateTMultiset(m);
    pred := PredictE_plus_m(m);
    Print("\n=== m = ", m, ":  Phase F' analytical T vs predictor ===\n");
    Print("  rank: analytical=", agg.total_rank, "  predictor=", pred.rank,
          "  match=", agg.total_rank = pred.rank, "\n");
    Print("  T=1:  analytical=", agg.TMultiset.one,
          "  predictor=", pred.TMultiset.one,
          "  match=", agg.TMultiset.one = pred.TMultiset.one, "\n");
    Print("  T=-1: analytical=", agg.TMultiset.minus_one,
          "  predictor=", pred.TMultiset.minus_one,
          "  match=", agg.TMultiset.minus_one = pred.TMultiset.minus_one, "\n");
    Print("  T=i:  analytical=", agg.TMultiset.i_val,
          "  predictor=", pred.TMultiset.i,
          "  match=", agg.TMultiset.i_val = pred.TMultiset.i, "\n");
    Print("  T=-i: analytical=", agg.TMultiset.minus_i,
          "  predictor=", pred.TMultiset.minus_i,
          "  match=", agg.TMultiset.minus_i = pred.TMultiset.minus_i, "\n");
end;;

# Persist a structural representation (NOT the 134M-entry flat vector,
# which would be 2 GB+ on disk; instead, sector-keyed and run-length
# encoded).
SaveStructuralT := function(m, outdir)
    local agg, counts, T_per, manifest_path, sector_index, idx,
          base_path;
    agg := AggregateTMultiset(m);
    counts := agg.sector_counts;
    T_per := agg.T_per_sector;
    Exec(Concatenation("mkdir -p ", outdir));

    # Single structural manifest is sufficient — the per-sector data is
    # uniformly determined by the sector type.
    manifest_path := Concatenation(outdir, "/manifest.g");
    PrintTo(manifest_path,
        "# Mod(D^1(E_+(", m, "))) untwisted, structural T-vector\n",
        "# 4 sector types; per-type T data is determined by type alone.\n",
        "# Total rank = ", agg.total_rank, "\n",
        "manifest := rec(\n",
        "    m := ", m, ",\n",
        "    group_order := ", agg.group_order, ",\n",
        "    rank := ", agg.total_rank, ",\n",
        "    cocycle := \"trivial\",\n",
        "    sector_counts := rec(\n",
        "        identity := ", counts.identity, ",\n",
        "        minus_one := ", counts.minus_one, ",\n",
        "        order2 := ", counts.order2, ",\n",
        "        order4 := ", counts.order4, "\n",
        "    ),\n",
        "    T_per_sector_RLE := rec(\n",
        "        identity := ", T_per.identity_sector, ",\n",
        "        minus_one := ", T_per.minus_one_sector, ",\n",
        "        order2 := ", T_per.order2_sector, ",\n",
        "        order4 := ", T_per.order4_sector, "\n",
        "    ),\n",
        "    TMultiset := rec(\n",
        "        one := ", agg.TMultiset.one, ",\n",
        "        minus_one := ", agg.TMultiset.minus_one, ",\n",
        "        i := ", agg.TMultiset.i_val, ",\n",
        "        minus_i := ", agg.TMultiset.minus_i, "\n",
        "    )\n",
        ");;\n");
    Print("Wrote ", manifest_path, "\n");
end;;
