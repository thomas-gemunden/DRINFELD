# run_e_plus_3_aut.g — A-3d driver: |Aut(N^0, T^0)| cross-validation
# on E_+(3) untwisted modular data.
#
# Implements issue #45 (A-3d). Closes the m=3 ladder begun by A-3a
# (#42, ker Tr) and A-3c (#44, candidate elimination).
#
# Goal:
#   Compute |Aut(N^0, T^0)| for the untwisted modular data of E_+(3)
#   and verify the BRW lower bound
#
#       |Aut(N^0, T^0)| >= |BRW(3) / E_+(3)|.
#
# Math anchor: BRW(m) acts on the simple objects of D(Vec^0_{E_+(m)})
# by outer automorphism (modulo inner = E_+(m) itself), so |Aut(N^0,
# T^0)| is a multiple of |BRW(m)/E_+(m)|. At m=3:
#   |BRW(3)| = |O+(6, F_2)| * |E_+(3)| = 1451520 * 128 / ... actually
#   |BRW(3)/E_+(3)| = |O+(6, F_2)| = 1451520, and |E_+(3)| = 128, so
#   the expected lower bound is 1451520.
#
# Scope: untwisted side only. Per-omega Aut comparisons across the
# 16 non-zero kernel orbits (A-3c) is a follow-up.
#
# Steps:
#   1. Build E_+(3) as a pc-group via BRWH3Action(3).em (cached).
#   2. Compute untwisted modular data (S, T) via
#      ComputeUntwistedModularData; rank = 2272.
#   3. Compute fusion coefficients N := FusionCoefficientsFromS(S)
#      and quantum dimensions QD := QuantumDimensionsFromS(S).
#   4. Run AutNT(N, T, QD) (V-5c) to get |Aut(N^0, T^0)|.
#   5. Compute the BRW lower bound and assert
#      |Aut| >= |BRW(3)/E_+(3)|.
#   6. Persist result to computed/aut_nt/3/untwisted.g.
#
# Usage:
#   gap -q -b -c 'Read("run_e_plus_3_aut.g");'
# from extraspecial_orbifolds/scripts/, or:
#   gap -q -b extraspecial_orbifolds/scripts/run_e_plus_3_aut.g
# from anywhere. We auto-cd to scripts/ so transitive Read()s work.

_driver_path := INPUT_FILENAME();;
if _driver_path <> fail and _driver_path <> "stream"
   and _driver_path <> "*stdin*" then
    _driver_dir := _driver_path{[1..Length(_driver_path)
                                   - Length("/run_e_plus_3_aut.g")]};;
    ChangeDirectoryCurrent(_driver_dir);
fi;

Read("untwisted_modular_data.g");
Read("aut_nt_partition.g");
Read("aut_nt_refine.g");
Read("aut_nt.g");
Read("brw_h3_action.g");      # for BRWH3Action(3).em (pc-group form)
Read("brw_construction.g");   # for BRW(m), EmGroup(m)

t_start := Runtime();;

Print("\n=== A-3d driver: |Aut(N^0, T^0)| for E_+(3) (#45) ===\n");

# ----------------------------------------------------------------------
# Step 1: build E_+(3) as a pc-group via BRWH3Action(3).em.
#
# BRWH3Action(3) does the EmGroup(3) -> IsomorphismPcGroup conversion
# once and caches the result (P-11/#130). We reuse this so we don't
# rebuild the HAP resolution or recompute the iso.
# ----------------------------------------------------------------------

Print("\n--- Step 1: build E_+(3) (pc-group form) ---\n");

m := 3;;
t_em := Runtime();;
h3_action := BRWH3Action(m);;
t_em_wall := (Runtime() - t_em) / 1000.;;
G := h3_action.em;;
Print("BRWH3Action(", m, ") wall: ", t_em_wall, " s\n");
Print("|G| = ", Order(G), " (expect 128)\n");
Assert(0, Order(G) = 128, "E_+(3) should have order 128");

# ----------------------------------------------------------------------
# Step 2: compute untwisted modular data (S, T).
#
# The rank is predicted as 2272 simples (PredictE_plus_m(3)). The
# expensive step is the S-matrix: per (i, j) block we sum
# |class_i| x |C_G(g_i)| terms (P-9/#126), so total work is
# |classes|^2 * |G| character evals = 65^2 * 128 ~ 5.4e5 character
# lookups, each O(r_C). Wall: expect minutes.
# ----------------------------------------------------------------------

Print("\n--- Step 2: untwisted modular data (S, T) ---\n");

t_md := Runtime();;
md := ComputeUntwistedModularData(G);;
t_md_wall := (Runtime() - t_md) / 1000.;;
Print("ComputeUntwistedModularData wall: ", t_md_wall, " s\n");
Print("rank = ", md.idx.rank, " (predicted 2272)\n");
Print("|classes| = ", Length(md.idx.classes), " (predicted 65)\n");

Assert(0, md.idx.rank = 2272, "Expected rank 2272 for E_+(3)");

# Quick T-spectrum sanity.
Tcollect := Collected(md.T);;
Print("T-multiset:\n");
for pair in Tcollect do
    Print("  T = ", pair[1], "  multiplicity ", pair[2], "\n");
od;

# ----------------------------------------------------------------------
# Step 3: fusion coefficients + quantum dimensions.
#
# FusionCoefficientsFromS uses the P-4/#113 native matrix-multiply
# reformulation: per i build M_i = S * diag(S[i] / S[1]) * Sbar^T via
# GAP's native matmul. Per-i cost O(r^3); total O(r^4).
# For r = 2272 this is ~5.3e13 mult-ops in native code.
# ----------------------------------------------------------------------

Print("\n--- Step 3: fusion coefficients + quantum dimensions ---\n");

t_qd := Runtime();;
QD := QuantumDimensionsFromS(md.S);;
t_qd_wall := (Runtime() - t_qd) / 1000.;;
Print("QuantumDimensionsFromS wall: ", t_qd_wall, " s\n");

Print("Computing fusion coefficients N (this is the big O(r^4) step)...\n");
t_fc := Runtime();;
N_fusion := FusionCoefficientsFromS(md.S);;
t_fc_wall := (Runtime() - t_fc) / 1000.;;
Print("FusionCoefficientsFromS wall: ", t_fc_wall, " s\n");

Assert(0, Length(N_fusion) = md.idx.rank,
       "FusionCoefficientsFromS returned wrong dimension");

# ----------------------------------------------------------------------
# Step 4: AutNT.
#
# Partition refinement + backtracking. Initial joint (T, QD) partition
# (V-5a) shrinks the search space dramatically. RefineByFusion (V-5b)
# iterates 1-WL on fusion-row signatures.
#
# We collect generators by default; if this stalls, the spec says we
# can pass {skip_generators := true}. Since AutNT signals the count
# even with skip_generators, we'd lose nothing essential.
# ----------------------------------------------------------------------

Print("\n--- Step 4: AutNT(N, T, QD) ---\n");

t_aut := Runtime();;
aut_result := AutNT(N_fusion, md.T, QD);;
t_aut_wall := (Runtime() - t_aut) / 1000.;;
Print("AutNT wall: ", t_aut_wall, " s\n");
Print("|Aut(N^0, T^0)| = ", aut_result.order, "\n");
Print("# generators returned: ", Length(aut_result.generators), "\n");

# ----------------------------------------------------------------------
# Step 5: BRW lower bound + assertion.
#
# |BRW(m)/E_+(m)| = |O+(2m, F_2)|. At m=3:
#   |BRW(3)| / |E_+(3)| should equal 1451520 (the order of O+(6, F_2)).
#
# We compute both orders directly from the groups: BRW(3) is built
# via brw_construction.g, E_+(3) is what we already have.
# ----------------------------------------------------------------------

Print("\n--- Step 5: BRW lower bound ---\n");

t_brw_lb := Runtime();;
brw_group := BRW(m);;
brw_order := Order(brw_group);;
e_plus_order := Order(G);;
brw_lower := brw_order / e_plus_order;;
t_brw_lb_wall := (Runtime() - t_brw_lb) / 1000.;;

Print("|BRW(", m, ")| = ", brw_order, "\n");
Print("|E_+(", m, ")| = ", e_plus_order, "\n");
Print("|BRW(", m, ")/E_+(", m, ")| = ", brw_lower,
      " (expect |O+(6, F_2)| = 1451520)\n");
Print("BRW build + order wall: ", t_brw_lb_wall, " s\n");

Assert(0, brw_lower = 1451520,
       Concatenation("Expected |BRW(3)/E_+(3)| = 1451520; got ",
                     String(brw_lower)));

# The key assertion.
if aut_result.order < brw_lower then
    Error("|Aut(N^0, T^0)| = ", aut_result.order,
          " < |BRW(3)/E_+(3)| = ", brw_lower,
          " — this contradicts the BRW math anchor!");
fi;
ratio := aut_result.order / brw_lower;;
Print("\n*** ANCHOR CHECK: |Aut| / |BRW/E_+| = ", aut_result.order,
      " / ", brw_lower, " = ", ratio, " ***\n");

# ----------------------------------------------------------------------
# Step 6: persist to computed/aut_nt/3/untwisted.g.
#
# Use OutputTextFile + SetPrintFormattingStatus(stream, false) to avoid
# the PrintTo line-wrap hazard (issues #43/#46). Lines like
#   # ... a long comment ...
# get wrapped at ~80 chars with a backslash continuation by default,
# silently corrupting the file.
# ----------------------------------------------------------------------

Print("\n--- Step 6: persist result ---\n");

OutDir := "../../computed/aut_nt/3";;
Exec(Concatenation("mkdir -p ", OutDir));
OutPath := Concatenation(OutDir, "/untwisted.g");;

# Generators can be large; we cap how many we serialise to avoid a
# multi-MB file. AutNT defaults max_generators = 32, so this is normally
# small (a handful of permutations of length 2272 = ~few KB each).
# We always include `order`; generators are optional.
n_gens_persisted := Length(aut_result.generators);;

total_wall := (Runtime() - t_start) / 1000.;;

stream := OutputTextFile(OutPath, false);;
SetPrintFormattingStatus(stream, false);
PrintTo(stream,
    "# |Aut(N^0, T^0)| for E_+(3) untwisted modular data.\n",
    "#\n",
    "# Generated by extraspecial_orbifolds/scripts/run_e_plus_3_aut.g\n",
    "# (issue #45, A-3d: m=3 |Aut(N, T)| cross-validation).\n",
    "#\n",
    "# G                : E_+(3) = pc-group form of EmGroup(3),\n",
    "#                    Order(G) = 128 (= 2^7).\n",
    "# rank             : 2272 (untwisted Drinfeld centre D(Vec^0_G)).\n",
    "# |Aut(N^0, T^0)|  : ", String(aut_result.order),
    "  (the answer).\n",
    "# BRW lower bound : |BRW(3) / E_+(3)| = ", String(brw_lower),
    " = |O+(6, F_2)|.\n",
    "# Ratio            : |Aut| / |BRW/E_+| = ", String(ratio), ".\n",
    "#\n",
    "# Math anchor (issue #45). BRW(m) acts on the simple objects of\n",
    "# D(Vec^0_{E_+(m)}) by outer automorphism, so |Aut(N^0, T^0)| is\n",
    "# a multiple of |BRW(m)/E_+(m)|. We verify the >= inequality.\n",
    "#\n",
    "# Wall-clock breakdown (this invocation):\n",
    "#   BRWH3Action(3).em (pc form)   : ", String(t_em_wall), " s\n",
    "#   ComputeUntwistedModularData  : ", String(t_md_wall), " s\n",
    "#   QuantumDimensionsFromS       : ", String(t_qd_wall), " s\n",
    "#   FusionCoefficientsFromS      : ", String(t_fc_wall), " s\n",
    "#   AutNT                        : ", String(t_aut_wall), " s\n",
    "#   BRW(3) + order               : ", String(t_brw_lb_wall), " s\n",
    "#   TOTAL                        : ", String(total_wall), " s\n",
    "#\n",
    "# Persisted fields:\n",
    "#   group               : human-readable label.\n",
    "#   id                  : [n, m] such that SmallGroup(n, m) ~= G\n",
    "#                         (pc-group form of EmGroup(3)).\n",
    "#   m                   : 3.\n",
    "#   rank                : # simple objects in D(Vec^0_G).\n",
    "#   aut_order           : |Aut(N^0, T^0)|.\n",
    "#   brw_order           : |BRW(3)|.\n",
    "#   e_plus_order        : |E_+(3)| = 128.\n",
    "#   brw_lower_bound     : |BRW(3)/E_+(3)|.\n",
    "#   ratio               : aut_order / brw_lower_bound.\n",
    "#   T_multiset          : Collected(T) as list of [value, count].\n",
    "#   generators_count    : # generators returned by AutNT.\n",
    "#   generators          : list of length-rank permutation images\n",
    "#                         (sigma[i] = image of i). Capped by AutNT's\n",
    "#                         max_generators (default 32).\n",
    "#   timings             : per-step wall-clock seconds.\n",
    "#\n",
    "# Reload via:\n",
    "#   data := ReadAsFunction(\"untwisted.g\")();\n",
    "\n",
    "return rec(\n",
    "    group              := \"E_+(3) untwisted\",\n",
    "    id                 := ", IdSmallGroup(G), ",\n",
    "    m                  := ", m, ",\n",
    "    rank               := ", md.idx.rank, ",\n",
    "    aut_order          := ", aut_result.order, ",\n",
    "    brw_order          := ", brw_order, ",\n",
    "    e_plus_order       := ", e_plus_order, ",\n",
    "    brw_lower_bound    := ", brw_lower, ",\n",
    "    ratio              := ", ratio, ",\n",
    "    T_multiset         := ", Tcollect, ",\n",
    "    generators_count   := ", n_gens_persisted, ",\n",
    "    generators         := ", aut_result.generators, ",\n",
    "    timings            := rec(\n",
    "        brwh3_action_em   := ", t_em_wall, ",\n",
    "        compute_md        := ", t_md_wall, ",\n",
    "        quantum_dim       := ", t_qd_wall, ",\n",
    "        fusion_coeffs     := ", t_fc_wall, ",\n",
    "        aut_nt            := ", t_aut_wall, ",\n",
    "        brw_lower         := ", t_brw_lb_wall, ",\n",
    "        total             := ", total_wall, "\n",
    "    )\n",
    ");;\n");
CloseStream(stream);
Print("Wrote ", OutPath, "\n");

# ----------------------------------------------------------------------
# Reload sanity check: re-parse the file to confirm it's syntactically
# valid GAP (catches the PrintTo line-wrap hazard early).
# ----------------------------------------------------------------------

Print("\n--- Reload sanity ---\n");
reload_f := ReadAsFunction(OutPath);;
if reload_f = fail then
    Error("Reload of ", OutPath, " failed (file not syntactically valid).");
fi;
reload_data := reload_f();;
Assert(0, reload_data.aut_order = aut_result.order,
       "Reload aut_order mismatch.");
Assert(0, reload_data.brw_lower_bound = brw_lower,
       "Reload brw_lower_bound mismatch.");
Print("Reload OK: aut_order = ", reload_data.aut_order,
      ", brw_lower_bound = ", reload_data.brw_lower_bound, "\n");

# ----------------------------------------------------------------------
# Final summary
# ----------------------------------------------------------------------

Print("\n=== A-3d driver: DONE ===\n");
Print("|Aut(N^0, T^0)|     = ", aut_result.order, "\n");
Print("|BRW(3)/E_+(3)|     = ", brw_lower, "\n");
Print("Ratio               = ", ratio,
      "  (anchor holds: ratio integer = ",
      IsInt(ratio), ")\n");
Print("Total wall          = ", total_wall, " s\n");
Print("Output              : ", OutPath, "\n");

QUIT;
