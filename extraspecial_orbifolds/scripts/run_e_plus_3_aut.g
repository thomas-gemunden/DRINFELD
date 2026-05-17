# run_e_plus_3_aut.g — A-3d driver: |Aut(N^0, T^0)| analysis on E_+(3)
# untwisted modular data.
#
# Implements issue #45 (A-3d). Closes the m=3 ladder begun by A-3a
# (#42, ker Tr) and A-3c (#44, candidate elimination).
#
# Goal:
#   Verify the BRW lower bound
#
#       |Aut(N^0, T^0)| >= |BRW(3) / E_+(3)|
#
#   for E_+(3)'s untwisted Drinfeld centre.
#
# Math anchor: BRW(m) acts on the simple objects of D(Vec^0_{E_+(m)})
# by outer automorphism (modulo inner = E_+(m) itself), so |Aut(N^0,
# T^0)| is a multiple of |BRW(m)/E_+(m)|. At m=3:
#   |BRW(3)/E_+(3)| = 40320 (= GAP's |GO+(6, F_2)|; this matches
#   test_brw_conjugacy_action.g and the BRW-class action subgroup size).
#
# Two paths to the |Aut| >= |BRW/E_+| anchor are available:
#
#   (1) Default (issue #239 / PR for A-3d perf-1): the constructive
#       lower-bound check. For each generator y of BRW(3) we build the
#       lifted permutation sigma_y in Sym(2272) (via
#       brw_aut_lower_bound.g) and verify it is an (N, T)-automorphism;
#       the generated subgroup has order |BRW(3)/E_+(3)|. This is fast
#       (~2 min wall) and gives |Aut| >= 40320 constructively, without
#       running the full AutNT backtracking.
#
#   (2) Optional (gated by A3D_FULL_AUTNT := true): the original full
#       AutNT backtracking path. Computes |Aut(N^0, T^0)| exactly, then
#       checks the BRW lower bound. Wall ~ 100h+ at r=2272 under the
#       V-5c implementation (well above the perf budget); use only
#       when an exact |Aut| value is needed for downstream comparisons.
#
# Scope: untwisted side only. Per-omega Aut comparisons across the
# 16 non-zero kernel orbits (A-3c) is a follow-up.
#
# Steps:
#   1. Build E_+(3) as a pc-group via BRWConjugacyAction(3).em.
#   2. Compute untwisted modular data (S, T) via
#      ComputeUntwistedModularData; rank = 2272.
#   3. Compute the BRW lower bound |BRW(m)/E_+(m)|.
#   4. Default (perf-1): explicit constructive certificate that each
#      BRW(m)/E_+(m) element is a valid (N, T)-automorphism via
#      VerifyBRWAutLowerBound — closes the structural inequality
#      |Aut(N^0, T^0)| >= |BRW(m)/E_+(m)| in ~minutes.
#      Gated with A3D_FULL_AUTNT := true: run full AutNT against the
#      streaming fusion oracle (PR #237) for the exact |Aut| value.
#      The streaming oracle avoids materialising the O(r^3) dense
#      tensor (~94 GB at r=2272).
#   5. Persist result to computed/aut_nt/3/brw_lower_bound.g (default)
#      or computed/aut_nt/3/untwisted.g (A3D_FULL_AUTNT).
#
# Usage:
#   gap -q -b -c 'Read("run_e_plus_3_aut.g");'
# from extraspecial_orbifolds/scripts/, or:
#   gap -q -b extraspecial_orbifolds/scripts/run_e_plus_3_aut.g
# from anywhere. We auto-cd to scripts/ so transitive Read()s work.
#
# Optional flags (set before Read):
#   A3D_FULL_AUTNT := true;   # use full AutNT instead of BRW lower bound
#   A3D_SKIP_PERSIST := true; # do not write computed/aut_nt/3/...

_driver_path := INPUT_FILENAME();;
if _driver_path <> fail and _driver_path <> "stream"
   and _driver_path <> "*stdin*" then
    _driver_dir := _driver_path{[1..Length(_driver_path)
                                   - Length("/run_e_plus_3_aut.g")]};;
    ChangeDirectoryCurrent(_driver_dir);
fi;

Read("untwisted_modular_data.g");
Read("brw_construction.g");
Read("brw_conjugacy_action.g");
Read("brw_aut_lower_bound.g");
# Lazy-loaded by the A3D_FULL_AUTNT branch (slow path):
#   aut_nt_partition.g, fusion_oracle.g, aut_nt_refine.g, aut_nt.g

# Small local helper (idempotent; defined identically elsewhere).
if not IsBound(If_) then
    If_ := function(c, a, b) if c then return a; else return b; fi; end;;
fi;

# Set defaults for optional flags.
if not IsBound(A3D_FULL_AUTNT) then
    A3D_FULL_AUTNT := false;
fi;
if not IsBound(A3D_SKIP_PERSIST) then
    A3D_SKIP_PERSIST := false;
fi;

t_start := Runtime();;

Print("\n=== A-3d driver: |Aut(N^0, T^0)| analysis for E_+(3) (#45) ===\n");
Print("Path: ", If_(A3D_FULL_AUTNT, "FULL AutNT (slow, exact)",
                    "BRW lower-bound check (fast, constructive)"), "\n");

# ----------------------------------------------------------------------
# Step 1: build E_+(3) as a pc-group via BRWConjugacyAction(3).em.
# ----------------------------------------------------------------------

Print("\n--- Step 1: build E_+(3) (pc-group form) ---\n");

m := 3;;
t_em := Runtime();;
conj_action := BRWConjugacyAction(m);;
t_em_wall := (Runtime() - t_em) / 1000.;;
G := conj_action.em;;
Print("BRWConjugacyAction(", m, ") wall: ", t_em_wall, " s\n");
Print("|G| = ", Order(G), " (expect 128)\n");
Assert(0, Order(G) = 128, "E_+(3) should have order 128");

# ----------------------------------------------------------------------
# Step 2: compute untwisted modular data (S, T).
# ----------------------------------------------------------------------

Print("\n--- Step 2: untwisted modular data (S, T) ---\n");

t_md := Runtime();;
md := ComputeUntwistedModularData(G);;
t_md_wall := (Runtime() - t_md) / 1000.;;
Print("ComputeUntwistedModularData wall: ", t_md_wall, " s\n");
Print("rank = ", md.idx.rank, " (predicted 2272)\n");
Assert(0, md.idx.rank = 2272, "Expected rank 2272 for E_+(3)");

# Quick T-spectrum sanity.
Tcollect := Collected(md.T);;

# ----------------------------------------------------------------------
# Step 3: BRW lower bound + assertion.
# ----------------------------------------------------------------------

Print("\n--- Step 3: BRW lower bound ---\n");

t_brw_lb := Runtime();;
brw_group := BRW(m);;
brw_order := Order(brw_group);;
e_plus_order := Order(G);;
brw_lower := brw_order / e_plus_order;;
t_brw_lb_wall := (Runtime() - t_brw_lb) / 1000.;;

Print("|BRW(", m, ")| = ", brw_order, "\n");
Print("|E_+(", m, ")| = ", e_plus_order, "\n");
Print("|BRW(", m, ")/E_+(", m, ")| = ", brw_lower, "\n");
Print("BRW build + order wall: ", t_brw_lb_wall, " s\n");

# Note. The original driver expected brw_lower = 1451520 here, but
# empirically (and in agreement with test_brw_conjugacy_action.g)
# |BRW(3)/E_+(3)| = 40320 in our brw_construction.g (= |GO+(6, F_2)|
# in GAP's convention). The issue spec had a math-convention error.

# ----------------------------------------------------------------------
# Step 4: BRW lower-bound certificate (default) OR full AutNT (gated).
# ----------------------------------------------------------------------

if A3D_FULL_AUTNT then
    Print("\n--- Step 4: full AutNT(N, T, QD) ---\n");
    Read("aut_nt_partition.g");
    Read("aut_nt_refine.g");
    Read("aut_nt.g");

    Print("Computing quantum dimensions ...\n");
    t_qd := Runtime();;
    QD := QuantumDimensionsFromS(md.S);;
    t_qd_wall := (Runtime() - t_qd) / 1000.;;
    Print("QuantumDimensionsFromS wall: ", t_qd_wall, " s\n");

    Read("fusion_oracle.g");

    Print("Building streaming fusion oracle (cache_size=64) ...\n");
    t_fc := Runtime();;
    N_cache_size := 64;;
    N_oracle := MakeStreamingFusionOracle(md.S,
                    rec(cache_size := N_cache_size,
                        integer_path := true));;
    t_fc_wall := (Runtime() - t_fc) / 1000.;;
    Print("MakeStreamingFusionOracle (cache_size=",
          N_cache_size, ") wall: ", t_fc_wall, " s\n");

    t_aut := Runtime();;
    aut_result := AutNT(N_oracle, md.T, QD);;
    t_aut_wall := (Runtime() - t_aut) / 1000.;;
    Print("AutNT wall: ", t_aut_wall, " s\n");
    Print("|Aut(N^0, T^0)| = ", aut_result.order, "\n");
    Print("# generators returned: ", Length(aut_result.generators), "\n");

    # The key assertion.
    if aut_result.order < brw_lower then
        Error("|Aut(N^0, T^0)| = ", aut_result.order,
              " < |BRW(3)/E_+(3)| = ", brw_lower,
              " — this contradicts the BRW math anchor!");
    fi;
    ratio := aut_result.order / brw_lower;;
    Print("\n*** ANCHOR CHECK: |Aut| / |BRW/E_+| = ", aut_result.order,
          " / ", brw_lower, " = ", ratio, " ***\n");

    out_subpath := "untwisted.g";
else
    Print("\n--- Step 4: BRW lower-bound constructive certificate ---\n");
    Print("Building BRWSimpleAction(", m, ") ...\n");
    t_action := Runtime();;
    action := BRWSimpleAction(m, md.idx);;
    t_action_wall := (Runtime() - t_action) / 1000.;;
    Print("BRWSimpleAction wall: ", t_action_wall, " s\n");

    Print("Verifying each generator's permutation preserves (S, T) ...\n");
    t_verify := Runtime();;
    verification := VerifyBRWAutLowerBound(md, action, rec(
        verbose := true,
        expected_lb := brw_lower,
        group_label := "E_+(3) untwisted"));;
    t_verify_wall := (Runtime() - t_verify) / 1000.;;
    Print("VerifyBRWAutLowerBound wall: ", t_verify_wall, " s\n");

    if verification.verdict <> "BOUND_VERIFIED" then
        Error("BRW lower-bound certificate failed: verdict = ",
              verification.verdict);
    fi;
    Print("\n*** ANCHOR CHECK (constructive): ",
          verification.count_verified,
          " BRW elements verified as (N, T)-automorphisms; ",
          "|Aut(N^0, T^0)| >= ", brw_lower, " ***\n");

    out_subpath := "brw_lower_bound.g";
fi;

# ----------------------------------------------------------------------
# Step 5: persist result.
# ----------------------------------------------------------------------

if not A3D_SKIP_PERSIST then
    Print("\n--- Step 5: persist result ---\n");
    OutDir := "../../computed/aut_nt/3";;
    Exec(Concatenation("mkdir -p ", OutDir));
    OutPath := Concatenation(OutDir, "/", out_subpath);;

    total_wall := (Runtime() - t_start) / 1000.;;

    stream := OutputTextFile(OutPath, false);;
    SetPrintFormattingStatus(stream, false);
    if A3D_FULL_AUTNT then
        PrintTo(stream,
            "# |Aut(N^0, T^0)| for E_+(3) untwisted modular data.\n",
            "# Generated by run_e_plus_3_aut.g (A3D_FULL_AUTNT path).\n",
            "# Issue #45 (A-3d).\n",
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
            "    generators_count   := ",
                Length(aut_result.generators), ",\n",
            "    generators         := ",
                aut_result.generators, ",\n",
            "    total_wall         := ", total_wall, "\n",
            ");;\n");
    else
        PrintTo(stream,
            "# BRW lower-bound certificate for E_+(3) untwisted.\n",
            "# Generated by run_e_plus_3_aut.g (default constructive path).\n",
            "# Issue #239 (A-3d perf-1), parent #45 (A-3d).\n",
            "#\n",
            "# count_verified BRW elements were explicitly checked to be\n",
            "# (N, T)-automorphisms of D(Vec^0_{E_+(3)}). This is a\n",
            "# constructive certificate of |Aut(N^0, T^0)| >= count_verified.\n",
            "return rec(\n",
            "    group              := \"E_+(3) untwisted\",\n",
            "    id                 := ", IdSmallGroup(G), ",\n",
            "    m                  := ", m, ",\n",
            "    rank               := ", md.idx.rank, ",\n",
            "    brw_order          := ", brw_order, ",\n",
            "    e_plus_order       := ", e_plus_order, ",\n",
            "    brw_lower_bound    := ", brw_lower, ",\n",
            "    count_verified     := ",
                verification.count_verified, ",\n",
            "    count_failed       := ",
                verification.count_failed, ",\n",
            "    subgroup_order     := ",
                verification.subgroup_order, ",\n",
            "    verdict            := \"", verification.verdict, "\",\n",
            "    T_multiset         := ", Tcollect, ",\n",
            "    total_wall         := ", total_wall, "\n",
            ");;\n");
    fi;
    CloseStream(stream);
    Print("Wrote ", OutPath, "\n");

    # Reload sanity.
    reload_f := ReadAsFunction(OutPath);;
    if reload_f = fail then
        Error("Reload of ", OutPath, " failed.");
    fi;
    reload_data := reload_f();;
    Assert(0, reload_data.brw_lower_bound = brw_lower,
           "Reload brw_lower_bound mismatch.");
    Print("Reload OK.\n");
fi;

total_wall := (Runtime() - t_start) / 1000.;;

Print("\n=== A-3d driver: DONE ===\n");
Print("Total wall = ", total_wall, " s\n");

QUIT;
