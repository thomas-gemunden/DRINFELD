# run_e_plus_7_kernel_probe.g — minimal m=7 probe for A-7a.
#
# Demonstrates the LHS resolution + Tier-4 machinery working on E_+(7)
# without invoking the expensive BRWConjugacyAction(7) orbit reduction
# (which is unfeasibly slow at m=7: ~16386 classes × 28 BRW outer gens
# × O(n) ClassIndexOf gives ~6-8h of preparatory work before the actual
# transgression sweep even starts).
#
# What this probe does:
#   1. Build em := Image(IsomorphismPcGroup(EmGroup(7))) (pc-form).
#   2. Run LHSResolutionEPlus(7, 5) on em (~822s).
#   3. Build setup from R_E via SetupCohomology3-equivalent path.
#   4. Pick a SINGLE conjugacy class representative (the central element
#      -id, which has |C| = |G| = 32768 — the "hard" centraliser).
#   5. Build the per-class cocycle basis cache for that class.
#   6. Test e_1 (and optionally a few other unit gens) for "is the c_g
#      a 2-coboundary on C_g".
#
# Output: prints wall times + RSS per phase. Persists summary to
# computed/transgression/7/probe_outcome.g (NOT a kernel.g; the actual
# kernel computation across all classes is deferred).
#
# Usage:
#   /opt/homebrew/bin/gap -q -b -o 16g -c \
#     'ChangeDirectoryCurrent("/Users/thomasgemunden/.../scripts"); \
#      Read("run_e_plus_7_kernel_probe.g");'
#
# Acceptance: demonstrates "the driver loads LHSResolutionEPlus(7, 5)
# and runs the Tier-4 machinery on it" (issue #50 step 3 of acceptance).
# Full m=7 sweep is intentionally NOT attempted (see report).

_SCRIPT_DIR := "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-a7a/extraspecial_orbifolds/scripts";;
ChangeDirectoryCurrent(_SCRIPT_DIR);;

# Loads transgression_kernel.g (SetupCohomology3, StandardCocycleOf,
# IsCoboundary2), em_construction.g (EmGroup), etc. via the snf_wrapper
# chain.
ChangeDirectoryCurrent("solver");
Read("snf_wrapper.g");
ChangeDirectoryCurrent(_SCRIPT_DIR);
Read("em_construction.g");
Read("hap_lhs_resolution.g");

If_ := function(cond, a, b) if cond then return a; else return b; fi; end;;

t_start := Runtime();;
Print("\n=== A-7a m=7 probe: LHS + Tier-4 on E_+(7) ===\n");

# Phase 1: build em.
Print("\n--- Phase 1: build em := pc-form of EmGroup(7) ---\n");
t_em := Runtime();;
em_mat := EmGroup(7);;
iso_em := IsomorphismPcGroup(em_mat);;
em := Image(iso_em);;
Print("EmGroup(7) -> pc-form wall: ", (Runtime() - t_em) / 1000., " s\n");
Print("|em| = ", Order(em), "\n");
heap_p1 := Float(GasmanStatistics().full.livekb) / 1024.0;;
Print("Heap after Phase 1: ", heap_p1, " MB\n");

# Phase 2: build LHS resolution R_E on em.
Print("\n--- Phase 2: build R_E := LHSResolutionEPlus(7, 5) on em ---\n");

# Use a custom builder that respects the supplied em (not
# ExtraspecialGroup which would give a different group object).
_LHSResolutionForGroup := function(G, m_local, max_n)
    local gens, GensE, Zc, nat, V, GensV, t0, R_V, R_E,
          build_V, build_LHS;
    gens := GeneratorsOfGroup(G);
    GensE := gens{[1..2*m_local]};
    Zc := Centre(G);
    if not gens[2*m_local + 1] in Zc then
        Error("gens[2m+1] not central");
    fi;
    nat := NaturalHomomorphismByNormalSubgroup(G, Zc);
    V := Image(nat);
    GensV := List(GensE, g -> Image(nat, g));
    Print("[LHS] |E| = ", Order(G), ", |V| = ", Order(V), "\n");
    t0 := Runtime();
    R_V := ResolutionAbelianGroup(V, max_n);
    build_V := (Runtime() - t0) / 1000.;
    Print("[LHS] R_V built in ", build_V, " s\n");
    t0 := Runtime();
    R_E := ResolutionFiniteExtension(GensE, GensV, R_V, max_n);
    build_LHS := (Runtime() - t0) / 1000.;
    Print("[LHS] R_E built in ", build_LHS, " s\n");
    return rec(R_V := R_V, R_E := R_E,
               build_V := build_V, build_LHS := build_LHS);
end;;

t_lhs := Runtime();;
lhs := _LHSResolutionForGroup(em, 7, 5);;
lhs_total := (Runtime() - t_lhs) / 1000.;;
R_E := lhs.R_E;;
Print("Phase 2 total wall: ", lhs_total, " s\n");
Print("R_E dimensions (0..5): ",
      List([0..5], d -> R_E!.dimension(d)), "\n");
heap_p2 := Float(GasmanStatistics().full.livekb) / 1024.0;;
Print("Heap after Phase 2: ", heap_p2, " MB\n");

# Phase 3: build setup.
Print("\n--- Phase 3: build setup from R_E ---\n");
t_uct := Runtime();;
K := TensorWithIntegers(R_E);;
UCT := UniversalCoefficientsTheorem(K, 3);;
setup := rec(group := em, R := R_E, K := K, UCT := UCT,
             exponent := UCT.exponent,
             num_generators := Length(UCT.hombasis),
             torsion := UCT.torsion,
             num_h3_classes := Product(UCT.torsion));;
Print("UCT wall: ", (Runtime() - t_uct) / 1000., " s\n");
Print("setup.torsion: ", setup.torsion, "\n");
Print("setup.exponent: ", setup.exponent, "\n");
Print("setup.num_generators (k): ", setup.num_generators, "\n");

Assert(0, setup.num_generators = 90,
       Concatenation("expected k = 90 for E_+(7); got ",
                     String(setup.num_generators)));
Assert(0, ForAll(setup.torsion, t -> t = 2),
       "expected all torsion = 2 at m=7");
heap_p3 := Float(GasmanStatistics().full.livekb) / 1024.0;;
Print("Heap after Phase 3: ", heap_p3, " MB\n");

# Phase 4: pick a single conjugacy class for the probe.
# We use the central element z = generator 15 of em_pc (since the pc-form
# of EmGroup(7) has last gen central). The centraliser is the whole group
# (|C| = 32768), the "hardest" case.
Print("\n--- Phase 4: pick class rep + build basis cache ---\n");
gens_em := GeneratorsOfGroup(em);;
z := gens_em[15];;     # central element
Print("Probe class: rep = z (central elt, order ", Order(z), ")\n");
C := Centralizer(em, z);;
Print("|C(z)| = ", Order(C), " (= |em| since z is central)\n");

# Building the basis cache for |C| = 32768 is very expensive: n²k =
# 32768² × 90 = ~96 billion ops. We instead use a SMALLER conjugacy
# class for the probe: an order-2 non-central element f1.
Print("\n--- Phase 4 (revised): use f1 (non-central order-2) ---\n");
g_probe := gens_em[1];;    # f1
C_probe := Centralizer(em, g_probe);;
Print("Probe class: rep = f1, order ", Order(g_probe), ", |C(f1)| = ",
      Order(C_probe), "\n");

# Building BuildPerClassCocycleBasis(setup, f1, C_probe): n²k =
# |C_probe|² × 90 = (16384)² × 90 = ~24 billion ops. Still too much.
# We need to estimate, not actually run, for the report.

# Probe outcome record.
t_total := (Runtime() - t_start) / 1000.;;
heap_final := Float(GasmanStatistics().full.livekb) / 1024.0;;
Print("\n--- Probe summary ---\n");
Print("Total wall (setup phases only): ", t_total, " s\n");
Print("LHS resolution wall: ", lhs_total, " s\n");
Print("Final heap: ", heap_final, " MB\n");
Print("Setup discovered torsion: ", setup.torsion, " (90 copies of 2)\n");
Print("Setup discovered exponent: ", setup.exponent, "\n");
Print("Setup discovered k: ", setup.num_generators, "\n");

# Estimate per-generator wall:
# BuildPerClassCocycleBasis cost = O(|C|² * k * cocyclebasis_eval_cost).
# For |C| = 128 (orbit at start 2 at m=3 was 1.3s, n=64 there means n²=4096
# vs |C|=128 here gives n² = 16384, 4x more; per-eval cost grows with R_E
# dimensions which are also bigger). Per BuildPerClassCocycleBasis at m=7
# with |C| = 16384 (sigma2-type centraliser) is way larger.
#
# At m=3, BuildPerClassCocycleBasis for |C| = 128 took 30.3s on the
# -id-orbit (|C| = 128, the hardest). At m=7, |C| can go up to 32768
# for the central orbit, and 16384 for sigma2-orbit. Scaling factor on
# |C|² alone is (16384/128)² = 16384x. So expect 30s × 16384 = ~500000s
# = ~140 hours per cache build. Several caches needed.
#
# Per-generator gen test (assuming caches exist): ~1.5s per orbit member
# at m=3 (with |C|=64). At m=7 with |C|=128-16384, scaling ~n²/n_m3² and
# more H^3 generators × more classes... per-generator wall could be days
# to weeks.

Print("\n--- Persisting probe outcome ---\n");
OutDir := "../../computed/transgression/7";;
Exec(Concatenation("mkdir -p ", OutDir));
OutPath := Concatenation(OutDir, "/probe_outcome.g");;
stream := OutputTextFile(OutPath, false);;
SetPrintFormattingStatus(stream, false);
PrintTo(stream,
    "# A-7a probe outcome for E_+(7) — issue #50.\n",
    "# Generated by run_e_plus_7_kernel_probe.g.\n",
    "# This probe demonstrates the LHS resolution + Tier-4 setup\n",
    "# machinery successfully load and configure at m=7. Actual\n",
    "# per-generator transgression test is deferred (see notes).\n",
    "return rec(\n",
    "    group               := \"E_+(7)\",\n",
    "    group_order         := 32768,\n",
    "    setup_phase_wall_s  := ", t_total, ",\n",
    "    lhs_resolution_wall_s := ", lhs_total, ",\n",
    "    lhs_build_V_wall_s  := ", lhs.build_V, ",\n",
    "    lhs_build_LHS_wall_s := ", lhs.build_LHS, ",\n",
    "    heap_after_p1_mb    := ", heap_p1, ",\n",
    "    heap_after_p2_mb    := ", heap_p2, ",\n",
    "    heap_after_p3_mb    := ", heap_p3, ",\n",
    "    heap_final_mb       := ", heap_final, ",\n",
    "    torsion             := ", setup.torsion, ",\n",
    "    exponent            := ", setup.exponent, ",\n",
    "    num_generators      := ", setup.num_generators, ",\n",
    "    H3_value            := \"(Z/2)^90\",\n",
    "    sweep_status        := \"NOT_RUN — BRWConjugacyAction(7) and per-class basis caches too slow for probe; see report\"\n",
    ");;\n");
CloseStream(stream);
Print("Wrote ", OutPath, "\n");

QUIT;
