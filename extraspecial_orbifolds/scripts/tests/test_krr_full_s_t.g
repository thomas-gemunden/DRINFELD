# K-3 extension (#211): full S matrix + T diagonal anchor at m=3.
#
# # Background
#
# K-3 (#40, completed) verified `SKeller(3, i, j) = S^0_central(i, j)`
# for all 295,360 central-row entries at m=3 (test
# `test_krr_vs_central_closed_form.g`, ~16.6s).
#
# Issue #211 extends that anchor to:
#   1. ALL ~5.16M S entries at m=3 (not just central rows).
#   2. ALL 2272 T-diagonal entries at m=3.
#
# Motivation: with T4c (#208) on the way, we want the densest possible
# ground-truth anchor at m=3 so that any character-misidentification bug
# in T4c manifests as off-central S^α divergence from S^0.
#
# # What we test
#
# At m=3, with the K-2 cache providing SKeller and the K-1 untwisted
# modular-data path providing the ground truth, we verify:
#
#   (S1)  For every (gi, gj) ∈ [1..rank] × [1..rank]:
#             SKeller(3, gi, gj) = S^0(gi, gj)
#         where S^0 is the dense untwisted S computed block-wise via
#         `ComputeSBlock` from `untwisted_modular_data.g`.
#
#         Total entries: idx.rank^2 = 2272^2 = 5,161,984.
#
#         Optimisation: S is symmetric (over the modular center), so it
#         suffices to iterate (ci, cj) class pairs with ci <= cj. For
#         ci < cj we also verify the symmetry
#             blockS_{ci,cj}[k1,k2] = blockS_{cj,ci}[k2,k1]
#         and SKeller's symmetry on a per-entry basis.
#
#   (T1)  For every gi ∈ [1..rank]:
#             T^Keller_diag[gi] = T^0_diag[gi]
#         where:
#           - T^Keller comes from `ComputeUntwistedT` on the K-2 cache's
#             lazy idx (exercising the lazy CT-materialisation path the
#             SKeller adapter uses internally).
#           - T^0 comes from `ComputeUntwistedT` on a freshly built
#             EAGER idx (`BuildSimpleIndex`), built independently from
#             the same group.
#
#         Total entries: idx.rank = 2272.
#
# # Independence of the two T paths
#
# The two paths both reduce to the same algebraic formula
#     T_{(g, chi)} = chi(g) / chi(1)
# but they exercise:
#   - LAZY `BuildSimpleIndexLazy` + on-demand CT builds via
#     `_EnsureClassData` (the cache path used by SKeller queries),
#     vs.
#   - EAGER `BuildSimpleIndex` with all CTs built up-front.
# Disagreement would indicate a lazy-vs-eager bug in the index plumbing,
# which is a real risk worth covering.
#
# # Runtime budget
#
# K-3 central-row sweep: ~16.6s for 295,360 entries (~56µs/entry, doing
# 3 computations per entry: SKeller + closed_form + helper).
#
# This test does 1 SKeller call per entry + 1 ComputeSBlock per (ci,cj)
# pair (block-amortised). For 5.16M entries we expect:
#   - SKeller per-entry cost: ~290s   (5.16M × ~56µs)
#   - ComputeSBlock total:    ~14s × (5.16M / 295k) ≈ 240s
# Pure ComputeSBlock at full S is ~4 min on the K-3 box. With symmetry
# we halve the off-diagonal work (only ci <= cj pairs).
#
# Acceptance ceiling: < 10 minutes wall.
#
# # Invocation
#
# Per K-4a-T1 convention, run by absolute path:
#
#   /opt/homebrew/bin/gap -q -b -c 'Read("/abs/path/to/test_krr_full_s_t.g");'
#
# The test prints PASS/FAIL with per-phase timings and calls QUIT at the
# end.

BreakOnError := false;;
SetInfoLevel(InfoWarning, 0);;

# ---- Locate self via INPUT_FILENAME (K-4a-T1 convention) ----------------
# The K-4a-T1 convention is to invoke by absolute path:
#   /opt/homebrew/bin/gap -q -b -c 'Read("/abs/path/to/test_krr_full_s_t.g");'
# In that case INPUT_FILENAME() returns the absolute path and we can
# derive the scripts/ directory deterministically.
#
# For compatibility with `run_tests.sh` (which `cd`s into scripts/ and
# invokes `gap -q -b "tests/test_krr_full_s_t.g"`), the derived
# SCRIPTSDIR is "" (empty), and we fall back to CWD-relative Read()
# calls — exactly the same pattern the older tests already use.
KRR_FULL_SELF := INPUT_FILENAME();;
if KRR_FULL_SELF = fail or KRR_FULL_SELF = "stream" then
    Error("test_krr_full_s_t.g: INPUT_FILENAME() unavailable; ",
          "Read the file by its absolute path.");
fi;
KRR_FULL_SELFDIR := KRR_FULL_SELF{[1..Length(KRR_FULL_SELF)
    - Length("/test_krr_full_s_t.g")]};;
# tests/test_krr_full_s_t.g -> .../tests/
# parent: .../extraspecial_orbifolds/scripts/  (if absolute)
#                              "" (if relative invocation, e.g. run_tests.sh)
KRR_FULL_SCRIPTSDIR := KRR_FULL_SELFDIR{
    [1..Length(KRR_FULL_SELFDIR) - Length("/tests")]};;

# Helper: load a sibling-script either via absolute path (K-4a-T1) or
# via CWD-relative path (run_tests.sh style).
KRR_FULL_ReadSibling := function(rel)
    local abs_path;
    if KRR_FULL_SCRIPTSDIR = "" then
        Read(rel);
    else
        abs_path := Concatenation(KRR_FULL_SCRIPTSDIR, "/", rel);
        Read(abs_path);
    fi;
end;;

# ---- Load dependencies, in order ----------------------------------------
KRR_FULL_ReadSibling("em_construction.g");
KRR_FULL_ReadSibling("untwisted_modular_data.g");
KRR_FULL_ReadSibling("krr_projector.g");
KRR_FULL_ReadSibling("skeller_adapter.g");


# ================================================================
# Phase 0: bookkeeping helpers.
# ================================================================
Print("\n=================================================================\n");
Print("  K-3 extension (#211): full S + T diagonal at m=3\n");
Print("=================================================================\n");

KRR_FULL_FAILURES := [];;
KRR_FULL_RegisterFail := function(label, info)
    Print("  [FAIL] ", label, "\n");
    if info <> fail then
        Print("         ", info, "\n");
    fi;
    Add(KRR_FULL_FAILURES, label);
end;;
KRR_FULL_RegisterPass := function(label)
    Print("  [ok] ", label, "\n");
end;;

t_total_start := Runtime();;


# ================================================================
# Phase 1: cache build for E_+(3) (lazy idx + eager transports).
# ================================================================
Print("\n--- Phase 1: build K-2 cache for E_+(3) ---\n");

t1_start := Runtime();;
entry3 := SKellerGetCache(3);;
data3 := entry3.data;;
idx_lazy := data3.idx;;
transport_lazy := data3.transport;;
t1_end := Runtime();;
t1_ms := t1_end - t1_start;;

Print("E_+(3): order ", Order(entry3.group),
      ", classes ", Length(idx_lazy.classes),
      ", rank ", idx_lazy.rank, "\n");
Print("Cache build/fetch: ", t1_ms, " ms (", t1_ms / 1000., " s)\n");

# Basic sanity: expect rank 2272 and 65 classes (E_+(3) standard).
if idx_lazy.rank <> 2272 then
    KRR_FULL_RegisterFail("rank check (expected 2272)",
        Concatenation("got rank = ", String(idx_lazy.rank)));
else
    KRR_FULL_RegisterPass("rank = 2272");
fi;
if Length(idx_lazy.classes) <> 65 then
    KRR_FULL_RegisterFail("class count check (expected 65)",
        Concatenation("got #classes = ",
                      String(Length(idx_lazy.classes))));
else
    KRR_FULL_RegisterPass("class count = 65");
fi;


# ================================================================
# Phase 2: build a fresh EAGER idx for the ground-truth path.
#
# We deliberately build a brand-new BuildSimpleIndex (eager) from the
# same group so the comparison crosses two independent idx builds. This
# also exercises the eager CT-materialisation path that BuildSimpleIndex
# itself uses.
# ================================================================
Print("\n--- Phase 2: build fresh eager idx for the same group ---\n");

t2_start := Runtime();;
idx_eager := BuildSimpleIndex(entry3.group);;
t2_end := Runtime();;
t2_ms := t2_end - t2_start;;

Print("Eager BuildSimpleIndex: ", t2_ms, " ms (", t2_ms / 1000., " s)\n");

if idx_eager.rank <> idx_lazy.rank then
    KRR_FULL_RegisterFail(
        "eager idx rank matches lazy idx rank",
        Concatenation("eager rank=", String(idx_eager.rank),
                      "  lazy rank=", String(idx_lazy.rank)));
else
    KRR_FULL_RegisterPass(Concatenation("eager rank = lazy rank = ",
                                        String(idx_eager.rank)));
fi;
if Length(idx_eager.classes) <> Length(idx_lazy.classes) then
    KRR_FULL_RegisterFail("eager #classes matches lazy #classes",
        Concatenation("eager #classes=",
                      String(Length(idx_eager.classes)),
                      "  lazy #classes=",
                      String(Length(idx_lazy.classes))));
else
    KRR_FULL_RegisterPass("eager #classes = lazy #classes");
fi;
# Class representatives should also agree element-wise (same group, same
# ConjugacyClasses call order under GAP — but defensive).
KRR_FULL_reps_match := List([1..Length(idx_eager.classes)],
    i -> idx_eager.reps[i] = idx_lazy.reps[i]);;
if not ForAll(KRR_FULL_reps_match, x -> x) then
    KRR_FULL_RegisterFail(
        "eager.reps = lazy.reps element-wise",
        Concatenation("first mismatch at i=",
            String(Position(KRR_FULL_reps_match, false))));
else
    KRR_FULL_RegisterPass("eager.reps = lazy.reps element-wise");
fi;


# ================================================================
# Phase 3: T-diagonal check.
#
#   T^Keller := ComputeUntwistedT(idx_lazy)
#   T^0      := ComputeUntwistedT(idx_eager)
#
# Both reduce to chi(g)/chi(1) but exercise different idx-internal
# paths (lazy CT materialisation vs eager). Expect element-wise
# cyclotomic equality.
# ================================================================
Print("\n--- Phase 3: T-diagonal (2272 entries) ---\n");

t3_start := Runtime();;
T_keller := ComputeUntwistedT(idx_lazy);;
t3_mid := Runtime();;
T_zero := ComputeUntwistedT(idx_eager);;
t3_end := Runtime();;
t3_keller_ms := t3_mid - t3_start;;
t3_zero_ms := t3_end - t3_mid;;
t3_total_ms := t3_end - t3_start;;

Print("T^Keller (lazy idx): ", t3_keller_ms, " ms\n");
Print("T^0      (eager idx): ", t3_zero_ms, " ms\n");
Print("Total T phase:        ", t3_total_ms, " ms\n");

KRR_FULL_t_mismatch := 0;;
KRR_FULL_t_first_mismatches := [];;
if Length(T_keller) <> Length(T_zero) then
    KRR_FULL_RegisterFail("T-diagonal lengths agree",
        Concatenation("|T^Keller|=", String(Length(T_keller)),
                      "  |T^0|=", String(Length(T_zero))));
    # Bump mismatch counter so summary reports a non-zero failure here.
    KRR_FULL_t_mismatch := AbsInt(Length(T_keller) - Length(T_zero));
else
    for KRR_FULL_i in [1..Length(T_keller)] do
        if T_keller[KRR_FULL_i] <> T_zero[KRR_FULL_i] then
            KRR_FULL_t_mismatch := KRR_FULL_t_mismatch + 1;
            if Length(KRR_FULL_t_first_mismatches) < 5 then
                Add(KRR_FULL_t_first_mismatches,
                    rec(gi := KRR_FULL_i,
                        T_keller := T_keller[KRR_FULL_i],
                        T_zero := T_zero[KRR_FULL_i]));
            fi;
        fi;
    od;
    Print("T-diagonal mismatches: ", KRR_FULL_t_mismatch, " / ",
          Length(T_keller), "\n");
    if KRR_FULL_t_mismatch = 0 then
        KRR_FULL_RegisterPass(Concatenation(
            "T-diagonal full agreement (",
            String(Length(T_keller)), " entries)"));
    else
        KRR_FULL_RegisterFail(
            "T-diagonal full agreement",
            Concatenation(String(KRR_FULL_t_mismatch),
                          " mismatches"));
        Print("  First mismatches:\n");
        for KRR_FULL_ex in KRR_FULL_t_first_mismatches do
            Print("    gi=", KRR_FULL_ex.gi,
                  ": T^Keller=", KRR_FULL_ex.T_keller,
                  "  T^0=", KRR_FULL_ex.T_zero, "\n");
        od;
    fi;
fi;

# Light T-multiset sanity (E_+(3) prediction): all entries should be
# fourth roots of unity (1, -1, i, -i).
KRR_FULL_t_unitlike := Filtered(T_keller, t -> t^4 <> 1);;
if Length(KRR_FULL_t_unitlike) > 0 then
    KRR_FULL_RegisterFail("T-diagonal entries are 4th roots of unity",
        Concatenation(String(Length(KRR_FULL_t_unitlike)),
                      " non-4th-root entries; first: ",
                      String(KRR_FULL_t_unitlike[1])));
else
    KRR_FULL_RegisterPass("T-diagonal: all entries are 4th roots of unity");
fi;


# ================================================================
# Phase 4: full S anchor.
#
# Strategy:
#   For each unordered pair (ci, cj) with ci <= cj:
#     - blockS := ComputeSBlock(idx_lazy, transport_lazy, ci, cj)
#       (batched dense; reuses transports and CT data)
#     - For each entry (k1, k2) in the block:
#         vK := SKeller(3, gi, gj)
#         vS := blockS[k1][k2]
#         compare; tally mismatches.
#       For the off-diagonal (ci < cj) case we ALSO verify by computing
#       the mirrored block via index swap (the SKeller call provides
#       this; ComputeSBlock(cj, ci) is then redundant but used as a
#       sanity check on symmetry of the batched path).
#
# Counters:
#   s_total_pairs   : # of (gi, gj) pairs visited (after symmetry)
#   s_total_entries : # of entries compared (including mirror)
#   s_mismatch_KS   : SKeller vs ComputeSBlock (headline)
#   s_mismatch_sym  : symmetry SKeller(i, j) = SKeller(j, i)
#   s_mismatch_bsym : symmetry blockS_{ci,cj}[k1,k2] = blockS_{cj,ci}[k2,k1]
# ================================================================
Print("\n--- Phase 4: full S matrix (",
      idx_lazy.rank, "^2 = ", idx_lazy.rank^2, " entries) ---\n");
Print("Sweeping unordered class pairs (ci <= cj) over ",
      Length(idx_lazy.classes), " classes...\n");

t4_start := Runtime();;
KRR_FULL_s_total_pairs := 0;;
KRR_FULL_s_total_entries := 0;;
KRR_FULL_s_mismatch_KS := 0;;
KRR_FULL_s_mismatch_sym := 0;;
KRR_FULL_s_mismatch_bsym := 0;;
KRR_FULL_s_first_ks := [];;
KRR_FULL_s_first_sym := [];;
KRR_FULL_s_first_bsym := [];;

KRR_FULL_n_classes := Length(idx_lazy.classes);;
KRR_FULL_progress_every := 5;;     # heartbeat every 5 ci values

for KRR_FULL_ci in [1..KRR_FULL_n_classes] do
    if KRR_FULL_ci mod KRR_FULL_progress_every = 0
       or KRR_FULL_ci = 1
       or KRR_FULL_ci = KRR_FULL_n_classes then
        Print("  ci=", KRR_FULL_ci, "/", KRR_FULL_n_classes,
              "  pairs=", KRR_FULL_s_total_pairs,
              "  entries=", KRR_FULL_s_total_entries,
              "  mismKS=", KRR_FULL_s_mismatch_KS,
              "  elapsed=",
              (Runtime() - t4_start) / 1000., " s\n");
    fi;
    KRR_FULL_Ni := idx_lazy.num_irreps[KRR_FULL_ci];;
    KRR_FULL_off_ci := idx_lazy.global_offset[KRR_FULL_ci];;
    for KRR_FULL_cj in [KRR_FULL_ci..KRR_FULL_n_classes] do
        KRR_FULL_Nj := idx_lazy.num_irreps[KRR_FULL_cj];;
        KRR_FULL_off_cj := idx_lazy.global_offset[KRR_FULL_cj];;
        # The two blocks: diagonal block when ci = cj uses only one
        # block, off-diagonal uses two (the (ci, cj) one for the
        # KSeller-vs-block check; the (cj, ci) one for the symmetry
        # cross-check).
        KRR_FULL_block_ij := ComputeSBlock(idx_lazy, transport_lazy,
                                           KRR_FULL_ci, KRR_FULL_cj);;
        KRR_FULL_block_ji := fail;;
        if KRR_FULL_ci <> KRR_FULL_cj then
            KRR_FULL_block_ji := ComputeSBlock(idx_lazy, transport_lazy,
                                               KRR_FULL_cj, KRR_FULL_ci);;
        fi;
        for KRR_FULL_k1 in [1..KRR_FULL_Ni] do
            for KRR_FULL_k2 in [1..KRR_FULL_Nj] do
                KRR_FULL_gi := KRR_FULL_off_ci + KRR_FULL_k1;
                KRR_FULL_gj := KRR_FULL_off_cj + KRR_FULL_k2;
                KRR_FULL_vK := SKeller(3, KRR_FULL_gi, KRR_FULL_gj);;
                KRR_FULL_vS := KRR_FULL_block_ij[KRR_FULL_k1][KRR_FULL_k2];;
                KRR_FULL_s_total_pairs := KRR_FULL_s_total_pairs + 1;
                KRR_FULL_s_total_entries := KRR_FULL_s_total_entries + 1;
                if KRR_FULL_vK <> KRR_FULL_vS then
                    KRR_FULL_s_mismatch_KS := KRR_FULL_s_mismatch_KS + 1;
                    if Length(KRR_FULL_s_first_ks) < 3 then
                        Add(KRR_FULL_s_first_ks,
                            rec(ci := KRR_FULL_ci, k1 := KRR_FULL_k1,
                                cj := KRR_FULL_cj, k2 := KRR_FULL_k2,
                                gi := KRR_FULL_gi, gj := KRR_FULL_gj,
                                SKeller := KRR_FULL_vK,
                                S_block := KRR_FULL_vS));
                    fi;
                fi;
                if KRR_FULL_ci <> KRR_FULL_cj then
                    # Mirror entry (gj, gi). S is symmetric, so
                    # SKeller(gj, gi) must equal SKeller(gi, gj).
                    KRR_FULL_vKmirror := SKeller(3, KRR_FULL_gj,
                                                 KRR_FULL_gi);;
                    KRR_FULL_vSmirror :=
                        KRR_FULL_block_ji[KRR_FULL_k2][KRR_FULL_k1];;
                    KRR_FULL_s_total_entries :=
                        KRR_FULL_s_total_entries + 1;
                    # SKeller symmetry check.
                    if KRR_FULL_vKmirror <> KRR_FULL_vK then
                        KRR_FULL_s_mismatch_sym :=
                            KRR_FULL_s_mismatch_sym + 1;
                        if Length(KRR_FULL_s_first_sym) < 3 then
                            Add(KRR_FULL_s_first_sym,
                                rec(gi := KRR_FULL_gi,
                                    gj := KRR_FULL_gj,
                                    SKeller_ij := KRR_FULL_vK,
                                    SKeller_ji := KRR_FULL_vKmirror));
                        fi;
                    fi;
                    # block symmetry check
                    if KRR_FULL_vSmirror <> KRR_FULL_vS then
                        KRR_FULL_s_mismatch_bsym :=
                            KRR_FULL_s_mismatch_bsym + 1;
                        if Length(KRR_FULL_s_first_bsym) < 3 then
                            Add(KRR_FULL_s_first_bsym,
                                rec(ci := KRR_FULL_ci,
                                    cj := KRR_FULL_cj,
                                    k1 := KRR_FULL_k1,
                                    k2 := KRR_FULL_k2,
                                    block_ij := KRR_FULL_vS,
                                    block_ji := KRR_FULL_vSmirror));
                        fi;
                    fi;
                    # Mirror SKeller-vs-block check.
                    if KRR_FULL_vKmirror <> KRR_FULL_vSmirror then
                        KRR_FULL_s_mismatch_KS :=
                            KRR_FULL_s_mismatch_KS + 1;
                        if Length(KRR_FULL_s_first_ks) < 3 then
                            Add(KRR_FULL_s_first_ks,
                                rec(ci := KRR_FULL_cj,
                                    k1 := KRR_FULL_k2,
                                    cj := KRR_FULL_ci,
                                    k2 := KRR_FULL_k1,
                                    gi := KRR_FULL_gj,
                                    gj := KRR_FULL_gi,
                                    SKeller := KRR_FULL_vKmirror,
                                    S_block := KRR_FULL_vSmirror));
                        fi;
                    fi;
                fi;
            od;
        od;
    od;
od;
t4_end := Runtime();;
t4_ms := t4_end - t4_start;;

Print("\n  Sweep done.\n");
Print("  Class pairs visited (unordered, ci<=cj): ",
      Length(idx_lazy.classes) * (Length(idx_lazy.classes) + 1) / 2,
      "\n");
Print("  S-entries compared:           ", KRR_FULL_s_total_entries, "\n");
Print("  Mismatches (SKeller vs blockS):  ",
      KRR_FULL_s_mismatch_KS, "\n");
Print("  SKeller(i,j) ≠ SKeller(j,i):     ",
      KRR_FULL_s_mismatch_sym, "\n");
Print("  blockS_{ci,cj}[k,l] ≠ blockS_{cj,ci}[l,k]: ",
      KRR_FULL_s_mismatch_bsym, "\n");
Print("  Total wall: ", t4_ms, " ms (", t4_ms / 1000., " s)\n");

# Acceptance: full agreement on the headline metric.
KRR_FULL_expected_entries := idx_lazy.rank ^ 2;;
if KRR_FULL_s_total_entries <> KRR_FULL_expected_entries then
    KRR_FULL_RegisterFail(
        Concatenation("S-entry count = rank^2 (expected ",
            String(KRR_FULL_expected_entries), ")"),
        Concatenation("got ", String(KRR_FULL_s_total_entries)));
else
    KRR_FULL_RegisterPass(Concatenation(
        "S-entry count = rank^2 = ",
        String(KRR_FULL_expected_entries)));
fi;

if KRR_FULL_s_mismatch_KS = 0 then
    KRR_FULL_RegisterPass(Concatenation(
        "S agreement: SKeller = blockS on all ",
        String(KRR_FULL_s_total_entries), " entries"));
else
    KRR_FULL_RegisterFail(
        "S agreement: SKeller = blockS",
        Concatenation(String(KRR_FULL_s_mismatch_KS),
                      " mismatches"));
    Print("  First SKeller-vs-blockS mismatches:\n");
    for KRR_FULL_ex in KRR_FULL_s_first_ks do
        Print("    (ci=", KRR_FULL_ex.ci, ", k1=", KRR_FULL_ex.k1,
              ") (cj=", KRR_FULL_ex.cj, ", k2=", KRR_FULL_ex.k2, ")",
              " (gi=", KRR_FULL_ex.gi, ", gj=", KRR_FULL_ex.gj, ")\n");
        Print("       SKeller = ", KRR_FULL_ex.SKeller, "\n");
        Print("       blockS  = ", KRR_FULL_ex.S_block, "\n");
    od;
fi;

if KRR_FULL_s_mismatch_sym = 0 then
    KRR_FULL_RegisterPass("S symmetric via SKeller: SKeller(i,j) = SKeller(j,i)");
else
    KRR_FULL_RegisterFail(
        "S symmetric via SKeller",
        Concatenation(String(KRR_FULL_s_mismatch_sym),
                      " asymmetric pairs"));
    Print("  First SKeller asymmetry pairs:\n");
    for KRR_FULL_ex in KRR_FULL_s_first_sym do
        Print("    (gi=", KRR_FULL_ex.gi, ", gj=", KRR_FULL_ex.gj, ")\n");
        Print("       SKeller(i,j) = ", KRR_FULL_ex.SKeller_ij, "\n");
        Print("       SKeller(j,i) = ", KRR_FULL_ex.SKeller_ji, "\n");
    od;
fi;

if KRR_FULL_s_mismatch_bsym = 0 then
    KRR_FULL_RegisterPass(
        "S symmetric via blockS: blockS_{ci,cj}[k,l] = blockS_{cj,ci}[l,k]");
else
    KRR_FULL_RegisterFail(
        "S symmetric via blockS",
        Concatenation(String(KRR_FULL_s_mismatch_bsym),
                      " asymmetric block-entries"));
fi;


# ================================================================
# Phase 5: cross-check on T using a sample of S diagonal entries.
#
# Modular T should satisfy T_{(g, chi)} = chi(g) / chi(1). For a quick
# spot-check we verify that for every class i and every irrep k,
#   T_keller[off_i + k] = irreps[i][k][class_index_of(g_i, in C_G(g_i))]
#                         / irrep_dims[i][k]
# computed via the eager idx (which we already did above), but here we
# pick a handful of random classes and use the cocycle-class signature
# to sanity-check.
#
# This is light (no per-entry SKeller call needed for T) and just adds
# defense-in-depth over a small sample.
# ================================================================
Print("\n--- Phase 5: T cross-check on random sample ---\n");

t5_start := Runtime();;
KRR_FULL_sample_indices := [1,
                            QuoInt(idx_lazy.rank, 4),
                            QuoInt(idx_lazy.rank, 2),
                            QuoInt(3 * idx_lazy.rank, 4),
                            idx_lazy.rank];;
KRR_FULL_t_sample_ok := true;;
for KRR_FULL_gi in KRR_FULL_sample_indices do
    KRR_FULL_pair := idx_eager.global_to_local[KRR_FULL_gi];;
    KRR_FULL_ci := KRR_FULL_pair[1];
    KRR_FULL_k1 := KRR_FULL_pair[2];
    KRR_FULL_rep := idx_eager.reps[KRR_FULL_ci];;
    KRR_FULL_chi := idx_eager.irreps[KRR_FULL_ci][KRR_FULL_k1];;
    KRR_FULL_dim := idx_eager.irrep_dims[KRR_FULL_ci][KRR_FULL_k1];;
    KRR_FULL_class_in_cent := ClassIndexInCentraliser(idx_eager,
                                                       KRR_FULL_ci,
                                                       KRR_FULL_rep);;
    KRR_FULL_expected := KRR_FULL_chi[KRR_FULL_class_in_cent] /
                         KRR_FULL_dim;;
    if T_keller[KRR_FULL_gi] <> KRR_FULL_expected then
        KRR_FULL_t_sample_ok := false;
        Print("    sample mismatch at gi=", KRR_FULL_gi,
              " (ci=", KRR_FULL_ci, ", k1=", KRR_FULL_k1, ")\n");
        Print("      T_keller = ", T_keller[KRR_FULL_gi], "\n");
        Print("      formula  = ", KRR_FULL_expected, "\n");
    fi;
od;
t5_end := Runtime();;
t5_ms := t5_end - t5_start;;

if KRR_FULL_t_sample_ok then
    KRR_FULL_RegisterPass(Concatenation(
        "T sample matches chi(g)/dim chi on ",
        String(Length(KRR_FULL_sample_indices)), " indices"));
else
    KRR_FULL_RegisterFail("T sample matches chi(g)/dim chi", fail);
fi;
Print("  T sample check wall: ", t5_ms, " ms\n");


# ================================================================
# Summary
# ================================================================
t_total_end := Runtime();;
t_total_ms := t_total_end - t_total_start;;

Print("\n=================================================================\n");
Print("  K-3 extension summary\n");
Print("=================================================================\n");
Print("  Phase 1 (cache build):    ", t1_ms, " ms (",
      t1_ms / 1000., " s)\n");
Print("  Phase 2 (eager idx):      ", t2_ms, " ms (",
      t2_ms / 1000., " s)\n");
Print("  Phase 3 (T-diagonal):     ", t3_total_ms, " ms (",
      t3_total_ms / 1000., " s)\n");
Print("  Phase 4 (full S sweep):   ", t4_ms, " ms (",
      t4_ms / 1000., " s)\n");
Print("  Phase 5 (T sample):       ", t5_ms, " ms (",
      t5_ms / 1000., " s)\n");
Print("  ----------------------------------------\n");
Print("  Total wall time:          ", t_total_ms, " ms (",
      t_total_ms / 1000., " s)\n");
Print("\n");
Print("  Entries verified:\n");
Print("    S entries:   ", KRR_FULL_s_total_entries,
      "  (rank^2 = ", idx_lazy.rank^2, ")\n");
Print("    T entries:   ", Length(T_keller),
      "  (rank = ", idx_lazy.rank, ")\n");
Print("\n");
Print("  Mismatches:\n");
Print("    SKeller vs blockS  : ", KRR_FULL_s_mismatch_KS, "\n");
Print("    SKeller symmetry   : ", KRR_FULL_s_mismatch_sym, "\n");
Print("    blockS symmetry    : ", KRR_FULL_s_mismatch_bsym, "\n");
Print("    T^Keller vs T^0    : ", KRR_FULL_t_mismatch, "\n");
Print("\n");
Print("  Failures registered: ", Length(KRR_FULL_FAILURES), "\n");

KRR_FULL_PASS := Length(KRR_FULL_FAILURES) = 0
                 and KRR_FULL_s_mismatch_KS = 0
                 and KRR_FULL_s_mismatch_sym = 0
                 and KRR_FULL_s_mismatch_bsym = 0
                 and KRR_FULL_t_mismatch = 0;;

if KRR_FULL_PASS then
    Print("\n=================================================================\n");
    Print("  K-3 EXTENSION (#211) PASS\n");
    Print("  SKeller(3, i, j) = S^0(i, j) on all ",
          KRR_FULL_s_total_entries, " entries.\n");
    Print("  T^Keller_diag = T^0_diag on all ",
          Length(T_keller), " entries.\n");
    Print("=================================================================\n");
else
    Print("\n=================================================================\n");
    Print("  K-3 EXTENSION (#211) FAIL\n");
    Print("  Failures:\n");
    for KRR_FULL_l in KRR_FULL_FAILURES do
        Print("    - ", KRR_FULL_l, "\n");
    od;
    Print("=================================================================\n");
fi;

QUIT;
