# test_k4a_anchor_m3.g
#
# K-4a-T7 anchor test (issue #201): m = 3 cross-pipeline consistency
# check between K-4a (modular-data classifier) and D-VAN (algebraic
# restriction-injectivity test), plus a trivial-by-construction sanity
# check that catches code-level bugs even if the K-4a-vs-D-VAN result
# is non-trivial.
#
# # FRAMING (per the corrected issue body)
#
# This is a CONSISTENCY check, not a "ground-truth-anchor" test. m = 3
# is NOT externally known to be untwisted -- the only previous claim
# that grounded that framing was a misattributed citation to
# arXiv:2410.18638, removed via PR #297; KRR (arXiv:2411.13646) verify
# only the cochain-level c_g triviality at m = 3, Conjecture 5.2 is
# m = 7-only, and [GK19, GK21] do not establish alpha = 0 at m = 3.
#
# Two independent pipelines compute "is alpha trivial at m = 3?" via
# different mathematical routes:
#
#   * K-4a (modular-data): K4aClassify(3) restricts KRR's lattice-derived
#     intertwiner data to the detecting subgroups {E, D_8, Q_8} of
#     E_+(3) and runs each restricted modular datum through a Drinfeld-
#     double classifier. Verdict: trivial iff E_class.is_coboundary AND
#     D_8 class_idx = 1 AND Q_8 class_idx = 1.
#
#   * D-VAN (algebraic): ResIsTrivialOnDetectingFamily(3, omega_vec)
#     restricts an EXPLICIT hom-basis coordinate vector omega_vec of
#     length k_G = 35 to the same detecting family (via
#     EquivariantChainMap + GroupCohomologyFunctor), and asks: are all
#     restrictions zero in their respective H^3(H_i; U(1)) coordinates?
#     Trivial iff every per-EA, per-D_8, per-Q_8 restriction vector is
#     zero mod its torsion.
#
# # WHY THE TWO MATCH AT m = 3
#
# K-4a at m = 3 uses `BuildIntertwinerDataUntwisted(branch.parent)` for
# each branch's restriction (per the K-4a-T6 spec in k4a_classify.g:
# `spectral_data.source = "untwisted_baseline"`). That intertwiner-data
# record has epsilon == 1 identically, which corresponds to the trivial
# 3-cocycle alpha = 0 -- equivalently, the all-zero hom-basis vector
# omega_vec_m3 = ListWithIdenticalEntries(35, 0).
#
# So the K-4a m = 3 verdict is the K-4a classifier's response to ω = 0;
# the matching D-VAN call passes omega_vec_m3 = [0, ..., 0] (length 35).
# Both must report `trivial = true`. Disagreement signals a bug in at
# least one pipeline.
#
# # CHECKS
#
# T1. K-4a verdict at m = 3:
#     K4aClassify(3).verdict == "trivial" (verdict for untwisted baseline).
#     K4aClassify(3).trivial == true.
# T2. D-VAN verdict on the all-zero omega_vec at m = 3:
#     ResIsTrivialOnDetectingFamily(3, [0, ..., 0]).trivial == true.
# T3. Consistency assertion: T1.trivial == T2.trivial. If they disagree,
#     this is a discovery (a bug in at least one pipeline) not a test
#     failure of itself -- diagnostic data is printed verbatim either way.
# T4. Trivial-by-construction sanity (the issue body's explicit sanity
#     check, distinct from T1 because it ALSO holds D-VAN to the same
#     standard): D-VAN on all-zero omega returns trivial=true. This
#     catches code-level bugs in D-VAN even when K-4a-vs-D-VAN would
#     otherwise agree.
# T5. Wall budget: total run < 5 minutes.
#
# # WHAT THIS TEST DOES NOT ESTABLISH
#
# - Does NOT establish alpha = 0 at m = 3. Neither pipeline computes
#   that directly. Both compute modular-data / restriction equivalence.
# - Does NOT rely on external ground truth from KRR or [GK19, GK21].
# - Is NOT a proof of triviality. It is a CROSS-PIPELINE CONSISTENCY
#   CHECK only.
#
# # RUN
#
# gap -q -b /Users/.../tests/test_k4a_anchor_m3.g
#
# (The test binds the symlink `k4a/anchor/Modular_Data -> modular_data`
# under the tests/ directory and chdirs into it before running, in the
# same pattern as test_k4a_classify.g.)

# ---- Test bookkeeping -------------------------------------------------

ANCHOR_PASSES   := 0;;
ANCHOR_FAILURES := [];;

AnchorAssertEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
        ANCHOR_PASSES := ANCHOR_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Print("         expected: ", expected, "\n");
        Print("         got:      ", got, "\n");
        Add(ANCHOR_FAILURES, label);
    fi;
end;;

AnchorAssertTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
        ANCHOR_PASSES := ANCHOR_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Add(ANCHOR_FAILURES, label);
    fi;
end;;

# ---- Locate worktree, scripts, sibling files --------------------------

ANCHOR_SELF := INPUT_FILENAME();;
if ANCHOR_SELF = fail or ANCHOR_SELF = "stream" then
    Error("test_k4a_anchor_m3.g: INPUT_FILENAME() unavailable; ",
          "Read the file by its absolute path.");
fi;
ANCHOR_SELFDIR := ANCHOR_SELF{
    [1..Length(ANCHOR_SELF) - Length("/test_k4a_anchor_m3.g")]};;
ANCHOR_SCRIPTSDIR := ANCHOR_SELFDIR{
    [1..Length(ANCHOR_SELFDIR) - Length("/tests")]};;
ANCHOR_WT_ROOT := ANCHOR_SCRIPTSDIR{
    [1..Length(ANCHOR_SCRIPTSDIR) - Length("/extraspecial_orbifolds/scripts")]};;

# Load order (matches test_k4a_classify.g):
#   1. src/modular_data.g (for LoadModularData, required by D_8 / Q_8
#      classifiers at their load time).
#   2. k4a_classify.g (orchestrator under test; transitively loads
#      every required sibling, including the classifiers once
#      LoadModularData is bound).
#   3. detecting_family_vanish.g and its transitive deps. These deps
#      use both CWD-relative `Read("foo.g")` (guarded by IsBoundGlobal)
#      AND a hardcoded relative `Read("../../src/modular_data.g")` in
#      transgression_kernel.g (NOT guarded). To survive subsequent
#      chdir into the symlink-based Modular_Data directory, we chdir
#      INTO the scripts/ dir for the duration of the D-VAN load and
#      then chdir back into the symlink dir for K-4a's LoadModularData
#      to resolve. This is the same trick test_b2_4_m3_anchor.g uses
#      implicitly (it runs from scripts/ throughout).

Read(Concatenation(ANCHOR_WT_ROOT, "/src/modular_data.g"));
AnchorAssertTrue("LoadModularData bound (from src/modular_data.g)",
                 IsBound(LoadModularData));

Read(Concatenation(ANCHOR_SCRIPTSDIR, "/k4a_classify.g"));
AnchorAssertTrue("K4aClassify bound (from k4a_classify.g)",
                 IsBound(K4aClassify));

# chdir to scripts/ to load detecting_family_vanish.g and its CWD-
# relative deps. transgression_kernel.g's unconditional Read of
# "../../src/modular_data.g" is the load-time hazard we work around
# by being in scripts/ for the duration of the load. After all deps
# are bound, downstream calls do not Read further files at runtime.
ANCHOR_OLD_CWD := DirectoryCurrent();;
ChangeDirectoryCurrent(ANCHOR_SCRIPTSDIR);
Read(Concatenation(ANCHOR_SCRIPTSDIR, "/detecting_family_vanish.g"));
AnchorAssertTrue("ResIsTrivialOnDetectingFamily bound",
                 IsBound(ResIsTrivialOnDetectingFamily));

# ---- Prepare Modular_Data symlink and chdir there ----------------------
#
# K-4a's D_8 / Q_8 classifiers call LoadModularData which reads
# `Modular_Data/<n>/<m>/<k>.txt` relative to GAP's CWD. We create a
# symlink tests/k4a/anchor/Modular_Data -> ../../modular_data so the
# classifiers resolve their data files. Same pattern as
# test_k4a_classify.g.

ANCHOR_MD_ROOT := fail;;
for ANCHOR_CAND in
    [ Concatenation(ANCHOR_WT_ROOT, "/../modular_data"),
      "/Users/thomasgemunden/Projects/group_cohomology/modular_data" ] do
    if ANCHOR_MD_ROOT = fail
       and IsExistingFile(Concatenation(ANCHOR_CAND, "/8/4/1.txt")) then
        ANCHOR_MD_ROOT := ANCHOR_CAND;
    fi;
od;
if ANCHOR_MD_ROOT = fail then
    Error("test_k4a_anchor_m3.g: cannot locate modular_data tree ",
          "containing 8/4/1.txt.");
fi;
Print("modular_data root: ", ANCHOR_MD_ROOT, "\n");

ANCHOR_LINKDIR := Concatenation(ANCHOR_SELFDIR, "/k4a/anchor");;
if not IsExistingFile(ANCHOR_LINKDIR) then
    Exec(Concatenation("mkdir -p '", ANCHOR_LINKDIR, "'"));
fi;
ANCHOR_LINKPATH := Concatenation(ANCHOR_LINKDIR, "/Modular_Data");;
if not IsExistingFile(ANCHOR_LINKPATH) then
    Exec(Concatenation("ln -s '", ANCHOR_MD_ROOT, "' '",
                       ANCHOR_LINKPATH, "'"));
fi;
if not IsExistingFile(Concatenation(ANCHOR_LINKPATH, "/8/4/1.txt")) then
    Error("test_k4a_anchor_m3.g: Modular_Data symlink at ",
          ANCHOR_LINKPATH, " does not resolve to a tree containing ",
          "8/4/1.txt.");
fi;
ChangeDirectoryCurrent(ANCHOR_LINKDIR);

# ---- T1: K-4a verdict at m = 3 ----------------------------------------
#
# K-4a's m = 3 path uses `BuildIntertwinerDataUntwisted(branch.parent)`
# per the K-4a-T6 spec, so the intertwiner-data has epsilon == 1 and
# the trace functional is the genuine centraliser character. That
# corresponds to alpha = 0 -- the all-zero hom-basis vector below.

Print("\n=================================================================\n");
Print("T1: K-4a verdict at m = 3 (K4aClassify(3) on untwisted baseline)\n");
Print("=================================================================\n");

ANCHOR_BUDGET_SEC := 300.0;;       # 5 min, per the issue spec.
ANCHOR_T0 := Runtime();;
ANCHOR_K4A_RES := K4aClassify(3);;
ANCHOR_K4A_WALL := (Runtime() - ANCHOR_T0) / 1000.0;;

Print("\n  T1 wall time: ", ANCHOR_K4A_WALL, " s\n");

AnchorAssertTrue("T1: K4aClassify(3) returned a record",
                 IsRecord(ANCHOR_K4A_RES));
AnchorAssertEqual("T1: K-4a verdict = 'trivial' at m=3",
                  ANCHOR_K4A_RES.verdict, "trivial");
AnchorAssertEqual("T1: K-4a trivial = true at m=3",
                  ANCHOR_K4A_RES.trivial, true);

# Per-branch sanity (each detecting subgroup independently classifies
# trivially). These give finer-grained diagnostics if any one branch
# misclassifies under the untwisted baseline.
AnchorAssertEqual("T1: E_class.is_coboundary = true",
                  ANCHOR_K4A_RES.E_class.is_coboundary, true);
AnchorAssertEqual("T1: D8_class.class_idx = 1 (trivial cocycle)",
                  ANCHOR_K4A_RES.D8_class.class_idx, 1);
AnchorAssertEqual("T1: Q8_class.class_idx = 1 (trivial cocycle)",
                  ANCHOR_K4A_RES.Q8_class.class_idx, 1);

# ---- T2: D-VAN verdict on the matching all-zero omega -----------------
#
# At m = 3, k_G = Length(UCT_G.hombasis) = 35 (the (Z/2)^34 (+) Z/4
# Harada-Kono integer cohomology summand structure). Pass the all-zero
# vector to D-VAN. Since K-4a at m = 3 effectively classifies the
# untwisted baseline (alpha = 0), the matching D-VAN input is the
# all-zero coordinate vector.

Print("\n=================================================================\n");
Print("T2: D-VAN verdict at m = 3 on all-zero omega_vec\n");
Print("=================================================================\n");

ANCHOR_T0 := Runtime();;
# k_G at m = 3 is 35. We build the zero vector directly; D-VAN's
# NormaliseOmegaToHomBasis recognises hom-basis input of length k_G
# and accepts it unchanged.
ANCHOR_OMEGA_ZERO_M3 := ListWithIdenticalEntries(35, 0);;
ANCHOR_DVAN_RES := ResIsTrivialOnDetectingFamily(3, ANCHOR_OMEGA_ZERO_M3);;
ANCHOR_DVAN_WALL := (Runtime() - ANCHOR_T0) / 1000.0;;

Print("\n  T2 wall time: ", ANCHOR_DVAN_WALL, " s\n");

AnchorAssertTrue("T2: ResIsTrivialOnDetectingFamily(3, 0) returned a record",
                 IsRecord(ANCHOR_DVAN_RES));
AnchorAssertEqual("T2: D-VAN trivial = true on all-zero omega (m=3)",
                  ANCHOR_DVAN_RES.trivial, true);

# Per-restriction sanity: every restriction vector must be all-zero.
AnchorAssertTrue("T2: D-VAN res_E_vec is all-zero",
                 ForAll(ANCHOR_DVAN_RES.res_E_vec, x -> x = 0));
AnchorAssertTrue("T2: D-VAN res_D8_vec is all-zero",
                 ForAll(ANCHOR_DVAN_RES.res_D8_vec, x -> x = 0));
AnchorAssertTrue("T2: D-VAN res_Q8_vec is all-zero (Q_8 present at m=3)",
                 ANCHOR_DVAN_RES.res_Q8_vec <> fail
                 and ForAll(ANCHOR_DVAN_RES.res_Q8_vec, x -> x = 0));

# Per-EA in the full max-EA family (D-VAN-FIX #151) -- every EA must
# also restrict to zero. Belt + braces on the all-zero input.
AnchorAssertTrue("T2: D-VAN every res_EA_vec_list[i] is all-zero",
                 ForAll(ANCHOR_DVAN_RES.res_EA_vec_list,
                        v -> ForAll(v, x -> x = 0)));

# ---- T3: Consistency assertion (the core regression check) ------------

Print("\n=================================================================\n");
Print("T3: K-4a vs D-VAN consistency at m = 3 (the core check)\n");
Print("=================================================================\n");

Print("  K-4a   verdict.trivial = ", ANCHOR_K4A_RES.trivial, "\n");
Print("  D-VAN  verdict.trivial = ", ANCHOR_DVAN_RES.trivial, "\n");

if ANCHOR_K4A_RES.trivial <> ANCHOR_DVAN_RES.trivial then
    # Disagreement: this is a discovery, not a test bug. Print full
    # diagnostic data so the user can decide which pipeline to trust.
    # Per the issue body's "What to do if the test fails" section:
    Print("\n  *** K-4a / D-VAN DISAGREEMENT AT m = 3 ***\n");
    Print("  This is a discovery: a bug in at least one pipeline,\n");
    Print("  or a math premise failure in one of them.\n");
    Print("\n  Per the issue body's diagnostic checklist:\n");
    Print("  1. K-4a per-branch breakdown:\n");
    Print("     E_class.is_coboundary  = ",
          ANCHOR_K4A_RES.E_class.is_coboundary, "\n");
    Print("     D8_class.class_idx     = ",
          ANCHOR_K4A_RES.D8_class.class_idx,
          " (trivial = 1)\n");
    Print("     Q8_class.class_idx     = ",
          ANCHOR_K4A_RES.Q8_class.class_idx,
          " (trivial = 1)\n");
    Print("     spectral_data.source   = ",
          ANCHOR_K4A_RES.spectral_data.source, "\n");
    Print("  2. D-VAN per-restriction breakdown:\n");
    Print("     #EA restrictions      = ",
          Length(ANCHOR_DVAN_RES.res_EA_vec_list), "\n");
    Print("     all EA all-zero       = ",
          ForAll(ANCHOR_DVAN_RES.res_EA_vec_list,
                 v -> ForAll(v, x -> x = 0)), "\n");
    Print("     res_D8_vec            = ",
          ANCHOR_DVAN_RES.res_D8_vec, "\n");
    Print("     res_Q8_vec            = ",
          ANCHOR_DVAN_RES.res_Q8_vec, "\n");
    Print("     source                = ", ANCHOR_DVAN_RES.source, "\n");
fi;

AnchorAssertEqual("T3: K-4a.trivial == D-VAN.trivial (consistency at m=3)",
                  ANCHOR_K4A_RES.trivial, ANCHOR_DVAN_RES.trivial);

# ---- T4: Trivial-by-construction sanity check -------------------------
#
# The issue body explicitly calls this out as a separate check
# distinct from the K-4a-vs-D-VAN agreement: feeding all-zero omega
# into K-4a must give trivial=true (this catches code-level bugs in
# K-4a even when K-4a-vs-D-VAN agreement is non-trivial).
#
# K-4a at m=3 by construction uses BuildIntertwinerDataUntwisted
# (epsilon = 1, c_g = 0), which is the all-zero omega encoding for
# this pipeline. So T1's verdict ALREADY answers this question for
# K-4a -- but the issue body's phrasing is explicit, so we re-assert
# here for clarity.
#
# For D-VAN, T2 covers the all-zero input case explicitly.

Print("\n=================================================================\n");
Print("T4: trivial-by-construction sanity (zero omega -> trivial)\n");
Print("=================================================================\n");

AnchorAssertEqual("T4: K-4a's all-zero-omega baseline returns trivial=true",
                  ANCHOR_K4A_RES.trivial, true);
AnchorAssertEqual("T4: D-VAN's all-zero-omega input returns trivial=true",
                  ANCHOR_DVAN_RES.trivial, true);

# ---- T5: wall budget --------------------------------------------------

Print("\n=================================================================\n");
Print("T5: wall budget (< 5 min total)\n");
Print("=================================================================\n");

ANCHOR_TOTAL_WALL := ANCHOR_K4A_WALL + ANCHOR_DVAN_WALL;;
Print("  K-4a    wall: ", ANCHOR_K4A_WALL, " s\n");
Print("  D-VAN   wall: ", ANCHOR_DVAN_WALL, " s\n");
Print("  Total   wall: ", ANCHOR_TOTAL_WALL, " s (budget ",
      ANCHOR_BUDGET_SEC, " s)\n");

AnchorAssertTrue(Concatenation(
                     "T5: total wall < ", String(Int(ANCHOR_BUDGET_SEC)),
                     " s (got ", String(ANCHOR_TOTAL_WALL), ")"),
                 ANCHOR_TOTAL_WALL < ANCHOR_BUDGET_SEC);

# ---- Final report -----------------------------------------------------

Print("\n=================================================================\n");
Print("Summary: ", ANCHOR_PASSES, " passes, ",
      Length(ANCHOR_FAILURES), " failures.\n");
Print("=================================================================\n");

if Length(ANCHOR_FAILURES) = 0 then
    Print("\nPASS test_k4a_anchor_m3\n");
else
    Print("\nFAIL test_k4a_anchor_m3:\n");
    for ANCHOR_F in ANCHOR_FAILURES do
        Print("  - ", ANCHOR_F, "\n");
    od;
fi;

QUIT;
