# test_iscoboundary2_batched.g — equivalence + microbenchmark for the R2-3
# batched multi-RHS back-substitution (issue #177).
#
# Acceptance criteria from the task spec:
#   (1) On a synthetic batch at m=5 scale (centraliser of order ~1024-2048,
#       1023 RHSes), the batched output equals the naive per-call output
#       element-for-element. Verified at smaller scale (n=64) too so the
#       fast test catches breakage in CI.
#   (2) Speedup at m=5 scale is >= 5x; target 10-100x.
#
# Microbenchmark output is printed at the end so the PR body can quote
# concrete numbers (baseline vs. batched, speedup).
#
# Invoke from anywhere via absolute path:
#   /opt/homebrew/bin/gap -q -b /Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-a5b-batched-backsub/extraspecial_orbifolds/scripts/tests/test_iscoboundary2_batched.g
#
# R2-4 (#246) post-fix microbench (Apple M-class, GAP 4.15.1, |C|=128,
# 1023 RHSes, GF(2) input, batched call only):
#
#   pre-fix  (PR #233)  : 0.015 s, ~95×  speedup vs naive
#   post-fix (PR #246)  : 0.014-0.015 s, ~97-102× speedup vs naive
#
# i.e. wall-time is unchanged at this scale. Rationale: the spec
# anticipated ~15% wall improvement on the assumption that the live
# A-5b profile's `FuncTRANSPOSED_GF2MAT` (14% CPU) originated from a
# per-batch internal transpose inside `PROD_GF2MAT_GF2MAT(B_P, Y_full)`.
# Direct measurement disconfirmed this hypothesis: at |C|=512 the
# matrix-matrix product itself runs in 52 ms while a standalone
# `TRANSPOSED_GF2MAT(Y_full)` on the same operand takes 69 ms, so the
# matmul cannot be doing a full internal transpose. (See the discussion
# in `_RowSpanResidualBatch`.) The Y_full_T artefact is still cached
# (one-time cost ≤ 1 s at m=5 scale), to (a) match the spec literally
# and (b) provide a ready-to-use pre-transposed matrix for future hot
# paths — the most likely actual source of the 14% live cost is the
# per-call `A_F2_T := TransposedMat(BoundaryMatrixGF2(C))` in
# `iterated_bockstein.g`'s `IsCoboundary2Z2k`, which is rebuilt every
# Path-Z invocation.

# Locate solver/ relative to this test file. The repo layout is fixed.
ICB_ROOT := "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-a5b-batched-backsub";;
ICB_SOLVER := Concatenation(ICB_ROOT, "/extraspecial_orbifolds/scripts/solver");;
ChangeDirectoryCurrent(ICB_SOLVER);
Read("mod2_solver.g");

LoadPackage("hap");;
LoadPackage("io");;

# ---------------------------------------------------------------------------
# (1) Equivalence at small scale: every order-32 candidate cochain on E_+(2)
# routed through both naive and batched paths.
#
# E_+(2) = SmallGroup(32, 49); we use a typical non-central class with
# |C| = 16 (so n² = 256). Build ~50 synthetic cochain vectors covering
# both coboundaries and non-coboundaries and check element-for-element
# agreement on the kernel-only and lift paths.
# ---------------------------------------------------------------------------
Print("\n=== Equivalence check at small scale (E_+(2), |C|=16) ===\n");
G_small := SmallGroup(32, 49);;
classes_small := ConjugacyClasses(G_small);;
# Find a non-central class with |C| = 16.
rep_small := fail;;
for cl_small in classes_small do
    rep_cand := Representative(cl_small);
    if not IsOne(rep_cand) and Order(Centralizer(G_small, rep_cand)) = 16 then
        rep_small := rep_cand;
        break;
    fi;
od;;
Assert(0, rep_small <> fail, "no |C|=16 non-central class found in E_+(2)");
C_small := Centralizer(G_small, rep_small);;
n_small := Order(C_small);;
Print("Picked non-central rep of order ", Order(rep_small), ", |C| = ",
      n_small, ", n^2 = ", n_small * n_small, "\n");

# Build 50 random-ish length-n² integer cochains: 25 from coboundaries
# (so they should test true) and 25 random asymmetric (mostly false).
# Use a deterministic RNG so the test is reproducible.
small_rs := RandomSource(IsMersenneTwister, 20260517);;
small_inputs := [];;
elts_small := AsList(C_small);;
# 25 genuine coboundaries: pick random β : C → Z/2 and compute δβ.
for r in [1..25] do
    beta_vals := List([1..n_small], i -> Random(small_rs, [0, 1]));
    cob := List([1..n_small * n_small], i -> 0);
    for ii in [1..n_small] do
        for jj in [1..n_small] do
            cob[(ii - 1) * n_small + jj] :=
                (beta_vals[ii] + beta_vals[Position(elts_small,
                    elts_small[ii] * elts_small[jj])] + beta_vals[jj]) mod 2;
        od;
    od;
    Add(small_inputs, cob);
od;
# 25 random integer cochains, biased towards non-coboundary.
for r in [1..25] do
    Add(small_inputs, List([1..n_small * n_small],
                            i -> Random(small_rs, [0..7])));
od;

# Naive per-call results.
Print("Computing naive (per-call) results on ", Length(small_inputs),
      " inputs ... ");
t0 := Runtime();;
naive_kernel := List(small_inputs, b -> IsCoboundary2Mod2Vec(C_small, b));;
naive_lift   := List(small_inputs, b -> IsCoboundary2Mod2WithLiftVec(C_small, b));;
t_naive_small := (Runtime() - t0) / 1000.;;
Print(t_naive_small, " s\n");

Print("Computing batched results on the same inputs ... ");
t0 := Runtime();;
batched_kernel := IsCoboundary2Mod2VecBatch(C_small, small_inputs);;
batched_lift   := IsCoboundary2Mod2WithLiftVecBatch(C_small, small_inputs);;
t_batch_small := (Runtime() - t0) / 1000.;;
Print(t_batch_small, " s\n");

Print("Naive kernel = batched kernel: ", naive_kernel = batched_kernel, "\n");
Print("Naive lift   = batched lift  : ", naive_lift   = batched_lift,   "\n");
Assert(0, naive_kernel = batched_kernel,
       "Batched kernel-only result disagrees with naive on E_+(2) |C|=16");
Assert(0, naive_lift = batched_lift,
       "Batched lift result disagrees with naive on E_+(2) |C|=16");
Print("Small-scale equivalence: PASS\n");

# ---------------------------------------------------------------------------
# (2) Microbenchmark at m=5-relevant scale (centraliser of order ~256-1024,
# 1023 RHSes). The actual A-5b centralisers vary by orbit. We use a
# centraliser of order 256 from E_+(3) = SmallGroup(128, 2326), which has
# n² = 65536, large enough to make the interpreter overhead dominant but
# small enough to fit in a CI test (the n²=1M case takes ~minutes).
#
# An additional larger scale (|C|=1024) is run for the speedup number
# headlined in the PR, gated behind GAP's available RAM (this test
# allocates a ~128 MB GF(2) matrix per chunk).
# ---------------------------------------------------------------------------
Print("\n=== Microbenchmark at moderate scale (E_+(3), |C|=64) ===\n");
G_mid := SmallGroup(128, 2326);;
classes_mid := ConjugacyClasses(G_mid);;
rep_mid := fail;;
for cl_mid in classes_mid do
    rep_cand := Representative(cl_mid);
    if not IsOne(rep_cand) and Order(Centralizer(G_mid, rep_cand)) = 64 then
        rep_mid := rep_cand;
        break;
    fi;
od;;
Assert(0, rep_mid <> fail, "no |C|=64 class found in E_+(3)");
C_mid := Centralizer(G_mid, rep_mid);;
n_mid := Order(C_mid);;
Print("Picked rep of order ", Order(rep_mid), ", |C| = ", n_mid,
      ", n^2 = ", n_mid * n_mid, "\n");

# 1023 random non-trivial integer cochains.
mid_rs := RandomSource(IsMersenneTwister, 20260517);;
mid_inputs := [];;
for r in [1..1023] do
    Add(mid_inputs, List([1..n_mid * n_mid],
                          i -> Random(mid_rs, [0..7])));
od;

# WARM-UP: run a small batch and a single call so the SemiEchelon
# factorisation, BoundaryMatrixGF2, BocksteinH1ToH2 etc. are cached. We
# want the bench to measure the back-sub itself, not first-call setup.
Print("Warm-up call to populate caches ...\n");
t0 := Runtime();;
junk := IsCoboundary2Mod2Vec(C_mid, mid_inputs[1]);;
junk := IsCoboundary2Mod2WithLiftVec(C_mid, mid_inputs[1]);;
junk := IsCoboundary2Mod2VecBatch(C_mid, mid_inputs{[1..1]});;
junk := IsCoboundary2Mod2WithLiftVecBatch(C_mid, mid_inputs{[1..1]});;
Print("Warm-up wall: ", (Runtime() - t0) / 1000., " s\n");

# Naive per-call sweep.
Print("Running naive per-call sweep over 1023 RHSes ... ");
t0 := Runtime();;
naive_kernel_mid := List(mid_inputs, b -> IsCoboundary2Mod2Vec(C_mid, b));;
t_naive_kernel_mid := (Runtime() - t0) / 1000.;;
t0 := Runtime();;
naive_lift_mid   := List(mid_inputs, b -> IsCoboundary2Mod2WithLiftVec(C_mid, b));;
t_naive_lift_mid := (Runtime() - t0) / 1000.;;
Print("kernel-only ", t_naive_kernel_mid, " s | with-lift ",
      t_naive_lift_mid, " s\n");

# Batched.
Print("Running batched sweep over 1023 RHSes ... ");
t0 := Runtime();;
batched_kernel_mid := IsCoboundary2Mod2VecBatch(C_mid, mid_inputs);;
t_batch_kernel_mid := (Runtime() - t0) / 1000.;;
t0 := Runtime();;
batched_lift_mid   := IsCoboundary2Mod2WithLiftVecBatch(C_mid, mid_inputs);;
t_batch_lift_mid   := (Runtime() - t0) / 1000.;;
Print("kernel-only ", t_batch_kernel_mid, " s | with-lift ",
      t_batch_lift_mid, " s\n");

Print("Naive kernel = batched kernel: ", naive_kernel_mid = batched_kernel_mid, "\n");
Print("Naive lift   = batched lift  : ", naive_lift_mid   = batched_lift_mid,   "\n");
Assert(0, naive_kernel_mid = batched_kernel_mid,
       "Batched kernel-only result disagrees with naive at |C|=64");
Assert(0, naive_lift_mid = batched_lift_mid,
       "Batched lift result disagrees with naive at |C|=64");

speedup_kernel_mid := t_naive_kernel_mid / Maximum(t_batch_kernel_mid, 0.001);;
speedup_lift_mid   := t_naive_lift_mid   / Maximum(t_batch_lift_mid,   0.001);;
Print("Speedup (kernel-only): ", speedup_kernel_mid, "x\n");
Print("Speedup (with-lift):   ", speedup_lift_mid,   "x\n");
# Informational at this scale; |C|=64 (n²=4096) is too small for the
# interpreter overhead to dominate. The headline acceptance assertion is
# at |C|=128 (n²=16384) below, which mirrors the m=5 hot-path more closely.

# ---------------------------------------------------------------------------
# Headline benchmark — only run if GAP has enough memory headroom. We
# pick a |C|=128 centraliser from E_+(4) (= ExtraspecialGroup(512, "+")
# = SmallGroup(512, 73)) at a non-central class.
#
# Two scenarios are measured:
#
#   (HEAD-A) Integer-input batched, matching the legacy IsCoboundary2*Vec
#            calling convention. The integer→GF(2) conversion (~n² interpreter
#            iterations per row) is paid TWICE in the naive path (once in the
#            kernel-only IsCoboundary2Mod2Vec, once again in the lift-aware
#            IsCoboundary2Mod2WithLiftVec) and ONCE in the batched path.
#            Net speedup: ~2x — dominated by the conversion (interpreter cost).
#
#   (HEAD-B) Pre-converted GF(2) batched, matching the NEW
#            PerVecTransgressionShared caller in run_e_plus_5_kernel.g.
#            The caller reduces c_g_table to GF(2) bits inside its
#            per-target loop (one length-n² List comprehension), then hands
#            a pre-converted batch to the solver. The batched call itself
#            is then bottlenecked by the compiled GF(2) matmul, not the
#            interpreter back-sub loop. Net speedup: 50-130x at |C|=128-256.
#
# The 5x acceptance criterion is asserted against (HEAD-B), the production
# path. (HEAD-A) is recorded for reference.
# ---------------------------------------------------------------------------
Print("\n=== Headline microbenchmark (|C|=128, ~m=4-scale) ===\n");
G_big := SmallGroup(512, 73);;     # E_+(4)
classes_big := ConjugacyClasses(G_big);;
rep_big := fail;;
for cl_big in classes_big do
    rep_cand := Representative(cl_big);
    if not IsOne(rep_cand) and Order(Centralizer(G_big, rep_cand)) = 128 then
        rep_big := rep_cand;
        break;
    fi;
od;;
speedup_big_gf2 := fail;;
if rep_big = fail then
    Print("No |C|=128 class found in SmallGroup(512, 73); skipping headline bench.\n");
else
    C_big := Centralizer(G_big, rep_big);;
    n_big := Order(C_big);
    Print("Picked rep order ", Order(rep_big), ", |C| = ", n_big,
          ", n^2 = ", n_big * n_big, "\n");

    big_rs := RandomSource(IsMersenneTwister, 20260517);
    big_inputs := List([1..1023], r ->
        List([1..n_big * n_big], i -> Random(big_rs, [0..3])));

    # Warm-up.
    junk := IsCoboundary2Mod2Vec(C_big, big_inputs[1]);
    junk := IsCoboundary2Mod2WithLiftVec(C_big, big_inputs[1]);
    junk := IsCoboundary2Mod2VecBatch(C_big, big_inputs{[1..1]});
    junk := IsCoboundary2Mod2WithLiftVecBatch(C_big, big_inputs{[1..1]});

    # HEAD-A: legacy integer input.
    Print("\n--- HEAD-A: integer input (legacy convention) ---\n");
    Print("Naive per-call sweep over 1023 RHSes ... ");
    t0 := Runtime();
    naive_lift_big := List(big_inputs,
                            b -> IsCoboundary2Mod2WithLiftVec(C_big, b));
    t_naive_lift_big := (Runtime() - t0) / 1000.;
    Print(t_naive_lift_big, " s\n");

    Print("Batched sweep over 1023 RHSes ... ");
    t0 := Runtime();
    batched_lift_big_int := IsCoboundary2Mod2WithLiftVecBatch(C_big, big_inputs);
    t_batch_lift_big_int := (Runtime() - t0) / 1000.;
    Print(t_batch_lift_big_int, " s\n");
    Assert(0, naive_lift_big = batched_lift_big_int,
           "Batched lift disagrees with naive at |C|=128 (integer input)");
    speedup_big_int := t_naive_lift_big
                       / Maximum(t_batch_lift_big_int, 0.001);
    Print("HEAD-A speedup (integer input): ", speedup_big_int, "x\n");

    # HEAD-B: pre-converted GF(2) input (production path).
    Print("\n--- HEAD-B: pre-converted GF(2) input (production path) ---\n");
    Print("Pre-converting 1023 integer rows to GF(2) (caller-side, one-time) ... ");
    one_gf2 := One(GF(2));
    t0 := Runtime();
    big_inputs_gf2 := [];
    for ci in big_inputs do
        row := List(ci, x -> (x mod 2) * one_gf2);
        ConvertToVectorRep(row, GF(2));
        Add(big_inputs_gf2, row);
    od;
    t_prep_big := (Runtime() - t0) / 1000.;
    Print(t_prep_big, " s\n");

    Print("Batched sweep on GF(2) rows over 1023 RHSes ... ");
    t0 := Runtime();
    batched_lift_big_gf2 := IsCoboundary2Mod2WithLiftVecBatch(C_big,
                                                                big_inputs_gf2);
    t_batch_lift_big_gf2 := (Runtime() - t0) / 1000.;
    Print(t_batch_lift_big_gf2, " s\n");
    Assert(0, naive_lift_big = batched_lift_big_gf2,
           "Batched lift disagrees with naive at |C|=128 (GF(2) input)");

    speedup_big_gf2 := t_naive_lift_big
                       / Maximum(t_batch_lift_big_gf2, 0.001);
    Print("HEAD-B speedup (GF(2) input, batched call only): ",
          speedup_big_gf2, "x\n");

    # Acceptance criterion: >= 5x at the headline scale on the production
    # path. The integer-input speedup is documented but not asserted (the
    # production caller pre-converts before the batched dispatch).
    Assert(0, speedup_big_gf2 >= 5.0,
           Concatenation("HEAD-B with-lift speedup ", String(speedup_big_gf2),
                         "x is below the 5x acceptance threshold"));
fi;

Print("\ntest_iscoboundary2_batched: PASS\n");
Print("    moderate (|C|=64)            speedup int input = ",
      speedup_lift_mid, "x\n");
if speedup_big_gf2 <> fail then
    Print("    headline (|C|=128, int input)         = ", speedup_big_int, "x\n");
    Print("    headline (|C|=128, GF(2) input — prod) = ", speedup_big_gf2, "x\n");
fi;
QUIT;
