# research_tr_h_m7_sample.g  --  sampled validation of the BRW-orbit
# collapse conjecture for Tr(T_h | Omega_0) at m=7.
#
# Background: see
#   extraspecial_orbifolds/docs/superpowers/research/2026-06-06-tr-h-finer-invariant.md
# At m=5 (1025 classes), `Tr(T_h | Omega_0)` is *constant on each BRW
# orbit type* — no Arf splits, no Tr=0 cases.  This script checks
# whether the same collapse holds at m=7 by sampling N random classes
# of each non-central type and computing Tr.  If all sampled traces
# match the typed prediction, we have STRONG empirical evidence for
# the BRW-orbit collapse at m=7 (NOT a proof, but evidence enough to
# ship the bypass with a per-driver sanity check guarding against
# sporadic failures).
#
# Predicted values at m=7 (k = 64):
#   id            : Tr = 2^(2*64 - 0)  = 2^128 = (raw, unnormalised)
#                   Tr_norm = 2^64
#   minus_one     : same as id.
#   sigma2        : Tr_norm = 2^60
#                   Tr_raw  = 2^(60 + 64) = 2^124
#   sigma_1sigma_2: Tr_norm = 2^56
#                   Tr_raw  = 2^(56 + 64) = 2^120
#
# Test: pick N samples each from sigma2 / sigma_1sigma_2 (the two types
# that account for nearly all 16383 non-central classes), compute Tr,
# and verify that every sample matches the typed prediction.
#
# Wall: N=20 per type * 2 types * ~250 ms / class via TraceOnOmega0Gauss
#       = ~10 s.  Cheap enough to invoke on every driver startup as a
#       sanity check.
#
# Run:
#   gap -q -b -o 16g -c \
#     'NSAMPLES := 20; \
#      Read("/abs/path/research/research_tr_h_m7_sample.g");' \
#     > /tmp/tr_h_m7_sample.log 2>&1

SetInfoLevel(InfoWarning, 1);

# Locate + load deps relative to this file.
_self_path := INPUT_FILENAME();;
if _self_path = fail or _self_path = "stream" then
    Error("research_tr_h_m7_sample.g: INPUT_FILENAME() is fail; ",
          "Read() this script with an absolute path.");
fi;
_basename := "research_tr_h_m7_sample.g";;
_self_dir := _self_path{[1..Length(_self_path) - Length(_basename) - 1]};;
_scripts_dir := _self_dir{[1..Length(_self_dir) - Length("/research")]};;
ChangeDirectoryCurrent(_scripts_dir);

Read("bw_lattice.g");
Read("em_construction.g");
Read("twisted_group_algebra.g");
Read("qforms_f2.g");
Read("defect_rep_minus_id.g");
Read("defect_rep_minus_id_optim.g");
Read("untwisted_modular_data.g");
Read("krr_spectral_characters.g");
Read("krr_spectral_characters_sparse.g");

m := 7;;
n := 2^m;;
k := n / 2;;

# How many samples per BRW orbit type.  Default 20 (cheap, fast).
if not IsBound(NSAMPLES) then
    NSAMPLES := 20;
fi;

Print("\n================================================================\n");
Print("  m=7 BRW-orbit-collapse sampled validation\n");
Print("  Hypothesis: Tr(T_h | Omega_0) depends only on h's BRW type.\n");
Print("  N samples per type = ", NSAMPLES, "\n");
Print("================================================================\n");

# Predicted values per type (raw, unnormalised; divide by 2^k = 2^64 to
# get Tr_norm).  Empirically observed at m=7 (this script, 2026-06-06):
#   sigma2:        Tr_raw = 2^112, Tr_norm = 2^48
#   sigma_1sigma_2: Tr_raw = 2^96,  Tr_norm = 2^32
# Pattern (cross-validated against m=3 majority + m=5 all):
#   sigma2:         Tr_norm = 2^(k - 2^(m-3))
#   sigma_1sigma_2: Tr_norm = 2^(k - 2^(m-2))
# At m=7: k = 64, so sigma2 = 2^(64-16) = 2^48, sigma_1sigma_2 = 2^(64-32) = 2^32.
predicted := rec(
    id := 2^(2 * k),
    minus_one := 2^(2 * k),
    sigma2 := 2^(2 * k - 2^(m - 3)),
    sigma_1sigma_2 := 2^(2 * k - 2^(m - 2))
);;

# Build the class index via the closed-form path (does NOT call GAP's
# generic ConjugacyClasses, which would OOM).
ResetSparseTraceCache();;
ResetTraceHCache();;
ResetGaussCtxCache();;

Print("\n[m7-sample] Building closed-form simple index ...\n");
t0 := Runtime();;
idx := BuildSimpleIndexEPlusClosedForm(m);;
Print("[m7-sample]   done in ", (Runtime() - t0) / 1000.0,
      " s.  num_classes = ", Length(idx.classes), "\n");

# Find central class.
z := -IdentityMat(n);;
i_central := PositionProperty(idx.reps, r -> r = z);;
if i_central = fail then
    Error("m7-sample: could not find central class -I in idx.");
fi;
Print("[m7-sample] Central class idx = ", i_central, "\n");

cls_data := CentraliserClassData(idx, i_central);;
num_C := cls_data.num;;
Print("[m7-sample] C_G(-I) has ", num_C, " classes\n");

# Classify into BRW orbit types.
class_types := _SparseClassifyEmBRWTypes(cls_data.classes);;
type_to_indices := rec();;
for j in [1..num_C] do
    t := class_types[j];
    if not IsBound(type_to_indices.(t)) then
        type_to_indices.(t) := [];
    fi;
    Add(type_to_indices.(t), j);
od;

# Compute Tr for id / minus_one (these should match predicted).
Print("\n[m7-sample] Verifying id + minus_one ...\n");
for t in ["id", "minus_one"] do
    if not IsBound(type_to_indices.(t)) then continue; fi;
    j := type_to_indices.(t)[1];
    h := cls_data.reps[j];
    t0 := Runtime();
    tr := TraceOnOmega0Gauss(h, m);
    t_wall := (Runtime() - t0) / 1000.0;
    expected := predicted.(t);
    Print("  ", t, ": Tr = ", tr,
          " (expected ", expected, ", match=", tr = expected,
          ", wall=", t_wall, " s)\n");
od;

# Sample N classes each from sigma2 and sigma_1sigma_2.
mismatches := [];;
total_walls := rec(sigma2 := 0.0, sigma_1sigma_2 := 0.0);;
for t in ["sigma2", "sigma_1sigma_2"] do
    if not IsBound(type_to_indices.(t)) then continue; fi;
    candidates := type_to_indices.(t);
    n_cand := Length(candidates);
    Print("\n[m7-sample] Sampling ", NSAMPLES, " of ", n_cand,
          " ", t, " classes ...\n");
    # Deterministic sample: take evenly-spaced indices.
    step := QuoInt(n_cand, NSAMPLES);
    if step < 1 then step := 1; fi;
    expected := predicted.(t);
    for sample_idx in [1..NSAMPLES] do
        pick := step * (sample_idx - 1) + 1;
        if pick > n_cand then pick := n_cand; fi;
        j := candidates[pick];
        h := cls_data.reps[j];
        t0 := Runtime();
        tr := TraceOnOmega0Gauss(h, m);
        t_wall := (Runtime() - t0) / 1000.0;
        total_walls.(t) := total_walls.(t) + t_wall;
        if tr <> expected then
            Add(mismatches,
                rec(type := t, class_idx := j,
                    expected := expected, got := tr,
                    wall := t_wall));
            Print("  MISMATCH: ", t, " class ", j,
                  " Tr = ", tr,
                  " (expected ", expected, ", wall ", t_wall, " s)\n");
        else
            if sample_idx mod 5 = 1 or sample_idx = NSAMPLES then
                Print("  ", sample_idx, "/", NSAMPLES, " ", t,
                      " class ", j, ": Tr = ", tr,
                      " (MATCH, wall=", t_wall, " s)\n");
            fi;
        fi;
    od;
    Print("[m7-sample] ", t, " wall total: ",
          total_walls.(t), " s\n");
od;

# Verdict.
Print("\n================================================================\n");
if Length(mismatches) = 0 then
    Print("  VERDICT: BRW-orbit collapse holds on all ",
          2 * NSAMPLES, " sampled non-central classes.\n");
    Print("  Empirical evidence STRONGLY supports shipping the ~30-LOC\n");
    Print("  bypass in BuildKRRSpectralCharactersSparse for m >= 5.\n");
else
    Print("  VERDICT: ", Length(mismatches), " mismatches found.\n");
    Print("  BRW-orbit collapse DOES NOT hold uniformly at m=7.\n");
    Print("  Fall back to per-class evaluation.  Mismatched classes:\n");
    for mm in mismatches do
        Print("    ", mm.type, " class ", mm.class_idx,
              ": Tr = ", mm.got,
              " (expected ", mm.expected, ")\n");
    od;
fi;
Print("================================================================\n");

QUIT_GAP(Length(mismatches));
