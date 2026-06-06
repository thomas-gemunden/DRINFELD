# d_van_7_xcheck_k4a.g — WITHDRAWN: math conflation between ker(Tr) and
#                       the detecting-family restriction kernel.
#
# Audit verdict (2026-06-06, PR #449 prerequisite audit): this harness's
# core comparison — "D-VAN's per-generator trivial bit matches A-5b's
# in_kernel_gens" — is mathematically wrong. The two flags test
# different things:
#
#   * D-VAN's `r.trivial`: `true` iff `[ω] = 0` in `H^3(G; U(1))`. By
#     AM04 IV.4-IV.5 + Quillen 1971 the restriction
#     `H^3(G; U(1)) -> ⊕_{H in {EA, D_8, Q_8}} H^3(H; U(1))` is
#     injective at every m ≥ 2, so the detecting-family kernel is
#     `{0}` and `r.trivial = true ⟺ [ω] = 0`.
#
#   * A-5b's `in_kernel_gens`: indices `i` for which
#     `e_i ∈ ker(Tr : H^3(G; U(1)) -> ⊕_g H^2(C_g; U(1)))`. This kernel
#     is generally large (`|ker(Tr)(E_+(5))| = 2^52` per the A-5b
#     production); the membership has nothing to do with `e_i = 0` in
#     `H^3`.
#
# The two kernels are DIFFERENT kernels of DIFFERENT maps. At m=3 the
# A-3a sweep found `ker(Tr) = full H^3`, so `in_kernel_gens = [1..35]`
# while D-VAN reports `trivial = false` on every unit generator (each
# is a non-zero class in H^3). The PR #416 test
# `test_dvan_m5_anchor_vs_kernel.g` returned 55 FAIL / 0 PASS for
# exactly this reason and was withdrawn (`ed5cc4a`).
#
# Replacement for D-VAN/K-4b cross-validation at m=5: see
# `k4b_xcheck_d_van.g`, which limits itself to the trivial-trivial
# axis (`K-4b RESULT.trivial = true ⟺ ResIsTrivialOnDetectingFamily(5, 0).trivial`)
# and does NOT involve `kernel.g`.
#
# This file is preserved (without an early QUIT) as a historical
# artefact of the conflated approach. The trivial-axis path it
# implements at the bottom is mathematically harmless (both pipelines
# agree on ω = 0); only the per-generator "agree" verdict is wrong.
#
# See: extraspecial_orbifolds/docs/superpowers/research/2026-06-06-ker-tr-detecting-family-audit.md
#
# === ORIGINAL DOC (preserved for reference) ===
#
# D-VAN-7 (issue #148) and K-4b (#189 / PR #227, sibling scaffold) are
# two independent witnesses for Keller's question at m=5:
#
#   * D-VAN-7 derives its verdict from an algebraic restriction
#     pipeline (`ResIsTrivialOnDetectingFamily`); the original design
#     was to compare per-generator against A-5b's HAP-derived
#     `computed/transgression/5/kernel.g`. THIS COMPARISON IS WRONG;
#     see the withdrawal notice above.
#
#   * K-4b orchestrates K4aClassify(5) on the modular-data side
#     (KRR projector / CGR §5.2 detecting-family classifier).
#
# At m=3 both pipelines were independently checked. This harness
# attempted the m=5 analogue under the conflated protocol.
#
# Strategy (parallels K-4b's k4b_xcheck_d_van.g):
#
#   * Trivial-axis check (always available):
#       - K-4b verdict = trivial             iff RESULT.trivial = true
#       - D-VAN-7 verdict = "agree" was originally computed as "every
#         D-VAN trivial bit matches A-5b's in_kernel_gens". THIS IS THE
#         CONFLATED FRAMING. The two flags genuinely test different
#         maps' kernels and should not be expected to agree on
#         per-generator bits.
#       - The trivial-axis check (both pipelines on ω=0) IS sound, but
#         provides only a single bit of confirmation, not a per-generator
#         sweep.
#
#   * Per-generator non-triviality detection (richer, requires K-4b
#     to expose per-generator restriction data which it currently does
#     not — `K4aClassify` returns a single verdict for the input α, not
#     a sweep over unit generators):
#       This is the strategy-(A) analogue. D-VAN gives a per-generator
#       trivial bit; K-4b at present gives only a single verdict for
#       α_KRR. To enable a full per-generator cross-check, K-4b would
#       need to be rerun once per unit generator. That's 165 K4aClassify
#       calls at the m=5 cost (~minutes each); deferred to a follow-up.
#
# Usage (after BOTH `computed/d_van_7/m5_result.g` (D-VAN-7) and
# `extraspecial_orbifolds/scripts/k4b_m5_result.g` (K-4b) exist):
#
#   gap -q -b -c 'Read("d_van_7_xcheck_k4a.g");'
#
# The harness prints a single-line summary
#   CONSISTENT | INCONSISTENT | BLOCKED-D-VAN-7 | BLOCKED-K-4B
# and QUITs cleanly.

# ---- Locate self ------------------------------------------------------
_DVAN7_XCHECK_SELF := INPUT_FILENAME();;
if _DVAN7_XCHECK_SELF <> fail and _DVAN7_XCHECK_SELF <> "stream" then
    _DVAN7_XCHECK_DIR := _DVAN7_XCHECK_SELF{
        [1..Length(_DVAN7_XCHECK_SELF) - Length("/d_van_7_xcheck_k4a.g")]};;
else
    _DVAN7_XCHECK_DIR := fail;;
fi;;

# ---- Step 1: load D-VAN-7 result --------------------------------------
# computed/d_van_7/m5_result.g is written by run_d_van_7_m5.sh. The
# canonical path is repo-root-relative; if we can locate the scripts/
# dir, we use that to resolve the absolute path.
_DVAN7_RESULT_PATH := "../../computed/d_van_7/m5_result.g";;
if _DVAN7_XCHECK_DIR <> fail then
    _DVAN7_RESULT_PATH := Concatenation(_DVAN7_XCHECK_DIR,
        "/../../computed/d_van_7/m5_result.g");;
fi;;

if not IsExistingFile(_DVAN7_RESULT_PATH) then
    Print("[d_van_7_xcheck] BLOCKED-D-VAN-7: ", _DVAN7_RESULT_PATH,
          " not found.\n");
    Print("[d_van_7_xcheck]   Run ./run_d_van_7_m5.sh first to generate it.\n");
    Print("[d_van_7_xcheck]   The result file is the persisted output of\n");
    Print("[d_van_7_xcheck]   D-VAN-7's per-generator sweep + half-vec test\n");
    Print("[d_van_7_xcheck]   and is required input here.\n");
    QUIT_GAP(0);
fi;

_DVAN7_DATA := ReadAsFunction(_DVAN7_RESULT_PATH)();;

if not IsRecord(_DVAN7_DATA) then
    Print("[d_van_7_xcheck] BLOCKED-D-VAN-7: ", _DVAN7_RESULT_PATH,
          " did not return a record.\n");
    Print("[d_van_7_xcheck]   The file should contain `return rec(...);;`.\n");
    Print("[d_van_7_xcheck]   Has it been hand-edited / truncated?\n");
    QUIT_GAP(0);
fi;

Print("[d_van_7_xcheck] Loaded D-VAN-7 verdict from ", _DVAN7_RESULT_PATH,
      "\n");
Print("[d_van_7_xcheck]   m              = ", _DVAN7_DATA.m, "\n");
Print("[d_van_7_xcheck]   verdict        = ", _DVAN7_DATA.verdict, "\n");
Print("[d_van_7_xcheck]   k_m5           = ", _DVAN7_DATA.k_m5, "\n");
Print("[d_van_7_xcheck]   #mismatches    = ", Length(_DVAN7_DATA.mismatches),
      "\n");
Print("[d_van_7_xcheck]   half_vec.agree = ", _DVAN7_DATA.half_vec.agree,
      "\n");

# ---- Step 2: load K-4b result ----------------------------------------
# k4b_m5_result.g is written by run_k4b_m5.sh and binds the global
# RESULT (= the K4aClassify(5) record). If it doesn't exist yet we
# emit a clear instruction rather than fail with a cryptic error.
_K4B_RESULT_PATH := "k4b_m5_result.g";;
if _DVAN7_XCHECK_DIR <> fail then
    _K4B_RESULT_PATH := Concatenation(_DVAN7_XCHECK_DIR,
                                       "/k4b_m5_result.g");;
fi;;

if not IsExistingFile(_K4B_RESULT_PATH) then
    Print("[d_van_7_xcheck] BLOCKED-K-4B: ", _K4B_RESULT_PATH,
          " not found.\n");
    Print("[d_van_7_xcheck]   Run ./run_k4b_m5.sh first to generate it.\n");
    Print("[d_van_7_xcheck]   The result file is the persisted output of\n");
    Print("[d_van_7_xcheck]   K4aClassify(5) and is required input here.\n");
    Print("[d_van_7_xcheck]   K-4b itself depends on issue #200 (T6) and\n");
    Print("[d_van_7_xcheck]   issue #220 (sparse trace) — both must merge\n");
    Print("[d_van_7_xcheck]   before run_k4b_m5.sh can execute.\n");
    QUIT_GAP(0);
fi;

Read(_K4B_RESULT_PATH);   # binds RESULT

if not IsBound(RESULT) then
    Print("[d_van_7_xcheck] BLOCKED-K-4B: ", _K4B_RESULT_PATH,
          " did not bind RESULT.\n");
    Print("[d_van_7_xcheck]   The file should contain `RESULT := rec(...);;`.\n");
    Print("[d_van_7_xcheck]   Has it been hand-edited / truncated?\n");
    QUIT_GAP(0);
fi;

Print("[d_van_7_xcheck] Loaded K-4b verdict from ", _K4B_RESULT_PATH, "\n");
Print("[d_van_7_xcheck]   m              = ", RESULT.m, "\n");
Print("[d_van_7_xcheck]   verdict        = ", RESULT.verdict, "\n");
Print("[d_van_7_xcheck]   trivial        = ", RESULT.trivial, "\n");

# ---- Step 3: m-coherence check ---------------------------------------
# Both files should be tagged m=5. A mismatch indicates one of the
# drivers was misconfigured.
if _DVAN7_DATA.m <> RESULT.m then
    Print("\n[d_van_7_xcheck] INCONSISTENT: m-axis disagrees.\n");
    Print("[d_van_7_xcheck]   D-VAN-7 m  = ", _DVAN7_DATA.m, "\n");
    Print("[d_van_7_xcheck]   K-4b    m  = ", RESULT.m, "\n");
    Print("[d_van_7_xcheck]   This means at least one of the drivers\n");
    Print("[d_van_7_xcheck]   was run with the wrong m parameter.\n");
    QUIT;
fi;

# ---- Step 4: trivial-axis cross-validation ---------------------------
# Under Keller's conjecture at m=5, the expected outcome is:
#
#   * K-4b:    RESULT.trivial = true, RESULT.verdict = "trivial".
#   * D-VAN-7: every D-VAN per-generator verdict matches A-5b's
#              HAP-derived in_kernel_gens (so verdict = "agree"), AND
#              the half-vector for the order-4 generator matches.
#
# The two together establish: K-4b's α = α_KRR is detected-trivial AND
# D-VAN-7's algebraic-restriction pipeline reproduces A-5b's
# kernel-of-Tr structure across the full unit-generator basis. Either
# pipeline could in principle fire false-positive (e.g. K-4b matches
# trivial via Aut-orbit ambiguity, or D-VAN's detecting family has
# an injectivity gap); their joint trivial-at-m=5 verdict is the
# strongest available cross-validation pre-Phase-2.
#
# Decision matrix:
#
#   K-4b.trivial | D-VAN-7.verdict = "agree" | outcome
#   ------------ | ------------------------- | ----------------
#   true         | true                      | CONSISTENT
#   true         | false                     | INCONSISTENT
#   false        | true                      | INCONSISTENT
#   false        | false                     | INCONSISTENT
#                                              (but both agree on
#                                               non-trivial — file
#                                               diagnostic issue)
#   fail         | _                         | INCONCLUSIVE (K-4b
#                                              "incomplete")

Print("\n[d_van_7_xcheck] === trivial-axis cross-validation ===\n");
Print("[d_van_7_xcheck]   K-4b    trivial = ", RESULT.trivial, "\n");
Print("[d_van_7_xcheck]   D-VAN-7 verdict = ", _DVAN7_DATA.verdict, "\n");
Print("[d_van_7_xcheck]   D-VAN-7 #mism   = ", Length(_DVAN7_DATA.mismatches),
      "\n");
Print("[d_van_7_xcheck]   D-VAN-7 half OK = ", _DVAN7_DATA.half_vec.agree,
      "\n");

_DVAN7_AGREE := _DVAN7_DATA.verdict = "agree";;

if RESULT.trivial = fail then
    Print("\n[d_van_7_xcheck] INCONCLUSIVE\n");
    Print("[d_van_7_xcheck]   K-4b returned verdict = \"incomplete\".\n");
    Print("[d_van_7_xcheck]   Rerun run_k4b_m5.sh and address whichever\n");
    Print("[d_van_7_xcheck]   branch failed before re-running this xcheck.\n");
elif RESULT.trivial = true and _DVAN7_AGREE = true then
    Print("\n[d_van_7_xcheck] CONSISTENT\n");
    Print("[d_van_7_xcheck]   K-4b reports α_KRR detected-trivial AND\n");
    Print("[d_van_7_xcheck]   D-VAN-7 agrees with A-5b on all ",
          _DVAN7_DATA.k_m5, " H^3(E_+(5); U(1)) unit generators plus\n");
    Print("[d_van_7_xcheck]   the half-vector. Both pipelines align at\n");
    Print("[d_van_7_xcheck]   m=5 — this is the expected outcome under\n");
    Print("[d_van_7_xcheck]   Keller's α = 0 conjecture and answers\n");
    Print("[d_van_7_xcheck]   Keller's open question affirmatively at\n");
    Print("[d_van_7_xcheck]   m=5 (combined with the m=3 anchor).\n");
elif RESULT.trivial = true and _DVAN7_AGREE = false then
    Print("\n[d_van_7_xcheck] INCONSISTENT\n");
    Print("[d_van_7_xcheck]   K-4b reports trivial but D-VAN-7 disagrees\n");
    if _DVAN7_DATA.half_vec.agree then
        Print("[d_van_7_xcheck]   with A-5b on ", Length(_DVAN7_DATA.mismatches),
              " generators.\n");
    else
        Print("[d_van_7_xcheck]   with A-5b on ", Length(_DVAN7_DATA.mismatches),
              " generators (and the half-vector).\n");
    fi;
    Print("[d_van_7_xcheck]   First mismatches:\n");
    _DVAN7_SHOW := Minimum(5, Length(_DVAN7_DATA.mismatches));;
    for _DVAN7_I in [1.._DVAN7_SHOW] do
        Print("[d_van_7_xcheck]     ", _DVAN7_DATA.mismatches[_DVAN7_I], "\n");
    od;
    Print("[d_van_7_xcheck]   This is a triage signal: either the\n");
    Print("[d_van_7_xcheck]   detecting family's injectivity at m=5 has\n");
    Print("[d_van_7_xcheck]   a gap (cf. R-1, issue #193), or one of\n");
    Print("[d_van_7_xcheck]   the pipelines has a bug. File a diagnostic\n");
    Print("[d_van_7_xcheck]   issue and block W-1's m=5 publication.\n");
elif RESULT.trivial = false and _DVAN7_AGREE = true then
    Print("\n[d_van_7_xcheck] INCONSISTENT\n");
    Print("[d_van_7_xcheck]   K-4b reports α_KRR NON-trivial but D-VAN-7\n");
    Print("[d_van_7_xcheck]   reproduces A-5b's kernel structure on every\n");
    Print("[d_van_7_xcheck]   unit generator. The two pipelines disagree\n");
    Print("[d_van_7_xcheck]   on the non-trivial verdict for α_KRR —\n");
    Print("[d_van_7_xcheck]   either K-4b's classifier is mis-routing\n");
    Print("[d_van_7_xcheck]   (e.g. σ-vs-conj(σ) ambiguity at T5b, or\n");
    Print("[d_van_7_xcheck]   ε extraction at T4b) or A-5b's empirical\n");
    Print("[d_van_7_xcheck]   kernel is incomplete (mixed-combination\n");
    Print("[d_van_7_xcheck]   Stage-2 verification deferred).\n");
    Print("[d_van_7_xcheck]   File a diagnostic issue.\n");
else
    # Both report non-trivial / disagree.
    Print("\n[d_van_7_xcheck] INCONSISTENT\n");
    Print("[d_van_7_xcheck]   K-4b trivial   = ", RESULT.trivial, "\n");
    Print("[d_van_7_xcheck]   D-VAN-7 verdict= ", _DVAN7_DATA.verdict, "\n");
    Print("[d_van_7_xcheck]   D-VAN-7 #mism  = ",
          Length(_DVAN7_DATA.mismatches), "\n");
    Print("[d_van_7_xcheck]   Both pipelines report disagreement with the\n");
    Print("[d_van_7_xcheck]   trivial baseline. If both report the SAME\n");
    Print("[d_van_7_xcheck]   non-trivial class (D-VAN's mismatches\n");
    Print("[d_van_7_xcheck]   localise on coordinates of α_KRR), this\n");
    Print("[d_van_7_xcheck]   would be a CONSISTENT non-trivial verdict\n");
    Print("[d_van_7_xcheck]   — but reconciling D-VAN's per-generator\n");
    Print("[d_van_7_xcheck]   sweep against K-4b's single-class verdict\n");
    Print("[d_van_7_xcheck]   requires the strategy-(A) inversion stub in\n");
    Print("[d_van_7_xcheck]   k4b_xcheck_d_van.g (`_DVAN_InvertRestriction`)\n");
    Print("[d_van_7_xcheck]   to be implemented.\n");
fi;

QUIT;
