#!/usr/bin/env bash
# run_d_van_7_m5.sh — WITHDRAWN: math conflation (PR #449 prereq audit,
#                    2026-06-06). DO NOT RUN — the cross-validation
#                    semantic is wrong.
#
# This driver compares `r.trivial` (D-VAN's zero-class detector under
# detecting-family restriction) against `(i in in_kernel_gens)` (A-5b's
# transgression-kernel membership) on the 165 hom-basis generators of
# H^3(E_+(5); U(1)). The two flags test DIFFERENT maps' kernels (see
# extraspecial_orbifolds/docs/superpowers/research/2026-06-06-ker-tr-detecting-family-audit.md
# and the earlier withdrawal commit `ed5cc4a`).
#
# The DETECTING-FAMILY restriction is injective on H^3 (AM04 + Quillen),
# so `r.trivial = true ⟺ [ω] = 0 in H^3`. The TRANSGRESSION map has a
# generally large kernel — at m=5 it is (Z/2)^52 inside (Z/2)^164 ⊕ Z/4.
# Running this driver as written produces an "agree_per_gen" record but
# the agreement is meaningless (at m=3 every unit gen is in ker(Tr) yet
# D-VAN reports trivial=false on every one).
#
# What this driver SHOULD be (TBD work, not in scope for the audit):
# the D-VAN m=5 anchor is a self-contained 165/165 trivial=false sweep
# on the unit basis (each `e_i ≠ 0` in H^3, hence trivial=false by
# injectivity of restriction). It does not need `kernel.g`.
#
# The original docstring is preserved below for context.
#
# === ORIGINAL DOC (preserved for reference) ===
#
# D-VAN-7 is the empirical anchor that cross-validates D-VAN's
# detecting-family vanishing test against A-5b's HAP-derived
# ker(Tr : H^3(E_+(5); U(1)) -> ⊕_g H^2(C_g; U(1))) at every one of the
# 165 hom-basis unit generators of H^3(E_+(5); U(1)) and at the
# half-vector for the unique order-4 generator. [THIS FRAMING IS WRONG;
# see the withdrawal notice above.]
#
# Pipeline:
#
#   1. Pre-check that A-5b's output exists at
#      `computed/transgression/5/kernel.g`. The A-5b driver writes that
#      file (issue #47, `run_e_plus_5_kernel.g`); D-VAN-7 cannot start
#      until it lands. Emit a clear "BLOCKED on #47 A-5b" message and
#      bail out cleanly if not present.
#
#   2. Read `detecting_family_vanish.g` (which transitively pulls in
#      `detecting_family_restriction.g`, `fsi_wrapper.g`,
#      `transgression_kernel.g`, and the HAP resolution machinery).
#
#   3. Load A-5b's kernel record. Extract:
#        * in_kernel_gens — indices i in [1..165] for which e_i ∈ ker(Tr)
#        * exp_index — index of the unique order-4 generator
#        * half_vec_in_kernel — bool: is 2 * e_{exp_index} in ker(Tr)?
#        * torsion — invariant-factor torsion vector (length 165)
#
#   4. For each i in [1..165]: compute
#        r_i := ResIsTrivialOnDetectingFamily(5, e_i)
#      and check whether r_i.trivial agrees with (i in in_kernel_gens).
#
#      Gating 1A clarification: at m=3, A-3a discovered ker(Tr) = full
#      H^3 (every class is in ker), so D-VAN reports trivial=false on
#      every unit generator (each is non-zero in H^3, hence non-trivial
#      under res). The "matches HAP kernel" framing is therefore NOT
#      generally a trivial=true/false flip — see test_detecting_family_vanish.g
#      Task 3.1 for the corrected framing. At m=5 we don't yet know
#      ker(Tr)'s shape (A-5b is the empirical anchor we are validating
#      against), so we simply record D-VAN's verdict for each generator
#      and compare against A-5b's in_kernel_gens / half_vec_in_kernel.
#
#   5. Run the half-vector test: 2 * e_{exp_index} -> r_half.trivial,
#      compare against half_vec_in_kernel.
#
#   6. Persist results to `computed/d_van_7/m5_result.g` as a record:
#        verdict (string), dvan_per_gen (list of bool), hap_in_kernel
#        (list of bool from A-5b), agree_per_gen (list of bool),
#        mismatches (list of indices), half_vec (rec), torsion,
#        k_m5 (=165), exp_index.
#
#   7. Mirror stdout/stderr to a timestamped log under
#      `extraspecial_orbifolds/perf/raw/d_van_7/` (override via
#      `D_VAN_7_LOG_DIR`).
#
# Sibling: `run_k4b_m5.sh` is the K-4b counterpart that produces
# K4aClassify(5).verdict. After both run, `d_van_7_xcheck_k4a.g`
# correlates the two and emits the cross-validation summary.
#
# Usage (from anywhere; the script chdirs to its own directory):
#   ./run_d_van_7_m5.sh
#
# This driver ships AHEAD of A-5b's `computed/transgression/5/kernel.g`
# being written. The gating in step (1) makes that explicit; the moment
# A-5b lands the file, this driver runs in one command.

set -euo pipefail

# ---- WITHDRAWN guard --------------------------------------------------
# This driver is withdrawn as of the 2026-06-06 ker(Tr) vs detecting-
# family audit (PR #449 prerequisite). Refuse to run unless the caller
# sets DVAN7_FORCE_WITHDRAWN_RUN=1 (intended only for archaeology /
# reproducing the original conflated comparison numerically).
if [[ -z "${DVAN7_FORCE_WITHDRAWN_RUN:-}" ]]; then
    echo "[run_d_van_7] WITHDRAWN: math conflation between ker(Tr) and" >&2
    echo "[run_d_van_7]            detecting-family restriction kernel." >&2
    echo "[run_d_van_7]            See header comment for details, or:" >&2
    echo "[run_d_van_7]            extraspecial_orbifolds/docs/superpowers/" >&2
    echo "[run_d_van_7]              research/2026-06-06-ker-tr-detecting-family-audit.md" >&2
    echo "[run_d_van_7]" >&2
    echo "[run_d_van_7]   Override (for archaeology only):" >&2
    echo "[run_d_van_7]     DVAN7_FORCE_WITHDRAWN_RUN=1 ./run_d_van_7_m5.sh" >&2
    exit 64
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"

# ---- Step 1 (upstream pre-checks) -------------------------------------
# Run BEFORE any expensive setup so we fail fast and loud.

KERNEL_FILE="${REPO_ROOT}/computed/transgression/5/kernel.g"
DVAN_FILE="${SCRIPT_DIR}/detecting_family_vanish.g"

if [[ ! -f "${KERNEL_FILE}" ]]; then
    echo "[run_d_van_7] BLOCKED on #47 A-5b: kernel.g missing." >&2
    echo "[run_d_van_7]   path checked : ${KERNEL_FILE}" >&2
    echo "[run_d_van_7]   dependency   : A-5b driver, issue #47" >&2
    echo "[run_d_van_7]                  (run_e_plus_m_kernel_hap.g with MPARAM:=5)." >&2
    echo "[run_d_van_7]   action       : wait for A-5b to complete and" >&2
    echo "[run_d_van_7]                  write the kernel file, then re-run." >&2
    echo "[run_d_van_7]                  PID 44998 is running A-5b as of" >&2
    echo "[run_d_van_7]                  2026-05-17; expected to ship in" >&2
    echo "[run_d_van_7]                  coming hours with the post-merge" >&2
    echo "[run_d_van_7]                  batched-backsub speedups." >&2
    exit 2
fi

if [[ ! -f "${DVAN_FILE}" ]]; then
    echo "[run_d_van_7] BLOCKED: detecting_family_vanish.g missing." >&2
    echo "[run_d_van_7]   path checked : ${DVAN_FILE}" >&2
    echo "[run_d_van_7]   dependency   : D-VAN-3, issue #144." >&2
    echo "[run_d_van_7]   action       : ensure detecting_family_vanish.g" >&2
    echo "[run_d_van_7]                  is present (should be on main)." >&2
    exit 2
fi

cd "${SCRIPT_DIR}"

# ---- Step 7 (logging) -------------------------------------------------
LOG_DIR="${D_VAN_7_LOG_DIR:-${REPO_ROOT}/extraspecial_orbifolds/perf/raw/d_van_7}"
mkdir -p "${LOG_DIR}"
TIMESTAMP="$(date -u +%Y%m%d_%H%M%SZ)"
LOG="${LOG_DIR}/d_van_7_m5_${TIMESTAMP}.log"

# ---- Output dir for results ------------------------------------------
RESULT_DIR="${REPO_ROOT}/computed/d_van_7"
mkdir -p "${RESULT_DIR}"
RESULT_FILE="${RESULT_DIR}/m5_result.g"

echo "[run_d_van_7] m              = 5"
echo "[run_d_van_7] script dir     = ${SCRIPT_DIR}"
echo "[run_d_van_7] A-5b kernel    = ${KERNEL_FILE}"
echo "[run_d_van_7] log            = ${LOG}"
echo "[run_d_van_7] result file    = ${RESULT_FILE}"

{
    echo "D-VAN-7 m=5 run started $(date -u +%FT%TZ)"
    echo "  driver       : ${BASH_SOURCE[0]}"
    echo "  script_dir   : ${SCRIPT_DIR}"
    echo "  kernel_file  : ${KERNEL_FILE}"
    echo "  result_file  : ${RESULT_FILE}"
} | tee "${LOG}"

# Optional virtual memory cap. BuildRestrictionMatrices(5, "hap") on a
# cold cache builds the HAP resolution for E_+(5) which is the heavy
# step (~10 min wall and a few GB RAM per A-5a / #138). 32 GB is plenty.
# `ulimit -v` is Linux-only; wrap in `|| true` for macOS.
ulimit -v $((32 * 1024 * 1024)) 2>/dev/null || true

# ---- Step 2-6 (run GAP) -----------------------------------------------
# -q -b suppresses banner and prompts. The GAP one-liner:
#   1. Reads detecting_family_vanish.g (transitively pulls in everything
#      D-VAN-3 needs: detecting_family_restriction.g, fsi_wrapper.g,
#      transgression_kernel.g, and HAP).
#   2. Reads A-5b's kernel.g via ReadAsFunction(...) (single shot).
#   3. Sweeps all 165 unit generators, calls
#      ResIsTrivialOnDetectingFamily(5, e_i) for each.
#   4. Runs the half-vector test on 2 * e_{exp_index}.
#   5. Compares D-VAN's per-generator verdict against A-5b's
#      in_kernel_gens / half_vec_in_kernel.
#   6. Persists the rec to RESULT_FILE using OutputTextFile +
#      SetPrintFormattingStatus (no PrintTo for data files, per
#      conventions).
#   7. Prints a single-line summary.
#   8. QUITs cleanly.
echo "[run_d_van_7] launching gap..." | tee -a "${LOG}"

set +e
gap -q -b -c "
    Read(\"detecting_family_vanish.g\");;
    ker_data := ReadAsFunction(\"${KERNEL_FILE}\")();;
    in_kernel_gens := ker_data.in_kernel_gens;;
    exp_index := ker_data.exp_index;;
    half_vec_in_kernel := ker_data.half_vec_in_kernel;;
    torsion := ker_data.torsion;;
    k_m5 := Length(torsion);;
    Print(\"\\n[run_d_van_7]   k_m5            = \", k_m5, \"\\n\");;
    Print(\"[run_d_van_7]   exp_index       = \", exp_index, \"\\n\");;
    Print(\"[run_d_van_7]   |in_kernel_gens|= \", Length(in_kernel_gens), \"\\n\");;
    Print(\"[run_d_van_7]   half_vec_in_ker = \", half_vec_in_kernel, \"\\n\");;

    Print(\"\\n[run_d_van_7] === building restriction matrices (cold) ===\\n\");;
    t0 := Runtime();;
    rec_m5 := BuildRestrictionMatrices(5, \"hap\");;
    Print(\"[run_d_van_7]   built in \", (Runtime() - t0) / 1000., \" s\\n\");;

    Print(\"\\n[run_d_van_7] === per-generator sweep over \", k_m5, \" gens ===\\n\");;
    dvan_per_gen := [];;
    hap_in_kernel := [];;
    agree_per_gen := [];;
    mismatches := [];;
    for i in [1..k_m5] do
        e_i := List([1..k_m5], j -> 0);;
        e_i[i] := 1;;
        r := ResIsTrivialOnDetectingFamily(5, e_i);;
        Add(dvan_per_gen, r.trivial);;
        in_hap := (i in in_kernel_gens);;
        Add(hap_in_kernel, in_hap);;
        Add(agree_per_gen, r.trivial = in_hap);;
        if r.trivial <> in_hap then
            Add(mismatches, rec(i := i, dvan := r.trivial, hap := in_hap));;
        fi;;
        if i mod 25 = 0 then
            Print(\"[run_d_van_7]   ... \", i, \" / \", k_m5,
                  \"  mismatches so far: \", Length(mismatches), \"\\n\");;
        fi;;
    od;;

    Print(\"\\n[run_d_van_7] === half-vector test (2 * e_\", exp_index, \") ===\\n\");;
    half_vec := List([1..k_m5], j -> 0);;
    half_vec[exp_index] := 2;;
    r_half := ResIsTrivialOnDetectingFamily(5, half_vec);;
    half_agree := (r_half.trivial = half_vec_in_kernel);;
    Print(\"[run_d_van_7]   D-VAN half      = \", r_half.trivial, \"\\n\");;
    Print(\"[run_d_van_7]   A-5b half       = \", half_vec_in_kernel, \"\\n\");;
    Print(\"[run_d_van_7]   agree           = \", half_agree, \"\\n\");;

    verdict := \"unknown\";;
    if IsEmpty(mismatches) and half_agree then
        verdict := \"agree\";;
    else
        verdict := \"disagree\";;
    fi;;

    Print(\"\\n[run_d_van_7] === verdict ===\\n\");;
    Print(\"[run_d_van_7]   verdict         = \", verdict, \"\\n\");;
    Print(\"[run_d_van_7]   mismatches      = \", Length(mismatches), \" / \", k_m5, \"\\n\");;
    Print(\"[run_d_van_7]   half_agree      = \", half_agree, \"\\n\");;

    # Persist results. Convention: no PrintTo for data files; use
    # OutputTextFile + SetPrintFormattingStatus(stream, false) so that
    # GAP does not wrap long lines at ~80 chars (which silently breaks
    # comments and large vectors when ReadAsFunction tries to parse it
    # back).
    out := OutputTextFile(\"${RESULT_FILE}\", false);;
    SetPrintFormattingStatus(out, false);;
    AppendTo(out, \"# D-VAN-7 m=5 verdict (auto-generated by run_d_van_7_m5.sh)\\n\");;
    AppendTo(out, \"#\\n\");;
    AppendTo(out, \"# Compares D-VAN's per-generator detecting-family verdict\\n\");;
    AppendTo(out, \"# against A-5b's HAP-derived in_kernel_gens at every\\n\");;
    AppendTo(out, \"# unit generator of H^3(E_+(5); U(1)).\\n\");;
    AppendTo(out, \"#\\n\");;
    AppendTo(out, \"# Loadable in a fresh GAP session:\\n\");;
    AppendTo(out, \"#   data := ReadAsFunction(\\\"m5_result.g\\\")();\\n\");;
    AppendTo(out, \"#\\n\");;
    AppendTo(out, \"# Fields:\\n\");;
    AppendTo(out, \"#   verdict        : \\\"agree\\\" | \\\"disagree\\\"\\n\");;
    AppendTo(out, \"#   m              : 5\\n\");;
    AppendTo(out, \"#   k_m5           : 165 (#unit generators)\\n\");;
    AppendTo(out, \"#   torsion        : invariant-factor torsion vector\\n\");;
    AppendTo(out, \"#   exp_index      : index of unique order-4 generator\\n\");;
    AppendTo(out, \"#   dvan_per_gen   : list of bool, D-VAN trivial verdict per gen\\n\");;
    AppendTo(out, \"#   hap_in_kernel  : list of bool, (i in in_kernel_gens)\\n\");;
    AppendTo(out, \"#   agree_per_gen  : list of bool, dvan = hap?\\n\");;
    AppendTo(out, \"#   mismatches     : list of rec(i, dvan, hap) for disagreements\\n\");;
    AppendTo(out, \"#   half_vec       : rec(dvan, hap, agree)\\n\");;
    AppendTo(out, \"\\n\");;
    AppendTo(out, \"return rec(\\n\");;
    AppendTo(out, \"    verdict        := \\\"\", verdict, \"\\\",\\n\");;
    AppendTo(out, \"    m              := 5,\\n\");;
    AppendTo(out, \"    k_m5           := \", k_m5, \",\\n\");;
    AppendTo(out, \"    torsion        := \", torsion, \",\\n\");;
    AppendTo(out, \"    exp_index      := \", exp_index, \",\\n\");;
    AppendTo(out, \"    dvan_per_gen   := \", dvan_per_gen, \",\\n\");;
    AppendTo(out, \"    hap_in_kernel  := \", hap_in_kernel, \",\\n\");;
    AppendTo(out, \"    agree_per_gen  := \", agree_per_gen, \",\\n\");;
    AppendTo(out, \"    mismatches     := \", mismatches, \",\\n\");;
    AppendTo(out, \"    half_vec       := rec(dvan := \", r_half.trivial,
            \", hap := \", half_vec_in_kernel,
            \", agree := \", half_agree, \")\\n\");;
    AppendTo(out, \");;\\n\");;
    CloseStream(out);;
    Print(\"[run_d_van_7]   wrote \", \"${RESULT_FILE}\", \"\\n\");;
    QUIT;
" 2>&1 | tee -a "${LOG}"
# Capture the gap exit code via PIPESTATUS (bash-only; shebang
# guarantees bash).
GAP_EXIT=${PIPESTATUS[0]}
set -e

echo "[run_d_van_7] gap exited with code ${GAP_EXIT}" | tee -a "${LOG}"

if [[ ${GAP_EXIT} -ne 0 ]]; then
    echo "[run_d_van_7] gap exited non-zero; result file may be partial/missing." | tee -a "${LOG}"
    exit ${GAP_EXIT}
fi

if [[ ! -f "${RESULT_FILE}" ]]; then
    echo "[run_d_van_7] gap exited 0 but ${RESULT_FILE} was not written." | tee -a "${LOG}" >&2
    exit 4
fi

echo "[run_d_van_7] result file written: ${RESULT_FILE}" | tee -a "${LOG}"
echo "D-VAN-7 m=5 run ended $(date -u +%FT%TZ)" | tee -a "${LOG}"
echo
echo "Next steps:"
echo "  1. Read ${RESULT_FILE} in a fresh GAP session to inspect."
echo "  2. Run cross-validation against K-4b (when k4b_m5_result.g exists):"
echo "       gap -q -b -c 'Read(\"${SCRIPT_DIR}/d_van_7_xcheck_k4a.g\");'"
echo "  3. Fill in docs/superpowers/research/TEMPLATE-d_van_7_m5_verdict.md"
echo "     (rename to a dated, descriptive filename) and commit."
