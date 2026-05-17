#!/usr/bin/env bash
# run_k4b_m5.sh — K-4b m=5 production driver.
#
# Wraps a single call to `K4aClassify(5)` (the K-4a-T6 orchestrator,
# issue #200) with all preconditions:
#
#   1. Read src/modular_data.g BEFORE k4a_classify.g, so the
#      D_8 / Q_8 classifiers can bind LoadModularData on load.
#   2. Place a `Modular_Data` symlink in CWD pointing at the
#      repo-level `modular_data/` tree, so LoadModularData(8, k, ...)
#      resolves.
#   3. Pre-check that the upstream dependencies exist on disk —
#        * krr_spectral_characters_sparse.g  (issue #220, sparse trace)
#        * k4a_classify.g                    (issue #200, T6 orchestrator)
#      Emit a clear "blocked on #NNN" message and bail out cleanly
#      if either is missing. The scaffold ships ahead of these so
#      the production run can execute the moment they both merge;
#      the gating below is the explicit handshake.
#   4. Persist the K4aClassify return record to `k4b_m5_result.g`
#      (loadable by a fresh GAP session via `Read("k4b_m5_result.g")`,
#      binding the global `RESULT`).
#   5. Mirror stdout/stderr to a timestamped log under
#      `extraspecial_orbifolds/perf/raw/k4b/` (override via
#      `K4B_LOG_DIR`).
#
# Usage (from anywhere; the script chdirs to its own directory):
#   ./run_k4b_m5.sh
#
# This driver is the K-4b deliverable for the K-4b spec at
#   docs/superpowers/specs/2026-05-17-k4b-m5-production-spec.md
# and is intended to be executed once T6 (#200) and the sparse trace
# follow-up (#220) have both landed. Until then, the gating in step (3)
# above guards against premature runs.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"

# ---- Step 3 (upstream pre-checks) -------------------------------------
# Run BEFORE any expensive setup so we fail fast and loud.

CLASSIFY_FILE="${SCRIPT_DIR}/k4a_classify.g"
SPARSE_FILE="${SCRIPT_DIR}/krr_spectral_characters_sparse.g"

if [[ ! -f "${CLASSIFY_FILE}" ]]; then
    echo "[run_k4b] BLOCKED: k4a_classify.g missing." >&2
    echo "[run_k4b]   path checked : ${CLASSIFY_FILE}" >&2
    echo "[run_k4b]   dependency   : K-4a-T6 orchestrator, issue #200." >&2
    echo "[run_k4b]   action       : merge #200 before running this driver." >&2
    exit 2
fi

if [[ ! -f "${SPARSE_FILE}" ]]; then
    echo "[run_k4b] BLOCKED: krr_spectral_characters_sparse.g missing." >&2
    echo "[run_k4b]   path checked : ${SPARSE_FILE}" >&2
    echo "[run_k4b]   dependency   : sparse trace_on_W replacement, issue #220." >&2
    echo "[run_k4b]   action       : merge #220 before running this driver." >&2
    echo "[run_k4b]                  (the dense T_h build in" >&2
    echo "[run_k4b]                   krr_spectral_characters.g is" >&2
    echo "[run_k4b]                   infeasible at m=5: ~3.7 years per" >&2
    echo "[run_k4b]                   intertwiner matrix.)" >&2
    exit 2
fi

# Additional check: the K4aClassify orchestrator currently hard-caps
# m at 3 (`n_max_supported := 3` in k4a_classify.g). When #220 lands,
# that cap should be lifted (or the orchestrator should switch over
# to BuildKRRSpectralCharactersSparse). The grep below catches the
# stale cap and prints a clear remediation pointer.
if grep -q 'n_max_supported := 3' "${CLASSIFY_FILE}"; then
    echo "[run_k4b] BLOCKED: k4a_classify.g still caps n_max_supported at 3." >&2
    echo "[run_k4b]   This means K4aClassify(5) will Error out." >&2
    echo "[run_k4b]   After #220 merges, the m>=4 deferral in" >&2
    echo "[run_k4b]   k4a_classify.g needs to be lifted (or the orchestrator" >&2
    echo "[run_k4b]   updated to call BuildKRRSpectralCharactersSparse" >&2
    echo "[run_k4b]   on the central branch when m>=4)." >&2
    echo "[run_k4b]   See docs/superpowers/specs/2026-05-17-k4b-m5-production-spec.md" >&2
    exit 3
fi

# ---- Step 2 (Modular_Data symlink) ------------------------------------
# Locate the repo-level modular_data/ tree. Layout:
#   <parent>/modular_data/8/3/k.txt  (D_8 cocycles)
#   <parent>/modular_data/8/4/k.txt  (Q_8 cocycles)
MODULAR_DATA_TREE="${REPO_ROOT}/../modular_data"
if [[ ! -d "${MODULAR_DATA_TREE}" ]]; then
    MODULAR_DATA_TREE="/Users/thomasgemunden/Projects/group_cohomology/modular_data"
fi
if [[ ! -f "${MODULAR_DATA_TREE}/8/4/1.txt" ]]; then
    echo "[run_k4b] cannot find Modular_Data tree (looked at ${MODULAR_DATA_TREE})" >&2
    exit 1
fi

cd "${SCRIPT_DIR}"

# Place the Modular_Data symlink for LoadModularData(...) to resolve.
# Mirrors the convention in run_k4a.sh.
if [[ -L "Modular_Data" || -e "Modular_Data" ]]; then
    rm -f Modular_Data
fi
ln -s "${MODULAR_DATA_TREE}" Modular_Data

# ---- Step 5 (logging) -------------------------------------------------
LOG_DIR="${K4B_LOG_DIR:-${REPO_ROOT}/extraspecial_orbifolds/perf/raw/k4b}"
mkdir -p "${LOG_DIR}"
TIMESTAMP="$(date -u +%Y%m%d_%H%M%SZ)"
LOG="${LOG_DIR}/k4b_m5_${TIMESTAMP}.log"

RESULT_FILE="${SCRIPT_DIR}/k4b_m5_result.g"

echo "[run_k4b] m              = 5"
echo "[run_k4b] script dir     = ${SCRIPT_DIR}"
echo "[run_k4b] modular_data   = ${MODULAR_DATA_TREE} (linked as Modular_Data)"
echo "[run_k4b] log            = ${LOG}"
echo "[run_k4b] result file    = ${RESULT_FILE}"

{
    echo "K-4b m=5 run started $(date -u +%FT%TZ)"
    echo "  driver       : ${BASH_SOURCE[0]}"
    echo "  script_dir   : ${SCRIPT_DIR}"
    echo "  modular_data : ${MODULAR_DATA_TREE}"
    echo "  result_file  : ${RESULT_FILE}"
} | tee "${LOG}"

# Optional virtual memory cap (per spec: 96 GB). `ulimit -v` is only
# available on Linux; on macOS it's silently ignored or errors. Wrap
# in `|| true` so the driver continues on macOS dev hosts.
ulimit -v $((96 * 1024 * 1024)) 2>/dev/null || true

# ---- Step 4 (run GAP) -------------------------------------------------
# -q -b suppresses banner and prompts. The GAP one-liner:
#   1. Reads src/modular_data.g  (binds LoadModularData and friends).
#   2. Reads k4a_classify.g       (defines K4aClassify; transitively
#                                  loads every classifier sibling).
#   3. Calls K4aClassify(5)       (the K-4b production run).
#   4. PrintTo(RESULT_FILE)       (persists the verdict record).
#   5. Prints a single-line summary to stdout for human-eyeballing.
#   6. QUITs cleanly.
#
# tee captures all of GAP's stdout + stderr into the log.
echo "[run_k4b] launching gap..." | tee -a "${LOG}"

set +e
gap -q -b -c "
    Read(\"../../src/modular_data.g\");;
    Read(\"k4a_classify.g\");;
    result := K4aClassify(5);;
    PrintTo(\"k4b_m5_result.g\",
        \"# K-4b m=5 result (auto-generated by run_k4b_m5.sh)\n\",
        \"# Loadable in a fresh GAP session: Read(\\\"k4b_m5_result.g\\\");\n\",
        \"# binds RESULT.\n\",
        \"RESULT := \", result, \";;\n\");;
    Print(\"\n=== K-4b m=5 verdict ===\n\");;
    Print(\"verdict  : \", result.verdict, \"\n\");;
    Print(\"trivial  : \", result.trivial, \"\n\");;
    Print(\"E_class  : is_coboundary = \", result.E_class.is_coboundary, \"\n\");;
    Print(\"D8_class : class_idx     = \", result.D8_class.class_idx,
          \" (trivial = 1)\n\");;
    Print(\"Q8_class : class_idx     = \", result.Q8_class.class_idx,
          \" (trivial = 1)\n\");;
    Print(\"wall_seconds : \", result.timing.wall_seconds, \"\n\");;
    QUIT;
" 2>&1 | tee -a "${LOG}"
# In a pipeline, $? is the last command's status (tee). Capture the
# gap exit code via PIPESTATUS (bash-only, but the shebang above
# guarantees bash).
GAP_EXIT=${PIPESTATUS[0]}
set -e

echo "[run_k4b] gap exited with code ${GAP_EXIT}" | tee -a "${LOG}"

if [[ ${GAP_EXIT} -ne 0 ]]; then
    echo "[run_k4b] gap exited non-zero; result file may be partial/missing." | tee -a "${LOG}"
    exit ${GAP_EXIT}
fi

if [[ ! -f "${RESULT_FILE}" ]]; then
    echo "[run_k4b] gap exited 0 but ${RESULT_FILE} was not written." | tee -a "${LOG}" >&2
    exit 4
fi

echo "[run_k4b] result file written: ${RESULT_FILE}" | tee -a "${LOG}"
echo "K-4b m=5 run ended $(date -u +%FT%TZ)" | tee -a "${LOG}"
echo
echo "Next steps:"
echo "  1. Read k4b_m5_result.g in a fresh GAP session to inspect RESULT."
echo "  2. Run cross-validation:"
echo "       gap -q -b -c 'Read(\"${SCRIPT_DIR}/k4b_xcheck_d_van.g\");'"
echo "  3. Fill in docs/superpowers/research/TEMPLATE-k4b-m5-verdict.md"
echo "     (rename to a dated, descriptive filename) and commit."
