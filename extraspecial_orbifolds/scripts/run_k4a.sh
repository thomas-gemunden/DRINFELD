#!/usr/bin/env bash
# run_k4a.sh -- CLI driver for the K-4a-T6 orchestrator (issue #200).
#
# Wraps `Read("k4a_classify.g");; K4aClassify(m);;` with the
# preconditions the orchestrator needs:
#
#   1. Read src/modular_data.g BEFORE k4a_classify.g, so the
#      D_8 / Q_8 classifiers can bind LoadModularData on load.
#   2. Place a `Modular_Data` symlink in CWD pointing at the
#      repo-level `modular_data/` tree, so LoadModularData(8, k, ...)
#      resolves.
#   3. Pass m as a CLI argument (default: 3, the K-4a-T7 anchor).
#
# Usage:
#   ./run_k4a.sh           # m = 3 (default; K-4a-T7 anchor)
#   ./run_k4a.sh 3         # m = 3 explicitly
#   ./run_k4a.sh 2         # m = 2 smoke test
#
# Output: the K4aClassify return record printed via PrintObj, followed
# by a newline. The orchestrator itself prints progress messages to
# stdout while running.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"

# Locate the repo-level modular_data/ tree.
# Layout: <parent>/modular_data/8/4/1.txt, etc.
# REPO_ROOT here is the worktree root (e.g. .../DRINFELD-wt-k4a-t6).
# The shared modular_data tree sits at <repo_root>/../modular_data
# (i.e. .../group_cohomology/modular_data).
MODULAR_DATA_TREE="${REPO_ROOT}/../modular_data"
if [[ ! -d "${MODULAR_DATA_TREE}" ]]; then
    # Fall back to absolute path.
    MODULAR_DATA_TREE="/Users/thomasgemunden/Projects/group_cohomology/modular_data"
fi
if [[ ! -f "${MODULAR_DATA_TREE}/8/4/1.txt" ]]; then
    echo "run_k4a.sh: cannot find Modular_Data tree (looked at ${MODULAR_DATA_TREE})" >&2
    exit 1
fi

# Place the Modular_Data symlink in a dedicated work directory under
# tests/k4a/orchestrator (mirrors the convention used by
# tests/test_q8_classifier.g, tests/test_ct_modular_data.g, etc., so we
# don't leave runtime artefacts in the source tree). Pass absolute
# paths into the GAP command so chdir-ing into the work directory
# doesn't break Read("...") resolution.
WORK_DIR="${SCRIPT_DIR}/tests/k4a/orchestrator"
mkdir -p "${WORK_DIR}"
if [[ -L "${WORK_DIR}/Modular_Data" || -e "${WORK_DIR}/Modular_Data" ]]; then
    rm -f "${WORK_DIR}/Modular_Data"
fi
ln -s "${MODULAR_DATA_TREE}" "${WORK_DIR}/Modular_Data"

cd "${WORK_DIR}"

m="${1:-3}"

# Absolute paths for the .g files (we chdir'd into WORK_DIR, so
# relative paths from SCRIPT_DIR would no longer resolve).
SRC_MODULAR_DATA="${REPO_ROOT}/src/modular_data.g"
K4A_CLASSIFY="${SCRIPT_DIR}/k4a_classify.g"

echo "[run_k4a] m = ${m}"
echo "[run_k4a] work dir     : ${WORK_DIR}"
echo "[run_k4a] modular_data : ${MODULAR_DATA_TREE} (linked as Modular_Data)"
echo "[run_k4a] launching gap..."

# -q -b suppresses banner and prompts. The driver QUITs after PrintObj.
gap -q -b -c "Read(\"${SRC_MODULAR_DATA}\");; Read(\"${K4A_CLASSIFY}\");; r := K4aClassify(${m});; PrintObj(r);; Print(\"\\n\"); QUIT;"
