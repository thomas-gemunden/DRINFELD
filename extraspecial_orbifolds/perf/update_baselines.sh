#!/usr/bin/env bash
#
# update_baselines.sh — populate test_baselines.json from local runs.
#
# P-8 (#116). Runs `run_tests.sh` N times (default 3), feeding each
# run's `/tmp/*.timing` files into `compare_timings.py record` so
# the baseline JSON ends up with the median over N runs.
#
# Usage:
#   ./update_baselines.sh                # 3 runs, FAST=1
#   N=5 ./update_baselines.sh            # 5 runs
#   FAST=0 ./update_baselines.sh         # include slow tests
#
# This is a deliberate, one-shot update — commit the resulting
# test_baselines.json change explicitly. Don't run from CI.

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
N="${N:-3}"
FAST="${FAST:-1}"

echo "Updating test_baselines.json from ${N} runs (FAST=${FAST})..."
echo "  repo root: ${REPO_ROOT}"
echo "  baseline:  ${SCRIPT_DIR}/test_baselines.json"
echo

# Reset wall_s_runs lists before the first run.
python3 - <<EOF
import json
from pathlib import Path
p = Path("${SCRIPT_DIR}/test_baselines.json")
data = json.loads(p.read_text())
for name, entry in data.items():
    if name == "_meta":
        continue
    entry["wall_s_runs"] = []
    entry["wall_s_median"] = 0
p.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
print(f"  cleared wall_s_runs for {len(data) - 1} tests")
EOF

for i in $(seq 1 "$N"); do
    echo
    echo "=== Run ${i} / ${N} ==="
    TIMING_DIR="/tmp/p8_baseline_run_${i}"
    rm -rf "${TIMING_DIR}"
    mkdir -p "${TIMING_DIR}"
    FAST="${FAST}" TIMING_DIR="${TIMING_DIR}" "${REPO_ROOT}/run_tests.sh" \
        > "${TIMING_DIR}/_runner.log" 2>&1 \
        || echo "  (run_tests.sh exited non-zero; recording partial timings anyway)"
    python3 "${SCRIPT_DIR}/compare_timings.py" record "${TIMING_DIR}" --append-runs
done

echo
echo "Done. Median values written to ${SCRIPT_DIR}/test_baselines.json."
echo "Review with: python3 ${SCRIPT_DIR}/compare_timings.py show"
