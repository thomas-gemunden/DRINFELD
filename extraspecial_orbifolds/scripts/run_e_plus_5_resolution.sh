#!/usr/bin/env bash
# run_e_plus_5_resolution.sh — A-5a wrapper around run_e_plus_5_resolution.g.
#
# Purpose: launch the GAP driver with a configurable memory cap, poll the
# process's RSS at a fixed interval, and patch peak_rss_mb into the
# outcome.g file on completion. On out-of-process failure (OOM-kill,
# SIGTERM, etc.) where the GAP driver never finishes writing outcome.g,
# this wrapper synthesises a failure outcome so dp_ii_dispatch.g still
# has something to branch on.
#
# Usage (from extraspecial_orbifolds/scripts/):
#   ./run_e_plus_5_resolution.sh [memory_cap_gb] [poll_interval_sec]
#
# Defaults: 48 GB cap, 10 s poll interval. The cap is passed to GAP via
# `-o <cap>g`; physical RAM on this host (64 GB) leaves ~16 GB headroom
# for the OS at the default.
#
# Issue #46 (A-5a).

set -euo pipefail

CAP_GB="${1:-48}"
POLL_SEC="${2:-10}"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
OUTCOME_DIR="${REPO_ROOT}/computed/transgression/5"
OUTCOME_PATH="${OUTCOME_DIR}/resolution_outcome.g"
LOG_PATH="${OUTCOME_DIR}/resolution.log"
PEAK_RSS_PATH="${OUTCOME_DIR}/peak_rss.txt"

mkdir -p "${OUTCOME_DIR}"

# Remove any stale outcome from a prior run so we can detect whether the
# current attempt wrote one.
rm -f "${OUTCOME_PATH}" "${PEAK_RSS_PATH}"

cd "${SCRIPT_DIR}"

echo "[a5a-sh] memory cap     : ${CAP_GB}g"
echo "[a5a-sh] poll interval  : ${POLL_SEC}s"
echo "[a5a-sh] outcome path   : ${OUTCOME_PATH}"
echo "[a5a-sh] log path       : ${LOG_PATH}"
echo "[a5a-sh] launching GAP..."

# Launch GAP in the background so we can poll its RSS. -q -b suppress
# banner and prompts; the driver QUITs after writing outcome.g.
gap -o "${CAP_GB}g" -q -b -c 'Read("run_e_plus_5_resolution.g"); QUIT;' \
    > "${LOG_PATH}" 2>&1 &
GAP_PID=$!

echo "[a5a-sh] gap pid        : ${GAP_PID}"

PEAK_RSS_KB=0
SAMPLE_COUNT=0
while kill -0 "${GAP_PID}" 2>/dev/null; do
    # ps RSS column on macOS is in KB.
    RSS_KB="$(ps -o rss= -p "${GAP_PID}" 2>/dev/null | tr -d ' ')"
    if [[ -n "${RSS_KB}" && "${RSS_KB}" -gt "${PEAK_RSS_KB}" ]]; then
        PEAK_RSS_KB="${RSS_KB}"
    fi
    SAMPLE_COUNT=$((SAMPLE_COUNT + 1))
    # Log every Nth sample to avoid flooding the log; every 6 samples =
    # once per minute at the 10 s default.
    if [[ $((SAMPLE_COUNT % 6)) -eq 1 ]]; then
        echo "[a5a-sh] $(date -u +%FT%TZ)  pid ${GAP_PID}  rss = ${RSS_KB} KB  peak = ${PEAK_RSS_KB} KB"
    fi
    sleep "${POLL_SEC}"
done

# Wait for the process to fully reap (in case it's between the polling
# kill check and exit). Captures exit status. `set -e` would abort on a
# non-zero wait exit, so guard with `|| true` and capture via $?.
EXIT_CODE=0
wait "${GAP_PID}" || EXIT_CODE=$?

PEAK_RSS_MB="$(awk -v kb="${PEAK_RSS_KB}" 'BEGIN { printf "%.2f", kb / 1024.0 }')"
echo "${PEAK_RSS_MB}" > "${PEAK_RSS_PATH}"

echo "[a5a-sh] gap exited with code ${EXIT_CODE}"
echo "[a5a-sh] peak rss       : ${PEAK_RSS_MB} MB  (${PEAK_RSS_KB} KB)"

if [[ -f "${OUTCOME_PATH}" ]]; then
    # GAP wrote an outcome. Patch peak_rss_mb in place.
    # The driver writes  `    peak_rss_mb      := "unknown",`
    # so we substitute that literal exact line.
    python3 - "${OUTCOME_PATH}" "${PEAK_RSS_MB}" <<'PYEOF'
import sys
path, peak = sys.argv[1], sys.argv[2]
with open(path, "r") as f:
    src = f.read()
needle = '    peak_rss_mb      := "unknown",'
replacement = f'    peak_rss_mb      := {peak},'
if needle not in src:
    print(f"[a5a-sh] warning: did not find '{needle}' in {path}; leaving peak_rss_mb as-is")
    sys.exit(0)
src = src.replace(needle, replacement, 1)
with open(path, "w") as f:
    f.write(src)
print(f"[a5a-sh] patched peak_rss_mb = {peak} into outcome.g")
PYEOF
    echo "[a5a-sh] outcome.g present; wrapper exiting normally."
    exit 0
else
    # GAP did not write outcome.g; assume out-of-process failure
    # (OOM-kill, SIGTERM, segfault, etc.). Synthesise a failure outcome
    # so dp_ii_dispatch.g still has a record to branch on.
    case "${EXIT_CODE}" in
        137) ERR_MSG="killed: SIGKILL (likely OOM)" ;;
        143) ERR_MSG="killed: SIGTERM" ;;
        139) ERR_MSG="segfault" ;;
        *)   ERR_MSG="exit ${EXIT_CODE} without writing outcome.g" ;;
    esac

    cat > "${OUTCOME_PATH}" <<EOF
# Resolution outcome synthesised by run_e_plus_5_resolution.sh
# because the GAP process exited without writing one (issue #46 A-5a).
# Exit code was ${EXIT_CODE}; peak RSS observed by the wrapper.
return rec(
    group_label      := "E_+(5)",
    group_order      := 2048,
    resolution_arity := 4,
    success          := false,
    wall_clock_sec   := -1.0,
    gap_heap_mb      := -1.0,
    peak_rss_mb      := ${PEAK_RSS_MB},
    error_msg        := "${ERR_MSG}",
    started_at       := "$(date -u +%FT%TZ)"
);;
EOF
    echo "[a5a-sh] synthesised failure outcome.g (${ERR_MSG})."
    exit 0
fi
