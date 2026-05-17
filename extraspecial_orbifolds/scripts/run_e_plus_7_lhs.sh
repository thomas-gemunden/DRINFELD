#!/usr/bin/env bash
# run_e_plus_7_lhs.sh — wrapper around run_e_plus_7_lhs.g for issue #238.
#
# Same shape as run_e_plus_5_resolution.sh: launches the GAP driver,
# polls the process's RSS at a fixed interval, and patches peak_rss_mb
# into the outcome.g file on completion. On out-of-process failure
# (OOM-kill, SIGTERM, etc.) the wrapper synthesises a failure outcome so
# downstream m=7 drivers still have a record to branch on.
#
# Usage (from extraspecial_orbifolds/scripts/):
#   ./run_e_plus_7_lhs.sh [memory_cap_gb] [poll_interval_sec]
#
# Defaults: 16 GB cap (LHS resolution at m=7 fits in ~200 MB, so this
# is generous), 10 s poll interval.

set -euo pipefail

CAP_GB="${1:-16}"
POLL_SEC="${2:-10}"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
OUTCOME_DIR="${REPO_ROOT}/computed/transgression/7"
OUTCOME_PATH="${OUTCOME_DIR}/lhs_resolution_outcome.g"
LOG_PATH="${OUTCOME_DIR}/lhs_resolution.log"
PEAK_RSS_PATH="${OUTCOME_DIR}/lhs_peak_rss.txt"

mkdir -p "${OUTCOME_DIR}"

# Remove any stale outcome from a prior run so we can detect whether the
# current attempt wrote one.
rm -f "${OUTCOME_PATH}" "${PEAK_RSS_PATH}"

cd "${SCRIPT_DIR}"

echo "[c2-sh] memory cap     : ${CAP_GB}g"
echo "[c2-sh] poll interval  : ${POLL_SEC}s"
echo "[c2-sh] outcome path   : ${OUTCOME_PATH}"
echo "[c2-sh] log path       : ${LOG_PATH}"
echo "[c2-sh] launching GAP..."

# Choose a gap binary the same way run_tests.sh does.
if command -v gap >/dev/null 2>&1; then
    GAP_BIN="gap"
elif [[ -x /opt/homebrew/bin/gap ]]; then
    GAP_BIN="/opt/homebrew/bin/gap"
elif [[ -x /usr/local/bin/gap ]]; then
    GAP_BIN="/usr/local/bin/gap"
else
    echo "[c2-sh] ERROR: no 'gap' binary found." >&2
    exit 2
fi
echo "[c2-sh] gap binary     : ${GAP_BIN}"

# Launch GAP in the background.
"${GAP_BIN}" -o "${CAP_GB}g" -q -b \
    -c 'Read("run_e_plus_7_lhs.g"); QUIT;' \
    > "${LOG_PATH}" 2>&1 &
GAP_PID=$!

echo "[c2-sh] gap pid        : ${GAP_PID}"

PEAK_RSS_KB=0
SAMPLE_COUNT=0
while kill -0 "${GAP_PID}" 2>/dev/null; do
    RSS_KB="$(ps -o rss= -p "${GAP_PID}" 2>/dev/null | tr -d ' ')"
    if [[ -n "${RSS_KB}" && "${RSS_KB}" -gt "${PEAK_RSS_KB}" ]]; then
        PEAK_RSS_KB="${RSS_KB}"
    fi
    SAMPLE_COUNT=$((SAMPLE_COUNT + 1))
    if [[ $((SAMPLE_COUNT % 6)) -eq 1 ]]; then
        echo "[c2-sh] $(date -u +%FT%TZ)  pid ${GAP_PID}  rss = ${RSS_KB} KB  peak = ${PEAK_RSS_KB} KB"
    fi
    sleep "${POLL_SEC}"
done

EXIT_CODE=0
wait "${GAP_PID}" || EXIT_CODE=$?

PEAK_RSS_MB="$(awk -v kb="${PEAK_RSS_KB}" 'BEGIN { printf "%.2f", kb / 1024.0 }')"
echo "${PEAK_RSS_MB}" > "${PEAK_RSS_PATH}"

echo "[c2-sh] gap exited with code ${EXIT_CODE}"
echo "[c2-sh] peak rss       : ${PEAK_RSS_MB} MB  (${PEAK_RSS_KB} KB)"

if [[ -f "${OUTCOME_PATH}" ]]; then
    # GAP wrote an outcome. Patch peak_rss_mb in place. The driver writes
    #   `    peak_rss_mb         := "unknown",`
    python3 - "${OUTCOME_PATH}" "${PEAK_RSS_MB}" <<'PYEOF'
import sys
path, peak = sys.argv[1], sys.argv[2]
with open(path, "r") as f:
    src = f.read()
needle = '    peak_rss_mb         := "unknown",'
replacement = f'    peak_rss_mb         := {peak},'
if needle not in src:
    print(f"[c2-sh] warning: did not find '{needle}' in {path}; "
          f"leaving peak_rss_mb as-is")
    sys.exit(0)
src = src.replace(needle, replacement, 1)
with open(path, "w") as f:
    f.write(src)
print(f"[c2-sh] patched peak_rss_mb = {peak} into outcome.g")
PYEOF
    echo "[c2-sh] outcome.g present; wrapper exiting normally."
    exit 0
else
    case "${EXIT_CODE}" in
        137) ERR_MSG="killed: SIGKILL (likely OOM)" ;;
        143) ERR_MSG="killed: SIGTERM" ;;
        139) ERR_MSG="segfault" ;;
        *)   ERR_MSG="exit ${EXIT_CODE} without writing outcome.g" ;;
    esac

    cat > "${OUTCOME_PATH}" <<EOF
# LHS resolution outcome synthesised by run_e_plus_7_lhs.sh because the
# GAP process exited without writing one (issue #238).
# Exit code was ${EXIT_CODE}; peak RSS observed by the wrapper.
return rec(
    group_label         := "E_+(7)",
    group_order         := 32768,
    resolution_arity    := 5,
    builder             := "abelian",
    success             := false,
    wall_clock_sec      := -1.0,
    build_time_V_sec    := -1.0,
    build_time_LHS_sec  := -1.0,
    gap_heap_mb         := -1.0,
    peak_rss_mb         := ${PEAK_RSS_MB},
    R_V_dims            := [],
    R_E_dims            := [],
    H3_value            := [],
    H3_pretty           := "",
    H4_value            := [],
    H4_pretty           := "",
    error_msg           := "${ERR_MSG}",
    started_at          := "$(date -u +%FT%TZ)"
);;
EOF
    echo "[c2-sh] synthesised failure outcome.g (${ERR_MSG})."
    exit 0
fi
