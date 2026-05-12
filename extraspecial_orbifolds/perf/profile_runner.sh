#!/usr/bin/env bash
#
# profile_runner.sh — P-1 profile harness.
#
# Usage:
#   ./profile_runner.sh <workload_name> [seconds]
#
# Launches the GAP workload at workloads/<workload_name>.g, samples its
# process for `seconds` seconds (default 30), and writes a markdown
# report to reports/<workload_name>.md plus the raw sample output to
# raw/<workload_name>.txt.
#
# The workload script is expected to:
#   - perform real work for at least `seconds` seconds (so the sample
#     captures the hot path),
#   - print a final wall-time line so the harness can record it,
#   - QUIT cleanly when done.
#
# Outputs:
#   raw/<workload>.txt        macOS `sample` output (full)
#   reports/<workload>.md     parsed top-3 hot leaves + the GAP-level
#                             function context (best-effort) and the
#                             workload's reported wall time.

set -uo pipefail

if [[ $# -lt 1 ]]; then
    echo "Usage: $0 <workload_name> [seconds]" >&2
    exit 2
fi

WORKLOAD="$1"
SECS="${2:-30}"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PERF_DIR="$SCRIPT_DIR"
WORKLOAD_FILE="$PERF_DIR/workloads/$WORKLOAD.g"
RAW_FILE="$PERF_DIR/raw/$WORKLOAD.txt"
LOG_FILE="$PERF_DIR/raw/$WORKLOAD.log"
REPORT_FILE="$PERF_DIR/reports/$WORKLOAD.md"
GAP="${GAP_BIN:-/opt/homebrew/bin/gap}"

if [[ ! -f "$WORKLOAD_FILE" ]]; then
    echo "error: workload file not found: $WORKLOAD_FILE" >&2
    echo "Available workloads:" >&2
    ls "$PERF_DIR/workloads/" 2>&1 | sed 's/^/  /' >&2
    exit 2
fi

mkdir -p "$PERF_DIR/raw" "$PERF_DIR/reports"

echo "=== Profile run: $WORKLOAD (sample for ${SECS}s) ==="
echo "  workload: $WORKLOAD_FILE"
echo "  raw:      $RAW_FILE"
echo "  report:   $REPORT_FILE"
echo "  GAP:      $GAP"
echo ""

# Launch GAP in background.
"$GAP" -q -b "$WORKLOAD_FILE" > "$LOG_FILE" 2>&1 &
GAP_PID=$!
echo "  GAP PID:  $GAP_PID"

# Brief warm-up so GAP gets past package loads before we start sampling.
sleep 5

# Run sample. If the GAP process exits before sample completes, sample
# returns gracefully and we keep going.
sample "$GAP_PID" "$SECS" -file "$RAW_FILE" 2>&1 | tail -3 || true

# Wait for GAP to finish (it may still be running after sample).
wait "$GAP_PID" 2>/dev/null
GAP_EXIT=$?

# Parse the sample output into a markdown report.
python3 "$PERF_DIR/parse_sample.py" \
    --raw "$RAW_FILE" \
    --log "$LOG_FILE" \
    --workload "$WORKLOAD" \
    --secs "$SECS" \
    --gap-exit "$GAP_EXIT" \
    --out "$REPORT_FILE"

echo ""
echo "  GAP exit: $GAP_EXIT"
echo "  report:   $REPORT_FILE"
exit "$GAP_EXIT"
