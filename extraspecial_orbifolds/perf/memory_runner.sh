#!/usr/bin/env bash
#
# memory_runner.sh — P-7 memory profile harness (issue #115).
#
# Usage:
#   ./memory_runner.sh <workload_name> [interval_seconds]
#
# Launches the GAP workload at workloads/<workload_name>.g and, every
# `interval_seconds` (default 5), polls `ps -p <PID> -o rss=` and
# appends one JSON sample per line to perf/memory/<workload>.jsonl.
# Stops when GAP exits. Emits a summary line: peak RSS, end RSS, mean.
#
# JSONL sample format (per line):
#   {"t": <unix-seconds>, "rss_kb": <integer-kb>}
#
# macOS `ps -p X -o rss=` reports KB. The summary converts to MB.
#
# This is the memory-axis complement to profile_runner.sh (P-1). It
# uses the same workloads/ convention so the same scripts can be
# profiled by both CPU and memory tooling.

set -uo pipefail

if [[ $# -lt 1 ]]; then
    echo "Usage: $0 <workload_name> [interval_seconds]" >&2
    exit 2
fi

WORKLOAD="$1"
INTERVAL="${2:-5}"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PERF_DIR="$SCRIPT_DIR"
WORKLOAD_FILE="$PERF_DIR/workloads/$WORKLOAD.g"
MEM_DIR="$PERF_DIR/memory"
OUTFILE="$MEM_DIR/$WORKLOAD.jsonl"
LOG_FILE="$MEM_DIR/$WORKLOAD.log"
GAP="${GAP_BIN:-/opt/homebrew/bin/gap}"

if [[ ! -f "$WORKLOAD_FILE" ]]; then
    echo "error: workload file not found: $WORKLOAD_FILE" >&2
    echo "Available workloads:" >&2
    ls "$PERF_DIR/workloads/" 2>&1 | sed 's/^/  /' >&2
    exit 2
fi

mkdir -p "$MEM_DIR"

# Truncate any previous output so each run starts fresh.
: > "$OUTFILE"

echo "=== Memory run: $WORKLOAD (poll every ${INTERVAL}s) ==="
echo "  workload: $WORKLOAD_FILE"
echo "  jsonl:    $OUTFILE"
echo "  log:      $LOG_FILE"
echo "  GAP:      $GAP"
echo ""

T_START=$(date +%s)

# Launch GAP in background.
"$GAP" -q -b "$WORKLOAD_FILE" > "$LOG_FILE" 2>&1 &
GAP_PID=$!
echo "  GAP PID:  $GAP_PID"

# Take an initial sample immediately, then poll on `interval`.
# kill -0 returns 0 iff the process is alive (and we can signal it).
while kill -0 "$GAP_PID" 2>/dev/null; do
    # `ps -p X -o rss=` prints just the RSS (in KB on macOS). The
    # `=` after the column name suppresses the header.
    rss=$(ps -p "$GAP_PID" -o rss= 2>/dev/null | tr -d ' ')
    if [[ -n "$rss" ]]; then
        echo "{\"t\": $(date +%s), \"rss_kb\": $rss}" >> "$OUTFILE"
    fi
    sleep "$INTERVAL"
done

wait "$GAP_PID" 2>/dev/null
GAP_EXIT=$?
T_END=$(date +%s)
WALL=$((T_END - T_START))

# Summary: peak, end, mean (in MB).
if [[ -s "$OUTFILE" ]]; then
    python3 - "$OUTFILE" "$WALL" <<'PY'
import json
import sys

path, wall_s = sys.argv[1], int(sys.argv[2])
rss_kb = []
with open(path) as fh:
    for line in fh:
        line = line.strip()
        if not line:
            continue
        try:
            rss_kb.append(json.loads(line)["rss_kb"])
        except (ValueError, KeyError):
            continue

if not rss_kb:
    print("  (no RSS samples captured)")
    sys.exit(0)

peak_mb = max(rss_kb) / 1024.0
end_mb = rss_kb[-1] / 1024.0
mean_mb = sum(rss_kb) / len(rss_kb) / 1024.0
print(f"  samples:  {len(rss_kb)}")
print(f"  wall_s:   {wall_s}")
print(f"  peak_mb:  {peak_mb:.1f}")
print(f"  end_mb:   {end_mb:.1f}")
print(f"  mean_mb:  {mean_mb:.1f}")
PY
else
    echo "  (no RSS samples captured; GAP may have exited too fast)"
fi

echo ""
echo "  GAP exit: $GAP_EXIT"
echo "  jsonl:    $OUTFILE"
exit "$GAP_EXIT"
