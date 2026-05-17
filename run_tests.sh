#!/usr/bin/env bash
#
# Regression test runner for the extraspecial_orbifolds GAP suite.
#
# Usage:
#   ./run_tests.sh           # run every test_*.g under tests/
#   FAST=1 ./run_tests.sh    # skip slow / heavy tests (used by CI)
#
# Exits 0 if every test passed, 1 otherwise.

set -uo pipefail

# Resolve the directory containing this script, then cd into the scripts
# directory that owns tests/.
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "${SCRIPT_DIR}/extraspecial_orbifolds/scripts"

FAST="${FAST:-0}"

# Choose a gap binary. Prefer one on PATH (CI / Linux) and fall back to
# the macOS Homebrew install location for local dev.
if command -v gap >/dev/null 2>&1; then
    GAP_BIN="gap"
elif [[ -x /opt/homebrew/bin/gap ]]; then
    GAP_BIN="/opt/homebrew/bin/gap"
elif [[ -x /usr/local/bin/gap ]]; then
    GAP_BIN="/usr/local/bin/gap"
else
    echo "ERROR: no 'gap' binary found on PATH or in standard locations." >&2
    exit 2
fi

echo "Using GAP at: ${GAP_BIN}"
echo "FAST=${FAST}"
echo

# Tests that are too slow / heavy for CI under FAST=1.
# test_quillen_vs_hap.g is gated by Q8_INCLUDE_M3 (cross-check against HAP).
# test_krr_spectral_characters_sparse.g runs the m=5 build (~23 min wall) by
#   default; FAST=1 skips this test entirely. To exercise only the m=3 anchor
#   without skipping, set SPARSE_SKIP_M5 := true; in the GAP session.
SKIP_SLOW=(
    "test_quillen_vs_hap.g"
    "test_krr_spectral_characters_sparse.g"
)

is_slow() {
    local name="$1"
    local s
    for s in "${SKIP_SLOW[@]}"; do
        if [[ "$s" == "$name" ]]; then
            return 0
        fi
    done
    return 1
}

PASS=0
FAIL=0
SKIP=0
FAILED_TESTS=()

shopt -s nullglob
TESTS=(tests/test_*.g)
shopt -u nullglob

if [[ ${#TESTS[@]} -eq 0 ]]; then
    echo "ERROR: no test files found under $(pwd)/tests/" >&2
    exit 2
fi

# Per-test wall-time recording. P-8 (#116) writes /tmp/<name>.timing
# (a single decimal number = seconds) so a downstream `compare_timings.py`
# can flag regressions against `extraspecial_orbifolds/perf/test_baselines.json`.
TIMING_DIR="${TIMING_DIR:-/tmp}"

for t in "${TESTS[@]}"; do
    base=$(basename "$t")
    name="${base%.g}"
    log="${TIMING_DIR}/${name}.log"
    timing="${TIMING_DIR}/${name}.timing"

    if [[ "$FAST" = "1" ]] && is_slow "$base"; then
        echo "SKIP  $name"
        SKIP=$((SKIP + 1))
        continue
    fi

    echo "RUN   $name"
    # `date +%s.%N` -- macOS may not support nanoseconds. Fall back to %s.
    t_start=$(python3 -c 'import time; print("%.3f" % time.time())' 2>/dev/null || date +%s)
    if "${GAP_BIN}" -q -b "$t" > "$log" 2>&1; then
        t_end=$(python3 -c 'import time; print("%.3f" % time.time())' 2>/dev/null || date +%s)
        wall=$(python3 -c "print('%.3f' % ($t_end - $t_start))" 2>/dev/null \
               || echo "$((t_end - t_start))")
        printf "%s\n" "$wall" > "$timing"
        echo "PASS  $name  (${wall} s)"
        PASS=$((PASS + 1))
    else
        t_end=$(python3 -c 'import time; print("%.3f" % time.time())' 2>/dev/null || date +%s)
        wall=$(python3 -c "print('%.3f' % ($t_end - $t_start))" 2>/dev/null \
               || echo "$((t_end - t_start))")
        echo "FAIL  $name  (${wall} s)"
        FAIL=$((FAIL + 1))
        FAILED_TESTS+=("$name")
        echo "---- last 20 lines of $log ----"
        tail -20 "$log"
        echo "---- end $log ----"
    fi
done

echo
echo "Summary: ${PASS} passed, ${FAIL} failed, ${SKIP} skipped (total ${#TESTS[@]})."
if [[ $FAIL -gt 0 ]]; then
    echo "Failed:"
    for n in "${FAILED_TESTS[@]}"; do
        echo "  - $n"
    done
    exit 1
fi
exit 0
