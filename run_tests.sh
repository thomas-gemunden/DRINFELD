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
SKIP_SLOW=(
    "test_quillen_vs_hap.g"
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

for t in "${TESTS[@]}"; do
    base=$(basename "$t")
    name="${base%.g}"
    log="/tmp/${name}.log"

    if [[ "$FAST" = "1" ]] && is_slow "$base"; then
        echo "SKIP  $name"
        SKIP=$((SKIP + 1))
        continue
    fi

    echo "RUN   $name"
    if "${GAP_BIN}" -q -b "$t" > "$log" 2>&1; then
        echo "PASS  $name"
        PASS=$((PASS + 1))
    else
        echo "FAIL  $name"
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
