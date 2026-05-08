#!/usr/bin/env bash
# Create the 7 workstream epic meta-issues.
# Bodies reference parallel_workstreams_design.md by section.
# Compatible with bash 3.2 (no associative arrays).
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

DESIGN_DOC="extraspecial_orbifolds/parallel_workstreams_design.md"

epic_name() {
  case "$1" in
    Q) echo "Quillen analytical H^3 pipeline" ;;
    T) echo "Transgression-kernel infrastructure" ;;
    V) echo "Validators for Tiers 1, 3, 5" ;;
    K) echo "KRR pipeline to S-entry adapter" ;;
    A) echo "Application sweeps for E_+(m) at m = 2, 3, 5, 7" ;;
    X) echo "Cross-checks and regression" ;;
    W) echo "Methodology paper / writeup synthesis" ;;
  esac
}

epic_section() {
  case "$1" in
    Q) echo "5.1" ;; T) echo "6.1" ;; V) echo "7.1" ;;
    K) echo "8.1" ;; A) echo "9.1" ;; X) echo "10.1" ;;
    W) echo "11.1" ;;
  esac
}

for ws in Q T V K A X W; do
  title="[${ws}-EPIC] $(epic_name "$ws")"
  body="See \`${DESIGN_DOC}\` §$(epic_section "$ws").

This is a tracking issue for workstream ${ws}. It closes when every leaf issue in the workstream closes."
  gh issue create \
    --title "$title" \
    --body "$body" \
    --label "in progress,epic" \
    --milestone "Workstream ${ws}"
done
