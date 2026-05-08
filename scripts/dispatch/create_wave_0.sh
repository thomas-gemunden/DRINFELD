#!/usr/bin/env bash
# Create the 14 Wave-0 ready-now issues.
# Each is labelled `ready` plus its attribute labels.
# Bodies extracted from extraspecial_orbifolds/parallel_workstreams_design.md.
# bash 3.2-compatible.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

# shellcheck source=./_helpers.sh
source "$(dirname "$0")/_helpers.sh"

# Smoke-test extraction before touching GitHub.
sample=$(extract_issue_body Q-1)
case "$sample" in
  "**Title.**"*) : ;;
  *) echo "Pre-flight check failed: Q-1 body did not start with '**Title.**'" >&2; exit 1 ;;
esac

# create_one ID 'Title' 'labels' 'Milestone'
create_one() {
  local id="$1" title="$2" labels="$3" milestone="$4"
  echo ">>> Creating ${id}"
  create_issue "$id" "$title" "$labels" "$milestone"
}

create_one "Q-1"   "[Q-1] Polynomial-times-exterior algebra data structure (F_2 coefficients)" \
           "ready,code,math" "Workstream Q"
create_one "Q-9"   "[Q-9] Detecting-subgroup variant for H^3(E_+(m); U(1))" \
           "ready,math,code" "Workstream Q"
create_one "T-1"   "[T-1] HAP-native IsCoboundary2 replacing SolutionIntMat-augmented baseline" \
           "ready,code,regression" "Workstream T"
create_one "T-2"   "[T-2] SNF wrapper for transgression matrix" \
           "ready,code,regression" "Workstream T"
create_one "T-3a"  "[T-3a] Explicit BRW(m) construction as a matrix subgroup of O(2^m, R)" \
           "ready,code,math" "Workstream T"
create_one "T-4"   "[T-4] Centraliser-type caching: persist HAP resolutions per centraliser type" \
           "ready,code" "Workstream T"
create_one "V-1"   "[V-1] Tier-1 epsilon-omega phase callable, CGR convention" \
           "ready,code,math" "Workstream V"
create_one "V-3"   "[V-3] Tier-5 FSIforDoubles thin wrapper for one-shot queries" \
           "ready,code,regression" "Workstream V"
create_one "V-4"   "[V-4] Fix GaugeInvariants undeclared-locals bug" \
           "ready,code" "Workstream V"
create_one "V-5a"  "[V-5a] Aut(N, T) engine: T-block + dimension partition" \
           "ready,code,math" "Workstream V"
create_one "V-7a"  "[V-7a] Single-S-entry primitive from canonical-block storage" \
           "ready,code" "Workstream V"
create_one "V-8"   "[V-8] Fix FSIforAGT parser errors" \
           "ready,code" "Workstream V"
create_one "K-1"   "[K-1] Implement projector formula KRR24 eq (2.1.2)" \
           "ready,code,math" "Workstream K"
create_one "W-1a"  "[W-1a] Methodology paper outline + introduction draft" \
           "ready,doc" "Workstream W"

echo "Wave-0 issue creation complete."
