#!/usr/bin/env bash
# Create the remaining workstream issues, all labelled `blocked`.
# Titles taken verbatim from the design doc; bodies extracted from the
# corresponding "### <ID>" sections of
#   extraspecial_orbifolds/parallel_workstreams_design.md.
# bash 3.2-compatible.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

# shellcheck source=./_helpers.sh
source "$(dirname "$0")/_helpers.sh"

# Smoke-test extraction before touching GitHub.
sample=$(extract_issue_body Q-2)
case "$sample" in
  "**Title.**"*) : ;;
  *) echo "Pre-flight check failed: Q-2 body did not start with '**Title.**'" >&2; exit 1 ;;
esac

create_one() {
  local id="$1" title="$2" labels="$3" milestone="$4"
  echo ">>> Creating ${id}"
  create_issue "$id" "$title" "$labels" "$milestone"
}

# ---- Workstream Q (Q-2..Q-8) ----
create_one "Q-2" "[Q-2] Quillen presentation specialised to E_+(m), degrees <= 4" \
           "blocked,math,code" "Workstream Q"
create_one "Q-3" "[Q-3] Bar-resolution cup product on E_+(m) via Frattini abelianisation" \
           "blocked,math,code" "Workstream Q"
create_one "Q-4" "[Q-4] Integral Bockstein at the cochain level" \
           "blocked,math,code" "Workstream Q"
create_one "Q-5" "[Q-5] Universal-coefficient sequence: extract H^*(G; Z) from H^*(G; F_2) and Bockstein" \
           "blocked,math,code" "Workstream Q"
create_one "Q-6" "[Q-6] H^n(G; U(1)) as H^{n+1}(G; Z) at n = 3" \
           "blocked,math,code" "Workstream Q"
create_one "Q-7" "[Q-7] Cocycle representatives: H^3 generators as callables G^3 -> Z/m" \
           "blocked,math,code" "Workstream Q"
create_one "Q-8" "[Q-8] Quillen pipeline cross-check against HAP at m = 2, 3" \
           "blocked,math,code,regression" "Workstream Q"

# ---- Workstream T (T-3b..T-6) ----
create_one "T-3b" "[T-3b] BRW(m) outer-automorphism action on E_+(m)-conjugacy classes" \
           "blocked,code,math" "Workstream T"
create_one "T-3c" "[T-3c] BRW(m) outer-automorphism action on H^3(E_+(m); U(1)) generators" \
           "blocked,code,math" "Workstream T"
create_one "T-3d" "[T-3d] Per-class loop integration: BRW reduction of the transgression evaluation" \
           "blocked,code" "Workstream T"
create_one "T-5"  "[T-5] Resumable run-state for long-running per-generator sweeps" \
           "blocked,code" "Workstream T"
create_one "T-6"  "[T-6] D_8 regression test for the upgraded Tier-4 pipeline" \
           "blocked,regression,code" "Workstream T"

# ---- Workstream V (V-2, V-5b, V-5c, V-6, V-7b) ----
create_one "V-2"  "[V-2] Tier-1 closed-form S-omega entry for central rows" \
           "blocked,code,math" "Workstream V"
create_one "V-5b" "[V-5b] Aut(N, T) engine: colour refinement on fusion-row signatures" \
           "blocked,code,math" "Workstream V"
create_one "V-5c" "[V-5c] Aut(N, T) engine: backtracking with refinement-based pruning" \
           "blocked,code,math" "Workstream V"
create_one "V-6"  "[V-6] Aut(N, T) BRW-quotient mode" \
           "blocked,code,math" "Workstream V"
create_one "V-7b" "[V-7b] Verlinde-on-canonical-blocks: fusion-coefficient query primitive" \
           "blocked,code" "Workstream V"

# ---- Workstream K (K-2, K-3) ----
create_one "K-2" "[K-2] Single-entry S-Keller adapter" \
           "blocked,code" "Workstream K"
create_one "K-3" "[K-3] Cross-check S-Keller vs S-0 closed forms at m = 3" \
           "blocked,regression,code" "Workstream K"

# ---- Workstream A (A-2, A-3a..d, A-5a..d, A-7a, A-7b) ----
create_one "A-2"  "[A-2] E_+(2) Tier-4 SNF closure" \
           "blocked,code" "Workstream A"
create_one "A-3a" "[A-3a] E_+(3) Tier-4 driver: full kernel computation" \
           "blocked,code" "Workstream A"
create_one "A-3b" "[A-3b] DP-I auto-dispatcher: m = 3 outcome -> next-stage selection" \
           "blocked,decision-point,code" "Workstream A"
create_one "A-3c" "[A-3c] E_+(3) Tier-1/5 candidate-elimination loop (conditional)" \
           "blocked,decision-point,code" "Workstream A"
create_one "A-3d" "[A-3d] E_+(3) Tier-3 |Aut(N, T)| cross-validation" \
           "blocked,code" "Workstream A"
create_one "A-5a" "[A-5a] E_+(5) Tier-4 HAP attempt + DP-II auto-dispatcher" \
           "blocked,decision-point,code" "Workstream A"
create_one "A-5b" "[A-5b] E_+(5) Tier-4 driver (HAP route)" \
           "blocked,decision-point,code" "Workstream A"
create_one "A-5c" "[A-5c] E_+(5) Tier-4 driver (Quillen route)" \
           "blocked,decision-point,code" "Workstream A"
create_one "A-5d" "[A-5d] E_+(5) Tier-3 on subset (central + one non-central class)" \
           "blocked,code" "Workstream A"
create_one "A-7a" "[A-7a] E_+(7) Tier-4 driver via Quillen analytical H^3" \
           "blocked,decision-point,code" "Workstream A"
create_one "A-7b" "[A-7b] E_+(7) Tier-1/5 candidate-elimination loop (conditional)" \
           "blocked,decision-point,code" "Workstream A"

# ---- Workstream X (X-1..X-4) ----
create_one "X-1" "[X-1] Q_8 regression suite" \
           "blocked,regression" "Workstream X"
create_one "X-2" "[X-2] D_8 regression suite" \
           "blocked,regression" "Workstream X"
create_one "X-3" "[X-3] E_+(2) regression suite" \
           "blocked,regression" "Workstream X"
create_one "X-4" "[X-4] CI integration: GAP test suite on every push" \
           "blocked,regression,code" "Workstream X"

# ---- Workstream W (W-1b..W-1d, W-2, W-3) ----
create_one "W-1b" "[W-1b] Paper section 3: cross-cutting infrastructure" \
           "blocked,doc" "Workstream W"
create_one "W-1c" "[W-1c] Paper section 4: per-m applications" \
           "blocked,doc" "Workstream W"
create_one "W-1d" "[W-1d] Paper section 5: conclusions and open questions" \
           "blocked,doc" "Workstream W"
create_one "W-2"  "[W-2] Final results tables and figures" \
           "blocked,doc" "Workstream W"
create_one "W-3"  "[W-3] Reproducibility appendix" \
           "blocked,doc" "Workstream W"

echo "Remaining (blocked) issue creation complete."
