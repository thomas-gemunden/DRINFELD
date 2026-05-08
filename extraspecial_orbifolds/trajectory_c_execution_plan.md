# Trajectory C Execution Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Convert `parallel_workstreams_design.md` into ~55 GitHub issues in the `thomas-gemunden/DRINFELD` repository, with labels, milestones, and a project board, so that 14+ agents can begin Wave 0 work in parallel.

**Architecture:** Three phases. (1) Repo machinery: status / attribute labels and per-workstream milestones. (2) Issue creation: epics first, then leaf issues, all via `gh issue create` with bodies sourced verbatim from the design doc. (3) A fully-detailed TDD-step plan for issue T-1 that any agent picking up an issue should follow as a template.

**Tech Stack:** GitHub CLI (`gh`), bash, GAP 4.14+ with HAP and IO packages (already a project dependency).

---

## File structure

| File | Purpose | Status |
|---|---|---|
| `extraspecial_orbifolds/parallel_workstreams_design.md` | Source of truth: 55 issue specs, 7 epics, dependency table | Exists |
| `extraspecial_orbifolds/trajectory_c_execution_plan.md` | This document | Created in this plan |
| `.github/ISSUE_TEMPLATE/workstream-issue.md` | Issue template enforcing the §4 schema | Created in Task 4 |
| `scripts/dispatch/create_epics.sh` | Bulk-create the 7 epic issues | Created in Task 5 |
| `scripts/dispatch/create_wave_0.sh` | Bulk-create the 14 Wave-0 issues | Created in Task 6 |
| `scripts/dispatch/create_remaining.sh` | Bulk-create the remaining ~34 issues | Created in Task 7 |
| `scripts/dispatch/dependency_graph.json` | Machine-readable dependency table | Created in Task 8 |
| `scripts/dispatch/relabel_on_close.sh` | Auto-`blocked → ready` transition on dependency closure | Created in Task 9 |
| `docs/superpowers/plans/2026-05-08-issue-T-1-tdd.md` | Worked TDD example for T-1 (template for agents) | Created in Task 10 |

All `scripts/dispatch/` files live in the DRINFELD repo (not in the parent `group_cohomology/` directory, which is not a git repo). Per CLAUDE.md, all `git` operations run from inside `DRINFELD/`.

---

## Task 1: Verify repo state and gh authentication

**Files:** none modified.

- [ ] **Step 1: Verify repo and remote**

Run: `cd /Users/thomasgemunden/Projects/group_cohomology/DRINFELD && git remote -v`

Expected output containing `origin\thttps://github.com/thomas-gemunden/DRINFELD`.

- [ ] **Step 2: Verify gh authentication**

Run: `gh auth status`

Expected: `Logged in to github.com account thomas-gemunden`. If not, run `gh auth login` interactively.

- [ ] **Step 3: Verify repo accessibility via gh**

Run: `gh repo view thomas-gemunden/DRINFELD --json name,owner -q '.name + " " + .owner.login'`

Expected: `DRINFELD thomas-gemunden`.

- [ ] **Step 4: Verify clean working tree**

Run: `git -C /Users/thomasgemunden/Projects/group_cohomology/DRINFELD status --short`

Expected: empty output (or only the design doc additions). If unexpected files appear, investigate before proceeding.

---

## Task 2: Create status and attribute labels

**Files:** none (GitHub-side state only).

- [ ] **Step 1: Create status labels (mutually exclusive)**

Run from inside `DRINFELD/`:

```bash
gh label create "ready"               --color "0E8A16" --description "All deps resolved; pickup-able now"
gh label create "in progress"         --color "FBCA04" --description "Claimed by an agent"
gh label create "blocked"             --color "B60205" --description "Has open upstream dependency"
gh label create "requires user input" --color "5319E7" --description "Needs human adjudication"
```

Expected: each command prints the label ID; no errors.

- [ ] **Step 2: Create attribute labels (independent)**

```bash
gh label create "epic"            --color "1D76DB" --description "Workstream meta-issue"
gh label create "math"            --color "0075CA" --description "Primarily mathematical work"
gh label create "code"            --color "008672" --description "Primarily implementation work"
gh label create "doc"             --color "D4C5F9" --description "Primarily documentation work"
gh label create "regression"      --color "FEF2C0" --description "Test/validation against ground truth"
gh label create "decision-point"  --color "E99695" --description "Triggers a branch in the trajectory"
```

- [ ] **Step 3: Verify all 10 labels exist**

Run: `gh label list --limit 100 | grep -E '^(ready|in progress|blocked|requires user input|epic|math|code|doc|regression|decision-point)\b' | wc -l`

Expected: `10`.

- [ ] **Step 4: Commit (no file changes; tag the milestone in repo history)**

```bash
cd /Users/thomasgemunden/Projects/group_cohomology/DRINFELD
git commit --allow-empty -m "chore(repo): create issue status and attribute labels"
```

---

## Task 3: Create per-workstream milestones

**Files:** none (GitHub-side state only).

- [ ] **Step 1: Create one milestone per workstream**

```bash
for ws in Q T V K A X W; do
  gh api repos/thomas-gemunden/DRINFELD/milestones \
    -f title="Workstream $ws" \
    -f description="See parallel_workstreams_design.md §$( case $ws in Q) echo 5;; T) echo 6;; V) echo 7;; K) echo 8;; A) echo 9;; X) echo 10;; W) echo 11;; esac )"
done
```

Expected: 7 JSON objects printed, one per milestone.

- [ ] **Step 2: Verify milestone count**

Run: `gh api repos/thomas-gemunden/DRINFELD/milestones | jq 'length'`

Expected: `7`.

---

## Task 4: Create the workstream issue template

**Files:**
- Create: `.github/ISSUE_TEMPLATE/workstream-issue.md`

- [ ] **Step 1: Write the template file**

Create `.github/ISSUE_TEMPLATE/workstream-issue.md` with the contents:

```markdown
---
name: Workstream issue
about: Use when manually creating an issue from parallel_workstreams_design.md
title: "[<workstream>-<id>] <title>"
labels: ["ready"]
---

**Workstream.** <Q | T | V | K | A | X | W> — <name>

**Background.**
<2–4 paragraphs>

**Goal.**
<single sentence>

**Acceptance criteria.**
- <bullet>

**Dependencies.**
- <list of upstream issue IDs>

**Estimated effort.**
<days>

**Files likely affected.**
- <paths>

**Out of scope.**
- <non-goals>
```

- [ ] **Step 2: Commit**

```bash
cd /Users/thomasgemunden/Projects/group_cohomology/DRINFELD
mkdir -p .github/ISSUE_TEMPLATE
git add .github/ISSUE_TEMPLATE/workstream-issue.md
git commit -m "chore(repo): add workstream issue template"
```

- [ ] **Step 3: Push**

```bash
git push origin HEAD
```

---

## Task 5: Create the 7 epic meta-issues

**Files:**
- Create: `scripts/dispatch/create_epics.sh`

- [ ] **Step 1: Write the bulk-creation script**

Create `scripts/dispatch/create_epics.sh`:

```bash
#!/usr/bin/env bash
# Create the 7 workstream epic meta-issues.
# Bodies are extracted from extraspecial_orbifolds/parallel_workstreams_design.md.
set -euo pipefail

DESIGN_DOC="extraspecial_orbifolds/parallel_workstreams_design.md"

declare -A EPICS=(
  [Q]="Quillen analytical H^3 pipeline"
  [T]="Transgression-kernel infrastructure"
  [V]="Validators for Tiers 1, 3, 5"
  [K]="KRR pipeline to S-entry adapter"
  [A]="Application sweeps for E_+(m) at m = 2, 3, 5, 7"
  [X]="Cross-checks and regression"
  [W]="Methodology paper / writeup synthesis"
)

for ws in Q T V K A X W; do
  title="[${ws}-EPIC] ${EPICS[$ws]}"
  body="See \`${DESIGN_DOC}\` §$(case $ws in Q) echo 5.1;; T) echo 6.1;; V) echo 7.1;; K) echo 8.1;; A) echo 9.1;; X) echo 10.1;; W) echo 11.1;; esac).

This is a tracking issue for workstream ${ws}. It closes when every leaf issue in the workstream closes."
  gh issue create \
    --title "$title" \
    --body "$body" \
    --label "in progress,epic" \
    --milestone "Workstream ${ws}"
done
```

- [ ] **Step 2: Make it executable and run it**

```bash
cd /Users/thomasgemunden/Projects/group_cohomology/DRINFELD
chmod +x scripts/dispatch/create_epics.sh
./scripts/dispatch/create_epics.sh
```

Expected: 7 issue URLs printed.

- [ ] **Step 3: Verify**

Run: `gh issue list --label epic --json number,title -q '.[] | "#\(.number) \(.title)"'`

Expected: 7 lines, one per epic.

- [ ] **Step 4: Record the epic issue numbers**

Capture the GitHub issue numbers (they will be `#1`–`#7` if the repo is empty, or higher otherwise) and save to a local file for reference:

```bash
gh issue list --label epic --json number,title -q '.[] | "\(.number) \(.title)"' \
  > scripts/dispatch/epic_numbers.txt
```

- [ ] **Step 5: Commit**

```bash
git add scripts/dispatch/create_epics.sh scripts/dispatch/epic_numbers.txt
git commit -m "chore(dispatch): create workstream epic meta-issues"
git push origin HEAD
```

---

## Task 6: Create the 14 Wave-0 ready-now leaf issues

**Files:**
- Create: `scripts/dispatch/create_wave_0.sh`

- [ ] **Step 1: Write the Wave-0 script**

Create `scripts/dispatch/create_wave_0.sh` with one `gh issue create` invocation per Wave-0 issue. The issue body for each must be sourced from the corresponding subsection of `parallel_workstreams_design.md`.

For brevity, a representative entry is shown below; the full script has 14 such blocks (Q-1, Q-9, T-1, T-2, T-3a, T-4, V-1, V-3, V-4, V-5a, V-7a, V-8, K-1, W-1a). Each block extracts the body from the design doc; see the worked example in `docs/superpowers/plans/2026-05-08-issue-T-1-tdd.md` for the canonical T-1 content.

```bash
#!/usr/bin/env bash
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

extract_issue_body() {
  # Extract the body of an issue from the design doc by anchoring on its § header.
  # Args: issue_id (e.g. "T-1")
  local issue_id="$1"
  awk -v id="### $issue_id\$" '
    $0 ~ id { found=1; next }
    found && /^### / { exit }
    found { print }
  ' extraspecial_orbifolds/parallel_workstreams_design.md
}

create_issue() {
  local issue_id="$1"
  local title="$2"
  local labels="$3"
  local milestone="$4"
  local body
  body=$(extract_issue_body "$issue_id")
  if [ -z "$body" ]; then
    echo "ERROR: empty body for $issue_id" >&2
    return 1
  fi
  gh issue create --title "$title" --body "$body" --label "$labels" --milestone "$milestone"
}

# Wave 0
create_issue "Q-1"  "[Q-1] Polynomial-times-exterior algebra data structure (F_2 coefficients)"     "ready,code,math"          "Workstream Q"
create_issue "Q-9"  "[Q-9] Detecting-subgroup variant for H^3(E_+(m); U(1))"                         "ready,math,code"          "Workstream Q"
create_issue "T-1"  "[T-1] HAP-native IsCoboundary2 replacing SolutionIntMat-augmented baseline"    "ready,code,regression"    "Workstream T"
create_issue "T-2"  "[T-2] SNF wrapper for transgression matrix"                                     "ready,code,regression"    "Workstream T"
create_issue "T-3a" "[T-3a] Explicit BRW(m) construction as a matrix subgroup of O(2^m, R)"        "ready,code,math"          "Workstream T"
create_issue "T-4"  "[T-4] Centraliser-type caching: persist HAP resolutions per centraliser type" "ready,code"               "Workstream T"
create_issue "V-1"  "[V-1] Tier-1 epsilon-omega phase callable, CGR convention"                    "ready,code,math"          "Workstream V"
create_issue "V-3"  "[V-3] Tier-5 FSIforDoubles thin wrapper for one-shot queries"                 "ready,code,regression"    "Workstream V"
create_issue "V-4"  "[V-4] Fix GaugeInvariants undeclared-locals bug"                              "ready,code"               "Workstream V"
create_issue "V-5a" "[V-5a] Aut(N, T) engine: T-block + dimension partition"                       "ready,code,math"          "Workstream V"
create_issue "V-7a" "[V-7a] Single-S-entry primitive from canonical-block storage"                 "ready,code"               "Workstream V"
create_issue "V-8"  "[V-8] Fix FSIforAGT parser errors"                                            "ready,code"               "Workstream V"
create_issue "K-1"  "[K-1] Implement projector formula KRR24 eq (2.1.2)"                          "ready,code,math"          "Workstream K"
create_issue "W-1a" "[W-1a] Methodology paper outline + introduction draft"                       "ready,doc"                "Workstream W"
```

- [ ] **Step 2: Test the body-extraction function on T-1 in isolation**

```bash
cd /Users/thomasgemunden/Projects/group_cohomology/DRINFELD
chmod +x scripts/dispatch/create_wave_0.sh
bash -c 'source scripts/dispatch/create_wave_0.sh; extract_issue_body "T-1" | head -30'
```

Expected: the first 30 lines of the T-1 issue body, starting with `**Title.** [T-1] HAP-native IsCoboundary2…`.

If the output is empty, the awk regex anchor needs adjustment for the actual heading style in the design doc.

- [ ] **Step 3: Run the Wave-0 creation script**

```bash
./scripts/dispatch/create_wave_0.sh
```

Expected: 14 issue URLs printed.

- [ ] **Step 4: Verify**

```bash
gh issue list --label ready --milestone "Workstream Q" --json number | jq 'length'  # 2 (Q-1, Q-9)
gh issue list --label ready --milestone "Workstream T" --json number | jq 'length'  # 4 (T-1, T-2, T-3a, T-4)
gh issue list --label ready --milestone "Workstream V" --json number | jq 'length'  # 6 (V-1, V-3, V-4, V-5a, V-7a, V-8)
gh issue list --label ready --milestone "Workstream K" --json number | jq 'length'  # 1 (K-1)
gh issue list --label ready --milestone "Workstream W" --json number | jq 'length'  # 1 (W-1a)
```

Total: 14.

- [ ] **Step 5: Commit**

```bash
git add scripts/dispatch/create_wave_0.sh
git commit -m "chore(dispatch): create Wave-0 ready-now issues"
git push origin HEAD
```

---

## Task 7: Create the remaining ~34 leaf issues (initially `blocked`)

**Files:**
- Create: `scripts/dispatch/create_remaining.sh`

- [ ] **Step 1: Write the bulk-creation script**

The script has the same structure as `create_wave_0.sh` but creates the issues whose dependency table entries (design doc §12) include at least one upstream not yet closed. All are labelled `blocked` initially.

```bash
#!/usr/bin/env bash
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
source scripts/dispatch/create_wave_0.sh  # reuse extract_issue_body, create_issue

# Workstream Q (downstream)
create_issue "Q-2"  "[Q-2] Quillen presentation specialised to E_+(m), degrees <= 4"                "blocked,math,code"        "Workstream Q"
create_issue "Q-3"  "[Q-3] Bar-resolution cup product on E_+(m) via Frattini abelianisation"        "blocked,math,code"        "Workstream Q"
create_issue "Q-4"  "[Q-4] Integral Bockstein at the cochain level"                                  "blocked,math,code"        "Workstream Q"
create_issue "Q-5"  "[Q-5] Universal-coefficient sequence: extract H^*(G; Z) from H^*(G; F_2) and Bockstein" "blocked,math,code" "Workstream Q"
create_issue "Q-6"  "[Q-6] H^n(G; U(1)) as H^{n+1}(G; Z) at n = 3"                                  "blocked,math,code"        "Workstream Q"
create_issue "Q-7"  "[Q-7] Cocycle representatives: H^3 generators as callables G^3 -> Z/m"         "blocked,math,code"        "Workstream Q"
create_issue "Q-8"  "[Q-8] Quillen pipeline cross-check against HAP at m = 2, 3"                    "blocked,regression,math,code" "Workstream Q"

# Workstream T (downstream)
create_issue "T-3b" "[T-3b] BRW(m) outer-automorphism action on E_+(m)-conjugacy classes"          "blocked,code,math"        "Workstream T"
create_issue "T-3c" "[T-3c] BRW(m) outer-automorphism action on H^3(E_+(m); U(1)) generators"      "blocked,code,math"        "Workstream T"
create_issue "T-3d" "[T-3d] Per-class loop integration: BRW reduction of the transgression evaluation" "blocked,code"          "Workstream T"
create_issue "T-5"  "[T-5] Resumable run-state for long-running per-generator sweeps"               "blocked,code"             "Workstream T"
create_issue "T-6"  "[T-6] D_8 regression test for the upgraded Tier-4 pipeline"                    "blocked,regression,code"  "Workstream T"

# Workstream V (downstream)
create_issue "V-2"  "[V-2] Tier-1 closed-form S^omega entry for central rows"                       "blocked,code,math"        "Workstream V"
create_issue "V-5b" "[V-5b] Aut(N, T) engine: colour refinement on fusion-row signatures"           "blocked,code,math"        "Workstream V"
create_issue "V-5c" "[V-5c] Aut(N, T) engine: backtracking with refinement-based pruning"           "blocked,code,math"        "Workstream V"
create_issue "V-6"  "[V-6] Aut(N, T) BRW-quotient mode"                                             "blocked,code,math"        "Workstream V"
create_issue "V-7b" "[V-7b] Verlinde-on-canonical-blocks: fusion-coefficient query primitive"       "blocked,code"             "Workstream V"

# Workstream K (downstream)
create_issue "K-2"  "[K-2] Single-entry S^Keller adapter"                                           "blocked,code"             "Workstream K"
create_issue "K-3"  "[K-3] Cross-check S^Keller vs S^0 closed forms at m = 3"                       "blocked,regression,code"  "Workstream K"

# Workstream A (downstream)
create_issue "A-2"   "[A-2] E_+(2) Tier-4 SNF closure"                                              "blocked,code"             "Workstream A"
create_issue "A-3a"  "[A-3a] E_+(3) Tier-4 driver: full kernel computation"                         "blocked,code"             "Workstream A"
create_issue "A-3b"  "[A-3b] DP-I auto-dispatcher: m = 3 outcome -> next-stage selection"           "blocked,decision-point,code" "Workstream A"
create_issue "A-3c"  "[A-3c] E_+(3) Tier-1/5 candidate-elimination loop (conditional)"              "blocked,code,decision-point" "Workstream A"
create_issue "A-3d"  "[A-3d] E_+(3) Tier-3 |Aut(N, T)| cross-validation"                            "blocked,code"             "Workstream A"
create_issue "A-5a"  "[A-5a] E_+(5) Tier-4 HAP attempt + DP-II auto-dispatcher"                     "blocked,decision-point,code" "Workstream A"
create_issue "A-5b"  "[A-5b] E_+(5) Tier-4 driver (HAP route)"                                       "blocked,decision-point,code" "Workstream A"
create_issue "A-5c"  "[A-5c] E_+(5) Tier-4 driver (Quillen route)"                                  "blocked,decision-point,code" "Workstream A"
create_issue "A-5d"  "[A-5d] E_+(5) Tier-3 on subset (central + one non-central class)"             "blocked,code"             "Workstream A"
create_issue "A-7a"  "[A-7a] E_+(7) Tier-4 driver via Quillen analytical H^3"                       "blocked,code,decision-point" "Workstream A"
create_issue "A-7b"  "[A-7b] E_+(7) Tier-1/5 candidate-elimination loop (conditional)"              "blocked,code,decision-point" "Workstream A"

# Workstream X (downstream)
create_issue "X-1" "[X-1] Q_8 regression suite"                                                     "blocked,regression"       "Workstream X"
create_issue "X-2" "[X-2] D_8 regression suite"                                                     "blocked,regression"       "Workstream X"
create_issue "X-3" "[X-3] E_+(2) regression suite"                                                  "blocked,regression"       "Workstream X"
create_issue "X-4" "[X-4] CI integration: GAP test suite on every push"                             "blocked,regression,code"  "Workstream X"

# Workstream W (downstream)
create_issue "W-1b" "[W-1b] Paper §3: cross-cutting infrastructure"                                 "blocked,doc"              "Workstream W"
create_issue "W-1c" "[W-1c] Paper §4: per-m applications"                                           "blocked,doc"              "Workstream W"
create_issue "W-1d" "[W-1d] Paper §5: conclusions and open questions"                               "blocked,doc"              "Workstream W"
create_issue "W-2"  "[W-2] Final results tables and figures"                                        "blocked,doc"              "Workstream W"
create_issue "W-3"  "[W-3] Reproducibility appendix"                                                "blocked,doc"              "Workstream W"
```

- [ ] **Step 2: Make executable and run**

```bash
chmod +x scripts/dispatch/create_remaining.sh
./scripts/dispatch/create_remaining.sh
```

Expected: ~38 issue URLs printed.

- [ ] **Step 3: Verify total issue count**

```bash
gh issue list --state open --limit 100 --json number | jq 'length'
```

Expected: 7 (epics) + 14 (Wave 0) + 38 (remaining) = **59**.

- [ ] **Step 4: Commit**

```bash
git add scripts/dispatch/create_remaining.sh
git commit -m "chore(dispatch): create remaining workstream issues (blocked)"
git push origin HEAD
```

---

## Task 8: Persist the dependency graph as machine-readable JSON

**Files:**
- Create: `scripts/dispatch/dependency_graph.json`

- [ ] **Step 1: Write the dependency JSON**

Create `scripts/dispatch/dependency_graph.json` with one entry per leaf issue, listing its upstream dependencies:

```json
{
  "Q-1":  {"deps": []},
  "Q-2":  {"deps": ["Q-1"]},
  "Q-3":  {"deps": ["Q-1"]},
  "Q-4":  {"deps": ["Q-1"]},
  "Q-5":  {"deps": ["Q-2", "Q-4"]},
  "Q-6":  {"deps": ["Q-5"]},
  "Q-7":  {"deps": ["Q-3", "Q-6"]},
  "Q-8":  {"deps": ["Q-7"]},
  "Q-9":  {"deps": []},

  "T-1":  {"deps": []},
  "T-2":  {"deps": []},
  "T-3a": {"deps": []},
  "T-3b": {"deps": ["T-3a"]},
  "T-3c": {"deps": ["T-3a"]},
  "T-3d": {"deps": ["T-2", "T-3b", "T-3c"]},
  "T-4":  {"deps": []},
  "T-5":  {"deps": ["T-2"]},
  "T-6":  {"deps": ["T-1", "T-2", "T-3d", "T-4"]},

  "V-1":  {"deps": []},
  "V-2":  {"deps": ["V-1"]},
  "V-3":  {"deps": []},
  "V-4":  {"deps": []},
  "V-5a": {"deps": []},
  "V-5b": {"deps": ["V-5a"]},
  "V-5c": {"deps": ["V-5b"]},
  "V-6":  {"deps": ["V-5c", "T-3c"]},
  "V-7a": {"deps": []},
  "V-7b": {"deps": ["V-7a"]},
  "V-8":  {"deps": []},

  "K-1":  {"deps": []},
  "K-2":  {"deps": ["K-1"]},
  "K-3":  {"deps": ["K-2", "V-2"]},

  "A-2":   {"deps": ["T-2"]},
  "A-3a":  {"deps": ["T-1", "T-2", "T-3d", "T-4", "T-5"]},
  "A-3b":  {"deps": ["A-3a"]},
  "A-3c":  {"deps": ["A-3b", "V-2", "V-3"]},
  "A-3d":  {"deps": ["V-5c", "V-7b"]},
  "A-5a":  {"deps": ["A-3a"]},
  "A-5b":  {"deps": ["A-5a"]},
  "A-5c":  {"deps": ["A-5a", "Q-7"]},
  "A-5d":  {"deps": ["V-5c", "V-7b", "A-5b"]},
  "A-7a":  {"deps": ["Q-7", "T-1", "T-2", "T-3d", "T-4", "T-5"]},
  "A-7b":  {"deps": ["A-7a", "V-2", "V-3"]},

  "X-1": {"deps": ["V-1", "V-2", "V-3", "V-5c"]},
  "X-2": {"deps": ["T-1", "T-2", "T-3d", "T-4"]},
  "X-3": {"deps": ["T-1", "T-2", "V-1", "V-2", "V-3", "V-5c"]},
  "X-4": {"deps": ["X-1", "X-2", "X-3"]},

  "W-1a": {"deps": []},
  "W-1b": {"deps": ["T-EPIC"]},
  "W-1c": {"deps": ["A-EPIC"]},
  "W-1d": {"deps": ["W-1c"]},
  "W-2":  {"deps": ["A-EPIC"]},
  "W-3":  {"deps": ["A-EPIC", "X-EPIC"]}
}
```

- [ ] **Step 2: Verify the JSON parses**

```bash
jq . scripts/dispatch/dependency_graph.json > /dev/null && echo "ok"
```

Expected: `ok`.

- [ ] **Step 3: Commit**

```bash
git add scripts/dispatch/dependency_graph.json
git commit -m "chore(dispatch): record dependency graph as JSON"
git push origin HEAD
```

---

## Task 9: Auto-relabel-on-close hook

**Files:**
- Create: `scripts/dispatch/relabel_on_close.sh`

- [ ] **Step 1: Write the relabel script**

The script takes a closed issue ID, looks up downstream dependents, and re-labels them `blocked → ready` if all *their* deps are now closed.

```bash
#!/usr/bin/env bash
# Usage: relabel_on_close.sh <closed-issue-id>
# e.g.   relabel_on_close.sh Q-1
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

closed_id="${1:?Usage: $0 <closed-issue-id>}"

graph="scripts/dispatch/dependency_graph.json"

# Find downstream issues that depend on the closed one.
downstream=$(jq -r --arg id "$closed_id" '
  to_entries[] | select(.value.deps | index($id)) | .key
' "$graph")

for dep_id in $downstream; do
  # Check whether all of dep_id's deps are now closed.
  all_deps_closed=true
  while read -r upstream; do
    [[ -z "$upstream" ]] && continue
    state=$(gh issue list --state all --search "in:title [${upstream}]" --json state -q '.[0].state' || true)
    if [ "$state" != "CLOSED" ]; then
      all_deps_closed=false
      break
    fi
  done < <(jq -r --arg id "$dep_id" '.[$id].deps[]' "$graph")

  if [ "$all_deps_closed" = "true" ]; then
    issue_number=$(gh issue list --search "in:title [${dep_id}]" --json number -q '.[0].number')
    gh issue edit "$issue_number" --remove-label "blocked" --add-label "ready"
    echo "Unblocked: $dep_id (issue #${issue_number})"
  fi
done
```

- [ ] **Step 2: Test on a synthetic dry-run**

The function must locate downstream-of-Q-1 from the JSON without needing GitHub state. Test:

```bash
chmod +x scripts/dispatch/relabel_on_close.sh
jq -r --arg id "Q-1" 'to_entries[] | select(.value.deps | index($id)) | .key' scripts/dispatch/dependency_graph.json
```

Expected output: `Q-2`, `Q-3`, `Q-4` (one per line).

- [ ] **Step 3: Commit**

```bash
git add scripts/dispatch/relabel_on_close.sh
git commit -m "chore(dispatch): add auto-relabel-on-close hook"
git push origin HEAD
```

- [ ] **Step 4: Document the workflow in README**

Add a paragraph to `DRINFELD/README.md` explaining: when an agent closes an issue, run `scripts/dispatch/relabel_on_close.sh <issue-id>` to advance dependents from `blocked` to `ready`. Optionally wire to a GitHub Action on issue close (deferred; manual invocation is sufficient initially).

```bash
git add DRINFELD/README.md
git commit -m "docs(readme): document auto-relabel workflow"
git push origin HEAD
```

---

## Task 10: Worked TDD example for issue T-1 (template for agents)

**Files:**
- Create: `docs/superpowers/plans/2026-05-08-issue-T-1-tdd.md`

This is the template that any agent should emulate when picking up *their* issue. It demonstrates the bite-sized step granularity expected for execution.

- [ ] **Step 1: Write the T-1 TDD plan**

Create `docs/superpowers/plans/2026-05-08-issue-T-1-tdd.md`:

````markdown
# Issue T-1 TDD Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:test-driven-development to implement this issue.

**Goal:** Replace the `SolutionIntMat`-augmented `IsCoboundary2` in `scripts/transgression_kernel.g` with a HAP-native variant that reuses the bar-resolution boundary maps.

**Architecture:** New file `scripts/iscoboundary2_hap.g` exporting `IsCoboundary2HAP(H, c, m)` with the same signature as `IsCoboundary2`. Implementation: get `R := ResolutionFiniteGroup(H, 3)`, build the cocycle as a HAP cocycle object, decide via HAP's existing exactness check.

**Tech Stack:** GAP 4.14+, HAP, IO.

---

### Task 1: Failing test on D_8

**Files:**
- Create: `extraspecial_orbifolds/scripts/test_iscoboundary2_hap.g`

- [ ] **Step 1: Write the test driver**

```gap
# Tests IsCoboundary2HAP against IsCoboundary2 baseline on D_8.
# Every input must produce identical Boolean output.
LoadPackage("hap");
Read("transgression_kernel.g");
Read("iscoboundary2_hap.g");

G := DihedralGroup(8);
classes := ConjugacyClasses(G);
testCount := 0;
mismatch := 0;
for i in [1..Length(classes)] do
  gRep := Representative(classes[i]);
  C := Centralizer(G, gRep);
  for omega_v in [[0], [1], [2], [3], [4], [5], [6], [7]] do
    setup := SetupCohomology3(G);
    omega := StandardCocycleOf(setup, omega_v);
    c_g := CGCocycleFunc(omega, gRep);
    a := IsCoboundary2(C, c_g, 8);
    b := IsCoboundary2HAP(C, c_g, 8);
    testCount := testCount + 1;
    if a <> b then
      Print("MISMATCH at class ", i, " omega ", omega_v, ": baseline=", a, " hap=", b, "\n");
      mismatch := mismatch + 1;
    fi;
  od;
od;
Print("Tested ", testCount, " inputs; ", mismatch, " mismatches.\n");
if mismatch > 0 then QUIT_GAP(1); fi;
```

- [ ] **Step 2: Run the test (expected to fail — `IsCoboundary2HAP` not yet defined)**

```bash
cd extraspecial_orbifolds/scripts
gap -q -b -c 'Read("test_iscoboundary2_hap.g");'
```

Expected: GAP error `Variable: 'IsCoboundary2HAP' must have a value`.

- [ ] **Step 3: Commit the failing test**

```bash
git add extraspecial_orbifolds/scripts/test_iscoboundary2_hap.g
git commit -m "test(transgression): add IsCoboundary2HAP regression vs baseline"
```

### Task 2: Minimal implementation

**Files:**
- Create: `extraspecial_orbifolds/scripts/iscoboundary2_hap.g`

- [ ] **Step 1: Write the implementation**

```gap
# HAP-native replacement for IsCoboundary2 using the bar-resolution
# boundary maps already constructed for H.
LoadPackage("hap");

IsCoboundary2HAP := function(H, c, m)
  local R, K, n, cVec, eltsList, i, j;
  R := ResolutionFiniteGroup(H, 3);
  eltsList := AsList(H);
  # Build c as a 2-cochain on the bar resolution by evaluating on
  # the standard pair-of-elements basis.
  cVec := List(eltsList, h1 -> List(eltsList, h2 -> c(h1, h2) mod m));
  # HAP's CocycleOnResolution + IsBoundaryOnResolution decide exactness
  # over the integers mod m. The returned object is fail iff the
  # cochain is a coboundary.
  return HAPIsBoundaryOnResolution(R, cVec, 2, m);
end;
```

(Note: `HAPIsBoundaryOnResolution` is a placeholder; the actual HAP
function names are `Cocycle`, `IsCocycleACoboundary`, or similar.
The implementer should consult HAP's documentation to find the
correct names and signatures.)

- [ ] **Step 2: Re-run the test**

```bash
gap -q -b -c 'Read("test_iscoboundary2_hap.g");'
```

Expected: `Tested 56 inputs; 0 mismatches.` (8 cocycles × 7 conjugacy classes minus collisions.)

If it fails, the implementer must consult HAP's `IsBoundaryOnResolution` / `Cocycle` documentation and adjust the call sequence.

- [ ] **Step 3: Commit the implementation**

```bash
git add extraspecial_orbifolds/scripts/iscoboundary2_hap.g
git commit -m "feat(transgression): implement HAP-native IsCoboundary2"
```

### Task 3: E_+(2) regression

**Files:**
- Modify: `extraspecial_orbifolds/scripts/test_iscoboundary2_hap.g`

- [ ] **Step 1: Extend test to E_+(2)**

Append to the test driver:

```gap
G := SmallGroup(32, 49);  # E_+(2)
# Compare per-generator transgression outputs.
setup := SetupCohomology3(G);
classes := ConjugacyClasses(G);
for i in [1..Length(classes)] do
  gRep := Representative(classes[i]);
  C := Centralizer(G, gRep);
  for genIdx in [1..setup.num_generators] do
    vec := List([1..setup.num_generators], j -> 0);
    vec[genIdx] := 1;
    omega := StandardCocycleOf(setup, vec);
    c_g := CGCocycleFunc(omega, gRep);
    a := IsCoboundary2(C, c_g, setup.exponent);
    b := IsCoboundary2HAP(C, c_g, setup.exponent);
    if a <> b then
      Print("E_+(2) MISMATCH class ", i, " gen ", genIdx, "\n");
      mismatch := mismatch + 1;
    fi;
  od;
od;
```

- [ ] **Step 2: Run extended test**

```bash
gap -q -b -c 'Read("test_iscoboundary2_hap.g");'
```

Expected: `0 mismatches`.

- [ ] **Step 3: Commit**

```bash
git add extraspecial_orbifolds/scripts/test_iscoboundary2_hap.g
git commit -m "test(transgression): extend HAP-native regression to E_+(2)"
```

### Task 4: Wall-clock benchmark at n = 64

**Files:**
- Create: `extraspecial_orbifolds/scripts/bench_iscoboundary2_hap.g`

- [ ] **Step 1: Write the benchmark**

```gap
# Compares wall-clock of IsCoboundary2 vs IsCoboundary2HAP on a
# centraliser of order 64 (E_+(3) non-central).
Read("transgression_kernel.g");
Read("iscoboundary2_hap.g");

G := SmallGroup(128, 2326);
gRep := Representative(ConjugacyClasses(G)[3]);  # a non-central class
C := Centralizer(G, gRep);
Assert(0, Order(C) = 64);

setup := SetupCohomology3(G);
vec := List([1..setup.num_generators], j -> 0); vec[1] := 1;
omega := StandardCocycleOf(setup, vec);
c_g := CGCocycleFunc(omega, gRep);

# Warm both functions
_ := IsCoboundary2(C, c_g, setup.exponent);;
_ := IsCoboundary2HAP(C, c_g, setup.exponent);;

t0 := Runtime();
for i in [1..3] do _ := IsCoboundary2(C, c_g, setup.exponent);; od;
t1 := Runtime() - t0;

t0 := Runtime();
for i in [1..3] do _ := IsCoboundary2HAP(C, c_g, setup.exponent);; od;
t2 := Runtime() - t0;

Print("Baseline: ", t1, " ms / 3 calls = ", t1/3, " ms/call\n");
Print("HAP:      ", t2, " ms / 3 calls = ", t2/3, " ms/call\n");
Print("Ratio:    ", Float(t2)/Float(t1), "\n");
```

- [ ] **Step 2: Run the benchmark**

```bash
gap -q -b -c 'Read("bench_iscoboundary2_hap.g");'
```

Expected: ratio ≤ 0.1 per the issue's acceptance criteria.

- [ ] **Step 3: Commit and post results to the issue**

```bash
git add extraspecial_orbifolds/scripts/bench_iscoboundary2_hap.g
git commit -m "perf(transgression): benchmark HAP-native vs baseline at n=64"
gh issue comment <T-1 issue number> --body "$(cat <<'EOF'
Benchmark results at n=64:

- Baseline: <ms> ms/call
- HAP-native: <ms> ms/call
- Ratio: <ratio> (target ≤ 0.1)

Acceptance criterion 4 met: <yes/no>.
EOF
)"
```

### Task 5: Close the issue

- [ ] **Step 1: Open a PR linking to the issue**

```bash
git push origin HEAD
gh pr create --title "[T-1] HAP-native IsCoboundary2" \
  --body "Closes #<T-1 issue number>." \
  --base main
```

- [ ] **Step 2: Once merged, close the issue and trigger the relabel hook**

```bash
gh issue close <T-1 issue number>
./scripts/dispatch/relabel_on_close.sh T-1
```

Expected: relabel hook reports any newly-`ready` downstream issues. T-1 has dependents in T-3d, T-6, A-3a, X-2, X-3 — most of which require *other* deps too, so the relabel will only flip those whose other deps have also closed.
````

- [ ] **Step 2: Commit the worked example**

```bash
cd /Users/thomasgemunden/Projects/group_cohomology/DRINFELD
mkdir -p docs/superpowers/plans
git add docs/superpowers/plans/2026-05-08-issue-T-1-tdd.md
git commit -m "docs(plans): worked TDD example for T-1 as agent template"
git push origin HEAD
```

- [ ] **Step 3: Link the example from the design doc**

Add a final subsection to `parallel_workstreams_design.md` §15 referencing the T-1 example file as the canonical agent-execution template.

```bash
# Edit extraspecial_orbifolds/parallel_workstreams_design.md to add:
#
# ### 15.1 Per-issue execution template
#
# See `docs/superpowers/plans/2026-05-08-issue-T-1-tdd.md` for the
# canonical TDD template every agent should follow when picking up
# their issue.

git add extraspecial_orbifolds/parallel_workstreams_design.md
git commit -m "docs(design): link T-1 TDD example as agent template"
git push origin HEAD
```

---

## Task 11: Dispatch handoff and monitoring

**Files:** none (operational task).

- [ ] **Step 1: Verify all 14 Wave-0 issues are visible to the GitHub UI**

```bash
gh issue list --label ready --json number,title,labels -q '.[] | "#\(.number) \(.title) [\(.labels | map(.name) | join(", "))]"'
```

Expected: 14 lines listing the Wave-0 issues, each carrying labels `ready` and zero or more attribute labels.

- [ ] **Step 2: Document the dispatch protocol**

Append to `extraspecial_orbifolds/parallel_workstreams_design.md` §15.2:

```markdown
### 15.2 Agent dispatch protocol

For each `ready`-labelled issue:

1. An agent claims it by adding the `in progress` label and removing
   `ready`, with a comment "Claimed by <agent ID>".
2. The agent works in a feature branch
   `<workstream>/<issue-id>-<short-slug>`.
3. The agent follows the TDD template in
   `docs/superpowers/plans/2026-05-08-issue-T-1-tdd.md`.
4. On completion, the agent opens a PR closing the issue and
   triggers `scripts/dispatch/relabel_on_close.sh <issue-id>` to
   advance dependents.
```

- [ ] **Step 3: Final commit**

```bash
git add extraspecial_orbifolds/parallel_workstreams_design.md
git commit -m "docs(design): document agent dispatch protocol"
git push origin HEAD
```

- [ ] **Step 4: Announce readiness**

The repo is now ready for parallel agent dispatch. Wave 0 (14
issues) carries `ready` labels and is pickup-able. The remaining ~38
issues carry `blocked` labels and will auto-promote to `ready` as
their dependencies close via Task 9's hook.

---

## Self-review

I checked the spec against the plan with fresh eyes:

1. **Spec coverage.** Each design-doc workstream (Q, T, V, K, A, X, W) has at least one corresponding task here that creates its issues; the worked T-1 example covers the §4 issue template and the §13 dispatcher logic; the relabel script (Task 9) implements the auto-dispatch from §13. The auto-dispatch label policy from §14 is reflected in the labels in Tasks 6 and 7.

2. **Placeholder scan.** Two cases of `<...>` remain — but each is a value an agent fills at execution time (issue numbers in Tasks 9 and 10) rather than missing content. The placeholder `HAPIsBoundaryOnResolution` in Task 10 is explicitly flagged as a placeholder for the implementer to research; no other "TODO" or "TBD" is present.

3. **Type consistency.** Function names `extract_issue_body`, `create_issue`, `relabel_on_close.sh`, `dependency_graph.json` are referenced consistently across tasks.

4. **Scope check.** The plan covers (a) repo prep, (b) issue creation from the design doc, (c) one worked TDD example. It does *not* attempt to TDD-step every workstream — that decision was made explicitly with the user.

---

## Execution choice

Plan complete and saved to `extraspecial_orbifolds/trajectory_c_execution_plan.md`. Two execution options:

1. **Subagent-Driven (recommended)** — dispatch a fresh subagent per task, review between tasks, fast iteration.
2. **Inline Execution** — execute tasks in this session using executing-plans, batch execution with checkpoints.

Which approach?
