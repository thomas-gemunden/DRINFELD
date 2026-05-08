#!/usr/bin/env bash
# Usage: relabel_on_close.sh <closed-issue-id>
# Example: relabel_on_close.sh Q-1
#
# When a workstream issue closes, advance any directly-dependent
# issues from `blocked` to `ready` if all of THEIR deps are now
# closed.
#
# Compatible with bash 3.2 (no associative arrays).
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"

closed_id="${1:?Usage: $0 <closed-issue-id>}"
graph="scripts/dispatch/dependency_graph.json"

if [ ! -f "$graph" ]; then
  echo "ERROR: $graph not found" >&2
  exit 1
fi

# Find downstream issues that list closed_id in their deps.
downstream=$(jq -r --arg id "$closed_id" '
  to_entries[] | select(.value.deps | index($id)) | .key
' "$graph")

if [ -z "$downstream" ]; then
  echo "No downstream issues depend on ${closed_id}."
  exit 0
fi

# For each downstream, check whether all its upstreams are closed.
issue_state() {
  # Returns OPEN | CLOSED | UNKNOWN for an issue identified by its
  # title prefix [<id>].
  local id="$1"
  local state
  state=$(gh issue list --state all --limit 100 --search "in:title \"[${id}]\"" --json state -q '.[0].state' 2>/dev/null || true)
  if [ -z "$state" ]; then
    echo "UNKNOWN"
  else
    echo "$state"
  fi
}

issue_number() {
  local id="$1"
  gh issue list --state all --limit 100 --search "in:title \"[${id}]\"" --json number -q '.[0].number' 2>/dev/null || echo ""
}

for dep_id in $downstream; do
  all_closed=true
  while IFS= read -r upstream; do
    [ -z "$upstream" ] && continue
    state=$(issue_state "$upstream")
    if [ "$state" != "CLOSED" ]; then
      all_closed=false
      break
    fi
  done < <(jq -r --arg id "$dep_id" '.[$id].deps[]' "$graph")

  if [ "$all_closed" = "true" ]; then
    num=$(issue_number "$dep_id")
    if [ -z "$num" ]; then
      echo "WARNING: could not find issue number for ${dep_id}; skipping." >&2
      continue
    fi
    if gh issue edit "$num" --remove-label "blocked" --add-label "ready" >/dev/null 2>&1; then
      echo "Unblocked: ${dep_id} (issue #${num})"
    else
      echo "WARNING: relabel failed for ${dep_id} (issue #${num})" >&2
    fi
  else
    echo "Still blocked: ${dep_id} (some upstream not closed)"
  fi
done
