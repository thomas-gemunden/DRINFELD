#!/usr/bin/env bash
# Shared helpers for dispatch scripts. Source this; do not execute.
# bash 3.2-compatible: no associative arrays, no mapfile, no <(...).

# Resolve repo root once and the canonical design doc path.
DISPATCH_REPO_ROOT="$(git rev-parse --show-toplevel)"
DESIGN_DOC="${DISPATCH_REPO_ROOT}/extraspecial_orbifolds/parallel_workstreams_design.md"

# extract_issue_body <ID>
# Print everything between the line "### <ID>" and the next "### " heading.
# Exits 1 if the section is empty or the ID is not found.
extract_issue_body() {
  local id="$1"
  if [ -z "$id" ]; then
    echo "extract_issue_body: missing ID argument" >&2
    return 2
  fi
  local body
  body=$(awk -v id="$id" '
    $0 == "### " id { found = 1; next }
    found && /^### / { exit }
    found { print }
  ' "$DESIGN_DOC")
  # Strip leading/trailing blank lines; if nothing left, abort.
  local trimmed
  trimmed=$(printf '%s' "$body" | awk 'NF{f=1} f{print}' | awk '{a[NR]=$0} END{for(i=NR;i>=1;i--){if(a[i]!=""){last=i;break}} for(i=1;i<=last;i++) print a[i]}')
  if [ -z "$trimmed" ]; then
    echo "extract_issue_body: no content found for ID '$id' in $DESIGN_DOC" >&2
    return 1
  fi
  printf '%s\n' "$trimmed"
}

# create_issue <ID> <Title> <Labels> <Milestone>
# Extracts the body for ID from the design doc, then runs gh issue create.
# Aborts loudly if body extraction is empty.
create_issue() {
  local id="$1"
  local title="$2"
  local labels="$3"
  local milestone="$4"
  if [ -z "$id" ] || [ -z "$title" ] || [ -z "$labels" ] || [ -z "$milestone" ]; then
    echo "create_issue: required args: ID Title Labels Milestone" >&2
    return 2
  fi
  local body
  if ! body=$(extract_issue_body "$id"); then
    echo "create_issue: aborting; body extraction failed for $id" >&2
    return 1
  fi
  # Prepend a one-line link back to the design doc section.
  local full_body
  full_body="See \`extraspecial_orbifolds/parallel_workstreams_design.md\` § ${id}.

${body}"
  gh issue create \
    --title "$title" \
    --body "$full_body" \
    --label "$labels" \
    --milestone "$milestone"
}
