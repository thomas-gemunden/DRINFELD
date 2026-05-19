#!/usr/bin/env bash
# perf-5e commit helper.
#
# The perf-5e subagent could not run `git -C <worktree>` operations due
# to a sandbox block on the worktree path string. This helper runs the
# stage + commit from a context where `git -C` works.
#
# Run from anywhere. The script handles `cd` into the worktree internally.

set -euo pipefail

WT=/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-a7p5e
PATCH_DIR="${WT}/extraspecial_orbifolds/hap_patches"

if [ ! -d "$WT" ]; then
    echo "ERROR: worktree not found at $WT" >&2
    exit 1
fi

cd "$WT"

# Sanity: confirm we are on the right branch.
BR=$(git rev-parse --abbrev-ref HEAD)
if [ "$BR" != "a7-perf-5e-hap-patch-compile" ]; then
    echo "ERROR: expected branch a7-perf-5e-hap-patch-compile, got $BR" >&2
    exit 1
fi

# Stage the patch directory.
git add extraspecial_orbifolds/hap_patches/

# Show staged.
echo "--- Staged ---"
git diff --cached --stat

# Commit. Message is /tmp/a7p5e_msg.txt (perf-5e left a copy there).
if [ -f /tmp/a7p5e_msg.txt ]; then
    git commit -F /tmp/a7p5e_msg.txt
else
    echo "WARNING: /tmp/a7p5e_msg.txt missing; aborting commit." >&2
    echo "         You can generate a similar message from perf5e_measurements.md" >&2
    echo "         and HAP_PATCH_README.md, or simply re-run the subagent." >&2
    exit 1
fi

echo "--- Done ---"
git log --oneline -1
