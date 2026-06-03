#!/bin/bash
# compile_codebase.sh — gac-compile hot-path .g files to .so (issue #286).
#
# Usage:
#   cd extraspecial_orbifolds/scripts
#   ./compile_codebase.sh
#
# Outputs to extraspecial_orbifolds/scripts/compiled/.
#
# Known gac limitations (GAP 4.15.1):
#   * No float literals (e.g. `1000.0`) — triggers `CANNOT COMPILE
#     EXPRESSION OF TNUM 170` (MACFLOAT). Use integer milliseconds and
#     convert externally where needed.
#   * Top-level `f := function() ... end;;` must be refactored to
#     `DeclareGlobalFunction("f"); InstallGlobalFunction(f, function() ... end);`
#   * `Read(...)` calls inside compiled functions are unsupported; hoist
#     to a bootstrap loader.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

OUT_DIR="$SCRIPT_DIR/compiled"
mkdir -p "$OUT_DIR"

# Hot-path files to compile, in order of dependency. Add more as they get
# refactored for gac-compatibility (see issue #286 file list).
FILES=(
    abelian_branch_fast.g
)

echo "[compile_codebase.sh] compiling ${#FILES[@]} file(s) -> $OUT_DIR/"

for src in "${FILES[@]}"; do
    if [ ! -f "$src" ]; then
        echo "[compile_codebase.sh] skip: $src not found"
        continue
    fi
    base="$(basename "$src" .g)"
    # gac doubles every underscore in the source basename when naming
    # the output .so (e.g. `abelian_branch_fast.g` -> `abelian__branch__fast.so`).
    gac_out_name="$(printf "%s" "$base" | sed 's/_/__/g').so"
    final_out="$OUT_DIR/${base}.so"
    echo "[compile_codebase.sh]   $src -> $final_out"
    # gac writes to CWD; cd to compiled/ first, then point at source via
    # absolute path so the .so lands where we want.
    (cd "$OUT_DIR" && gac -d "$SCRIPT_DIR/$src")
    if [ ! -f "$OUT_DIR/$gac_out_name" ]; then
        echo "[compile_codebase.sh]   ERROR: gac did not produce $OUT_DIR/$gac_out_name"
        exit 1
    fi
    # Rename to the expected (un-mangled) name.
    mv "$OUT_DIR/$gac_out_name" "$final_out"
done

echo "[compile_codebase.sh] done. ls -la $OUT_DIR:"
ls -la "$OUT_DIR"
