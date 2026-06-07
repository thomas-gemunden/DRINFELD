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
#
# Files that compile cleanly (no source changes needed):
#   * mod2_solver.g — GF(2) coboundary tests (BoundaryMatrixGF2,
#     IsCoboundary2Mod2, IsCoboundary2Mod2WithLift, +Vec variants).
#   * transgression_kernel.g — SetupCohomology3, StandardCocycleOf,
#     IsCoboundary2, TransgressionKernel.
#
# Files NOT YET compilable (each needs its own refactor):
#   * abelian_branch_fast.g — done in PR #438 (issue #434 follow-up).
#   * iterated_bockstein.g — has top-level Read("transgression_kernel.g")
#     bootstrap that errors out under LoadDynamicModule. Need to extract
#     to a separate loader before this compiles.
#   * iscoboundary2_split.g — same Read-at-top issue.
#   * z4_fallback.g — same Read-at-top issue.
#   * snf_wrapper.g — triggers CANNOT COMPILE EXPRESSION OF TNUM 170.
#     Likely a float literal somewhere; needs to be tracked down.
#   * run_e_plus_m_kernel_hap.g — driver, not a library; not a compile
#     target.
FILES=(
    # Tier 1 — leaf modules
    solver/mod2_solver.g
    transgression_kernel.g
    abelian_branch_fast.g
    abelian_modular_data_closed_form.g
    joint_permutation_matcher.g
    untwisted_modular_data.g
    em_construction.g
    bw_lattice.g
    quillen_detecting_subgroup.g
    fsi_wrapper.g
    # Tier 2 — depend on tier 1
    solver/z4_fallback.g
    solver/iterated_bockstein.g
    krr_projector.g
    d8_classifier.g
    q8_classifier.g
    restrict_to_subgroup.g
    brw_construction.g
    # Tier 3
    solver/iscoboundary2_split.g
    ct_modular_data.g
    brw_h3_action.g
    brw_simples_action.g
    keller/keller_twist_is_trivial.g
    # Tier 4
    detecting_family_restriction.g
    keller/keller_s_entry.g
    # Tier 5 — K-4b m=7 #449 hot-path additions (PR #460 float-literal
    # cleanup + #472 vectorisation made these gac-compatible). Includes
    # transitive deps so the load_compiled.g chain self-satisfies all
    # symbols K4aClassify expects (UnimodSigma, EmUnimodGroup,
    # TranslateSpectralDataToEPlus, etc.).
    twisted_group_algebra.g
    qforms_f2.g
    defect_rep_minus_id.g
    defect_rep_minus_id_optim.g
    krr_spectral_characters.g
    krr_spectral_characters_sparse.g
    eplus_classes_closed_form.g
    eplus_irreps_closed_form.g
    em_eplus_translate.g
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
