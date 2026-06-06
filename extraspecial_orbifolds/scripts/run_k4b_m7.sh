#!/usr/bin/env bash
# run_k4b_m7.sh — K-4b m=7 production driver.
#
# Wraps a single call to `K4aClassify(7)` (the K-4a-T6 orchestrator,
# issue #200) with all preconditions:
#
#   1. Read src/modular_data.g BEFORE k4a_classify.g, so the
#      D_8 / Q_8 classifiers can bind LoadModularData on load.
#   2. Place a `Modular_Data` symlink in CWD pointing at the
#      repo-level `modular_data/` tree, so LoadModularData(8, k, ...)
#      resolves.
#   3. Pre-check that the upstream dependencies exist on disk —
#        * krr_spectral_characters_sparse.g  (issue #220, sparse trace)
#        * k4a_classify.g                    (issue #200, T6 orchestrator)
#      Emit a clear "blocked on #NNN" message and bail out cleanly
#      if either is missing. The scaffold ships ahead of these so
#      the production run can execute the moment they both merge;
#      the gating below is the explicit handshake.
#   4. Persist the K4aClassify return record to `k4b_m7_result.g`
#      (loadable by a fresh GAP session via `Read("k4b_m7_result.g")`,
#      binding the global `RESULT`).
#   5. Mirror stdout/stderr to a timestamped log under
#      `extraspecial_orbifolds/perf/raw/k4b/` (override via
#      `K4B_LOG_DIR`).
#
# Usage (from anywhere; the script chdirs to its own directory):
#   ./run_k4b_m7.sh
#
# This driver is the K-4b deliverable for the K-4b spec at
#   docs/superpowers/specs/2026-05-17-k4b-m7-production-spec.md
# and is intended to be executed once T6 (#200) and the sparse trace
# follow-up (#220) have both landed. Until then, the gating in step (3)
# above guards against premature runs.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"

# ---- Step 3 (upstream pre-checks) -------------------------------------
# Run BEFORE any expensive setup so we fail fast and loud.

CLASSIFY_FILE="${SCRIPT_DIR}/k4a_classify.g"
SPARSE_FILE="${SCRIPT_DIR}/krr_spectral_characters_sparse.g"

if [[ ! -f "${CLASSIFY_FILE}" ]]; then
    echo "[run_k4b] BLOCKED: k4a_classify.g missing." >&2
    echo "[run_k4b]   path checked : ${CLASSIFY_FILE}" >&2
    echo "[run_k4b]   dependency   : K-4a-T6 orchestrator, issue #200." >&2
    echo "[run_k4b]   action       : merge #200 before running this driver." >&2
    exit 2
fi

if [[ ! -f "${SPARSE_FILE}" ]]; then
    echo "[run_k4b] BLOCKED: krr_spectral_characters_sparse.g missing." >&2
    echo "[run_k4b]   path checked : ${SPARSE_FILE}" >&2
    echo "[run_k4b]   dependency   : sparse trace_on_W replacement, issue #220." >&2
    echo "[run_k4b]   action       : merge #220 before running this driver." >&2
    echo "[run_k4b]                  (the dense T_h build in" >&2
    echo "[run_k4b]                   krr_spectral_characters.g is" >&2
    echo "[run_k4b]                   infeasible at m=7: ~3.7 years per" >&2
    echo "[run_k4b]                   intertwiner matrix.)" >&2
    exit 2
fi

# Additional check: the K4aClassify orchestrator currently hard-caps
# m at 3 (`n_max_supported := 3` in k4a_classify.g). When #220 lands,
# that cap should be lifted (or the orchestrator should switch over
# to BuildKRRSpectralCharactersSparse). The grep below catches the
# stale cap and prints a clear remediation pointer.
if grep -q 'n_max_supported := 3' "${CLASSIFY_FILE}"; then
    echo "[run_k4b] BLOCKED: k4a_classify.g still caps n_max_supported at 3." >&2
    echo "[run_k4b]   This means K4aClassify(7) will Error out." >&2
    echo "[run_k4b]   After #220 merges, the m>=4 deferral in" >&2
    echo "[run_k4b]   k4a_classify.g needs to be lifted (or the orchestrator" >&2
    echo "[run_k4b]   updated to call BuildKRRSpectralCharactersSparse" >&2
    echo "[run_k4b]   on the central branch when m>=4)." >&2
    echo "[run_k4b]   See docs/superpowers/specs/2026-05-17-k4b-m7-production-spec.md" >&2
    exit 3
fi

# ---- Step 2 (Modular_Data symlink) ------------------------------------
# Locate the repo-level modular_data/ tree. Layout:
#   <parent>/modular_data/8/3/k.txt  (D_8 cocycles)
#   <parent>/modular_data/8/4/k.txt  (Q_8 cocycles)
MODULAR_DATA_TREE="${REPO_ROOT}/../modular_data"
if [[ ! -d "${MODULAR_DATA_TREE}" ]]; then
    MODULAR_DATA_TREE="/Users/thomasgemunden/Projects/group_cohomology/modular_data"
fi
if [[ ! -f "${MODULAR_DATA_TREE}/8/4/1.txt" ]]; then
    echo "[run_k4b] cannot find Modular_Data tree (looked at ${MODULAR_DATA_TREE})" >&2
    exit 1
fi

cd "${SCRIPT_DIR}"

# Place the Modular_Data symlink for LoadModularData(...) to resolve.
# Mirrors the convention in run_k4a.sh.
if [[ -L "Modular_Data" || -e "Modular_Data" ]]; then
    rm -f Modular_Data
fi
ln -s "${MODULAR_DATA_TREE}" Modular_Data

# ---- Step 5 (logging) -------------------------------------------------
LOG_DIR="${K4B_LOG_DIR:-${REPO_ROOT}/extraspecial_orbifolds/perf/raw/k4b}"
mkdir -p "${LOG_DIR}"
TIMESTAMP="$(date -u +%Y%m%d_%H%M%SZ)"
LOG="${LOG_DIR}/k4b_m7_${TIMESTAMP}.log"

# Two result file locations:
#   * RESULT_FILE_DRIVER : `scripts/k4b_m7_result.g` — written by the
#     GAP one-liner below. Used by `k4b_xcheck_d_van.g`, which is
#     sibling to scripts/ and reads relative to its own location.
#   * RESULT_FILE_CANON  : `extraspecial_orbifolds/computed/k4b/m7_verdict.g`
#     — the canonical persisted location per the K-4b spec
#     (`docs/.../2026-05-17-k4b-m7-production-spec.md`). Symlinked from
#     the driver output after the run completes; ensures
#     `tests/test_k4a_classify_m7_smoke.g` can find the artefact in its
#     canonical location.
RESULT_FILE_DRIVER="${SCRIPT_DIR}/k4b_m7_result.g"
RESULT_DIR_CANON="${REPO_ROOT}/extraspecial_orbifolds/computed/k4b"
RESULT_FILE_CANON="${RESULT_DIR_CANON}/m7_verdict.g"
mkdir -p "${RESULT_DIR_CANON}"

echo "[run_k4b] m              = 5"
echo "[run_k4b] script dir     = ${SCRIPT_DIR}"
echo "[run_k4b] modular_data   = ${MODULAR_DATA_TREE} (linked as Modular_Data)"
echo "[run_k4b] log            = ${LOG}"
echo "[run_k4b] result file    = ${RESULT_FILE_DRIVER}"
echo "[run_k4b] canonical file = ${RESULT_FILE_CANON}"

{
    echo "K-4b m=7 run started $(date -u +%FT%TZ)"
    echo "  driver       : ${BASH_SOURCE[0]}"
    echo "  script_dir   : ${SCRIPT_DIR}"
    echo "  modular_data : ${MODULAR_DATA_TREE}"
    echo "  result_file  : ${RESULT_FILE_DRIVER}"
    echo "  canonical    : ${RESULT_FILE_CANON}"
} | tee "${LOG}"

# Optional virtual memory cap (per spec: 96 GB). `ulimit -v` is only
# available on Linux; on macOS it's silently ignored or errors. Wrap
# in `|| true` so the driver continues on macOS dev hosts.
ulimit -v $((96 * 1024 * 1024)) 2>/dev/null || true

# ---- Step 4 (run GAP) -------------------------------------------------
# -q -b suppresses banner and prompts. The GAP one-liner:
#   1. Reads src/modular_data.g  (binds LoadModularData and friends).
#   2. Reads k4a_classify.g       (defines K4aClassify; transitively
#                                  loads every classifier sibling).
#   3. Calls K4aClassify(7)       (the K-4b production run).
#   4. PrintTo(RESULT_FILE)       (persists the verdict record).
#   5. Prints a single-line summary to stdout for human-eyeballing.
#   6. QUITs cleanly.
#
# tee captures all of GAP's stdout + stderr into the log.
echo "[run_k4b] launching gap..." | tee -a "${LOG}"

set +e
# -o 48g: increase GAP's pre-set memory limit. The default (a few GB on
# macOS Homebrew) is too small for m=7's class-data + spectral build,
# which can spike to 15-20 GB during ExponentsOfPcElement / OnTuples
# inside HAP's permutation-group conjugacy enumeration.
gap -q -b -o 48g -c "
    Read(\"../../src/modular_data.g\");;
    # PR #440 / load_compiled.g: pre-bind 23 hot-path modules
    # (untwisted_modular_data, restrict_to_subgroup, ct_modular_data,
    # mod2_solver, abelian_branch_fast, ...) via their gac-compiled .so
    # siblings where available; the loader falls back to interpreted
    # .g on any missing .so. ~2-5x speedup on EvalIrr / restriction
    # calls which dominate the m=7 post-spectral E/D_8/Q_8 sweep.
    # MUST load BEFORE k4a_classify.g so that the latter's
    # _K4A_LoadSibling(\"BuildSimpleIndex\", ...) checks find the
    # pre-bound compiled symbols and skip re-reading the interpreted .g.
    Read(\"load_compiled.g\");;
    Read(\"k4a_classify.g\");;
    # B5 (#449 audit): route the post-spectral E branch through the
    # closed-form q_omega + b_omega path (PR #437). At m = 7 the slow
    # path is O(|H|^4) = 4e9 entries per EA; the fast path is O(|H|^2)
    # = 65536 -- ~256x speedup across the 8-EA detecting family.
    _K4A_USE_FAST_ABELIAN_BRANCH := true;;
    Print(\"[run_k4b] _K4A_USE_FAST_ABELIAN_BRANCH = \", _K4A_USE_FAST_ABELIAN_BRANCH, \"\n\");;
    result := K4aClassify(7);;

    # Persist the result. The full record contains very heavy fields
    # for the E branch at m = 7: \`E_class.modular_ct.S\` and
    # \`E_class.modular_untwisted.S\` are 4096 x 4096 cyclotomic
    # matrices (~80-150 MB each on disk), and \`E_class.match.pi\`
    # holds the 4096-element permutation. We strip those down to
    # meta-fields (rank, ok-flag) so the persisted file stays
    # manageable for downstream smoke tests / Read calls.
    # The full sparse spectral data (functions + GAP groups + 1025
    # lazy classes) is similarly stripped to a meta-summary.
    persist := ShallowCopy(result);;
    persist.spectral_data := rec(
        source                := result.spectral_data.source,
        rationale             := result.spectral_data.rationale,
        spectral_call_skipped := result.spectral_data.spectral_call_skipped,
        wall_seconds          := result.spectral_data.wall_seconds,
        sparse                := rec(
            source         := result.spectral_data.sparse.source,
            m              := result.spectral_data.sparse.m,
            num_classes    := Length(result.spectral_data.sparse.idx.classes),
            group          := result.spectral_data.sparse.group,
            group_order    := Order(result.spectral_data.sparse.group)
        )
    );;
    # Issue #449: at m >= 5 with the multi-EA spectral E-branch dispatch,
    # result.E_class is the aggregate record from
    # _K4A_ClassifySpectralEBranchMulti — it does NOT have .modular_ct,
    # .modular_untwisted, or .match fields. Persist the multi-EA shape
    # when present, else fall back to single-EA fields.
    if IsBound(result.E_class.spectral_multi_ea)
       and result.E_class.spectral_multi_ea = true then
        persist.E_class := rec(
            is_abelian          := result.E_class.is_abelian,
            is_coboundary       := result.E_class.is_coboundary,
            modular_ct_rank     := result.E_class.modular_ct_rank,
            modular_untwisted_rank :=
                result.E_class.modular_untwisted_rank,
            match_ok            := result.E_class.is_coboundary,
            spectral_multi_ea   := true,
            family_source       := result.E_class.family_source,
            per_ea_results      := result.E_class.per_ea_results,
            wall_seconds        := result.E_class.wall_seconds
        );;
    else
        persist.E_class := rec(
            is_abelian          := result.E_class.is_abelian,
            is_coboundary       := result.E_class.is_coboundary,
            modular_ct_rank     := Length(result.E_class.modular_ct.S),
            modular_untwisted_rank :=
                Length(result.E_class.modular_untwisted.S),
            match_ok            := result.E_class.match.ok,
            wall_seconds        := result.E_class.wall_seconds
        );;
    fi;;
    # For D_8 / Q_8 (rank 22, small), keep the full modular_ct so
    # downstream consumers can re-classify if needed. Drop only
    # \`all_matches\` and \`pi\` which are list-typed and well-shaped
    # but could be re-derived from the stored modular_ct trivially.
    persist.D8_class := rec(
        is_abelian       := result.D8_class.is_abelian,
        class_idx        := result.D8_class.class_idx,
        modular_ct_rank  := Length(result.D8_class.modular_ct.S),
        all_matches      := result.D8_class.all_matches,
        wall_seconds     := result.D8_class.wall_seconds
    );;
    persist.Q8_class := rec(
        is_abelian       := result.Q8_class.is_abelian,
        class_idx        := result.Q8_class.class_idx,
        modular_ct_rank  := Length(result.Q8_class.modular_ct.S),
        all_matches      := result.Q8_class.all_matches,
        wall_seconds     := result.Q8_class.wall_seconds
    );;
    PrintTo(\"k4b_m7_result.g\",
        \"# K-4b m=7 result (auto-generated by run_k4b_m7.sh)\n\",
        \"# Loadable in a fresh GAP session: Read(\\\"k4b_m7_result.g\\\");\n\",
        \"# binds RESULT.\n\",
        \"RESULT := \", persist, \";;\n\");;
    Print(\"\n=== K-4b m=7 verdict ===\n\");;
    Print(\"verdict  : \", result.verdict, \"\n\");;
    Print(\"trivial  : \", result.trivial, \"\n\");;
    Print(\"E_class  : is_coboundary = \", result.E_class.is_coboundary, \"\n\");;
    Print(\"D8_class : class_idx     = \", result.D8_class.class_idx,
          \" (trivial = 1)\n\");;
    Print(\"Q8_class : class_idx     = \", result.Q8_class.class_idx,
          \" (trivial = 1)\n\");;
    Print(\"spectral src : \", result.spectral_data.source, \"\n\");;
    Print(\"spectral wall_s : \", result.spectral_data.wall_seconds, \"\n\");;
    Print(\"total wall_s : \", result.timing.wall_seconds, \"\n\");;
    QUIT;
" 2>&1 | tee -a "${LOG}"
# In a pipeline, $? is the last command's status (tee). Capture the
# gap exit code via PIPESTATUS (bash-only, but the shebang above
# guarantees bash).
GAP_EXIT=${PIPESTATUS[0]}
set -e

echo "[run_k4b] gap exited with code ${GAP_EXIT}" | tee -a "${LOG}"

if [[ ${GAP_EXIT} -ne 0 ]]; then
    echo "[run_k4b] gap exited non-zero; result file may be partial/missing." | tee -a "${LOG}"
    exit ${GAP_EXIT}
fi

if [[ ! -f "${RESULT_FILE_DRIVER}" ]]; then
    echo "[run_k4b] gap exited 0 but ${RESULT_FILE_DRIVER} was not written." | tee -a "${LOG}" >&2
    exit 4
fi

echo "[run_k4b] result file written: ${RESULT_FILE_DRIVER}" | tee -a "${LOG}"

# Copy to the canonical location for the smoke test and downstream
# consumers. Use `cp -f` (not `ln -s`) so the canonical artefact is
# self-contained and survives moves of the scripts/ directory.
cp -f "${RESULT_FILE_DRIVER}" "${RESULT_FILE_CANON}"
echo "[run_k4b] canonical copy : ${RESULT_FILE_CANON}" | tee -a "${LOG}"
echo "K-4b m=7 run ended $(date -u +%FT%TZ)" | tee -a "${LOG}"
echo
echo "Next steps:"
echo "  1. Read k4b_m7_result.g in a fresh GAP session to inspect RESULT."
echo "  2. Run cross-validation:"
echo "       gap -q -b -c 'Read(\"${SCRIPT_DIR}/k4b_xcheck_d_van.g\");'"
echo "  3. Fill in docs/superpowers/research/TEMPLATE-k4b-m7-verdict.md"
echo "     (rename to a dated, descriptive filename) and commit."
