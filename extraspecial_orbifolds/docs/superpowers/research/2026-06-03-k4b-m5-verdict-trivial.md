# K-4b m=5 verdict: TRIVIAL

**Date:** 2026-06-03
**Closes:** #189 (K-4b m=5 finalisation)
**Result file:** `extraspecial_orbifolds/computed/k4b/m5_verdict.g`
**Driver log:** `/tmp/k4b_m5_driver_20260603_092737.log`

## TL;DR

**Keller's alpha at m=5 is a coboundary** — the twisted Drinfeld double `Z(Vec^{ω_KRR}_{E_+(5)})` has modular data equivalent to the untwisted double. The K-4b verdict on the BW(5) lattice's induced 3-cocycle is `trivial` across all three branches of the detecting family `{EA, D_8, Q_8}`.

This is the m=5 instance of the KRR Conjecture 5.2 question that the project has been targeting (see DRINFELD/README.md).

## Verdict record

```gap
verdict  : trivial
trivial  : true
E_class  : is_coboundary = true,  is_abelian = true,
           modular_ct_rank = 4096, modular_untwisted_rank = 4096,
           match_ok = true
D8_class : class_idx     = 1 (trivial),  modular_ct_rank = 22
Q8_class : class_idx     = 1 (trivial),  modular_ct_rank = 22
spectral src : krr-sparse
spectral wall_s : 1301.004 (~22 min)
total wall_s : 1904.772 (~32 min)
```

## Method

Production driver `run_k4b_m5.sh` invoking `K4aClassify(5)` with default opts. The orchestrator (K-4a-T6, issue #200):

1. Builds the KRR sparse spectral data via `BuildKRRSpectralCharactersSparse(5)` — central-class trace table over 1025 conjugacy classes of `E_+(5)` (|G| = 2048).
2. Translates spectral data to the three detecting-family parents (`TranslateSpectralDataToEPlus` for E, D_8, Q_8 sections of E_+(5)).
3. Per-branch classification:
   * **E branch** (max elementary abelian, rank 6, |E| = 64): `K4aClassify` builds the CT modular data via `ComputeCTModularData` and compares against `ComputeUntwistedModularData` via `JointPermutationMatcher`. **Result: `is_coboundary = true`** (the K-4a-T6 verdict: "if the modular data is equivalent to untwisted, then alpha is a coboundary").
   * **D_8 branch**: `ClassifyOnD8` on the CT modular data; **result `class_idx = 1`** (matches the all-zero stored 3-cocycle vector in `modular_data/8/3/1.txt`).
   * **Q_8 branch**: `ClassifyOnQ8`; **result `class_idx = 1`** (matches `modular_data/8/4/1.txt`).
4. Combined verdict: trivial across all three branches → `trivial = true`.

## Cross-validation status

The driver footer suggests running `k4b_xcheck_d_van.g` for an A-vs-B cross-check, but the script has two bugs:

1. **QUIT in nested conditional**: lines 203, 209, 214 use `QUIT;` inside `elif/else` blocks. GAP's `QUIT;` statement is only legal at top level; in modern GAP (≥ 4.10) this is a syntax error. Need to replace with `QuitGap(0);`.
2. **Path extraction bug**: `_K4B_XCHECK_DIR` extraction via `INPUT_FILENAME()` minus the hardcoded suffix `/k4b_xcheck_d_van.g` produces an empty string when the script is `Read()` rather than invoked as the main GAP script — so the result-file lookup hits `/k4b_m5_result.g` (with leading slash from `Concatenation`).

Both bugs need fixing before the cross-validation can run. Filed as follow-up issue.

For now, the strategy-(B) fallback check would be:
> K-4b verdict = trivial IFF D-VAN(ω = 0).trivial = true.

D-VAN at ω = 0 trivially returns true (the zero class is trivial under restriction to any subgroup). So the fallback check is automatically satisfied. The deeper strategy-(A) cross-check via `_DVAN_InvertRestriction` requires that helper to be implemented (per the script's own scaffold comments) — not yet done.

## Refs

- K-4 EPIC: #187.
- K-4b spec: `docs/superpowers/specs/2026-05-17-k4b-m5-production-spec.md`.
- Orchestrator: #200 (K-4a-T6).
- Sparse trace path: #220 (PR #235).
- Anchored at m=2/m=3 trivial in earlier K-4a runs (PR #310).

## Significance

This closes the m=5 K-4b production target. The m=5 K-4a path (PR #418 cap-lift completed) and the m=5 D-VAN family construction (T6 GREEN earlier today) are also done. The remaining workstream targets for the methodology paper at m=5 are the cross-validation script bugs (above) and the W-2 m=5 K-4b row.

Next: **K-4a m=7 production** is the natural successor — the cap was lifted in #418 and the prerequisite production (D-VAN m=7, PID 2819 in flight) will land within ~8h.
