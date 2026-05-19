# `computed/k4b/`

Persisted artefacts of the K-4b production run at m = 5
(`run_k4b_m5.sh`).

## Files

- `m5_verdict.g` — the canonical persisted output of `K4aClassify(5)`,
  written by `run_k4b_m5.sh` after each successful run. Loadable in
  a fresh GAP session via `Read("m5_verdict.g")`, which binds the
  global `RESULT`. The driver writes a lite copy of the full result
  record: the 4096 x 4096 cyclotomic matrices in
  `E_class.modular_ct.S` / `modular_untwisted.S` and the sparse
  spectral data's `idx` / `trace_on_W` payload are stripped to
  meta-summaries (`modular_ct_rank`, `sparse.num_classes`,
  `sparse.group`, etc.). The smoke test
  `tests/test_k4a_classify_m5_smoke.g` asserts on these meta-fields.

The driver also writes `extraspecial_orbifolds/scripts/k4b_m5_result.g`
as a sibling of `k4a_classify.g`; the canonical file here is a copy
for the smoke test and downstream consumers.

## Verdict summary

See `docs/superpowers/research/2026-05-17-k4b-m5-verdict.md` for the
full verdict note with per-branch class indices, wall times, and the
implications for Keller's conjecture at m = 5.
