# INPUT_FILENAME() audit + fix (issue #325)

Branch: `infra-inputfn-325`. Closes #325. Surfaced during PR #324.

## TL;DR

- 33 of 91 tests under `extraspecial_orbifolds/scripts/tests/` use
  `INPUT_FILENAME()` for sibling-path resolution.
- **6 of those 33 are fragile**: they call
  `Read(Concatenation(<sliced-INPUT_FILENAME>, "/<sibling>.g"))` with no
  `IsExistingFile` guard or fallback. When the test is loaded by a
  relative path, the slice produces a wrong / empty string and the
  downstream `Read` fails with
  `file "<bogus>/foo.g" must exist and be readable`.
- **27 of the 33** are already robust — they wrap the sliced-path Read
  in `IsExistingFile` and have an explicit fallback list of candidate
  paths. These work in all three load modes unchanged.
- Applied a uniform 4-line fix to the 6 fragile tests: promote
  `INPUT_FILENAME()` to absolute via `Filename(DirectoryCurrent(), ...)`
  when its first character is not `'/'`. The slicing logic below the
  fix stays identical to before.
- All 6 fixed tests verified to pass under all three load modes
  (absolute / `cd scripts && Read("tests/...")` / `cd repo_root &&
  Read("extraspecial_orbifolds/scripts/tests/...")`).
- Spot-check on 2 robust tests confirms no regression.

## Load modes audited

1. **Absolute** — `gap -q -b -c 'Read("/abs/path/to/test_X.g");'`. The
   subagent / harness convention. `INPUT_FILENAME()` returns the
   absolute path.
2. **scripts/ relative** — `cd extraspecial_orbifolds/scripts && gap -q
   -b -c 'Read("tests/test_X.g");'`. The `run_tests.sh` convention.
   `INPUT_FILENAME()` returns `"tests/test_X.g"`.
3. **repo-root relative** — `cd <repo_root> && gap -q -b -c
   'Read("extraspecial_orbifolds/scripts/tests/test_X.g");'`. The
   `gh pr check` / arbitrary-CWD convention.

## Bug pattern

```gap
_SCRIPT_SELF := INPUT_FILENAME();;
if _SCRIPT_SELF = fail or _SCRIPT_SELF = "stream" then
    Error("INPUT_FILENAME() unavailable; ...");
fi;
_TEST_DIR := _SCRIPT_SELF{
    [1..Length(_SCRIPT_SELF) - Length("/test_X.g")]};;
_SCRIPT_DIR := _TEST_DIR{
    [1..Length(_TEST_DIR) - Length("/tests")]};;
# unconditional Read with the sliced path:
Read(Concatenation(_SCRIPT_DIR, "/sibling.g"));
```

In mode 2, `_SCRIPT_SELF = "tests/test_X.g"` → `_TEST_DIR = "tests"`
→ `_SCRIPT_DIR = ""` (stripping "/tests" produces empty because the
"/" is gone) → `Read("/sibling.g")` → "file must exist and be readable".

In mode 3, `_SCRIPT_SELF = "extraspecial_orbifolds/scripts/tests/test_X.g"`
→ `_TEST_DIR = "extraspecial_orbifolds/scripts/tests"` → `_SCRIPT_DIR
= "extraspecial_orbifolds/scripts"` → `Read("extraspecial_orbifolds/scripts/sibling.g")`,
but the CWD is repo_root, so it works at first. **However**, several
of the broken tests follow with `ChangeDirectoryCurrent(_SCRIPT_DIR)`
before the Reads — after that chdir, CWD becomes
`repo_root/extraspecial_orbifolds/scripts`, and the relative
`Read("extraspecial_orbifolds/scripts/sibling.g")` now looks for
`repo_root/extraspecial_orbifolds/scripts/extraspecial_orbifolds/scripts/sibling.g`
which doesn't exist. Hence the same "file must exist" error in mode 3.

## Fix pattern

Inserted 4 lines immediately after the `fail / "stream"` guard:

```gap
# Issue #325: when this file is Read via a relative path,
# INPUT_FILENAME() returns the relative path as-given and the slicing
# below would produce wrong/empty results. Promote to absolute first.
if Length(_SCRIPT_SELF) > 0 and _SCRIPT_SELF[1] <> '/' then
    _SCRIPT_SELF := Filename(DirectoryCurrent(), _SCRIPT_SELF);
fi;
```

`Filename(Directory, "rel/path")` joins them; if the relative path is
already empty it does the right thing. `DirectoryCurrent()` reflects
the GAP process's CWD at the moment of evaluation — i.e. exactly the
directory from which a relative `Read(...)` was resolved by GAP.

This fix is **mode-1-safe**: when `_SCRIPT_SELF` already starts with
`/`, the `if` body is skipped. Slicing logic below the fix is
unchanged.

## Fragile tests (6) — fixed

| test | mode 1 (abs) | mode 2 (scripts/) | mode 3 (repo-root) | notes |
|---|---|---|---|---|
| `test_em_eplus_translate.g` | PASS | PASS | PASS | 36/36 assertions |
| `test_em_eplus_translate_m5_synthetic.g` | PASS | PASS | PASS | 8/8 assertions |
| `test_em_eplus_translate_pipeline.g` | PASS | PASS | PASS | 21/21 assertions |
| `test_k2c_lazy_transports.g` | PASS | PASS | PASS | 20/20 assertions |
| `test_restrict_to_subgroup.g` | PASS | PASS | PASS | 42/42 assertions |
| `test_build_krr_intertwiner_data.g` | PASS | PASS | PASS | 33/33 assertions |

All three em_eplus_translate variants share the same bug pattern (they
were copy-pasted; the `_SCRIPT_DIR := ...` slicing is identical except
for the test-file name). `test_k2c_lazy_transports.g` and
`test_restrict_to_subgroup.g` use the same pattern with all-caps
namespaced var names (`K2C_*`, `RTS_*`). `test_build_krr_intertwiner_data.g`
already had an `IsExistingFile` sanity check that would surface the
bug as a clean error rather than the cryptic GAP "file must exist"
— but it still failed (just with a clearer message) in modes 2/3 before
this fix.

## Robust tests (27) — no change

These have either:

- (a) An `IsExistingFile(<sliced-path>)` guard around every Read,
      plus a fallback `for _p in [list-of-candidate-relative-paths] do
      if IsExistingFile(_p) then Read(_p); ... fi; od;` loop, or
- (b) A `KRR_FULL_ReadSibling(rel)` helper that falls back to
      `Read(rel)` (CWD-relative) when the sliced absolute path is the
      empty string — works because the `run_tests.sh` convention is
      `cd scripts/` and `Read("tests/test_X.g")` resolves to the empty
      `KRR_FULL_SCRIPTSDIR`.

These 27 tests were not modified. Two of them (`test_quillen_algebra.g`,
`test_aut_nt_partition.g`) were spot-checked under modes 2 and 3 and
both pass.

Full list of robust INPUT_FILENAME() users:

```
test_abelian_e_form_check.g            test_k4a_classify_lattice_source.g
test_aut_nt.g                          test_k4a_classify_m5_smoke.g
test_aut_nt_mod_brw.g                  test_k4a_honour_parent_m3_nontrivial.g
test_aut_nt_partition.g                test_k4b_scaffold_smoke.g
test_aut_nt_refine.g                   test_krr_full_s_t.g
test_brw_aut_lower_bound.g             test_q8_classifier.g
test_cocyclebasis_quillen_bridge.g     test_q_b3_5_m5_z4.g
test_ct_modular_data.g                 test_quillen_algebra.g
test_d8_classifier.g                   test_quillen_cup_product.g
test_d_van_7_scaffold_smoke.g          test_quillen_detecting_subgroup.g
test_integral_bockstein.g              test_quillen_h3_callable.g
test_joint_permutation_matcher.g       test_quillen_presentation.g
test_k4a_anchor_m3.g                   test_quillen_vs_hap.g
test_k4a_classify.g
```

## Out of scope (not INPUT_FILENAME() users)

Issue #325 cites two more tests in passing —
`tests/test_quillen_h3_u1.g` and `tests/test_iscoboundary2_batched.g`
— as broken in modes 2/3. **Neither uses `INPUT_FILENAME()`**, so they
are not in scope for this issue. Their bugs are different:

- `test_quillen_h3_u1.g` does `Read("../quillen_h3_u1.g")`, a
  CWD-relative path that only works from `tests/`. This is the
  `cd scripts/` convention bug, which #319/PR #324 chose to leave
  in place.
- `test_iscoboundary2_batched.g` has a hardcoded `ICB_ROOT :=
  "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-a5b-batched-backsub";;`
  pointing at a stale predecessor worktree path. This is a different
  category of bug (stale absolute path).

Filed as out-of-scope; could be fixed in a follow-up if desired.

## Static-analysis driver

For reproducibility, the static-analysis driver that identifies
fragile-vs-robust patterns is at `/tmp/static_audit.g` during this
audit (not committed — it's an ad-hoc helper). It loads each test as
text and counts occurrences of:

- `IsExistingFile`
- `IsAbsoluteFilename`
- `Read(Concatenation(<var>, ...))` for any of the named slicing vars
  used across the 33 tests
- `for _p in [...]` fallback loops
- `ChangeDirectoryCurrent(<sliced-var>)` calls

A test is FRAGILE when it has `raw_reads > 0 AND guards = 0 AND
abs_check = 0`, or when it does `ChangeDirectoryCurrent(<sliced-var>)`
without verifying the path is absolute. All 6 hits matched the bug
empirically (verified by running each test in modes 2/3 and observing
"file must exist and be readable" before the fix).

## Verification protocol

For each of the 6 fragile tests:

1. Reproduce the bug on `main` by running mode 2 (`cd scripts/ && gap
   -q -b -c 'Read("tests/test_X.g");'`). Confirmed all 6 fail with
   `Error, file "/sibling.g" must exist and be readable` (or the
   equivalent path-prefix variant for mode 3).
2. Apply the 4-line fix.
3. Re-run modes 1, 2, 3. All three modes complete with the test's
   own "PASS" / "ALL TESTS PASS: true" line.

## Files modified

- `extraspecial_orbifolds/scripts/tests/test_em_eplus_translate.g`
- `extraspecial_orbifolds/scripts/tests/test_em_eplus_translate_m5_synthetic.g`
- `extraspecial_orbifolds/scripts/tests/test_em_eplus_translate_pipeline.g`
- `extraspecial_orbifolds/scripts/tests/test_k2c_lazy_transports.g`
- `extraspecial_orbifolds/scripts/tests/test_restrict_to_subgroup.g`
- `extraspecial_orbifolds/scripts/tests/test_build_krr_intertwiner_data.g`
- `extraspecial_orbifolds/docs/superpowers/research/2026-05-21-input-filename-audit.md`
  (this file)

## Why this matters

Per the issue body: subagent test invocations commonly use absolute-
path Reads (cd-harness limitation). The 6 tests above silently failed
in this mode, costing dispatch cycles when their bugs were assumed to
be substantive. The fix is mechanical and unit-cost; the harder work
was the audit + per-mode empirical verification.
