# CI environment

The GitHub Actions workflow at `.github/workflows/ci.yml` runs the
GAP regression suite on every push to `main` and on every pull request
targeting `main`.

## Pinned versions

- GAP: **4.13.0** (via `gap-actions/setup-gap@v2`)
- HAP: latest available (pulled / built against the GAP install)
- IO: latest (built via the `GAP_PKGS_TO_BUILD` input to `setup-gap`)
- hapco: optional. Only needed for `DRINFELD/src/universal_coefficients.g`,
  which is not exercised by the current test suite. Add it to
  `GAP_PKGS_TO_BUILD` if/when those tests come online.

### GAP version note

Local development uses GAP **4.15.1**. CI runs on **4.13.0** because that
is the latest version exposed by `gap-actions/setup-gap@v2` at the time
of writing. The regression suite avoids 4.15-only features, so this is
fine in practice; if a test ever depends on something newer, either
bump the action when a 4.15-capable release is available or run that
test outside CI.

## Gating

The runner skips heavy tests when invoked with `FAST=1`, which is what
the workflow sets. The current skip list is:

- `test_quillen_vs_hap.g` — slow cross-check of the Quillen-presentation
  H^3 against HAP, gated by `Q8_INCLUDE_M3` for the m=3 cocycle.

To run everything locally including the slow tests:

```bash
./run_tests.sh
```

To match what CI does (skip slow tests):

```bash
FAST=1 ./run_tests.sh
```

## Local execution

The runner expects a `gap` binary on `$PATH`. It falls back to
`/opt/homebrew/bin/gap` and `/usr/local/bin/gap` for macOS Homebrew
installs.

```bash
./run_tests.sh                # all tests, verbose
FAST=1 ./run_tests.sh         # skip slow ones (CI mode)
```

Per-test logs are written to `/tmp/<test_name>.log`. On a CI failure,
the workflow uploads them as a `test-logs` artifact.

## What the runner does

1. `cd extraspecial_orbifolds/scripts`.
2. Iterate over `tests/test_*.g` in lexical order.
3. For each test, run `gap -q -b <test>` and capture stdout/stderr to
   `/tmp/<name>.log`.
4. Print `PASS` / `FAIL` / `SKIP` per test, plus the last 20 lines of
   the log on failure.
5. Exit 0 iff every non-skipped test exited 0.
