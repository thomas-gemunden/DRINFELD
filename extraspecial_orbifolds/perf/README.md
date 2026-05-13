# Profile harness (P-1 / P-7, P-EPIC = issue #109)

Standardises two complementary workflows for the GAP code:

- **CPU sampling** (P-1, #110): `profile_runner.sh` uses macOS
  `sample` to capture C-level hot leaves over a fixed window.
- **Memory profiling** (P-7, #115): `memory_runner.sh` polls RSS over
  the full run, emits a JSONL stream, and `compare_memory.py`
  flags regressions against a baseline.

One workload script per hot path; one report per run.

## Usage

```bash
cd extraspecial_orbifolds/perf
./profile_runner.sh <workload_name> [seconds]
```

`workload_name` matches a script under `workloads/`. Example:

```bash
./profile_runner.sh eplus3_build_per_class_cocycle_basis 30
```

Outputs:

- `raw/<workload>.txt` — full macOS `sample` capture
- `raw/<workload>.log` — GAP stdout
- `reports/<workload>.md` — parsed top-3 hot leaves + deepest
  single-frame concentration + workload's wall-time line

## Adding a workload

Drop a `<name>.g` file in `workloads/` that:

1. Loads the code under test.
2. Performs real work for at least `<seconds>` (so the sample captures
   the hot path).
3. Prints a final wall-time line.
4. Calls `QUIT;`.

The harness sleeps 5 s after launching GAP to let package loads
finish, then samples the live PID for `<seconds>`. Set the
`GAP_BIN` environment variable to override the GAP binary path
(default `/opt/homebrew/bin/gap`).

## Interpreting the report

`sample` resolves only C symbols, not GAP-level functions. The
"Top hot leaves" table is usually dominated by primitives like
`PosPlist`, `EqPlist`, `EqNot`, `CollectBags`. The hot leaf alone
doesn't tell you *which* GAP function is calling it.

The "Deepest single-frame concentration" line picks the deepest
high-count node in the call graph; that is typically the C-level
function immediately above the leaf. To identify the GAP function:

1. Open `raw/<workload>.txt` and find the deepest frame line.
2. Look at its `Eval...` / `Exec...` ancestor frames (they describe
   the GAP interpreter operations: `EvalFunccall2args` etc.).
3. Cross-reference against the workload source to identify the
   GAP-level loop that's hot.

Once the GAP-level function is known, the standard P-* fix patterns
are: hoist a redundant computation out of a loop, replace `Position`
with a binary-search or dictionary lookup, or pre-compute a table.

## Available workloads

| Name | What it profiles |
|---|---|
| `eplus3_build_per_class_cocycle_basis` | `BuildPerClassCocycleBasis` on one |C|=64 orbit-2 rep of E_+(3); the bottleneck found in the A-3a debug. |

## Memory profiling (P-7, #115)

Run a workload under RSS polling and write a JSONL stream:

```bash
cd extraspecial_orbifolds/perf
chmod +x memory_runner.sh compare_memory.py   # first time only
./memory_runner.sh <workload_name> [interval_seconds]
```

Defaults: poll every 5 s. Outputs:

- `memory/<workload>.jsonl` — one `{"t", "rss_kb"}` sample per line
- `memory/<workload>.log` — GAP stdout
- A console summary line: samples, wall_s, peak_mb, end_mb, mean_mb

Polling uses `ps -p <PID> -o rss=`, which on macOS reports KB. The
summary converts to MB. The runner stops when GAP exits, so the JSONL
covers the full run (not a fixed window like `profile_runner.sh`).

### Baseline + regression check

`memory/baseline.json` records per-workload `{peak_rss_mb, end_rss_mb,
mean_rss_mb, wall_s}`. To record a new baseline from a run:

```bash
./memory_runner.sh eplus3_build_per_class_cocycle_basis
python3 compare_memory.py record eplus3_build_per_class_cocycle_basis \
    memory/eplus3_build_per_class_cocycle_basis.jsonl
```

To compare a new run against the baseline:

```bash
python3 compare_memory.py compare eplus3_build_per_class_cocycle_basis \
    memory/eplus3_build_per_class_cocycle_basis.jsonl
```

Exits 0 (OK), 1 (REGRESSION), or 2 (file/arg error). Default
threshold: +20 % on peak RSS; override with `--threshold 0.30`. The
shipped `baseline.json` contains placeholder zeros — re-run
`compare_memory.py record ...` for each of the three P-1 workloads on
the target machine to populate real numbers before relying on the
regression check.

To smoke-test the comparator without running GAP:

```bash
python3 compare_memory.py selftest
```

This builds a synthetic baseline + two synthetic JSONL runs in a
temp dir and verifies that a fake +50 % run is flagged REGRESSION
and a fake +5 % run is OK.

### Available memory workloads

The runner reuses the P-1 `workloads/` directory. The three workloads
shipped with P-1 (and listed in `baseline.json`) are:

| Name | What it profiles |
|---|---|
| `eplus3_build_per_class_cocycle_basis` | `BuildPerClassCocycleBasis` on one `\|C\|=64` orbit-2 rep of E_+(3); ~130 s wall. |
| `eplus3_iscoboundary2_one_call` | One `IsCoboundary2Split` call after building the same cache; ~130 s wall (dominated by cache). |
| `eplus3_per_gen_brw_two_calls` | Two consecutive `PerGeneratorTransgressionBRW` calls on E_+(3) to exercise P-5's cache (1 cold + 1 warm); ~30 min wall. |

## Adding to CI

P-8 (#116) will extend X-4's CI runner to record both wall times
(P-1) and peak RSS (P-7) for these workloads on every push and fail
on >20 % regression in either axis. The baseline file
`memory/baseline.json` is the canonical RSS reference for CI; the
JSONL emitted by `memory_runner.sh` is the canonical run format.
