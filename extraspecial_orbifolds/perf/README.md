# Profile harness (P-1, P-EPIC = issue #109)

Standardises the `sample`-based profile + report workflow we used ad
hoc when debugging the A-3a driver slowness. One workload script per
hot path; one report per run.

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

## Adding to CI

P-8 (#116) will extend X-4's CI runner to record wall times for these
workloads on every push and fail on >20 % regression.
