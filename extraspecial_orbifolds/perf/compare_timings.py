#!/usr/bin/env python3
"""compare_timings.py — P-8 perf-regression gate.

Loads per-test wall times produced by `run_tests.sh` (one
`<TIMING_DIR>/<test_name>.timing` file per test) and compares them
against `test_baselines.json`. Exits non-zero if any test regresses
by more than the configured threshold (default 20%).

The baseline JSON is a record per test:

    {
      "test_d8_regression": {
        "wall_s_median": 5.2,
        "wall_s_runs": [5.1, 5.2, 5.3],
        "_note": "optional human note"
      },
      ...,
      "_meta": {"populated_at": "...", "threshold": 0.20}
    }

Entries with `wall_s_median <= 0` are treated as PLACEHOLDERS and skipped
(a WARNING is emitted, not a FAIL). Tests absent from the baseline are
likewise skipped with a WARNING. Tests absent from the timing dir
(skipped at runtime via FAST=1) are reported as INFO and not counted
against the gate.

Subcommands:
  compare <timing_dir>             default behaviour; exit 1 on regression
  record  <timing_dir> [<runs>]    take median over N runs of <timing_dir>
                                   and update test_baselines.json
  show                             print the baseline table
  selftest                         build synthetic +50% case in a tempdir
                                   and assert exit-code semantics
"""

import argparse
import json
import os
import statistics
import sys
import tempfile
from pathlib import Path


DEFAULT_THRESHOLD = 0.20  # 20% regression budget


def baselines_path() -> Path:
    """Path to the committed baseline file (next to this script)."""
    return Path(__file__).resolve().parent / "test_baselines.json"


def load_baselines(path: Path | None = None) -> dict:
    path = path or baselines_path()
    if not path.exists():
        return {"_meta": {"threshold": DEFAULT_THRESHOLD}}
    return json.loads(path.read_text())


def save_baselines(data: dict, path: Path | None = None) -> None:
    path = path or baselines_path()
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")


def load_timings(timing_dir: Path) -> dict:
    """Return {test_name: wall_s} from <timing_dir>/<name>.timing files."""
    out = {}
    for p in sorted(timing_dir.glob("test_*.timing")):
        name = p.stem
        try:
            wall = float(p.read_text().strip())
        except (ValueError, OSError):
            continue
        out[name] = wall
    return out


def cmd_compare(args):
    timing_dir = Path(args.timing_dir)
    threshold = args.threshold

    baselines = load_baselines()
    new = load_timings(timing_dir)

    rc = 0
    print(f"perf-regression gate (threshold = {threshold:.0%})")
    print(f"  timing dir: {timing_dir}")
    print(f"  baseline:   {baselines_path()}")
    print()

    # Anything in baseline but not measured -> INFO (skipped by FAST=1?).
    # Anything measured but not in baseline -> WARNING.
    # Anything measured AND in baseline -> compare.
    names = sorted(set(new.keys()) | set(baselines.keys()) - {"_meta"})
    for name in names:
        if name == "_meta":
            continue
        if name not in new:
            print(f"  INFO    {name:<48} not measured this run (skipped?)")
            continue
        if name not in baselines:
            print(f"  WARN    {name:<48} {new[name]:>7.2f} s  (no baseline)")
            continue
        bl = baselines[name].get("wall_s_median", 0.0)
        wall = new[name]
        if bl <= 0:
            print(f"  WARN    {name:<48} {wall:>7.2f} s  (placeholder baseline)")
            continue
        delta = (wall - bl) / bl
        if delta > threshold:
            print(f"  FAIL    {name:<48} {wall:>7.2f} s  vs baseline {bl:.2f} s  ({delta:+.1%})")
            rc = 1
        else:
            print(f"  OK      {name:<48} {wall:>7.2f} s  vs baseline {bl:.2f} s  ({delta:+.1%})")
    print()
    if rc == 0:
        print("perf-regression: PASS")
    else:
        print("perf-regression: FAIL")
    return rc


def cmd_record(args):
    """Populate baseline from one or more runs in <timing_dir>.

    A single timing_dir is a single run. To take the median of N runs the
    caller (typically `update_baselines.sh`) iterates: pass `--append-runs`
    on subsequent calls so the per-run list grows.
    """
    timing_dir = Path(args.timing_dir)
    new = load_timings(timing_dir)
    baselines = load_baselines()
    meta = baselines.get("_meta", {})

    for name, wall in new.items():
        entry = baselines.get(name, {"wall_s_runs": []})
        if args.append_runs:
            entry["wall_s_runs"].append(wall)
        else:
            entry["wall_s_runs"] = [wall]
        entry["wall_s_median"] = statistics.median(entry["wall_s_runs"])
        baselines[name] = entry

    meta.setdefault("threshold", DEFAULT_THRESHOLD)
    baselines["_meta"] = meta
    save_baselines(baselines)
    print(f"recorded {len(new)} test timings from {timing_dir}")
    print(f"  baseline updated: {baselines_path()}")
    return 0


def cmd_show(args):
    baselines = load_baselines()
    meta = baselines.get("_meta", {})
    print(f"baseline @ {baselines_path()}")
    print(f"  threshold: {meta.get('threshold', DEFAULT_THRESHOLD):.0%}")
    print()
    for name in sorted(k for k in baselines if k != "_meta"):
        entry = baselines[name]
        bl = entry.get("wall_s_median", 0.0)
        runs = entry.get("wall_s_runs", [])
        flag = "placeholder" if bl <= 0 else ""
        print(f"  {name:<48} median {bl:>7.2f} s   ({len(runs)} runs) {flag}")
    return 0


def cmd_selftest(args):
    """Build a synthetic baseline + runs in a tempdir and assert exit-code semantics."""
    rc_overall = 0

    with tempfile.TemporaryDirectory() as td:
        td_path = Path(td)
        base = td_path / "test_baselines.json"
        timings_ok = td_path / "ok"
        timings_bad = td_path / "bad"
        timings_ok.mkdir()
        timings_bad.mkdir()

        # Baseline: alpha @ 10s, beta @ 20s, gamma @ 5s.
        baselines = {
            "test_alpha": {"wall_s_median": 10.0, "wall_s_runs": [10.0]},
            "test_beta":  {"wall_s_median": 20.0, "wall_s_runs": [20.0]},
            "test_gamma": {"wall_s_median":  5.0, "wall_s_runs": [5.0]},
            "_meta": {"threshold": 0.20},
        }
        base.write_text(json.dumps(baselines))

        # OK run: each within +5%.
        (timings_ok / "test_alpha.timing").write_text("10.4\n")
        (timings_ok / "test_beta.timing").write_text("20.5\n")
        (timings_ok / "test_gamma.timing").write_text("5.0\n")

        # Bad run: alpha at 50% over baseline.
        (timings_bad / "test_alpha.timing").write_text("15.0\n")  # +50%
        (timings_bad / "test_beta.timing").write_text("21.0\n")
        (timings_bad / "test_gamma.timing").write_text("5.1\n")

        # Re-run cmd_compare with overrides.
        old_baselines = baselines_path
        try:
            globals()["baselines_path"] = lambda: base
            class A:
                threshold = 0.20
                timing_dir = str(timings_ok)
            rc1 = cmd_compare(A())
            print()
            class B:
                threshold = 0.20
                timing_dir = str(timings_bad)
            rc2 = cmd_compare(B())
        finally:
            globals()["baselines_path"] = old_baselines

        if rc1 == 0:
            print(f"selftest +5% case -> rc {rc1} = OK ✓")
        else:
            print(f"selftest +5% case -> rc {rc1} (expected 0) FAIL")
            rc_overall = 1
        if rc2 == 1:
            print(f"selftest +50% case -> rc {rc2} = REGRESSION DETECTED ✓")
        else:
            print(f"selftest +50% case -> rc {rc2} (expected 1) FAIL")
            rc_overall = 1

    return rc_overall


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_cmp = sub.add_parser("compare", help="compare a timing dir against the baseline")
    p_cmp.add_argument("timing_dir", help="dir containing <name>.timing files")
    p_cmp.add_argument("--threshold", type=float, default=DEFAULT_THRESHOLD,
                       help="regression budget (default 0.20 = 20%%)")
    p_cmp.set_defaults(func=cmd_compare)

    p_rec = sub.add_parser("record", help="record timings into the baseline JSON")
    p_rec.add_argument("timing_dir", help="dir containing <name>.timing files")
    p_rec.add_argument("--append-runs", action="store_true",
                       help="append to wall_s_runs (rather than replacing)")
    p_rec.set_defaults(func=cmd_record)

    p_show = sub.add_parser("show", help="print the baseline table")
    p_show.set_defaults(func=cmd_show)

    p_self = sub.add_parser("selftest", help="run an internal regression-detection check")
    p_self.set_defaults(func=cmd_selftest)

    args = parser.parse_args()
    sys.exit(args.func(args))


if __name__ == "__main__":
    main()
