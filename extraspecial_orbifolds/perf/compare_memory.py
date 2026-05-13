#!/usr/bin/env python3
"""compare_memory.py — P-7 memory baseline tool (issue #115).

Three subcommands operate on JSONL runs produced by memory_runner.sh:

  summarise <run.jsonl>
      Print peak / end / mean RSS for a single run.

  record <workload> <run.jsonl> [--baseline ...]
      Record the given run as the baseline for <workload> in
      baseline.json, overwriting any existing entry.

  compare <workload> <run.jsonl> [--baseline ...] [--threshold 0.20]
      Compare the run against the baseline entry and emit
      "OK" or "REGRESSION" with deltas. The intent is that CI
      (P-8 #116) will use this exact subcommand and exit code.

  selftest
      Synthetic smoke test: builds a baseline JSON and two JSONL runs
      in a temp dir, then verifies that compare flags a +50 % run as
      REGRESSION and a +5 % run as OK. Exits 0 on success.

JSONL run format (one object per line, produced by memory_runner.sh):
    {"t": <unix-seconds>, "rss_kb": <int-kb>}

Baseline JSON format:
    {
      "<workload_name>": {
        "peak_rss_mb": <float>,
        "end_rss_mb":  <float>,
        "mean_rss_mb": <float>,
        "wall_s":      <int>
      },
      ...
    }

Exit codes for `compare`:
    0  - OK (or workload not in baseline; warning emitted)
    1  - REGRESSION
    2  - argument / file error
"""

import argparse
import json
import sys
import tempfile
from pathlib import Path


def load_jsonl(path: Path):
    samples = []
    with path.open() as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            try:
                samples.append(json.loads(line))
            except json.JSONDecodeError:
                # Skip malformed lines, keep going.
                continue
    return samples


def summarise(samples):
    """Reduce a JSONL run to (peak_mb, end_mb, mean_mb, wall_s)."""
    if not samples:
        return None
    rss_kb = [s["rss_kb"] for s in samples if "rss_kb" in s]
    if not rss_kb:
        return None
    peak_mb = max(rss_kb) / 1024.0
    end_mb = rss_kb[-1] / 1024.0
    mean_mb = sum(rss_kb) / len(rss_kb) / 1024.0
    ts = [s["t"] for s in samples if "t" in s]
    wall_s = (max(ts) - min(ts)) if len(ts) >= 2 else 0
    return peak_mb, end_mb, mean_mb, wall_s


def default_baseline_path() -> Path:
    return Path(__file__).parent / "memory" / "baseline.json"


def load_baseline(path: Path) -> dict:
    if not path.is_file():
        return {}
    with path.open() as fh:
        return json.load(fh)


def cmd_summarise(args) -> int:
    run_path = Path(args.run_jsonl)
    if not run_path.is_file():
        print(f"error: run jsonl not found: {run_path}", file=sys.stderr)
        return 2
    summary = summarise(load_jsonl(run_path))
    if summary is None:
        print(f"error: no samples in {run_path}", file=sys.stderr)
        return 2
    peak_mb, end_mb, mean_mb, wall_s = summary
    print(f"# Run summary: {run_path}")
    print(f"  peak_mb: {peak_mb:.1f}")
    print(f"  end_mb:  {end_mb:.1f}")
    print(f"  mean_mb: {mean_mb:.1f}")
    print(f"  wall_s:  {wall_s}")
    return 0


def cmd_record(args) -> int:
    run_path = Path(args.run_jsonl)
    baseline_path = Path(args.baseline) if args.baseline else default_baseline_path()
    if not run_path.is_file():
        print(f"error: run jsonl not found: {run_path}", file=sys.stderr)
        return 2
    summary = summarise(load_jsonl(run_path))
    if summary is None:
        print(f"error: no samples in {run_path}", file=sys.stderr)
        return 2
    peak_mb, end_mb, mean_mb, wall_s = summary
    baseline = load_baseline(baseline_path)
    baseline[args.workload] = {
        "peak_rss_mb": round(peak_mb, 1),
        "end_rss_mb": round(end_mb, 1),
        "mean_rss_mb": round(mean_mb, 1),
        "wall_s": wall_s,
    }
    baseline_path.parent.mkdir(parents=True, exist_ok=True)
    with baseline_path.open("w") as fh:
        json.dump(baseline, fh, indent=2, sort_keys=True)
        fh.write("\n")
    print(f"# Baseline updated: {baseline_path}")
    print(f"  {args.workload}: peak_mb={peak_mb:.1f} end_mb={end_mb:.1f} "
          f"mean_mb={mean_mb:.1f} wall_s={wall_s}")
    return 0


def cmd_compare(args) -> int:
    run_path = Path(args.run_jsonl)
    baseline_path = Path(args.baseline) if args.baseline else default_baseline_path()
    if not baseline_path.is_file():
        print(f"error: baseline file not found: {baseline_path}", file=sys.stderr)
        return 2
    if not run_path.is_file():
        print(f"error: run jsonl not found: {run_path}", file=sys.stderr)
        return 2
    baseline = load_baseline(baseline_path)
    summary = summarise(load_jsonl(run_path))
    if summary is None:
        print(f"error: no samples in {run_path}", file=sys.stderr)
        return 2
    peak_mb, end_mb, mean_mb, wall_s = summary

    print(f"# Memory comparison: {args.workload}")
    print(f"  run jsonl:  {run_path}")
    print(f"  baseline:   {baseline_path}")
    print(f"  threshold:  +{args.threshold:.0%} on peak RSS")
    print()
    print(f"  new peak_mb:  {peak_mb:.1f}")
    print(f"  new end_mb:   {end_mb:.1f}")
    print(f"  new mean_mb:  {mean_mb:.1f}")
    print(f"  new wall_s:   {wall_s}")

    if args.workload not in baseline:
        print()
        print(f"WARNING: workload '{args.workload}' not in baseline. "
              "Treating as OK; record a baseline with this name "
              "(`record` subcommand) to enable regression checks.")
        return 0

    base = baseline[args.workload]
    base_peak = base["peak_rss_mb"]

    # A placeholder baseline (peak_rss_mb = 0) means "not yet
    # recorded on this machine"; treat as a warning, not a regression.
    if base_peak <= 0:
        print()
        print(f"WARNING: baseline peak_rss_mb for '{args.workload}' is "
              f"{base_peak} (placeholder). Run "
              f"`compare_memory.py record {args.workload} "
              f"<run.jsonl>` to populate a real baseline. Treating as OK.")
        return 0

    delta_abs = peak_mb - base_peak
    delta_frac = delta_abs / base_peak

    print()
    print(f"  base peak_mb: {base_peak:.1f}")
    print(f"  base end_mb:  {base.get('end_rss_mb', float('nan')):.1f}")
    print(f"  base wall_s:  {base.get('wall_s', float('nan'))}")
    print()
    print(f"  delta peak_mb: {delta_abs:+.1f} MB  ({delta_frac:+.1%})")
    print()

    if delta_frac > args.threshold:
        print(f"REGRESSION: peak RSS up by {delta_frac:+.1%} "
              f"(>{args.threshold:.0%} threshold).")
        return 1
    print(f"OK: peak RSS within +{args.threshold:.0%} threshold "
          f"(actual {delta_frac:+.1%}).")
    return 0


def cmd_selftest(_args) -> int:
    """Build synthetic baseline + JSONL and verify regression detection.

    Used to verify the comparator's logic end-to-end without needing
    to run GAP. The acceptance criterion for #115 says "compare_memory
    correctly flags a fake +50% regression"; this is that check.
    """
    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        baseline_path = tmp / "baseline.json"
        baseline = {
            "demo": {
                "peak_rss_mb": 1000.0,
                "end_rss_mb": 800.0,
                "mean_rss_mb": 700.0,
                "wall_s": 60,
            }
        }
        baseline_path.write_text(json.dumps(baseline, indent=2) + "\n")

        # +50% peak run: peak 1500 MB == 1536000 KB.
        # Times must monotonically increase so wall_s is positive.
        regress = tmp / "regress.jsonl"
        with regress.open("w") as fh:
            fh.write('{"t": 1000, "rss_kb": 1024000}\n')
            fh.write('{"t": 1010, "rss_kb": 1536000}\n')
            fh.write('{"t": 1020, "rss_kb": 1500000}\n')

        # +5% peak run: peak 1050 MB == 1075200 KB. Within threshold.
        ok = tmp / "ok.jsonl"
        with ok.open("w") as fh:
            fh.write('{"t": 2000, "rss_kb": 800000}\n')
            fh.write('{"t": 2010, "rss_kb": 1075200}\n')
            fh.write('{"t": 2020, "rss_kb": 900000}\n')

        # Run both comparisons via the in-process compare command.
        class Ns:  # lightweight argparse.Namespace stand-in
            pass

        # Regression case.
        a = Ns()
        a.workload = "demo"
        a.run_jsonl = str(regress)
        a.baseline = str(baseline_path)
        a.threshold = 0.20
        print("--- regression case (expect exit 1) ---")
        rc_regress = cmd_compare(a)

        # OK case.
        a2 = Ns()
        a2.workload = "demo"
        a2.run_jsonl = str(ok)
        a2.baseline = str(baseline_path)
        a2.threshold = 0.20
        print()
        print("--- ok case (expect exit 0) ---")
        rc_ok = cmd_compare(a2)

        # Verify exit codes.
        print()
        if rc_regress == 1 and rc_ok == 0:
            print("SELFTEST PASS: regression case returned 1, "
                  "ok case returned 0.")
            return 0
        print(f"SELFTEST FAIL: regress rc={rc_regress} "
              f"(want 1), ok rc={rc_ok} (want 0).")
        return 1


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)

    p_sum = sub.add_parser("summarise",
                           help="Print peak/end/mean RSS for a JSONL run.")
    p_sum.add_argument("run_jsonl")

    p_rec = sub.add_parser("record",
                           help="Record a JSONL run as baseline for <workload>.")
    p_rec.add_argument("workload")
    p_rec.add_argument("run_jsonl")
    p_rec.add_argument("--baseline", default=None,
                       help="Baseline JSON path "
                            "(default: perf/memory/baseline.json)")

    p_cmp = sub.add_parser("compare",
                           help="Compare a JSONL run against baseline.")
    p_cmp.add_argument("workload")
    p_cmp.add_argument("run_jsonl")
    p_cmp.add_argument("--baseline", default=None,
                       help="Baseline JSON path "
                            "(default: perf/memory/baseline.json)")
    p_cmp.add_argument("--threshold", type=float, default=0.20,
                       help="Fractional peak-RSS regression threshold "
                            "(default 0.20 = 20%%)")

    sub.add_parser("selftest",
                   help="Synthetic smoke test of the regression check.")

    args = ap.parse_args()

    handlers = {
        "summarise": cmd_summarise,
        "record": cmd_record,
        "compare": cmd_compare,
        "selftest": cmd_selftest,
    }
    return handlers[args.cmd](args)


if __name__ == "__main__":
    sys.exit(main())
