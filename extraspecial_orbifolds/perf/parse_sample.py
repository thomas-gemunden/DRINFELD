#!/usr/bin/env python3
"""parse_sample.py — turn a macOS `sample` capture into a markdown report.

The expected input is the file produced by `sample <PID> <secs> -file <out>`.
The report extracts:
  * the "Sort by top of stack" leaves table (top-3),
  * the deepest single-frame chain that accumulates most samples
    (best-effort identification of the GAP-level call site),
  * the workload's stdout (last 30 lines), to capture any wall-time
    line the workload printed.

We deliberately do NOT try to symbolicate GAP-level function names from
the raw stack; macOS `sample` only resolves C symbols. Instead the
parser pulls out the largest single-frame fan-out (something like
`22831 EvalFunccall2args ... + 16699 PosPlist`) and the workload's
self-reported timing, leaving the human reviewer to correlate the two.
"""

import argparse
import re
import sys
from pathlib import Path


def parse_leaves(raw: str, top_n: int = 5):
    """Extract the 'Sort by top of stack' section."""
    m = re.search(
        r"Sort by top of stack[^\n]*\n((?:\s+\S.*\d+\n)+)",
        raw,
    )
    if not m:
        return []
    rows = []
    for line in m.group(1).splitlines():
        line = line.strip()
        # Pattern: "FuncName  (in lib.dylib)        12345"
        parts = re.split(r"\s{2,}", line)
        # Last token is the count.
        if not parts:
            continue
        try:
            count = int(parts[-1])
        except ValueError:
            continue
        name_part = "  ".join(parts[:-1]).strip() if len(parts) > 1 else line
        rows.append((name_part, count))
        if len(rows) >= top_n:
            break
    return rows


def parse_hot_path_excerpt(raw: str, max_lines: int = 8):
    """Extract a tail of the deepest concentrated branch of the call
    graph, for human inspection. Heuristic: walk from the end of the
    'Call graph:' section backwards and collect the first contiguous
    block of lines with single-call-stack frames at the deepest indent.
    """
    # Find the end of the call graph section (just before
    # "Binary Images:" or "Sort by top of stack").
    cg_end = raw.find("Binary Images:")
    if cg_end == -1:
        cg_end = raw.find("Sort by top of stack")
    if cg_end == -1:
        cg_end = len(raw)
    cg = raw[:cg_end]

    # Find the maximum indent in the call graph.
    lines = [ln for ln in cg.splitlines() if ln.strip()]
    max_indent = 0
    for ln in lines:
        m = re.match(r"^(\s+)", ln)
        if m:
            max_indent = max(max_indent, len(m.group(1)))
    if max_indent == 0:
        return ""

    # Return the last `max_lines` lines that are at indent >= 80% of max.
    threshold = int(0.8 * max_indent)
    deep_lines = [ln for ln in lines
                  if (m := re.match(r"^(\s+)", ln)) and len(m.group(1)) >= threshold]
    return "\n".join(deep_lines[-max_lines:])


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--raw", required=True)
    p.add_argument("--log", required=True)
    p.add_argument("--workload", required=True)
    p.add_argument("--secs", type=int, required=True)
    p.add_argument("--gap-exit", type=int, required=True)
    p.add_argument("--out", required=True)
    args = p.parse_args()

    raw_path = Path(args.raw)
    log_path = Path(args.log)
    out_path = Path(args.out)

    raw = raw_path.read_text() if raw_path.exists() else ""
    log_tail = ""
    if log_path.exists():
        log_lines = log_path.read_text().splitlines()
        log_tail = "\n".join(log_lines[-30:])

    leaves = parse_leaves(raw)
    total = sum(c for _, c in leaves) if leaves else 0

    lines = []
    lines.append(f"# Profile report: {args.workload}")
    lines.append("")
    lines.append(f"- **Workload:** `workloads/{args.workload}.g`")
    lines.append(f"- **Sample window:** {args.secs} s")
    lines.append(f"- **GAP exit code:** {args.gap_exit}")
    lines.append(f"- **Raw capture:** `raw/{args.workload}.txt`")
    lines.append("")
    lines.append("## Top hot leaves (sample-count, C-level symbol)")
    lines.append("")
    if leaves:
        lines.append("| count | % | symbol |")
        lines.append("|---:|---:|---|")
        for sym, count in leaves:
            pct = 100.0 * count / total if total else 0.0
            lines.append(f"| {count} | {pct:.1f}% | {sym} |")
    else:
        lines.append("(no leaves parsed; check raw sample)")
    lines.append("")

    lines.append("## Notes")
    lines.append("")
    lines.append("- `sample` only resolves C-level symbols, so the GAP "
                 "function names don't appear in the table above.")
    lines.append("- To find the GAP-level hot path, open "
                 "`raw/{0}.txt` and follow the chain of `EvalFunccall*` / "
                 "`ExecFor*` interpreter frames around the dominant leaf.".format(args.workload))
    lines.append("- The dominant leaf and the workload's reported wall-time "
                 "line (below) usually pinpoint the fix together.")
    lines.append("")

    lines.append("## Workload stdout (last 30 lines)")
    lines.append("")
    lines.append("```")
    lines.append(log_tail if log_tail else "(no log captured)")
    lines.append("```")
    lines.append("")

    out_path.write_text("\n".join(lines))
    print(f"  wrote {out_path}")


if __name__ == "__main__":
    main()
