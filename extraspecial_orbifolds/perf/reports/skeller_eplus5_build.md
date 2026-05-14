# Profile report: skeller_eplus5_build

- **Workload:** `workloads/skeller_eplus5_build.g`
- **Sample window:** 60 s
- **GAP exit code:** 0
- **Raw capture:** `raw/skeller_eplus5_build.txt`

## Top hot leaves (sample-count, C-level symbol)

| count | % | symbol |
|---:|---:|---|
| 2265 | 23.2% | CollectBags  (in libgap.10.dylib) |
| 2116 | 21.7% | MarkArrayOfBags  (in libgap.10.dylib) |
| 1979 | 20.3% | PositionPRec  (in libgap.10.dylib) |
| 1735 | 17.8% | DoExecFunc1args  (in libgap.10.dylib) |
| 1661 | 17.0% | EvalFunccall1args  (in libgap.10.dylib) |

## Notes

- `sample` only resolves C-level symbols, so the GAP function names don't appear in the table above.
- To find the GAP-level hot path, open `raw/skeller_eplus5_build.txt` and follow the chain of `EvalFunccall*` / `ExecFor*` interpreter frames around the dominant leaf.
- The dominant leaf and the workload's reported wall-time line (below) usually pinpoint the fix together.

## Workload stdout (last 30 lines)

```

#I  polymake command not found. Please set POLYMAKE_COMMAND by hand
#I  HAP warning: Set NEATO_PATH manually if needed.
#I  HAP warning: Set DOT_PATH manually if needed.
#I  HAP warning: Set DISPLAY_PATH manually if needed.
#I  HAP warning: Set BROWSER_PATH manually if needed.
#I  HAP warning: Set ASY_PATH manually if needed.

=== workload: BuildIntertwinerDataUntwisted on E_+(5) ===
E_+(5) built (|G| = 2048)
BuildSimpleIndex wall: 96.63 s
  num classes: 1025
BuildTransports wall: 0.218 s
workload total wall: 96.958 s
DONE
```
