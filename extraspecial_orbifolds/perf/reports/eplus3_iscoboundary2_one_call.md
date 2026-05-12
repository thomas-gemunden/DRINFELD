# Profile report: eplus3_iscoboundary2_one_call

- **Workload:** `workloads/eplus3_iscoboundary2_one_call.g`
- **Sample window:** 60 s
- **GAP exit code:** 0
- **Raw capture:** `raw/eplus3_iscoboundary2_one_call.txt`

## Top hot leaves (sample-count, C-level symbol)

| count | % | symbol |
|---:|---:|---|
| 15683 | 37.2% | PosPlist  (in libgap.10.dylib) |
| 13985 | 33.2% | EqPlist  (in libgap.10.dylib) |
| 7625 | 18.1% | PosPlistDense  (in libgap.10.dylib) |
| 3138 | 7.4% | EqNot  (in libgap.10.dylib) |
| 1736 | 4.1% | IncRecursionDepth  (in libgap.10.dylib) |

## Notes

- `sample` only resolves C-level symbols, so the GAP function names don't appear in the table above.
- To find the GAP-level hot path, open `raw/eplus3_iscoboundary2_one_call.txt` and follow the chain of `EvalFunccall*` / `ExecFor*` interpreter frames around the dominant leaf.
- The dominant leaf and the workload's reported wall-time line (below) usually pinpoint the fix together.

## Workload stdout (last 30 lines)

```

#I  polymake command not found. Please set POLYMAKE_COMMAND by hand
#I  HAP warning: Set NEATO_PATH manually if needed.
#I  HAP warning: Set DOT_PATH manually if needed.
#I  HAP warning: Set DISPLAY_PATH manually if needed.
#I  HAP warning: Set BROWSER_PATH manually if needed.
#I  HAP warning: Set ASY_PATH manually if needed.
Finished loading Modular Data.g
Syntax warning: Unbound global variable in transgression_kernel.g:120
    sol := AugmentedSolve(A, b, m, n);
           ^^^^^^^^^^^^^^
Syntax warning: Unbound global variable in transgression_kernel.g:130
        List([1..n_eq], j -> If_(i = j, -m, 0))));
                             ^^^

=== workload: IsCoboundary2Split one call on E_+(3) |C|=64 ===
setup wall: 4.246 s
k = 35
rep: f1 (|C| = 64)
cache build wall: 123.139 s

Timing one IsCoboundary2Split call ...
IsCoboundary2Split wall: 0.013 s   (result = true)
Projection: 35 calls per orbit = 0.007583333333333333 min wall.
workload total wall: 127.405 s
DONE
```
