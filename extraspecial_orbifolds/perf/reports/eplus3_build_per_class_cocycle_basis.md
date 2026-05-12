# Profile report: eplus3_build_per_class_cocycle_basis

- **Workload:** `workloads/eplus3_build_per_class_cocycle_basis.g`
- **Sample window:** 30 s
- **GAP exit code:** 0
- **Raw capture:** `raw/eplus3_build_per_class_cocycle_basis.txt`

## Top hot leaves (sample-count, C-level symbol)

| count | % | symbol |
|---:|---:|---|
| 8753 | 41.5% | PosPlist  (in libgap.10.dylib) |
| 7382 | 35.0% | EqPlist  (in libgap.10.dylib) |
| 2525 | 12.0% | PosPlistDense  (in libgap.10.dylib) |
| 1465 | 6.9% | EqNot  (in libgap.10.dylib) |
| 965 | 4.6% | IncRecursionDepth  (in libgap.10.dylib) |

## Notes

- `sample` only resolves C-level symbols, so the GAP function names don't appear in the table above.
- To find the GAP-level hot path, open `raw/eplus3_build_per_class_cocycle_basis.txt` and follow the chain of `EvalFunccall*` / `ExecFor*` interpreter frames around the dominant leaf.
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

=== workload: BuildPerClassCocycleBasis on E_+(3) orbit-2 ===
Group order: 128
setup wall: 4.087 s
k = 35 H^3 generators
orbit-2 rep: f1  (order 2, |C| = 64)
BuildPerClassCocycleBasis wall: 124.244 s
cache table: 4096 x 35
workload total wall: 128.334 s
DONE
```
