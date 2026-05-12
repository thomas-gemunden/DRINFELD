# Profile report: eplus3_per_generator_brw_one_gen

- **Workload:** `workloads/eplus3_per_generator_brw_one_gen.g`
- **Sample window:** 60 s
- **GAP exit code:** 0
- **Raw capture:** `raw/eplus3_per_generator_brw_one_gen.txt`

## Top hot leaves (sample-count, C-level symbol)

| count | % | symbol |
|---:|---:|---|
| 4572 | 25.5% | MarkArrayOfBags  (in libgap.10.dylib) |
| 4386 | 24.5% | CollectBags  (in libgap.10.dylib) |
| 3718 | 20.7% | LtPlist  (in libgap.10.dylib) |
| 2805 | 15.6% | DoExecFunc1args  (in libgap.10.dylib) |
| 2455 | 13.7% | EqPlist  (in libgap.10.dylib) |

## Notes

- `sample` only resolves C-level symbols, so the GAP function names don't appear in the table above.
- To find the GAP-level hot path, open `raw/eplus3_per_generator_brw_one_gen.txt` and follow the chain of `EvalFunccall*` / `ExecFor*` interpreter frames around the dominant leaf.
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
Finished loading Modular Data.g

=== workload: PerGeneratorTransgressionBRW(G, 1) on E_+(3) ===
Group order: 128
WARNING: G is not the identical EmGroup(m) group object; results assume identi\
cal conjugacy class numbering.
```
