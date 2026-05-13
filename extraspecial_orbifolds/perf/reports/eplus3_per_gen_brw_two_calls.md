# Profile report: eplus3_per_gen_brw_two_calls

- **Workload:** `workloads/eplus3_per_gen_brw_two_calls.g`
- **Sample window:** 30 s
- **GAP exit code:** 0
- **Raw capture:** `raw/eplus3_per_gen_brw_two_calls.txt`

## Top hot leaves (sample-count, C-level symbol)

| count | % | symbol |
|---:|---:|---|
| 4077 | 32.4% | MarkArrayOfBags  (in libgap.10.dylib) |
| 3617 | 28.7% | CollectBags  (in libgap.10.dylib) |
| 2033 | 16.2% | DoExecFunc1args  (in libgap.10.dylib) |
| 1558 | 12.4% | EvalElmList  (in libgap.10.dylib) |
| 1297 | 10.3% | CollectBags_Mark  (in libgap.10.dylib) |

## Notes

- `sample` only resolves C-level symbols, so the GAP function names don't appear in the table above.
- To find the GAP-level hot path, open `raw/eplus3_per_gen_brw_two_calls.txt` and follow the chain of `EvalFunccall*` / `ExecFor*` interpreter frames around the dominant leaf.
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

=== workload: PerGeneratorTransgressionBRW x 2 on E_+(3) ===
WARNING: G is not the identical EmGroup(m) group object; results assume identi\
cal conjugacy class numbering.
call 1 (i=1) wall: 1884.739 s
WARNING: G is not the identical EmGroup(m) group object; results assume identi\
cal conjugacy class numbering.
call 2 (i=2) wall: 6.033 s

Speedup ratio (cache effect): 312.4049394994199x
Per-call wall extrapolated for 35-gen driver:
  cold:  1884.739 s
  warm:  6.033 s
  total (1 cold + 34 warm) projection: 2089.861 s
DONE
```
