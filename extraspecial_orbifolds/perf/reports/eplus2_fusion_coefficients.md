# Profile report: eplus2_fusion_coefficients

- **Workload:** `workloads/eplus2_fusion_coefficients.g`
- **Sample window:** 30 s
- **GAP exit code:** 0
- **Raw capture:** `raw/eplus2_fusion_coefficients.txt`

## Top hot leaves (sample-count, C-level symbol)

| count | % | symbol |
|---:|---:|---|
| 882 | 26.4% | ProdInt  (in libgap.10.dylib) |
| 759 | 22.7% | GcdInt  (in libgap.10.dylib) |
| 717 | 21.4% | FAKEMPZ_GMPorINTOBJ  (in libgap.10.dylib) |
| 514 | 15.4% | __gmpn_gcd_1  (in libgmp.10.dylib) |
| 471 | 14.1% | GMP_NORMALIZE  (in libgap.10.dylib) |

## Notes

- `sample` only resolves C-level symbols, so the GAP function names don't appear in the table above.
- To find the GAP-level hot path, open `raw/eplus2_fusion_coefficients.txt` and follow the chain of `EvalFunccall*` / `ExecFor*` interpreter frames around the dominant leaf.
- The dominant leaf and the workload's reported wall-time line (below) usually pinpoint the fix together.

## Workload stdout (last 30 lines)

```

Loaded aut_nt_refine.g (RefineByFusion, RefineOnePass, FusionRowSignature, Fus\
ionCoefficientsFromS, ColourFromPartition, PartitionCanonical).
#I  polymake command not found. Please set POLYMAKE_COMMAND by hand
#I  HAP warning: Set NEATO_PATH manually if needed.
#I  HAP warning: Set DOT_PATH manually if needed.
#I  HAP warning: Set DISPLAY_PATH manually if needed.
#I  HAP warning: Set BROWSER_PATH manually if needed.
#I  HAP warning: Set ASY_PATH manually if needed.

=== workload: FusionCoefficientsFromS on D^0(E_+(2)) ===
rank r = 184
S matrix nonzero entries: 17536 / 33856 (51.79584120982987%)

Calling FusionCoefficientsFromS ...
wall: 10.8 s
N tensor: 65536 / 6229504 nonzero (1.052025971891181%)
DONE
```
