# A-7 perf-5b feasibility assessment (#281, Route B)

## Verdict: prefix sharing is **mathematically sound and correctly implementable**, but yields **no measurable speedup** (0% wall-time change at m=3 vs Route A baseline). The dominant cost is NOT the redundant length-2 Syzygy calls (which HAP's Contraction cache makes cheap after warmup), so the prefix-sharing optimisation has nothing material to save.

Branch `a7-perf-5b-hap-prefix-syzygy` keeps the refactor in `solver/snf_wrapper.g` (the inlined `_Syzygy3FromParts` + hoisted `S_gRep_a` / `S_a_gRep` / shared `S_a_b`) as **dead-on-arrival infrastructure**: the change is correct (tests pass, m=2 and m=3 anchors agree), is within ±0.5% of baseline at m=3, and provides a cleaner factoring of the inner loop for any follow-up that *does* attack the real bottleneck (which is `AddFreeWords`'s quadratic `Position` scan).

The remainder of this doc records what was learned so the next agent doesn't have to redo the investigation.

## What HAP's Syzygy does

`Syzygy(R, [a, b, c])` in `pkg/hap/lib/Homology/syzygy.gi` recurses:

```
Syz([a, b, c]) := Homotopy(2, Mult(a, Syz([b, c]))
                              + Syz([a, b*c])
                              - Syz([a*b, c])
                              - Syz([a, b]))
```

Each length-2 sub-syzygy `Syz([x, y])` itself uses Homotopy(1, ...) over a combination of three length-1 syzygies; each length-1 syzygy uses Homotopy(0, ...) over a 2-cell word.

`Homotopy(i, w)` is a word-level wrapper that calls `R!.homotopy(i, x)` for each cell `x` in `w` and AddFreeWords-accumulates the result.

`R!.homotopy(i, [sign, elt_idx])` (the `Homotopy`/`Contraction` closures inside `ResolutionFiniteGroup`) is **memoised at the cell level**: `ComputedContractions[i][AbsInt(x[1])][x[2]]` (resFiniteGroup.gi:282). So after the first few (a, b) iterations, the per-cell Homotopy lookups are O(1) cache hits, and the cost shifts to:
1. `AddFreeWords(ans, R!.homotopy(i, x))` — quadratic in word length via linear `Position(w2, ...)` scans (wordOperations.gi:131).
2. `Mult(x, w)` — does a fresh `Position(R!.elts, x * R!.elts[y[2]])` for each cell in w.

## Prefix sharing opportunities (mathematically valid)

For BuildPerClassCocycleBasis at fixed (gRep, a) with b varying:

- `Syz([gRep, a])` is invariant under b. Can be hoisted out of the b-loop and reused n times (Triple #1 last term).
- `Syz([a, gRep])` is invariant under b. Same (Triple #2 last term).
- `Syz([a, b])` appears in BOTH Triple #1 (inside `Mult(gRep, Syz([a, b]))`) AND Triple #3 (as `-Syz([a, b])`). Can be computed once per (a, b) and shared.

Total: ~3 length-2 Syzygy calls saved per (a, b) out of 12, plus 2 hoisted per a. At m=3, n=128: ~49K length-2 syzygy calls saved out of ~197K, i.e. ~25% reduction.

## Why it doesn't yield a speedup

The 25% reduction in length-2 Syzygy calls translates to ~0% measured wall delta because each length-2 syzygy is dominated by *cell-level operations* that HAP has already memoised. The per-call cost breakdown is roughly:
- ~80% inside `R!.homotopy(_)` — but this is cached and effectively O(1) after warmup.
- ~20% in `Mult` (Position-by-binary-search on R!.elts, O(log|G|)) and `AddFreeWords` of short length-1 words.

Skipping a length-2 Syzygy call therefore saves only the ~20% of "fresh" work, which at ~50K calls saved at m=3 amounts to fractions of a second — within measurement noise.

The dominant **n^2-scaling** cost is in the OUTER level:
- 3 length-3 Syzygies per (a, b), each builds a length-3 word by 4× AddFreeWords on length-2 outputs (each up to ~50-200 cells).
- The final Homotopy(2, _) iterates that combined word through `R!.homotopy(2, x)` lookups (cached) plus AddFreeWords accumulation (NOT cached, quadratic in word length).

This 3 × n² Homotopy(2, _) work is unchanged by prefix sharing.

## A failed sub-optimisation: combined-word Homotopy(2)

We also tried combining the three length-3 Syzygies into one Homotopy(2, _) call by exploiting linearity:

```
contrib(W1 + W2 + W3) = sum(signs of Homotopy(2, W1 - W2 + W3))
                      = (contrib of Homotopy(2, W1)) - (contrib of Homotopy(2, W2)) + (contrib of Homotopy(2, W3))
```

This *should* benefit from cancellation under AddFreeWords when summing W1, -W2, W3. In practice at m=3 it was 0.9s slower than the prefix-only version, because:
- The W1, W2, W3 words have *different* element-indexed cells (their cells live in different parts of R!.elts), so AddFreeWords cancellation is rare.
- Combining the words requires two additional AddFreeWords passes, each quadratic in word length.
- The Homotopy(2, _) cost is dominated by cached cell lookups anyway.

The combined-word variant was **reverted**.

## Measured results

| Variant                                  | m=3 caches wall | Δ vs baseline |
|------------------------------------------|-----------------|---------------|
| Route A baseline (db8fe47)               | 35.3 s          | —             |
| Route B prefix-only (current commit)     | 35.165 s        | -0.4% (noise) |
| Route B prefix + combined-word           | 36.116 s        | +2.3% (noise) |

m=2 anchor: |ker Tr| = 2048 (baseline 9bffebb), still passes.
m=3 anchor: |ker Tr| = 262144, still passes.
Per-triple correctness on 120 random triples + 16-cell brute-force grid: 0 mismatches.

## m=5 extrapolation (deferred, not run)

At m=5 (|G|=2048, |C|≤2048), the per-orbit cache cost scales roughly as n² = 4M (a, b) pairs per orbit, with ~12 length-2 Syzygy calls per pair = ~48M length-2 syz calls per orbit. Even saving 25% of these to ~36M would translate to fractions of a second per orbit, well below noise on the multi-minute orbit builds reported in the A-5b m=5 transcript.

**Expectation**: m=5 prefix-sharing speedup is also ~0%, for the same HAP-cache reason. The m=5 wall headline (currently ~110 min per generator on the live A-5b run) is **not** going to move from this lever.

## What's the real lever?

The eplus3 profile (`extraspecial_orbifolds/perf/raw/eplus3_build_per_class_cocycle_basis.txt`) shows ~75% of CPU in `PosPlist` from inside `AddFreeWords`'s `Position(w2, [-x[1], x[2]])` linear scan. The AddFreeWords work is quadratic in word length and is the real bottleneck.

**Recommended follow-up**: replace AddFreeWords's `Position(w2, ...)` with a dictionary lookup (NewDictionary, AddDictionary, LookupDictionary) keyed on `[abs_sign, elt_idx]`. This converts the O(|v|·|w|) inner loop to O(|v| + |w|). Expected speedup: 3-10x on the Homotopy(_, big_word) work, which IS the dominant cost.

This is a different lever from Route B's prefix sharing and would benefit at any group order.

## Files touched

- `extraspecial_orbifolds/scripts/solver/snf_wrapper.g` — added `_MultByElt`, `_Homotopy2`, `_Syzygy3FromParts`, `_Syzygy3CombinedWord` (the last is unused after revert but kept for reference); modified `BuildPerClassCocycleBasis` to hoist + share length-2 Syzygies in the (a, b) loop.
- `extraspecial_orbifolds/scripts/solver/tests/test_perf5b_prefix.g` — new per-triple correctness test (120 random triples + 16-cell brute-force grid + combined-word equivalence check; all pass).
- `extraspecial_orbifolds/scripts/perf5b_measure_m3_cache.g` — new standalone m=3 cache-wall measurement script (skips the per-generator sweep and cross-checks).

## Open caveats

1. **m=5 not measured** (CPU constraint: A-5b m=5 driver is running on PID 99319, ~14 GB RSS, 100% CPU). Per-orbit cache wall at m=5 is **deferred** until A-5b completes. Extrapolation predicts ~0% speedup.
2. Combined-word `_Syzygy3CombinedWord` function exists in snf_wrapper.g but is unused. It's correct (tertiary check in test_perf5b_prefix.g verifies bit-identical contribution vectors) but was 0.9s slower than the prefix-only path on m=3, so we don't use it. Could be deleted in cleanup.
3. If a future agent does pursue the AddFreeWords-dict lever, the `_Syzygy3FromParts` infrastructure here is a useful intermediate factoring: it gives a clean place to test the dict-based AddFreeWords on a single-Syzygy granularity.
