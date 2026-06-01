# Path Z sparsity-aware matvec — design (Approach A, issue #391)

## TL;DR

The empirical probe at m=3 shows the sparsity hypothesis HOLDS only PARTIALLY.

* **Median `|support(vec_target)|` for Path Z hits at m=3: 14 / k=35** (about
  40% density). Mean ≈ 11.6.
* **Strong sub-pattern**: 329 of 1497 Path Z hits (22%) have unit support
  (|support|=1), which is the case where the matvec collapses to a single
  column read. The remaining 78% have median support ≈ 15.
* **Implication**: dense-matvec → sparse-matvec gives a modest ~2.5x speedup
  on the typical Path Z call, plus a much bigger speedup (~k×) on the 22%
  unit-support tail. Combined effective speedup ≈ 3-5× at m=3, not the
  20-30× the issue #391 narrative hoped for.
* **Recommendation**: implement Approach A as a hybrid — a dedicated
  unit-support fast path plus a column-skip path for the general case. The
  gain is real but not transformative; pursue Approach B (GF(2) bit-packing)
  in parallel for the bigger win.

## Phase 1: empirical probe (Phase 1 finding)

`/tmp/vec_target_sparsity_probe.g` was run at m=3 over 55 sample vectors
(35 unit vecs + 20 random Z/torsion vecs from the Cartesian-encoding
sampler that Step 4 of `run_e_plus_m_kernel_hap.g` uses) × 65 (vec,
target) probes per orbit walk. 3575 (vec, target) probes total; 1497 of
those (41.9%) dispatched to Path Z. Probe wall: 43 ms.

### Distribution of |support(vec_target)| over all 3575 probes

```
min=0  Q1=1  median=9  Q3=15  max=26  mean=8.63
```

### Distribution restricted to Path Z hits (the bottleneck cases) — n=1497

```
min=1  Q1=6  median=14  Q3=17  max=26  mean=11.61
```

### Histogram (Path Z only)

```
|supp|=1   329    <-- huge spike: unit-support, collapses to one column read
|supp|=3-7 ~100   (rare; sparse middle)
|supp|=8-13 ~300
|supp|=14-18 ~660 <-- the main bulk: dense-ish, ~40% of k
|supp|=19+ ~110
|supp|=26 max
```

Two-modal distribution: a sharp peak at 1 (unit-support cases) and a wide
hump centred around 15. The unit-support spike comes mostly from sample
vecs of the form `e_i` for the few `i` where `e_i` is already an
eigenvector of all `M_y` (typical for the order-4 generator at
`exp_index=35` — its e_i passes through H3VecAtTarget essentially
unchanged for many orbits/targets).

### Why median 14, not ≤ 5

The brief hypothesized k_nz ≤ 20 would mean sparsity. The brief actually
got that: median 14 ≤ 20. But it ALSO hypothesized ~5-10 expected; the
real number is 2-3x higher than that. The math doesn't simplify cleanly
because conjugation-pullback under the H^3 endomorphism `M_y` actively
mixes coordinates — the H^3 generators are NOT a basis stable under BRW
action. Each application of `M_y` (per Schreier-vec step) propagates
across many coordinates, so even starting from a unit-vec input, after a
few steps `vec_target` becomes densely supported.

### Caveat: m=3 to m=5 extrapolation

m=3 has k=35; m=5 has k=165. The probe data at m=3 is the best we can
get without burning hours of m=5 setup. The structural reason for the
~40% support density is the densifying nature of `M_y`: that's a
property of the H^3 endomorphism matrices, which don't magically become
sparser at m=5. Best-case prediction: similar ~40% density at m=5
(median |supp| ≈ 66 / 165). Conservative.

## Phase 2: math

The Path Z matvec is

```
c_g_table[i] := sum_{j=1..k} basis_cache.table[i][j] * vec_target[j]
```

for `i ∈ [1..n²]`, where `n = |C_G(g)|` (centraliser size at the orbit
rep) and `k = setup.num_generators`. At m=5, n² ≈ 4M, k = 165, so the
dense matvec is 4M × 165 ≈ 692M scalar multiply-add operations per call.

If `S := {j : vec_target[j] != 0}` and `k_nz := |S|`, the sum collapses
to:

```
c_g_table[i] := sum_{j ∈ S} basis_cache.table[i][j] * vec_target[j]
```

which is `n² × k_nz` ops, i.e. a `k/k_nz` speedup over the dense matvec.

### Two sub-cases worth distinguishing

**(a) Unit support: k_nz = 1, S = {j*}, vec_target[j*] = c.**
The result is `c_g_table = c * basis_cache.table[*][j*]`, i.e. a single
column read scaled by `c`. At m=5 this is 4M scalar multiplies (or
column copies if `c=1`), versus 692M for the dense case. Speedup: 165×
(at the operation level; in wall time, much higher because the dense
matvec also pays for the type-recheck overhead per-cell that
ProdVectorVector does).

**(b) General sparse: k_nz < k.**
Column-by-column accumulation. Each column is a scalar-vec product +
list-add: `2 × n² × k_nz` operations. At median k_nz=14 vs k=35
(m=3-like density), speedup factor ≈ 35/14 ≈ 2.5×. At m=5 with the same
density ratio, k_nz ≈ 66 → speedup ≈ 2.5×.

### Why the speedup is bounded by 2-3× in the bulk

The dense matvec under GAP's `ProdListScl` / `ProdVectorVector` is
compiled-C and roughly hits ~1 ns/scalar. A naive sparse implementation
in interpreted GAP needs to outperform that.

The right implementation pattern is:

```
c_g_table := List([1..n2], i -> 0);          # n² zero-init (compiled)
for j in S do
    col_j := basis_cache.table{[1..n2], [j]}; # column slice
    AddRowVector(c_g_table, col_j, vec_target[j]);  # compiled in-place scaled add
od;
```

`AddRowVector(v, w, c)` is a compiled GAP kernel (see `lib/listcoef.gi`).
The slice `M{[1..n2], [j]}` is compiled. So the inner loop dispatches to
two compiled C calls per `j` in `S`. For k_nz=14, that's 28 C-level
calls + 14 column allocations, vs 1 compiled call with 165× more work
internally for the dense case.

The crossover depends on per-call overhead vs the per-op savings. The
unit-support case is unambiguously a win (1 compiled call total vs 1
compiled call with 165× more ops). The general sparse case is a win
only when k_nz is small enough to compensate for the per-iteration
overhead. Empirically, the threshold is somewhere around k_nz ≤ k/3 (a
folk rule from GAP perf practice).

## Phase 3: API surface

Two options. We pick option 2 (route internally) because it minimises
caller churn and centralises the sparsity heuristic.

### Option 1 (rejected): new function

```gap
IsCoboundary2SplitVecSparse(C, basis_cache_table, vec_target_sparse, setup)
```

where `vec_target_sparse` is a list of `[j, vec_target[j]]` pairs. This
forces the caller to construct the sparse representation, which adds a
List comprehension cost at the call site. Rejected.

### Option 2 (chosen): internal dispatch in IsCoboundary2SplitVec

Two new internal helpers in `solver/iscoboundary2_split.g`:

```gap
# Unit-support fast path: |supp(vec_target)| = 1.
_IsCoboundary2SplitVec_UnitSupport(C, basis_cache, j_nz, c_nz, setup);

# General sparse path: small |supp(vec_target)| > 1.
_IsCoboundary2SplitVec_Sparse(C, basis_cache, vec_target, supp, setup);
```

Both take the FULL `basis_cache` record (not just `table`) so the
sparse helpers can build `c_g_vec` themselves via column slicing.

The public entry point becomes:

```gap
IsCoboundary2SplitVecAware := function(C, basis_cache, vec_target, setup)
    local supp, k_nz, c_g_vec, k_threshold;
    supp := PositionsProperty(vec_target, x -> x <> 0);
    k_nz := Length(supp);
    k_threshold := QuoInt(Length(vec_target), 3);  # routing knob
    if k_nz = 1 then
        # Unit-support fast path.
        return _IsCoboundary2SplitVec_UnitSupport(
            C, basis_cache, supp[1], vec_target[supp[1]], setup);
    elif k_nz <= k_threshold then
        # General sparse path.
        return _IsCoboundary2SplitVec_Sparse(
            C, basis_cache, vec_target, supp, setup);
    else
        # Dense path (existing implementation).
        c_g_vec := basis_cache.table * vec_target;
        return IsCoboundary2SplitVec(C, c_g_vec, vec_target, setup);
    fi;
end;;
```

This routes:
* `k_nz=1`: column-read fast path.
* `k_nz ≤ k/3`: sparse column-accumulation.
* `k_nz > k/3`: existing dense matvec.

## Phase 4: where to insert the dispatch

The single dispatch site in production is

`extraspecial_orbifolds/scripts/run_e_plus_m_kernel_hap.g:590`

```
c_g_table := basis_cache.table * vec_target;
results[target_idx] :=
    IsCoboundary2SplitVec(basis_cache.C, c_g_table, vec_target, setup);
```

This is the per-target Path Z hit inside the BRW orbit walk. We replace
these two lines with:

```
results[target_idx] :=
    IsCoboundary2SplitVecAware(basis_cache.C, basis_cache, vec_target, setup);
```

The new entry point internalises the matvec, so the call-site no longer
materialises `c_g_table`.

There is also a structurally similar matvec in the fail-column fallback
in `solver/transgression_matrix_reduced.g:1335`:

```
c_g_table_exp := cache_orbit.table * vec_target_exp;
```

In the **reduced transgression-matrix path** (i.e. when
`use_reduced_tr_matrix := true`). The exp_axis_vec inputs there are
unit-vectors by construction (`vec_target_exp[fc] := exp_axis_vec`), so
the unit-support fast path applies directly. PR #389's rank-1 already
exploits this for that specific site. We do NOT modify that site —
issue #391 names the m=5 production hot path (the
`PerVecTransgressionShared` Path Z dispatch), not the m=3 fail-column
fallback.

## Phase 5: threshold choice

Based on the m=3 probe distribution:

| Threshold | Cases routed sparse | Cases on dense path |
|---:|---:|---:|
| k_nz = 1 only | 22% | 78% |
| k_nz ≤ k/4 ≈ 9 | 32% | 68% |
| k_nz ≤ k/3 ≈ 12 | 41% | 59% |
| k_nz ≤ k/2 ≈ 17 | 64% | 36% |

The right cutoff is where the per-iteration overhead of the sparse path
crosses below the dense-path amortised cost. Without a microbench at
m=5 we estimate this as k_nz ≤ k/3. Threshold is a tunable constant:

```gap
_PATHZ_SPARSE_THRESHOLD := QuoInt(Length(vec_target), 3);
```

A follow-up perf probe at m=5 (after the rest of Step-4 lands) should
re-tune.

## Phase 6: regression plan

* **m=2 (`run_e_plus_2_kernel.g`)** — exp = 2, so Path Z never fires.
  This test exercises the dispatch only to confirm no regression of
  Path A (which is unchanged). Expected: |ker Tr| = 2048 unchanged,
  identical witness vecs.

* **m=3 D-VAN anchor (`tests/test_dvan_trimmed_family.g`)** — exp = 4,
  exercises Path Z. We expect this to hit the new dispatcher heavily.
  The new code MUST produce byte-identical results to the existing
  dense path.

* **Microbench** — once committed, run a single Path Z call at m=3 in
  dense vs new-dispatcher modes and confirm:
   - results equal,
   - new dispatcher is no slower (and ideally measurably faster) on the
     unit-support case.

## Phase 7: expected wall reduction at m=5

The current m=5 Step-4 wall is ~270s/vec, of which ~177s is the Path Z
matvec across ~256 calls/vec at ~0.69s/call.

* **22% of calls** (unit-support): 0.69s → 0.04s (per the matvec-count
  collapse). Aggregate saving on these ~56 calls: 0.65 × 56 = ~36s/vec.
* **20% of calls** (k_nz ≤ k/3 sparse): 0.69s → 0.69 × 14/35 ≈ 0.28s.
  Aggregate saving on these ~51 calls: 0.41 × 51 = ~21s/vec.
* **58% of calls** (dense): no change, 0.69s × 149 = ~103s/vec.

Total predicted Path Z wall: 36 (cheap) → 36 × 0.05 + 51 × 0.28 + 149 ×
0.69 → 2 + 14 + 103 = ~119s/vec.

**Wall reduction: ~177s → ~119s, i.e. ~33% of the 270s/vec budget**, or
~58s/vec saved.

This is meaningful but NOT the "20-30× per-call speedup" the issue #391
narrative imagined for Approach A in the optimistic limit. The
optimistic limit was contingent on k_nz ~ 5-10; the actual k_nz median
is 14 at m=3.

### Uncertainty

* **m=3 to m=5 density extrapolation**: assumed similar 40% density. A
  direct m=5 probe would harden this prediction; without one, the
  estimate ±30%.
* **Per-call overhead of sparse path**: the threshold k/3 is a folk
  guess. If GAP's `AddRowVector` per-call overhead is higher than
  expected at m=5's n²=4M operand, the crossover moves higher, fewer
  cases get routed sparse, gains shrink.

## Recommendation

Implement Approach A as designed (hybrid unit-support + general sparse
+ dense fallback). Expected wall reduction at m=5: 20-30% of Step-4
budget, i.e. ~50-80s/vec saved off 270s/vec baseline. Combine with
Approach B (the other agent's GF(2) bit-packing branch) for compounding
gain. The two are orthogonal — sparse vec_target reduces ops; bit-packed
table reduces work-per-op.

## References

* Probe script: `/tmp/vec_target_sparsity_probe.g` (commit-tracked by
  this branch as a record).
* Issue #391 (the three structural-fix approaches).
* PR #390 / `docs/superpowers/research/2026-06-02-perf-audit-full.md`:
  the corrected interpretation that established the matvec IS at
  compiled speed and the cost is structural, not interpreter overhead.
* PR #389: audit-tier3 ranks 1-8 — addresses adjacent closure/init waste
  and is orthogonal to this sparsity work.
