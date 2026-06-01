# Approach B — GF(2) bit-packing for Path Z's `basis_cache.table` (issue #391)

Status: design doc. Math derivation + API contract for the m=5 case.

## Problem

`c_g_table := basis_cache.table * vec_target` in `PerVecTransgressionShared`
(`extraspecial_orbifolds/scripts/run_e_plus_m_kernel_hap.g:590`) dominates
A-5b's m=5 Step-4 wall. The matvec is at compiled C speed (~1 ns/scalar)
but the operand shape `n² × k = 4,194,304 × 165 ≈ 692M` scalar ops per call
× ~256 calls per vec = ~177 s of Path Z matvec per vec. See PR #390 +
`docs/superpowers/research/2026-06-02-perf-audit-corrected-interpretation.md`.

Approach B: cache `basis_cache.table` as **two packed GF(2) matrices**
(`table_gf2_bot` for bit 0, `table_gf2_top` for bit 1) and answer Path Z
queries with packed GF(2) matvecs (`PROD_GF2MAT_GF2VEC`, ~64× the
per-element rate of integer matvec).

The existing `basis_cache.table_gf2` (`snf_wrapper.g:719`) IS the top bit
at m=5 (`r_half = exp/2 = 2`, so `(x div 2) mod 2 = bit_1(x)`). What is
NEW in Approach B is the bottom bit `table_gf2_bot[i][j] = bit_0(table[i][j])`
plus a refactor of the Path Z consumer (the iterated Bockstein) to read
bit slices instead of an integer table.

## Phase 1 math derivation

### Table-column structure at m=5

At m=5 the H^3(E_+(5); U(1)) torsion vector has shape `[2, 2, ..., 2, 4]`
(many order-2 generators plus one order-4 generator at `exp_index`).
Cocycle-basis entries `basis[j]` are integer mod-`exp` cocycles
representing a Z/`torsion[j]` cohomology class. So:

- For `j != exp_index` (torsion[j] = 2): basis[j] is r-times an integer
  cocycle, so `table[i][j] ∈ {0, r} = {0, 2}` ⊂ Z/4. **`bit_0(table[i][j]) = 0`**
  for all i and these j.
- For `j = exp_index` (torsion[j] = 4): basis[j] is the Z/4 generator,
  so `table[i][exp_index] ∈ {0, 1, 2, 3}`. Both bits can be nontrivial.

Path Z's entry condition is `vec_target[exp_index] != 0`, so
`vec_target[exp_index] ∈ {1, 2, 3}`. For order-2 j, `vec_target[j] ∈ {0, 1}`.

### Decomposition of `c_g_table[i]`

Let A_i := contribution from order-2 columns, B_i := contribution from
the exp_index column.

```
c_g_table[i] = A_i + B_i  (integer sum, before mod 4)

A_i = sum_{j != exp_index} table[i][j] * vec_target[j]
B_i =                       table[i][exp_index] * vec_target[exp_index]
```

For order-2 j: `table[i][j] ∈ {0, 2}` = `2 * bit_1(table[i][j])`, and
`vec_target[j] ∈ {0, 1}` = `bit_0(vec_target[j])`. So:

```
A_i = 2 * sum_{j != exp_index} bit_1(table[i][j]) * bit_0(vec_target[j])
    = 2 * A'_i
```

where A'_i is an INTEGER (possibly large) equal to a length-(k-1) inner
product over GF(2)-like operands (but the sum is an integer sum).

### Bit slices of c_g_table mod 4

Let `t = table[i][exp_index]`, `v = vec_target[exp_index]`, both in
{0,1,2,3}. Then `B_i = t*v`, an integer in [0, 9]; `B_i mod 4` is in
{0,1,2,3}.

```
c_g_table[i] mod 4 = (2*A'_i + B_i) mod 4
```

A_i = 2*A'_i is even, so:
- `bit_0(c_g_table[i] mod 4) = bit_0(B_i mod 4) = bit_0(t*v) = bit_0(t) AND bit_0(v)`.
- For bit_1: A'_i contributes via `(A'_i mod 2)` shifted into bit 1.
  Since A'_i mod 2 = sum_{j != exp_index} bit_1(table[i][j]) * bit_0(vec_target[j]) mod 2,
  this is exactly the GF(2) inner product of bit_1(table[i]) (restricted
  to j != exp_index) and bit_0(vec_target).

  `bit_1(c_g_table[i] mod 4) = (A'_i mod 2) XOR bit_1(B_i mod 4)`
  
  with `bit_1(t*v mod 4) = bit_1(t)*bit_0(v) XOR bit_0(t)*bit_1(v)` over GF(2).
  (Verified by enumeration of the 16 (t,v) pairs.)

### Final formula (with GF(2) simplification)

Naively:
```
bit_0_slice[i] := bit_0(table[i][exp_idx]) AND bit_0(vec_target[exp_idx])
bit_1_slice[i] := A'_i mod 2
                 XOR bit_1(table[i][exp_idx])*bit_0(vec_target[exp_idx])
                 XOR bit_0(table[i][exp_idx])*bit_1(vec_target[exp_idx])
```

`A'_i mod 2 = sum_{j != exp_idx} bit_1(table[i][j]) * bit_0(vec_target[j]) mod 2`
is computable as one packed GF(2) matvec `table_gf2_top * vec_bot` MINUS
the j=exp_index contribution `bit_1(table[i][exp_idx]) * bit_0(vec_target[exp_idx])`.
In GF(2), `−` = `+`, so the exp-column term cancels the exp-column term
inside `bit_1_slice`:

```
A'_i mod 2 = (table_gf2_top * u_bot)[i] + (col_top_exp[i] * v_bot_exp)   [GF(2)]
bit_1_slice[i] = A'_i mod 2
                 + col_top_exp[i] * v_bot_exp         [from B_bit1]
                 + col_bot_exp[i] * v_top_exp
              = (table_gf2_top * u_bot)[i]
                 + 0                                   [the two col_top_exp*v_bot_exp cancel]
                 + col_bot_exp[i] * v_top_exp
```

**Final simplified formula** (used in the implementation):

```
slice_top[i] = (table_gf2_top * u_bot)[i] + col_bot_exp[i] * v_top_exp     [GF(2)]
slice_bot[i] =                              col_bot_exp[i] * v_bot_exp     [GF(2)]
```

where:
- `u_bot = (vec_target mod 2) * One(GF(2))` (length-k GF(2) vector, the
  full Path A input)
- `col_bot_exp` = the exp_index column of `table_gf2_bot` (length-n² GF(2)
  vector)
- `v_bot_exp = bit_0(vec_target[exp_index]) * One(GF(2))`
- `v_top_exp = bit_1(vec_target[exp_index]) * One(GF(2))`

This is **one packed GF(2) matvec** (Path A reused on `table_gf2_top`)
plus **two length-n² scalar*vec ops** (negligible) plus **one length-n²
vec+vec XOR** (negligible). The dispatch-site work is essentially that
of Path A on the same shape — i.e. one packed `PROD_GF2MAT_GF2VEC` call.

### The "carry" concern from the spec — non-issue at m=5

The task description warned about a carry from popcount of bit-0 partial
sums when computing bit_1 of a general (k-element) product. **At m=5
this carry vanishes by design**: all order-2 columns have bit_0(table) = 0
identically, so bit_0(c_g_table) is a SCALAR multiple of a single column
(no sum, no popcount). Only the exp_idx column contributes to bit_0, and
its contribution to bit_1 is computed exactly via the t*v mod 4 formula
above.

This is a structural feature of the m=5 cocycle basis: order-2 generators
contribute multiples of r in the cocycle table, leaving bit_0 free. The
property holds for any m where the torsion is `[2,...,2, exp]` with
exp = 2^k, which covers the entire extraspecial-orbifold family.

## Estimated speedup

Per Path Z call:

| Op | Current cost | Approach B cost |
|---|---|---|
| Integer matvec n²×k | ~700 ms (4M×165 int mul+add) | — |
| Packed GF(2) matvec n²×k | — | ~10–15 ms |
| Bit-1 correction (single column × scalar) | — | <1 ms |
| Bit-0 slice (single column × scalar) | — | <1 ms |
| IB chain (mod-2 backsub, etc.) | ~few ms | ~few ms (slightly different bit logic but same shape) |
| **Per-call total** | **~700 ms** | **~20 ms** |

**Per-call speedup: ~30–50×**, dominated by the matvec replacement.

At m=5 with ~256 Path Z calls per Step-4 vec, this should reduce the
Path-Z per-vec wall from ~177 s to ~5 s. Combined with ~90 s/vec residual
from other paths, the total per-vec wall would drop from ~270 s to ~90 s,
roughly a 3× end-to-end speedup at m=5.

Worst case (if `PROD_GF2MAT_GF2VEC` doesn't word-parallelize as expected
on this shape, or if IB-on-bit-slices reveals an unexpected scalar
hotspot): still ~16× per-call from the bitwidth savings alone.

## IB refactor: working on bit slices

`IsCoboundary2Z2kVec(C, c_g_vec, k=2)` (modulus=4) does:

```
c_table   = c_g_vec mod 4
beta_int  = IB_StrictF2Witness(C, c_table, n)     # uses c_table mod 2
delta_beta= IB_DeltaBetaMult(beta_int, n, mult, 4) # int vector
c_next    = IB_DivBy2(c_table, delta_beta, 2)     # ((c-db) mod 4)/2 mod 2
return IB_TableMod2WithLift(C, c_next, n)
```

We refactor to a parallel API `IsCoboundary2Z4VecBits(C, c_bot, c_top, n)`:

```
# c_bot = bit_0(c_g_vec), c_top = bit_1(c_g_vec), both packed GF(2)
# (modulus = 4 fixed for now; will generalise later)

beta_int  = IsCoboundary2Mod2VecWithWitness(C, c_bot)
            # already takes packed GF(2) (after a small overload tweak —
            # see T3 below)
if beta_int.yes = false: return false
beta_bot  = beta_int.witness  # packed GF(2), length n

# IB_DeltaBetaMult(β, n, mult, 4) produces δβ[i,j] = (β_i + β_j - β_{mult_ij}) mod 4
# We compute this on bit slices:
#   db_bot[i,j] = β_bot[i] XOR β_bot[j] XOR β_bot[mult_ij]
#   db_top[i,j] = (β_bot[i] XOR β_bot[mult_ij]) AND (β_bot[j] XOR β_bot[mult_ij])
# (Derivation: enumerate the 8 (β_i, β_j, β_mult) cases — see design doc Section "bit_1 of subtract" below.)

# IB_DivBy2(c, db, 2) = ((c - db) mod 4) / 2 mod 2 = bit_1((c - db) mod 4).
# On bit slices:
#   bit_1((c - db) mod 4) = c_top XOR db_top XOR (db_bot AND NOT c_bot)
c_next_bot = c_top XOR db_top XOR (db_bot AND NOT c_bot)

return IsCoboundary2Mod2WithLiftVec(C, c_next_bot)
```

All operations on c_bot, c_top, db_bot, db_top, β_bot are length-n² packed
GF(2) vectors (≈ 65k 64-bit words at n=2048 — fits in L2 cache).

### Subtraction `(c - db) mod 4` on bit slices (derivation)

For x, y ∈ {0,1,2,3} (single cells):
- bit_0((x-y) mod 4) = bit_0(x) XOR bit_0(y).
- bit_1((x-y) mod 4) = bit_1(x) XOR bit_1(y) XOR (bit_0(y) AND NOT bit_0(x)).
  (The third term is the borrow: bit_0 borrow happens iff x_0 < y_0.)

We only need bit_1((c-db) mod 4) for c_next_bot. Above.

### δβ̃₀ on bit slices (derivation)

For β ∈ Z/2 lifted to {0, 1} ⊂ Z, the integer δβ̃[i,j] = β_i + β_j − β_{i·j}
takes values in {−1, 0, 1, 2}. Reduced mod 4:

| (β_i, β_j, β_{ij}) | δβ̃ | δβ̃ mod 4 | bit_0 | bit_1 |
|---|---|---|---|---|
| (0,0,0) | 0  | 0 | 0 | 0 |
| (1,0,0) | 1  | 1 | 1 | 0 |
| (0,1,0) | 1  | 1 | 1 | 0 |
| (1,1,0) | 2  | 2 | 0 | 1 |
| (0,0,1) | −1 | 3 | 1 | 1 |
| (1,0,1) | 0  | 0 | 0 | 0 |
| (0,1,1) | 0  | 0 | 0 | 0 |
| (1,1,1) | 1  | 1 | 1 | 0 |

bit_0 = β_i XOR β_j XOR β_{ij}.
bit_1 = (β_i XOR β_{ij}) AND (β_j XOR β_{ij}).

Both are packed GF(2) ops at the matrix level (KroneckerProduct + XOR
+ AND), but the existing `IB_DeltaBetaMult` runs an interpreter for-loop
over n². For Approach B, we compute δβ on bit slices via the formulas
above. Since β_bot is length-n and lives on n indices (not n²), we can
materialise db_bot and db_top as packed GF(2) length-n² vectors via
`KroneckerProduct` + per-element XOR. This was already a hotspot in the
prior audit; bit-slice computation here is a side-benefit.

## API surface

### New: `bit_table_pair` in basis_cache

`basis_cache.table_gf2_bot` (length n² × k, packed GF(2)) — bottom bit
of `basis_cache.table`. At m=5 this is identically zero except in the
exp_idx column; we still materialise the full matrix for uniformity and
because the GF(2) matvec is cheap.

`basis_cache.table_gf2_top` — RENAMED from current `basis_cache.table_gf2`
for clarity. Same matrix (`bit_1(table)`).

Backwards compat: keep `basis_cache.table_gf2` as an alias pointing at
the same matrix as `table_gf2_top` so existing Path A callers don't
break.

### New: `IsCoboundary2Z4VecBits(C, c_bot, c_top, n)`

Specialised entry point for k=2 (modulus=4) consuming bit slices. For
m=5 only. We do NOT generalise to k≥3 in this PR (the algorithm still
works but the enumeration in `IB_RecCob` requires recursive descent on
bit slices; we ship the modulus=4 case and leave m=7 for follow-up).

### Updated: Path Z dispatch site

`PerVecTransgressionShared` Path Z branch computes the bit slices once
per (vec_target, basis_cache) pair and passes them to
`IsCoboundary2Z4VecBits` (replacing the current
`IsCoboundary2SplitVec(... c_g_table ...)`).

### Cache version bump

`_ORBIT_CACHE_FORMAT_VERSION := 2`. Existing on-disk caches lack
`table_gf2_bot` (it doesn't exist) but ALSO can be derived from
`table_rows` on load — same as `table_gf2_top` is today. We add the
derivation step to `LoadOrbitCache`. Since version-2 caches add a
new derived field, existing version-1 caches can be loaded and
upgraded without rebuild (preserving the 6 GB at m=5). We bump the
version anyway so that if downstream code changes the `table_rows`
format the upgrade path is explicit.

### Backwards compatibility

- m=2, m=3 callers: existing `table_gf2` reference is preserved; `table_gf2_top`
  is just another alias. No code change required there.
- Path A (`vec_target[exp_index] = 0`): unchanged; still uses `table_gf2`
  (= `table_gf2_top`).
- Path Z dispatch: bit-slice path active only when `setup.exponent = 4`
  AND `LogInt(setup.exponent, 2) = 2`. For m=2 (exp=2) and other exponents,
  fall back to the existing `IsCoboundary2SplitVec` API. The dispatch
  guards live in `run_e_plus_m_kernel_hap.g` so the solver files stay
  generic.

## m=2 / m=3 regression plan

- m=2: smoke test under existing `test_brw_orbit_cache_quick.g` infra.
  Exp=2 means Path Z is never taken (the dispatch condition
  `vec_target[exp_index] != 0` fires only when exp > 2 — see
  `run_e_plus_m_kernel_hap.g:588`). So m=2 hits Path A only, unchanged.
- m=3: anchor against the existing m=3 kernel computation. exp=4,
  exercises Path Z. The new bit-slice path activates here and must
  produce the SAME kernel as the integer-table path.

Verification:
1. Solver-level: enable the new path under a feature flag
   `USE_PATHZ_GF2PACK := true/false`. Run both paths on m=3 and assert
   identical `c_g_table` reconstructions and identical `IsCoboundary2Z2k`
   results across 100+ Path Z calls.
2. End-to-end: m=3 anchor — same kernel size, same `in_kernel_gens` set.

## Open questions (none blocking the m=5 path)

1. **m=7 generalisation (k=3 / modulus=8)**: requires bit slices for
   three bits. The IB recursion enumerates 2^|hom_basis| α candidates at
   each level. Each α produces a length-n² bit-1 table; computing α∪α
   on bit slices is cheap (KroneckerProduct of length-n bit vector
   with itself). The recursion does need to track bit_2 explicitly,
   not just bit_0/bit_1. Out of scope here; deferred to a follow-up issue.

2. **`IsCoboundary2Mod2VecWithWitness` packed-GF(2) input**: the current
   function applies `(x mod 2) * one` element-wise. If we pass a packed
   GF(2) vector, we either (a) IntFFE first (cost: ~n² ms — measurable
   but not catastrophic) or (b) extend the function to accept GF(2) input
   directly. (a) is simpler for the first PR; switch to (b) if profiling
   shows the boundary cost is significant.

3. **Cache size on disk**: `table_gf2_bot` derives from `table_rows` on
   load, so disk size is unchanged. No serialisation work needed.

## References

- `docs/superpowers/research/2026-06-02-perf-audit-corrected-interpretation.md`
  (PR #390) — establishes that GAP's integer matvec IS compiled.
- `extraspecial_orbifolds/scripts/run_e_plus_m_kernel_hap.g:580-620` —
  Path Z dispatch site.
- `extraspecial_orbifolds/scripts/solver/iscoboundary2_split.g:111-150` —
  `IsCoboundary2SplitVec`.
- `extraspecial_orbifolds/scripts/solver/iterated_bockstein.g:421-547` —
  `IB_RecCob`, `IsCoboundary2Z2kVec`.
- `extraspecial_orbifolds/scripts/solver/snf_wrapper.g:699-725` —
  `BuildPerClassCocycleBasis` table assembly + `table_gf2` (= top bit).
- `extraspecial_orbifolds/scripts/solver/orbit_cache_persist.g:465-486` —
  `LoadOrbitCache` rebuild of `table_gf2`.
