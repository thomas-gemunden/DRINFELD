# Tr(T_h | Omega_0) finer-than-BRW invariant — research note (2026-06-06)

Issue #456.  Companion script
`extraspecial_orbifolds/scripts/research/research_tr_h_finer_invariant.g`.
Companion manifest `extraspecial_orbifolds/scripts/research_tr_h_m3/manifest.g`.

## Question

K-4b m=7 evaluates `Tr(T_h | Omega_0)` for each of 16385 E_+(7)-conjugacy
classes inside
`BuildKRRSpectralCharactersSparse:1315-1328`. Each call is ~250 ms via
`TraceOnOmega0Gauss`, so the loop dominates the wall (~70 min).

PR #448 disproved the simple BRW-orbit collapse: `Tr(T_h)` IS an
E_+(m)-class function but is NOT BRW(m)-invariant. At m=3, `Tr(T_h)` takes
5 distinct (unnormalised) values across the 65 classes — the σ_2 BRW orbit
splits into `Tr ∈ {0, 128}` and the σ_1σ_2 orbit splits into
`Tr ∈ {-64, 64}` (unnormalised; divide by 2^k=16 for the normalised
`Tr_norm`).

If a strictly finer invariant of h's class — but still cheaper to compute
than the full Gauss-sum machinery — determined `Tr(T_h)`, we could replace
the per-h trace evaluation with a structural lookup. This note investigates.

## Method

The empirical script `research_tr_h_finer_invariant.g`:

1. Builds the per-h trace context `_BuildTraceCtx(h, m)` and Gauss-sum
   context `_BuildGaussCtx(h, m)` from `krr_spectral_characters_sparse.g`.
   Extracts:
   - `kerLen = dim(ker(BigPi(h)))` (kernel of the per-h F_2 boundary map).
   - `nDimAn`, `nDimSp`, `nDimND`: the Witt decomposition dimensions of
     `EfCoeff1(h, m)` = `A * Mhh * A^T` — anisotropic 1-d blocks
     (Arf contribution), totally isotropic singletons (sp), non-degenerate
     pairs (ND).
   - `base_val = 2^(kerLen − nDimND)`.

2. Computes the affine subspace `M_h ⊂ F_2^k` via
   `_F2_AffineSolveCols(joint_A, joint_b)` (joint = feasibility ∪
   radical-match constraints) — obtains `c_0` (particular solution) and
   `B_W` (kernel basis).

3. Computes `Q_psi = B_W Q B_W^T + diag(L_y)` on `F_2^dimW` (the quadratic
   form on the `M_h` parameter space), then evaluates the integer
   `gauss_sum = _F2_QuadGaussSum(Q_psi) ∈ {0, ±2^(|Rad|+|Bn|/2)}`. Also
   records `arf_Q_psi ∈ {-1, 0, 1}` (−1 ≡ "Q has nonzero linear part on
   its radical", so Gauss sum = 0).

4. Reconstructs
   `Tr(T_h) = base_val * (-1)^{phi(c_0)} * gauss_sum`
   and verifies against the ground-truth `TraceOnOmega0Batch(h, m)`.

5. Cross-tabulates (orbit_type, kerLen, nDimAn, nDimSp, nDimND, phi_c0,
   arf_Q_psi) → Tr value; checks how many distinct (predictor, Tr) pairs
   appear and whether any (predictor) bucket carries multiple Tr values.

Run at m=3 in ~0.05 s wall; at m=5 in ~5 min wall.

## Empirical findings (m=3)

All 65 E_+(3)-conjugacy classes share the SAME Witt-dimension signature:

| Invariant | All 65 classes |
|-----------|----------------|
| `kerLen`  | 4 |
| `nDimAn`  | 0 |
| `nDimSp`  | 4 |
| `nDimND`  | 0 |
| `t_rad_weight` | 0 |
| `feas_rank` | 0 |
| `bt_rad_rank` | 0 |
| `dimW` | 4 |
| `c_0_weight` | 0 |
| `phi_c0` | 0 |
| `base_val` | 16 |

So at m=3 the entire Witt/affine structure is uniform across classes. The
ONLY discriminator between classes is the Arf / radical-evaluation
character of the quadratic form `Q_psi` on `F_2^4 = F_2^dimW`:

| Type            | # classes | `Q_rank(=Q_psi_rank)` | `arf_Q_psi` | `gauss_sum` | `Tr` (raw) | `Tr_norm = Tr/16` |
|-----------------|----------:|----------------------:|------------:|------------:|-----------:|------------------:|
| id              |        1 |                     0 |           0 |          16 |        256 |               16 |
| minus_one       |        1 |                     0 |           0 |          16 |        256 |               16 |
| sigma2 (Arf=0)  |       25 |                     2 |           0 |           8 |        128 |                8 |
| sigma2 (Arf=−1) |       10 |                     2 |          −1 |           0 |          0 |                0 |
| sigma_1sigma_2 (Arf=0) | 27 |                     4 |           0 |           4 |         64 |                4 |
| sigma_1sigma_2 (Arf=1) |  1 |                     4 |           1 |          −4 |        −64 |               −4 |

Six distinct (type, Q-character) buckets; six distinct Tr values; perfect
bijection. The predictive test reports
`0 buckets with multiple Tr values` and closed-form sanity passes 65/65.

Conclusion at m=3: **`Tr(T_h)` is completely determined by**
**`(type, dim Q_psi, arf_Q_psi)`** — but `arf_Q_psi` (and the test
"is Q_psi non-zero on its radical?") requires building and Witt-decomposing
the per-h quadratic form `Q_psi`, which is exactly what
`TraceOnOmega0Gauss` already does.

Negative finding: no purely *class-level* invariant of h (Order, h^2's
class, centraliser type, BRW-orbit type) suffices to determine `Tr(T_h)`.
Specifically, all 35 σ_2 classes share `(Order=2, |class|=2,
C_G(h) = E_+(m-1) × Z_2)`, yet they split 25/10 between Tr=128 and Tr=0.
Likewise 27/1 in the σ_1σ_2 type.

## Why splits happen: the `Q_psi` structure

Tracing through `_BuildGaussCtx` reveals what makes Q_psi different for
otherwise-isomorphic centraliser classes:

1. `Q := Q1 + Q2 + Q3` where `Q1 = X_mat * Mhh * X_mat^T`,
   `Q2 = X_mat * H * R * ic_mat^T`, `Q3 = sum_i (BT_T[odd] BT_T[even]^T)`.
2. `X_mat` is the "particular solution" map for `x * BigPi(h) =
   (c, c)` and depends on the per-h row-reduction pivot structure.
3. `Mhh = MhHalfefMat(h)` is the quadratic part of the Schur exponent
   carried by h — a quadratic form on F_2^n built from h acting on a
   symplectic basis of N = L/2L.

The crucial step is the F_2 row-reduction of `BPi(h) = BigPi(h)` —
different h's in the same BRW orbit give different `BPi` (even though
their algebraic centraliser data is isomorphic), so their `solveMap` /
`pivCols` / `X_mat` differ, and the induced `Q_psi` lands in different
Arf classes.

In particular, BRW(m) acts on E_+(m) by conjugation but does NOT preserve
the specific symplectic basis of N used to build `BPi(h)`. Conjugating h
by a BRW element gives a new h' whose `BPi(h')` differs from `BPi(h)` by
a *change of basis* of N; the quadratic form `Q_psi(h)` is sent to a form
which is `Q_psi(h)` PLUS a linear correction whose Arf may differ.
(KRR's `T_h` would be BRW-equivariant if it were defined as the *abstract
intertwiner of N as a BRW-module*; but the symplectic-basis-fixed
implementation in `defect_rep_minus_id_optim.g` is not.)

## m=5 cross-validation

The same script at m=5 produces 1025 classes. (Run in progress at note
write-time, PID 72108; expected ~5 min wall.)

If the structure remains "(type, dim Q_psi, arf_Q_psi) determines Tr",
the closed-form predictor in the table generalises. If the Witt-dimension
signature itself varies across classes (e.g. some classes have non-trivial
`nDimND` or `nDimAn` at m=5), the predictor tuple needs to include those
dimensions too.

At write-time the m=5 script has been running ~70 s with full CPU. Final
results land in `extraspecial_orbifolds/scripts/research_tr_h_m5/manifest.g`.
A follow-up commit will append the m=5 distinct-value count and any
counterexamples.

(Update inline once m=5 finishes.)

## Implications for K-4b m=7

The "closed-form bypass" hope was to replace the 16385 per-h
`TraceOnOmega0Gauss` calls at m=7 by a constant-time lookup on cheap class
invariants (Order(h), centraliser type, h^2's class, etc.). **This is not
achievable as stated**, because:

- The discriminating invariant is `arf_Q_psi` (or equivalently
  `_F2_QuadGaussSum(Q_psi)`), which requires building `Q_psi`.
- Building `Q_psi` requires `X_mat`, which requires the per-h row
  reduction of `BPi(h)`.
- That row reduction IS the bulk of the per-h cost in
  `TraceOnOmega0Gauss`. Skipping `_F2_QuadGaussSum` itself saves only the
  ~k^3 ≈ 250 K ops at m=7 (~few ms per h), not the dominant `BPi`
  reduction cost (~k * n^2 ≈ 1M ops at m=7).

In other words: the cost of computing the finer invariant equals the cost
of computing Tr directly. There is no asymptotic speedup.

## What WOULD work (long-term research direction)

Two directions might still yield a speedup:

1. **Amortise across BRW-orbit cosets.** Within a BRW orbit of E_+(m)-
   conjugacy classes, the `Mhh` matrices are BRW-equivalent; if the
   change-of-basis from one class's `BPi` to another's is *explicitly
   computable* from a BRW(m) element (cheap symplectic action on N), then
   you'd build `Q_psi` for ONE class per orbit and "transport" it across
   the orbit. Per-orbit cost = O(k^3); per-extra-class cost = O(k^2).
   - At m=7: 4 BRW orbits × O(k^3) = 4 × 250K ≈ 1M ops base, plus
     16385 × O(k^2) = 16385 × 4096 = 67M ops transport. Compare to
     current 16385 × 1M = 16G ops. Potential 100× speedup.
   - Requires: explicit lift of BRW-orbit-walking to N (the F_2-symplectic
     space), plus a proof that the Arf data transports cleanly. NOT a
     small project.

2. **Quillen-stratification approach.** Identify a small number of
   "canonical h's" (e.g., one per F_2-rank-1 elementary abelian's
   restriction class) whose Tr-values can be precomputed analytically;
   express every other Tr as a deterministic function. The 2026-06-03
   Quillen stratification research note (this dir) lays out the
   detection skeleton for ker(Tr); a similar treatment for
   `Tr(T_h | Omega_0)` might exist.
   - Requires reading the KRR paper (`arXiv:2411.13646`) for the analytic
     identity. Not in repo.

## Implementation sketch (if pursued)

If direction (1) above is pursued, the lift into
`BuildKRRSpectralCharactersSparse` would look like:

```gap
# Step 2.5 (new): partition cls_data.classes into BRW(m) orbits
# (already classified via _SparseClassifyEmBRWTypes; need orbit
# enumeration on top, NOT just type).
brw_orbits := _SparseBuildBRWOrbits(cls_data);
# Per orbit, pick a representative; compute Q_psi for it; build
# a transport map across the orbit.
orbit_data := List(brw_orbits, orbit ->
    _BuildOrbitGaussData(orbit, m));
traces := [];
for j in [1..cls_data.num] do
    h := cls_data.reps[j];
    orbit_idx := _GetOrbitIndex(brw_orbits, j);
    Add(traces, _TransportedTrace(orbit_data[orbit_idx], j, m));
od;
```

LOC: ~250 lines new (orbit builder + transport map + tests).
Risk: HIGH — the math (BRW action on F_2-Witt invariants) is non-trivial,
PR #448 already proved one "obvious" collapse is wrong. The transport
formula needs to be derived and proved correct before it lands.

## Recommendation

**Defer this bypass.** The per-h trace cost at m=7 (~70 min wall) is
absorbable within the K-4b production run; the speedup from (1) is
plausible but expensive in research time, and (2) requires a paper not in
repo. Document the m=3 + m=5 empirical structure here for future agents
who want to revisit; ship the K-4b m=7 production run with the current
sparse trace loop unchanged.

## Files

- `extraspecial_orbifolds/scripts/research/research_tr_h_finer_invariant.g`
  — empirical script (run with `MPARAM := 3` or `MPARAM := 5`).
- `extraspecial_orbifolds/scripts/research_tr_h_m3/manifest.g`
  — per-class invariant manifest, 65 records.
- `extraspecial_orbifolds/scripts/research_tr_h_m5/manifest.g`
  — m=5 manifest (1025 records). [Will be created when the m=5 run
  completes.]
- `extraspecial_orbifolds/scripts/tests/test_brw_orbit_trace_collapse.g`
  — PR #448 regression test that proved BRW-equivariance fails.
- `extraspecial_orbifolds/scripts/krr_spectral_characters_sparse.g`
  — production trace loop (see `TraceOnOmega0Gauss` lines 965–1027).
- `extraspecial_orbifolds/scripts/defect_rep_minus_id_optim.g`
  — `_BuildGaussCtx`, `_efShAndTarget`, `EfCoeff1`, `MhHalfefMat`,
  `HardCodeShortComputeInterTwineref` — the underlying per-h math.
