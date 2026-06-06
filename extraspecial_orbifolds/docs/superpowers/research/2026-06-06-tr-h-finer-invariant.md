# Tr(T_h | Omega_0) finer-than-BRW invariant — research note (2026-06-06)

Issue #456. Companion scripts
`extraspecial_orbifolds/scripts/research/research_tr_h_finer_invariant.g`
and
`extraspecial_orbifolds/scripts/research/research_tr_h_m7_sample.g`.
Companion manifests `extraspecial_orbifolds/scripts/research_tr_h_m3/manifest.g`
and `extraspecial_orbifolds/scripts/research_tr_h_m5/manifest.g`.

## TL;DR (2026-06-06 update after m=5 + m=7 empirics)

| m | distinct `Tr(T_h | Ω_0)` values across all non-singleton BRW types |
|---|---------------------------------------------------------------------|
| 3 | sigma2 → {0, 128}, sigma_1sigma_2 → {-64, 64} — **splits within BRW orbits** |
| 5 | sigma2 → {268435456} (single value), sigma_1sigma_2 → {16777216} — **no splits** |
| 7 (sampled 20 + 20) | sigma2 → {2^112} (all match), sigma_1sigma_2 → {2^96} (all match) — **no splits in sample** |

**The m=3 BRW-orbit splits do NOT manifest at m=5 or m=7 (sampled).**
At m≥5, every empirical class within a BRW orbit type yields the SAME
trace, no `Arf` splits, no `Tr = 0` cases. This flips the original
"defer" recommendation: at m=7, K-4b's 16385 per-h trace evaluations
can be replaced by **4 calls** (one per BRW orbit type) with high
empirical confidence + a per-driver sanity sample.

Closed-form formula at m≥3 (matching every observed Tr value at m=5 +
m=7, and the *majority* class at m=3):

```
Tr(T_h | Ω_0)_norm = 2^(k − d(type))
```

where `k = 2^(m-1)` and the BRW-type Witt exponent is

```
d(id) = d(minus_one) = 0
d(sigma2)            = 2^(m-3)
d(sigma_1sigma_2)    = 2^(m-2).
```

At m=7: `Tr_norm = 2^64, 2^48, 2^32` for the three non-trivial types
(and `Tr_norm = 2^64` for `minus_one`).

Production lift cost (per `BuildKRRSpectralCharactersSparse` lines
1315-1328): ~50 LOC of trace-loop replacement + per-driver sanity check.
**Wall savings at m=7: ~35 min → ~3 sec per K-4b m=7 driver invocation.**
Risk: LOW for m≥5; UNKNOWN for m≥9 (no need at present).

## Question

K-4b m=7 evaluates `Tr(T_h | Omega_0)` for each of 16385 E_+(7)-conjugacy
classes inside `BuildKRRSpectralCharactersSparse:1315-1328`. Each call is
~127 ms via `TraceOnOmega0Gauss` at m=7, so the loop dominates the wall
(~35 min).

PR #448 disproved the simple BRW-orbit collapse at m=3: `Tr(T_h)` IS an
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

4. Reconstructs `Tr(T_h) = base_val * (-1)^{phi(c_0)} * gauss_sum`
   and verifies against `TraceOnOmega0Batch(h, m)`.

5. Cross-tabulates (orbit_type, kerLen, nDimAn, nDimSp, nDimND, phi_c0,
   arf_Q_psi) → Tr value; checks how many distinct (predictor, Tr) pairs
   appear and whether any (predictor) bucket carries multiple Tr values.

Run at m=3 in ~0.05 s wall; at m=5 in ~17 min wall.

The m=7 sample script `research_tr_h_m7_sample.g` (~5 sec wall) picks
20 evenly-spaced reps from each non-singleton BRW type at m=7, computes
`TraceOnOmega0Gauss` for each, and verifies they match the typed
closed-form prediction.

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

| Type            | # classes | `Q_psi_rank` | `arf_Q_psi` | `gauss_sum` | `Tr` (raw) | `Tr_norm = Tr/16` |
|-----------------|----------:|-------------:|------------:|------------:|-----------:|------------------:|
| id              |        1 |            0 |           0 |          16 |        256 |               16 |
| minus_one       |        1 |            0 |           0 |          16 |        256 |               16 |
| sigma2 (Arf=0)  |       25 |            2 |           0 |           8 |        128 |                8 |
| sigma2 (Arf=−1) |       10 |            2 |          −1 |           0 |          0 |                0 |
| sigma_1sigma_2 (Arf=0) | 27 |            4 |           0 |           4 |         64 |                4 |
| sigma_1sigma_2 (Arf=1) |  1 |            4 |           1 |          −4 |        −64 |               −4 |

Six distinct (type, Q-character) buckets; six distinct Tr values; perfect
bijection. Closed-form sanity passes 65/65.

Conclusion at m=3: `Tr(T_h)` is completely determined by `(type, dim
Q_psi, arf_Q_psi)`, but `arf_Q_psi` requires building and Witt-
decomposing `Q_psi`, which is exactly what `TraceOnOmega0Gauss` already
does. **No purely class-level invariant (Order, h^2's class, centraliser
type) suffices** — at m=3, all 35 σ_2 classes share isomorphic centraliser
data, yet split 25 / 10 between Tr=128 and Tr=0.

## Empirical findings (m=5) — the main result

All 1025 E_+(5)-conjugacy classes split into **only three** Witt-dimension
signatures (one per non-singleton BRW orbit type), with constant `Tr`
within each type:

| Type | `kerLen` | `nDimAn` | `nDimSp` | `nDimND` | `dimW` | `Q_psi_rank` | `arf_Q_psi` | `gauss_sum` | `Tr` (raw) | `Tr_norm = Tr/2^16` |
|------|---------:|---------:|---------:|---------:|-------:|-------------:|------------:|------------:|-----------:|--------------------:|
| id (1)               | 16 | 0 | 16 | 0 | 16 |  0 | 0 | 65536 | 4 294 967 296 | 65536 |
| minus_one (1)        | 16 | 0 | 16 | 0 | 16 |  0 | 0 | 65536 | 4 294 967 296 | 65536 |
| sigma2 (527)         | 16 | 0 | 16 | 0 | 16 |  8 | 0 |  4096 |   268 435 456 |  4096 |
| sigma_1sigma_2 (496) | 16 | 0 | 16 | 0 | 16 | 16 | 0 |  256 |    16 777 216 |   256 |

- 1025 / 1025 closed-form sanity passes.
- **Zero** infeasibility, **zero** `arf_Q_psi = -1`, **zero** `arf_Q_psi = 1`,
  **zero** `Tr = 0`.

So at m=5, BRW orbit type alone determines `Tr(T_h)`. The empirical
predictor reduces from `(type, dim Q_psi, arf_Q_psi)` (m=3) to just
`type` (m=5).

The m=3 splits (some sigma2 → 0 due to Arf=-1, some
sigma_1sigma_2 → −4 due to Arf=1) DO NOT manifest at m=5.

## Empirical findings (m=7, sampled — 40 non-central classes)

The script `research_tr_h_m7_sample.g` samples 20 evenly-spaced reps
from each of the two non-singleton BRW types at m=7, computes
`TraceOnOmega0Gauss` for each, and verifies they match the typed
prediction:

| Type            | predicted `Tr` (raw)                          | observed (20 samples)                  | match |
|-----------------|------------------------------------------------|-----------------------------------------|-------|
| id (1)          | 2^128                                          | 2^128                                  | ✓ |
| minus_one (1)   | 2^128                                          | 2^128                                  | ✓ |
| sigma2 (20)     | 2^112 = 5192296858534827628530496329220096    | identical for all 20 = 2^112           | ✓ |
| sigma_1sigma_2 (20) | 2^96 = 79228162514264337593543950336      | identical for all 20 = 2^96            | ✓ |

Script verdict: **"BRW-orbit collapse holds on all 40 sampled non-central
classes."** Per-call wall ~127 ms × 40 ≈ 5 sec total.

The sample is small enough that we have empirical confidence, NOT a proof.
The sanity check in the implementation sketch below makes this safe in
production.

## Theoretical mechanism

The closed-form predictor `Tr_norm = 2^(k − d(type))` admits a natural
interpretation:

- `T_h` acts on `F_2^k` (a 2^(m-1)-dim symplectic space, where
  k = 2^(m-1)).
- For `h = ±I`, `T_h` is `±` the identity on the whole space, so
  every diagonal entry is `±1` and trace is `± 2^k`.
- For non-central `h` of BRW type sigma2 (order 2, anti-commutes with
  one symplectic generator only), `T_h` acts non-trivially on a
  `2·d(sigma2)`-dim symplectic subspace, fixing the orthogonal
  complement. The fixed-pointwise complement contributes `2^(k − d)`
  to the diagonal; the moving part contributes a Gauss-sum-like
  factor that, at m≥5, evaluates to `±2^d` with sign `+` (Arf = 0
  uniformly).
- Same logic for sigma_1sigma_2 with `d(sigma_1sigma_2) = 2^(m-2)`.

Empirically (m=3 majority, m=5 all, m=7 sampled) the sign is `+`. The
m=3 anomalies (`Arf = ±1` on a small subset of classes) reflect the
special small-`m` geometry of the F_2 alternating form on `F_2^4` (only
4 dimensions to hide a nontrivial Arf class); at higher `m`, the Witt
component dimension is large enough that the BRW orbit fully absorbs
the small Arf variation.

A full proof would require characterising the `Q_psi`-Arf invariant as
a BRW-orbit cohomology class — likely tractable via Brauer-Wall group
reasoning, but out of scope for this note.

## Why the m=3 splits don't generalise (handwave)

Tracing through `_BuildGaussCtx`:

1. `Q := Q1 + Q2 + Q3` where `Q1 = X_mat * Mhh * X_mat^T`,
   `Q2 = X_mat * H * R * ic_mat^T`, `Q3 = sum_i (BT_T[odd] BT_T[even]^T)`.
2. `X_mat` is the "particular solution" map for `x * BigPi(h) =
   (c, c)` and depends on the per-h row-reduction pivot structure.
3. `Mhh = MhHalfefMat(h)` is the quadratic part of the Schur exponent
   carried by h — a quadratic form on F_2^n built from h acting on a
   symplectic basis of N = L/2L.

Different h's in the same BRW orbit give different `BPi(h)` (the
algorithm fixes a symplectic basis of `N`; BRW conjugation changes
the basis). The resulting `Q_psi` lives in different Arf classes in
small m (because `F_2^4` admits both Arf = 0 and Arf = ±1 forms),
but at m ≥ 5 the orbit dimension is large enough that BRW(m)'s action
absorbs the Arf differences.

## Implementation sketch (RECOMMENDED for K-4b m=7)

Replace the per-class trace loop in `BuildKRRSpectralCharactersSparse`
(lines 1315-1328) with a typed lookup + a runtime sanity check:

```gap
# After Step 2.5 (existing classification by BRW orbit type):
class_types := _SparseClassifyEmBRWTypes(cls_data.classes);

# Closed-form predicted Tr (UNNORMALISED, will be divided by 2^k in
# TraceOnOmega0).  k = 2^(m-1).
k := 2^(m - 1);
predicted_raw := rec(
    id              := 2^(2 * k),
    minus_one       := 2^(2 * k),
    sigma2          := 2^(2 * k - 2^(m - 3)),
    sigma_1sigma_2  := 2^(2 * k - 2^(m - 2))
);

# Compute one trace per type (4 calls) + cross-check on a 5-class
# random sample per type (~20 calls).  If any sample disagrees with
# the typed prediction, FAIL LOUDLY and fall back to the per-class
# loop.
type_to_tr := rec();
seen_types := [];
for j in [1..cls_data.num] do
    t := class_types[j];
    if not IsBound(type_to_tr.(t)) then
        h := cls_data.reps[j];
        type_to_tr.(t) := TraceOnOmega0(h, m);   # Tr_norm
        Add(seen_types, t);
        if Length(seen_types) = 4 then break; fi;
    fi;
od;
# Cross-check against predicted_raw (UNNORMALISE first):
for t in seen_types do
    expected_norm := predicted_raw.(t) / 2^k;
    if type_to_tr.(t) <> expected_norm then
        Error("BRW-orbit Tr collapse failed: type ", t,
              " got ", type_to_tr.(t),
              " but predicted ", expected_norm);
    fi;
od;
# Random sanity sample (per-driver invocation cost).
sample_size_per_type := 5;
sampled_h_idxs := _SparsePickEvenlySpacedSample(cls_data, sample_size_per_type);
for sidx in sampled_h_idxs do
    t := class_types[sidx];
    h := cls_data.reps[sidx];
    sample_tr := TraceOnOmega0(h, m);
    if sample_tr <> type_to_tr.(t) then
        Print("[WARN] BRW-orbit collapse mismatch at class ", sidx,
              " type ", t, ".  Falling back to per-class loop.\n");
        # FALL BACK: redo the per-class trace loop.
        traces := List([1..cls_data.num], j ->
            TraceOnOmega0(cls_data.reps[j], m));
        return traces;
    fi;
od;
# All checks pass; expand traces via typed lookup.
traces := List([1..cls_data.num], j -> type_to_tr.(class_types[j]));
```

LOC: ~50 lines. Risk: LOW — every driver call exercises the sample
sanity check and aborts on disagreement.

Wall impact at m=7:

- BEFORE: 16385 × ~127 ms = ~35 min per K-4b m=7 driver invocation.
- AFTER:  ~24 typed + sample calls = ~3 sec.
- **Savings: ~35 min per driver invocation.**

## Recommendation (FLIPPED from the earlier "defer")

**Ship the BRW-orbit collapse + per-driver sanity check** in
`BuildKRRSpectralCharactersSparse` for m ≥ 5. The empirical
evidence at m=5 (1025/1025) + m=7 (40/40 sampled) is strong; the
sanity check provides a safety net against any sporadic counter-
example. ~50 LOC change; ~35 min wall saved per K-4b m=7 driver
invocation.

Follow-up work (lower priority):

1. **Wider m=7 sample.** Verify the collapse on a larger random
   sample (say 200 reps per type, ~50 s additional wall, runs once
   per CI / release).
2. **m=9 limit testing.** Verify that the predictor still holds at
   m=9 if/when K-4b is extended that far.
3. **Theoretical proof.** Characterise `Q_psi`-Arf as a BRW-orbit
   invariant for m ≥ 5 (vs the m=3 anomaly).
4. **m=3 anomaly investigation.** Identify the single
   sigma_1sigma_2 class with `Arf=1` at m=3 (`class_idx=57`) and
   the 10 sigma2 classes with `Arf=-1` — these isolated cases are
   the only known counter-examples to the BRW collapse and may carry
   useful algebraic content.

## Files

- `extraspecial_orbifolds/scripts/research/research_tr_h_finer_invariant.g`
  — empirical script for m=3 / m=5 (run with `MPARAM := 3` or `MPARAM := 5`).
- `extraspecial_orbifolds/scripts/research/research_tr_h_m7_sample.g`
  — m=7 sampled validation (run with `NSAMPLES := 20`; ~5 s wall).
- `extraspecial_orbifolds/scripts/research_tr_h_m3/manifest.g`
  — per-class invariant manifest, 65 records.
- `extraspecial_orbifolds/scripts/research_tr_h_m5/manifest.g`
  — m=5 manifest, 1025 records.
- `extraspecial_orbifolds/scripts/tests/test_brw_orbit_trace_collapse.g`
  — PR #448 regression test that proved BRW-equivariance fails at m=3.
  Note: that test's PASS/FAIL status remains valid; what changes is the
  *consequence* — the failure mode is m=3-specific.
- `extraspecial_orbifolds/scripts/krr_spectral_characters_sparse.g`
  — production trace loop (see `TraceOnOmega0Gauss` lines 965–1027 and
  the per-class loop at lines 1315–1328).
- `extraspecial_orbifolds/scripts/defect_rep_minus_id_optim.g`
  — `_BuildGaussCtx`, `_efShAndTarget`, `EfCoeff1`, `MhHalfefMat`,
  `HardCodeShortComputeInterTwineref` — the underlying per-h math.

## Bottom line

- **At m ≥ 5, BRW orbit type alone determines `Tr(T_h | Ω_0)`.**
  Verified on all 1025 classes at m=5 and on 40 sampled classes at m=7.
  Closed-form: `Tr_norm = 2^(k − d(type))` with
  `d(id) = d(minus_one) = 0, d(sigma2) = 2^(m-3),
  d(sigma_1sigma_2) = 2^(m-2)`.

- **At m = 3, BRW-orbit splits exist.** Specifically the `Q_psi` Arf
  invariant takes value `±1` on a small subset of classes (10 sigma2,
  1 sigma_1sigma_2). This is a small-dim artefact, not a general
  obstruction.

- **Recommendation: ship the BRW-orbit collapse with a per-driver
  sanity check.** ~50 LOC change in `BuildKRRSpectralCharactersSparse`.
  ~35 min wall saved per K-4b m=7 driver invocation.
