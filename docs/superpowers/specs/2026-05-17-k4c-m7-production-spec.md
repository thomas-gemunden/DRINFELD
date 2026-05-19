# K-4c: m = 7 production run of the K-4a pipeline

**Date:** 2026-05-17
**Workstream prefix:** K-4c
**Status:** Spec (this doc); awaits three upstream unblocks (see §2).
**Parent EPIC:** #187 (K-4)
**Sibling phases:** K-4a (m = 3 anchor + pipeline, #200 / #201), K-4b (m = 5 production, #189 + scaffold PR #227)
**Issue:** #190 (K-4c)
**Depends on:**
- K-4b m = 5 verdict landed (cross-check that K-4c follows the same recipe).
- #236 (K-4a-T4c m = 7 Gauss-sum closed form for `Tr(T_h | Omega_0)`) — in flight.
- #129 (K-2c / P-10 lazy `BuildSimpleIndex` for the m = 7 single-query path) — in flight.
- #137 (Q-int C low-memory HAP resolution alternative for `E_+(7)`) — in flight; LHS-perturbed `ResolutionFiniteExtension` route not yet implemented.

## Section 1: Goal

Produce a definitive verdict on Keller's question for the Barnes--Wall--type lattice orbifold at $m = 7$: does the resulting 3-cocycle
$[\alpha_{\mathrm{KRR}}] \in H^3(E_+(7); U(1))$ vanish?

The verdict from this workstream is one of:

- **trivial** -- `K4aClassify(7).verdict = "trivial"`, all three detecting-subgroup checks return the trivial class. Combined with D-VAN Phase 2 (m = 7 cross-validation, see §5) agreement, this answers Keller's open question affirmatively at $m = 7$ and closes out the $m \in \{3, 5, 7\}$ programme.
- **non-trivial** -- at least one detecting-subgroup check returns a non-trivial class. Combined with D-VAN Phase 2 agreement, this answers Keller's question negatively at $m = 7$ and identifies the specific cohomology class.
- **inconsistent** -- K-4c and D-VAN Phase 2 disagree. Triggers diagnostic workflow (#152 or sibling); blocks publication.

This spec mirrors the K-4b m = 5 production spec
([`2026-05-17-k4b-m5-production-spec.md`](2026-05-17-k4b-m5-production-spec.md))
and the K-4b scaffold landed in PR #227. The structural difference at m = 7 is the three additional upstream unblocks documented in §2.

## Section 2: What's blocking and what's needed

K-4b at m = 5 needed only **two** things to be in place: the sparse spectral-trace pipeline (PR #235 / closed #220) and HAP's `ResolutionFiniteGroup(E_+(5), 4)` (which fits in ~1.2 GB / ~9 min per A-5a / #138). Everything else (detecting-subgroup classifiers, `K4aClassify` orchestrator, modular-data storage, the `BuildIntertwinerDataUntwisted` cache) carried over from K-4a Phase 2 unchanged.

K-4c at m = 7 needs **three** things, none of which are yet in main:

| # | Blocker | Issue | What it provides | Status |
|---|---|---|---|---|
| (1) | Sparse `TraceOnOmega0Gauss(h, 7)` | #236 (parent #220, PR #235) | Gauss-sum closed form for the trace evaluation on $\Omega_0$ at $m = 7$; reduces per-trace cost from $\sim 150$ days (naive entry sum at $k = 32$) to $\sim O(k)$ poly-time. | In flight (agent currently working on #236). |
| (2) | Lazy `BuildSimpleIndex` for single-query path | #129 (K-2c / P-10) | Defers per-class `CharacterTable` / `ConjugacyClasses` / `Irr` work; without it, `BuildIntertwinerDataUntwisted(E_+(7))` OOMs after $\sim 20$ min during cache build (per K-2 regression test C). | In flight (agent currently working on #129). |
| (3) | LHS-perturbed `ResolutionFiniteExtension(E_+(7), 4)` | #137 (Q-int C) | Low-memory $\mathbb{Z}E_+(7)$ resolution avoiding the OOM of `ResolutionFiniteGroup(E_+(7), 4)` (which dies at $\sim 60$ GB). Needed by `SetupCohomology3(E_+(7))` and consequently by every $H^3$-restriction call (`BuildRestrictionMatrices(7, "hap")`) that K-4c's cross-validation will require. | In flight; **LHS-perturbed implementation NOT YET LANDED**. The B3-6 stage of the Path 3 redesign ([`2026-05-16-path3-hap-resolution-redesign.md`](2026-05-16-path3-hap-resolution-redesign.md)) calls for `ResolutionFiniteExtension(gens_E, gens_V, R_V, 4, ...)` via Lyndon--Hochschild--Serre perturbation; this is the work item that needs to land. |

### 2.1: Path to landing for each

#### (1) `TraceOnOmega0Gauss(h, 7)` -- #236

The math is standard $\mathbb{F}_2$ Witt decomposition (AM04 Ch. III, Tezuka--Yagita) of a quadratic form $Q_h$ on a linear-feasibility subspace of $\mathbb{F}_2^k$, with $k = 32$ at $m = 7$. Closed form:
$$
\operatorname{Tr}(T_h \mid \Omega_0) = 2^{(k + r)/2} \cdot \operatorname{sign}\bigl(Q_h \bigm|_{L_h}\bigr)
$$
where $r$ is the rank of the bilinear form associated to $Q_h$ restricted to $L_h$, and the sign is $\pm 1$ or $\pm i$ depending on the Witt invariant. Both $r$ and the sign are `poly(k)`-computable. Acceptance: cross-validates against the entry-sum `TraceOnOmega0` at $m = 5$ (PR #235), then all $\sim 32{,}768$ traces at $m = 7$ complete in $\le 5$ minutes total.

After #236 merges, `BuildKRRSpectralCharactersSparse(7)` becomes feasible.

#### (2) Lazy `BuildSimpleIndex` -- #129

Per the K-2c issue body and the K-2 regression test, the bottleneck is `BuildIntertwinerDataUntwisted(E_+(7))` performing $\sim 16{,}385$ `CharacterTable(C_G(g_i))` builds for centralisers whose order exceeds the `smallgrp` library threshold ($> 2048$). Path 1 (recommended) introduces a lazy variant that defers per-class CT construction to first access. After K-2c merges, `K4aClassify(7)` becomes feasible from the cache side; this is the prerequisite that lets the three `BuildIntertwinerDataUntwisted(...)` calls in the K4aClassify body (E, D_8, Q_8 branches) survive at $m = 7$.

Note: K-4c uses `BuildIntertwinerDataUntwisted` on each detecting *subgroup's* `EPlusGroup(m)` instance, all of which are $E_+(7)$. The lazy cache is the single shared bottleneck across all three branches.

#### (3) LHS-perturbed `ResolutionFiniteExtension(E_+(7), 4)` -- #137

This is the substantive research workstream of the three. The B3 redesign spec ([`2026-05-16-path3-hap-resolution-redesign.md`](2026-05-16-path3-hap-resolution-redesign.md)) outlines the route:

- Build `R_V := ResolutionAbelianGroup((F_2)^{14}, 4)` (small, fast: $V = E_+(7) / Z(E_+(7))$ is elementary abelian of rank $2m = 14$).
- Build `R_Z2 := ResolutionFiniteGroup(Z/2, 4)` (trivially small).
- Compose via `ResolutionFiniteExtension(gens_E, gens_V, R_V, 4, ...)` -- the central extension $\mathbb{Z}/2 \hookrightarrow E_+(7) \twoheadrightarrow (\mathbb{F}_2)^{14}$ with the LHS spectral sequence perturbation handled by HAP.

Acceptance per #137:
1. `SetupCohomology3(E_+(7))` returns the full record without OOM (wall-clock budget $\le 1$ day single-CPU per #137).
2. `StandardCocycleOf(setup, vec)` returns a valid $\mathbb{Z}/\operatorname{exp}$-valued bar 3-cocycle (zero violations of the bar 3-cocycle equation on a probe).
3. Byte-for-byte regression at $m \in \{1, 2, 3\}$ against the existing `ResolutionFiniteGroup`-based path.
4. Successful $m = 7$ run.

Until #137 lands the LHS-perturbed path, K-4c's D-VAN cross-validation (§5) cannot run because `BuildRestrictionMatrices(7, "hap")` depends on `SetupCohomology3(E_+(7))`.

### 2.2: Order of landing

The three blockers are roughly independent in code, but for K-4c production runs they should land in the order:

1. **#236 first** (Gauss-sum): unblocks the spectral-character path at $m = 7$; cheap to validate against $m = 5$ ground truth.
2. **#129 second** (lazy index): unblocks the `BuildIntertwinerDataUntwisted` cache; once landed, K4aClassify can in principle run on `E_+(7)` for the three branches *without* needing #137 (since the K4aClassify body itself only reads `EPlusGroup(m)`'s character theory, not its $H^3$).
3. **#137 last** (LHS-perturbed resolution): the heaviest research item; unblocks D-VAN Phase 2 and the K-4c cross-validation harness. K-4c's *primary* verdict can be produced once (1) and (2) ship, but the *consistency* check against D-VAN waits on (3).

This staging matters for partial-release planning -- see §5 (Acceptance).

## Section 3: Deliverables

Following K-4b's pattern (PR #227), three artefacts:

### 3.1: Driver script -- `extraspecial_orbifolds/scripts/run_k4c_m7.sh`

Mirrors `run_k4b_m5.sh` with the following $m = 7$ adaptations:

- **Argument**: hard-codes `m = 7` (call: `gap -c 'K4aClassify(7);'`).
- **Upstream pre-checks**: at start of script, gate on the three blockers above. Specifically grep / `IsExistingFile`-equivalent guards on:
  - `extraspecial_orbifolds/scripts/krr_spectral_characters_sparse.g` containing a non-stub `TraceOnOmega0Gauss` implementation for $m = 7$ (i.e., no `TODO` / `Error("not implemented at m=7")` near that function). Bail with `[run_k4c] BLOCKED: #236 (TraceOnOmega0Gauss m=7 stub still in place)` if absent.
  - `extraspecial_orbifolds/scripts/untwisted_modular_data.g` (or its successor) exposing a `BuildSimpleIndexLazy` (or the eager `BuildSimpleIndex` being lazy-by-default). Bail with `[run_k4c] BLOCKED: #129 (lazy BuildSimpleIndex not present)` if absent.
  - The `k4a_classify.g` cap `n_max_supported := 3` must be lifted *and* the code path for $m \ge 4$ must route through the sparse spectral source (`use_spectral := true` / `BuildKRRSpectralCharactersSparse(m)`) rather than the untwisted-baseline placeholder used at $m = 3$. Bail with `[run_k4c] BLOCKED: k4a_classify.g still caps n_max_supported at 3 (and/or sparse-spectral route not wired)` if either condition fails.
- **Memory cap**: raise the K-4b $96$ GB virtual-memory cap to $\sim 200$ GB (Linux only -- `ulimit -v $((200 * 1024 * 1024)) 2>/dev/null || true`). The reason: even with the lazy cache, the three `BuildIntertwinerDataUntwisted(EPlusGroup(7))` calls and the sparse-trace tables together can reach $\sim 100$ GB resident at peak. K-4b at $m = 5$ peaked at $\sim 30$ GB; $m = 7$'s $|G|$ jumps by $16\times$ and class counts by $\sim 16\times$, so the empirical scaling suggests a $4\times$--$8\times$ peak-memory multiplier.
- **Logging**: identical structure to `run_k4b_m5.sh`, with log dir `extraspecial_orbifolds/perf/raw/k4c/` and timestamped log file `k4c_m7_YYYYMMDD_HHMMSSZ.log`.
- **Result file**: `k4c_m7_result.g`, persisting the `K4aClassify(7)` return record. Same shape as `k4b_m5_result.g` (binds the global `RESULT` on a fresh `Read`).
- **Next-steps printout**: at end of run, print pointers to (a) the cross-validation harness (§3.2) and (b) the interpretation note template (§3.3).

The script is non-executable until all three blockers land. Until then, running it bails cleanly with a `BLOCKED` diagnostic and exit code 2.

### 3.2: Cross-validation harness -- `extraspecial_orbifolds/scripts/k4c_xcheck_d_van.g`

Same structural shape as `k4b_xcheck_d_van.g`. Key differences at $m = 7$:

- **Loads `k4c_m7_result.g`** (binds `RESULT`) and falls back to a `BLOCKED:` diagnostic if absent, identical to the K-4b harness.
- **Strategy (A) -- full restriction-inversion**: the same `_DVAN_InvertRestriction(m, E_class, D8_class, Q8_class)` helper, called with $m = 7$. The K-4b spec notes this helper is a stub (returns `fail`); for K-4c it remains a stub *unless* D-VAN Phase 2 (separate workstream, see §5 acceptance criterion 4) has implemented it. The K-4c harness should NOT block K-4c shipping on (A) -- it falls back to (B) just as K-4b does.
- **Strategy (B) -- trivial-axis fallback**: identical iff structure to K-4b's:
  > "K-4c verdict = trivial IFF D-VAN($\omega = 0$).trivial = true"

  but D-VAN at $m = 7$ requires `BuildRestrictionMatrices(7, "hap")` which itself depends on `SetupCohomology3(E_+(7))` which depends on the LHS-perturbed resolution (blocker (3) above). So the harness has *two* states even after the K-4c driver succeeds:

  - **(B.0)** Blocker (3) not landed: `_K4C_BLOCKED_DVAN := true`. The harness prints `TRIVIAL-AXIS BLOCKED-ON-#137` and exits cleanly. Records the K-4c verdict as *uncross-validated*. This is the partial-release state that lets K-4c's primary verdict ship ahead of #137.
  - **(B.1)** Blocker (3) landed: full `BuildRestrictionMatrices(7, "hap")` + `ResIsTrivialOnDetectingFamily(7, zero_omega_vec)` cross-check runs. Prints `TRIVIAL-AXIS OK` / `TRIVIAL-AXIS DISAGREE` / `TRIVIAL-AXIS INCONCLUSIVE` per the K-4b convention.

- **Gating helper at top of file**: a `_K4C_HasResolutionAtM7()` predicate that probes for the presence of the LHS-perturbed resolution path. If `false`, the harness skips (B.1) and emits (B.0). Implementation: try `SetupCohomology3(EPlusGroup(7))` in a wrapped `CALL_WITH_CATCH` with a small time budget (or simply check for a sentinel file recording that the resolution has been cached).
- **At $m = 7$ the per-coordinate vector dim** $k_G$ is much larger than at $m = 5$ -- the homology basis of $H^3(E_+(7); U(1))$ has $\sim 2^{m+1} + \text{small} = 256 + 91$ generators per Quillen 1971 + Harada--Kono (the exact number is the output of `BuildRestrictionMatrices(7, "hap")`'s `setup_G.num_generators`). The zero vector used in the trivial-axis check is therefore much longer; this is purely a coding detail (`ListWithIdenticalEntries(k_G, 0)`), not a math difference.

### 3.3: Interpretation note template -- `docs/superpowers/research/TEMPLATE-k4c-m7-verdict.md`

Mirrors `TEMPLATE-k4b-m5-verdict.md` with the following $m = 7$ adaptations:

- **Header**: `K-4c m = 7 verdict -- Keller's question at the Barnes--Wall--type orbifold (m = 7 final case)`.
- **Section 1: Verdict** identical to K-4b but with $m = 7$ throughout. Cross-table the three classes against the trivial references:
  - $E$ branch: max elementary abelian of $E_+(7)$ has rank $m + 1 = 8$; trivial reference is `E_class.is_coboundary = true`.
  - $D_8$ branch: same `class_idx in [1..22]` storage (in `modular_data/8/3/`); trivial reference is `class_idx = 1`.
  - $Q_8$ branch: same `class_idx in [1..8]` storage (in `modular_data/8/4/`); trivial reference is `class_idx = 1`.
- **Section 2: Per-subgroup classes (detail)** -- analogous to K-4b's Section 2 with $m = 7$ updates. For the $E$ branch specifically, the cohomology shape becomes $H^3((\mathbb{Z}/2)^8; U(1))$; cross-cite the A-3a / A-5a torsion output for $E_+(7)$'s elementary abelian Quillen part.
- **Section 3: Cross-validation against D-VAN Phase 2** -- new sub-states relative to K-4b: include `TRIVIAL-AXIS BLOCKED-ON-#137` as a documented outcome alongside the K-4b sub-states.
- **Section 4: Confidence assessment** -- include sub-section 4.3 *additionally* checking that (a) K-4b m = 5 anchor passes (i.e., the same recipe at $m = 5$ produced a non-`fail` verdict that cross-validated against D-VAN-7), and (b) the K-4a m = 3 anchor regression (`test_k4a_classify.g`) is GREEN at the K-4c run time. Adds one row to the K-4b confidence table.
- **Section 5: Implications for Keller's conjecture at m = 7** -- this is the "final case" subsection. Specifically:
  - **5.1 Trivial case**: closes Keller's conjecture for the Barnes--Wall--type lattice orbifold programme across $m \in \{3, 5, 7\}$. Cite the methodology paper W-1 §4.4 application slot (see §7 below).
  - **5.2 Non-trivial case**: identifies the precise cohomology class at $m = 7$. Combined with $m = 3, 5$ data, this characterises the dependence of $[\alpha_{\mathrm{KRR}}]$ on $m$ -- e.g., does it stabilise? Cycle? Branch?
- **Section 6: Reproducibility** -- identical to K-4b but pointing at `run_k4c_m7.sh`, `k4c_xcheck_d_van.g`, `k4c_m7_result.g`.
- **Section 7: Follow-ups** -- explicitly enumerate (i) D-VAN Phase 2 cross-validation completion if it lagged the primary verdict (the (B.0) state above), (ii) full W-1 §4.4 fill-in, (iii) W-1d (#58) conclusions section updates.

The template ships with the K-4c spec PR but is filled in only after the production run completes (same flow as K-4b's template).

## Section 4: Compute budget at m = 7

Anchored to the K-4b m = 5 measured numbers and the sparse-trace projection in #236.

### 4.1: Per-branch budget at m = 7 (after all three blockers land)

| Stage | m = 5 cost (measured) | m = 7 cost (projected) | Rationale |
|---|---|---|---|
| Sparse trace `BuildKRRSpectralCharactersSparse` | $\sim 23$ min wall (PR #235) | $\le 5$ min wall (per #236 acceptance) | Gauss-sum closed form is `poly(k)`; per #236, all $\sim 32{,}768$ traces complete in seconds-to-minutes once the closed form lands. |
| `BuildIntertwinerDataUntwisted` (per branch) | $\sim 1$--$2$ min | $\sim 5$--$15$ min (depends on K-2c laziness) | $|E_+(7)| = 32{,}768$ vs $|E_+(5)| = 2{,}048$; lazy index defers most work. |
| `RestrictTraceOnWToSubgroup` | seconds | seconds--minutes | Trace projections, modest matrix work. |
| $E$ branch classifier (`_K4A_ClassifyAbelianBranch`) | seconds | seconds | Abelian closed form; no growth in cost. |
| $D_8$ branch classifier (`_K4A_ClassifyNonAbelianBranch` via `ClassifyOnD8`) | seconds | seconds | Operates on $D_8$ data; independent of $m$. |
| $Q_8$ branch classifier (analogous via `ClassifyOnQ8`) | seconds | seconds | Same as $D_8$. |
| **K-4c driver total (without cross-validation)** | **~30--40 min** | **~1--3 hours** | Order-of-magnitude comparable; dominated by `BuildIntertwinerDataUntwisted` at $m = 7$. |

### 4.2: Cross-validation budget at m = 7 (after blocker (3) lands)

| Stage | Cost |
|---|---|
| `SetupCohomology3(E_+(7))` via LHS-perturbed resolution | $\le 1$ day single-CPU per #137 acceptance criterion 4. |
| `BuildRestrictionMatrices(7, "hap")` (chain maps on top of the resolution) | $\sim 1$--$3$ hours (extrapolating from $m = 5$'s $\sim 10$ min total) |
| `ResIsTrivialOnDetectingFamily(7, zero_omega_vec)` | seconds (one vector evaluation; the matrix is cached). |
| **D-VAN Phase 2 cross-validation total** | **~1 day on first run, seconds on cached subsequent runs.** |

### 4.3: Combined budget

- **Primary K-4c verdict** (after blockers (1)+(2)): **a few hours** wall-clock on a workstation with $\ge 200$ GB.
- **K-4c verdict + D-VAN Phase 2 cross-validation** (after blocker (3) additionally): **+~1 day** on first run.

Compared to K-4b m = 5's $\sim 30$--$40$ min total, K-4c m = 7 is one order of magnitude larger in wall-clock; both fit within a single working day from start to verdict-with-cross-check.

### 4.4: Risks to the budget

- The K-2c lazy-cache `BuildIntertwinerDataUntwisted` projection (15 min per branch) is an extrapolation from K-2 regression test data; the actual cost depends on which classes the K-4a code path actually touches in `RestrictTraceOnWToSubgroup` (which selects only the subgroup's conjugacy class reps via the transport bookkeeping). If the touched-class count is small (a few per branch), the per-branch cost may be tens of seconds, not minutes. If full $\sim 32{,}768$-class enumeration is implicitly required, the cost balloons.
- The LHS-perturbed resolution timing is itself a research output, not a measured number. #137 specifies "$\le 1$ day single-CPU" as the acceptance target but does not pre-commit to it.

## Section 5: Acceptance

Five criteria (one more than K-4b, reflecting K-4c's three blockers and the partial-release option):

| # | Criterion | Reference |
|---|---|---|
| 1 | K-4b m = 5 verdict landed and cross-checked. (Same recipe at $m = 5$ produced a verdict that passed at least the (B) trivial-axis check; ideally also (A) once the inversion helper lands.) | [`2026-05-17-k4b-m5-production-spec.md`](2026-05-17-k4b-m5-production-spec.md), PR #227 scaffold, K-4b run. |
| 2a | Blocker (1): #236 `TraceOnOmega0Gauss(h, 7)` lands. Acceptance: cross-validates against entry-sum at $m = 5$; produces valid sparse multiplicities at $m = 7$. | #236 |
| 2b | Blocker (2): #129 lazy `BuildSimpleIndex` lands. Acceptance: single `SKeller(7, i, j)` query completes in $\le 5$ min wall, K-2 regression test C green. | #129 |
| 2c | Blocker (3): #137 LHS-perturbed `ResolutionFiniteExtension(E_+(7), 4)` lands. Acceptance: per #137's own criteria 1--4. **Required only for the D-VAN Phase 2 cross-validation (acceptance #4)**; not required for the K-4c primary verdict (acceptance #3). | #137 |
| 3 | K-4c driver produces a verdict record. `run_k4c_m7.sh` runs to completion (exit 0); `k4c_m7_result.g` is loadable in a fresh GAP session and binds a `RESULT` record with `verdict in {"trivial", "non-trivial"}` (i.e. not `"incomplete"`). | This spec, §3.1. |
| 4 | D-VAN cross-validation passes. `k4c_xcheck_d_van.g` reports `TRIVIAL-AXIS OK` or strategy (A) `CONSISTENT`. **Blocked on blocker (3) (#137)**; until then, the harness emits `TRIVIAL-AXIS BLOCKED-ON-#137` and acceptance #4 is **deferred** rather than `fail`. | This spec, §3.2. |
| 5 | Interpretation note filled in and committed to `docs/superpowers/research/`. | This spec, §3.3. |

### 5.1: Partial-release option

If (1), (2a), (2b), and (3) ship but (2c) lags, K-4c can ship a *primary verdict* with the cross-validation deferred. This is captured in the (B.0) state of `k4c_xcheck_d_van.g` and the K-4c interpretation note's Section 3 / Section 4. The methodology paper W-1 §4.4 can cite the primary verdict with a footnote about the deferred cross-validation.

If all five close in one tranche, the K-4c verdict is fully cross-validated and W-1's §4.4 can claim a definitive result.

## Section 6: Risks

### High: LHS-perturbed resolution is non-trivial research

Blocker (3) is the most uncertain of the three. The B3 redesign spec lays out the route but does not yet have a working implementation; the chain-level operations (`HAP_SteenrodCup1`, `HAP_PontryaginSquare`, `HAP_IntegrateToZ4Cocycle`) are partly landed (B3-1, B3-2, B3-3 issues #171, #172, #173) but the integration into a working `ResolutionFiniteExtension(E_+(7), 4)` substrate is open. If #137 stalls, K-4c's D-VAN Phase 2 cross-validation cannot run.

**Mitigation**: the partial-release option (§5.1) lets K-4c's primary verdict ship even if #137 lags. The methodology paper can defer the cross-validation citation to a follow-up. Avoid making W-1's results section depend on #137 completion.

### Medium: Gauss-sum closed form may have edge cases at m = 7

Per #236's "Risk" subsection: if the $\mathbb{F}_2$ Witt decomposition has degenerate cases at $m = 7$ that the cross-validation at $m = 5$ didn't exercise (e.g. fully isotropic $Q_h$ on $L_h$), the implementation may need a case split. The cross-check at $m = 5$ catches most issues but cannot cover a case that only appears at $m \ge 7$.

**Mitigation**: add unit tests in `tests/test_krr_spectral_characters_sparse.g` that probe degenerate $Q_h$ shapes specifically; cross-check sparse mults sum to $\dim \Omega_0 = 2^{32}$ as a sanity invariant at $m = 7$ (per #236 acceptance criterion 4).

### Medium: detecting-family injectivity at m = 7

R-1 (#193) and its follow-up [`2026-05-17-d8-vs-q8-detection.md`](../research/2026-05-17-d8-vs-q8-detection.md) established injectivity of $\{E, D_8, Q_8\}$ at $m = 3$ (and observed that $D_8$ alone fails on $2 \cdot A(4)_{\mathrm{gen}}$). The injectivity argument is structural -- Harada--Kono 1987 Theorem 1.1 + AM04 §IV.2 -- and applies at all $m \ge 2$, but it has only been *empirically* verified at $m = 3$. At $m = 7$ the same Harada--Kono $A(4) \cong \mathbb{Z}/4$ structure persists (since $m \ge 3$ uses $a(4, Q) = n(4) = 2$ uniformly), so the same restriction-map analysis applies and the same triple $\{E, D_8, Q_8\}$ is sufficient.

**Mitigation**: nothing to do for K-4c; the math is upstream-mitigated. If K-4c returns a non-trivial verdict, cross-cite the R-1 follow-up note in the interpretation.

### Medium: Aut(N, T) cross-validation at m = 7 is intractable at full rank

K-4b at $m = 5$ benefits from a possible Aut($N$, $T$)-based cross-validation against $\operatorname{Aut}(E_+(5))$ orbits of $H^3(E_+(5); U(1))$ (since $|H^3| < \infty$ and small enough at $m = 5$). At $m = 7$:
- $|H^3(E_+(7); U(1))|$ is the product of torsion factors; at $m = 7$ with $E$ of rank 8 the elementary abelian Quillen part alone has $\sim 2^{40}$+ classes, plus higher Harada--Kono summands.
- Enumeration over Aut($E_+(7)$)-orbits is intractable.

Therefore at $m = 7$ only **modular-data-comparison via K-4a** (i.e. the K-4c primary verdict) and **D-VAN Phase 2** apply as cross-checks. The Aut-based path that *could* serve at smaller $m$ is unavailable.

**Mitigation**: nothing to do; this is a structural property of the $m = 7$ case. The interpretation note's confidence assessment should call this out explicitly so readers don't expect an Aut-orbit consistency claim.

### Low: K-4b verdict surfaces upstream issues

If K-4b m = 5 returns `verdict = "incomplete"` (a branch failed) or the K-4b D-VAN cross-check reports a `TRIVIAL-AXIS DISAGREE`, K-4c should pause until the upstream issue is diagnosed -- following the K-4b spec's diagnostic-workflow reference (#152). The acceptance criterion #1 above is what gates this.

## Section 7: What this unblocks (post K-4c)

- **Full Keller verdict at all $m \in \{3, 5, 7\}$**: the three-data-point result that answers Keller's open question for the Barnes--Wall--type lattice orbifold across the small-extraspecial regime.
- **Methodology paper W-1, §4.4 (Applications) fills in**: per the W-1c per-$m$ applications subsection ([`docs/superpowers/specs/...w-1c...`](../specs)), §4.4 currently has placeholders for the $m = 5$ and $m = 7$ rows of the results table. K-4b fills $m = 5$; K-4c fills $m = 7$.
- **W-1d conclusions (#58) can claim definitive results**: the W-1d conclusions section depends on $m = 7$ being settled. With K-4c landed (primary verdict at minimum), W-1d can move from "anchored at $m = 3$, work in progress at higher $m$" to a concrete statement of the full programme outcome.
- **D-VAN Phase 2 itself unblocks**: once #137 (which D-VAN Phase 2 at $m = 7$ also needs) lands and K-4c's cross-validation runs, the D-VAN-1 EPIC (#142) Phase 2 follow-up sibling can advance. K-4c's `k4c_xcheck_d_van.g` is the first consumer of D-VAN Phase 2.
- **Follow-on programme: m = 9 and beyond**: a separate workstream if the $m \in \{3, 5, 7\}$ trio motivates pushing higher. Out of scope for K-4c.

## Section 8: What K-4c does NOT do

- Compute $H^3(E_+(7); U(1))$ kernel directly (that's A-7a / A-7b under Q-int B2-6 #166).
- Compute the modular data of $Z(\mathrm{Vec}_{E_+(7)}^{\alpha_{\mathrm{KRR}}})$ in full (intractable at $m = 7$; the detecting-family route is the whole point).
- Resolve #137's research question (that's #137 itself).
- Implement `_DVAN_InvertRestriction` (strategy (A) in `k4c_xcheck_d_van.g`); inherits the K-4b status (stub, fallback to (B)).
- Run automatically -- this is an explicit human-triggered run after the three blockers land.

## Section 9: Out of scope

- $m \ge 9$ production runs (separate follow-on programme).
- Generalisation to non-CT twists (outside KRR's verified setting; mirrors K-4b §"Out of scope").
- Statistical confidence quantification (verdict is deterministic yes/no modulo bugs).
- Aut-orbit cross-validation at $m = 7$ (intractable; see §6).

## Section 10: Issues to file (after this spec lands)

- **[K-4c-T1]** Driver + cross-validation harness + interpretation template (`run_k4c_m7.sh`, `k4c_xcheck_d_van.g`, `TEMPLATE-k4c-m7-verdict.md`). Sibling of K-4b PR #227 scaffold; ships ahead of the production run with `BLOCKED:` guards.
- **[K-4c-T2]** Interpretation note (depends on T1 + production run completing).
- **[K-4c-T3]** Driver smoke tests (`tests/test_k4c_scaffold_smoke.g`), mirroring K-4b PR #227's smoke test (bash syntax, harness parses, template structure).
- **[K-4c-T4]** Production run gate-keeper (once all three blockers (1)-(3) close, file the actual run as a single-shot task).

## Section 11: References

- Spec: K-4b m = 5 production: [`2026-05-17-k4b-m5-production-spec.md`](2026-05-17-k4b-m5-production-spec.md)
- Spec: K-4a Phase 2 implementation: [`2026-05-17-k4a-phase2-implementation-spec.md`](2026-05-17-k4a-phase2-implementation-spec.md)
- Spec: Path 3 HAP resolution redesign (B3): [`2026-05-16-path3-hap-resolution-redesign.md`](2026-05-16-path3-hap-resolution-redesign.md)
- Spec: Detecting-family vanishing test design: [`2026-05-15-detecting-family-vanishing-test-design.md`](2026-05-15-detecting-family-vanishing-test-design.md)
- Research: D_8 vs {D_8, Q_8} detection: [`../research/2026-05-17-d8-vs-q8-detection.md`](../research/2026-05-17-d8-vs-q8-detection.md)
- Research: Detecting-family literature: [`../research/2026-05-17-detecting-family-literature.md`](../research/2026-05-17-detecting-family-literature.md)
- K-4b scaffold (PR #227): `extraspecial_orbifolds/scripts/run_k4b_m5.sh`, `k4b_xcheck_d_van.g`, `tests/test_k4b_scaffold_smoke.g`, `docs/superpowers/research/TEMPLATE-k4b-m5-verdict.md`.
- K-4 EPIC: #187.
- This spec's K-4c issue: #190.
- Blockers: #236 (Gauss-sum), #129 (lazy index), #137 (Q-int C resolution).
- Related: #148 (D-VAN-7, m = 5 anchor), #142 (D-VAN-1 EPIC), #58 (W-1d conclusions).
