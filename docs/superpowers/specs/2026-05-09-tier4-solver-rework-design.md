# Tier-4 transgression-kernel solver rework — design

Date: 2026-05-09. Author: Thomas Gemunden + Claude Opus 4.7.
Issues: #10 (T-1), #11 (T-2), #13 (T-4), #31 (T-3d), #42 (A-3a), #61 (T-1a).
Supersedes the cost-model assumptions in `extraspecial_orbifolds/parallel_workstreams_design.md` §2.1 / §3.

## 1. Motivation

The current `IsCoboundary2` (`extraspecial_orbifolds/scripts/transgression_kernel.g:94–134`) builds an $n^2 \times (n + n^2)$ augmented integer matrix and calls `SolutionIntMat` over $\mathbb Z$. On $E_+(3)$ this is GC-bound, not algorithm-bound: a 2026-05-09 run got 0 / 35 generators done in 3 h 13 min wall, peak 29 GB RSS, with ~44 % of CPU in `CollectBags` per a live `sample` of the GAP process (full hot-stack excerpt on issue #10 comment of 2026-05-09). The killing issue is GMP-big-integer allocation pressure during `SolutionIntMat`'s row reduction; the heap is so large that every allocation triggers a multi-second mark-sweep.

Replacement target: full $\ker \mathrm{Tr}(E_+(3))$ as an explicit subgroup of $(\mathbb Z/2)^{34} \oplus \mathbb Z/4$, in $\le 1$ h wall and $\le 8$ GB peak RSS. Stretch target ~10 min wall.

## 2. Scope

This spec covers four GitHub-issue workstreams as one coordinated change:

* **T-1** (#10) — replace `IsCoboundary2` with a torsion-split solver (mod-2 + Bockstein-image test for order-2 generators; $\mathbb Z/\exp$ fallback for the unique order-$\exp$ generator).
* **T-1a** (#61) — four math / HAP-API edge cases that need documented answers during T-1 implementation.
* **T-2** (#11) — SNF wrapper accumulating the per-generator transgression matrix $M$ and computing $\ker M$.
* **T-3d** (#31) — BRW-orbit reduction on conjugacy classes (4 orbit reps instead of 65 classes at $m = 3$).
* **T-4** (#13) — caching of resolutions and Bockstein images by centraliser isomorphism type.
* **A-3a** (#42) — end-to-end driver `run_e_plus_3_kernel.g` producing `computed/transgression/3/kernel.g`.

Out of scope: $m = 5$ / $m = 7$ work (separate epics); refactoring of `transgression_kernel.g` beyond adding the new entry point.

## 3. Spike result (2026-05-09)

`SolutionMat` over $\mathbb F_2$, single-process GAP 4.15.1 on the design machine:

| Scale | Build matrix | `SolutionMat` |
|---|---:|---:|
| $\|C\| = 64$, boundary system $4096 \times 64$ | 0.06 s | **1 ms** |
| $\|C\| = 128$, boundary system $16384 \times 128$ | 0.31 s | **10 ms** |

Per-generator inner cost on $E_+(3)$: $63 \times 1 \mathrm{\,ms} + 2 \times 10 \mathrm{\,ms} \approx 83 \mathrm{\,ms}$. Full per-generator-sweep inner-loop wall: ~3 s. Comfortably under the §3 design-doc target of ~10 min once cocycle-evaluation and Bockstein-image overhead are added.

The cost model is no longer "$\mathrm{SNF}$ over $\mathbb Z$ is expensive" (the old §2.1 framing) — it is "GMP big-int allocation under a multi-GB heap is expensive". Switching to GF(2) drops both ends: faster algorithm and immediate single-word GAP objects with no large bag headers, so GC stops dominating.

## 4. Architecture

Three new modules under `extraspecial_orbifolds/scripts/solver/`, plus the existing `transgression_kernel.g` left in place (kept as the regression baseline; new code routes to it for the order-$\exp$ generator if HAP's $\mathbb Z/\exp$ path is unavailable).

```
extraspecial_orbifolds/scripts/
    solver/
        iscoboundary2_split.g       # public entry point
        mod2_solver.g               # GF(2) coboundary + Bockstein image
        z4_fallback.g               # order-exp path (HAP first, augmented-Z fallback)
        snf_wrapper.g               # T-2: build M, compute ker via NormalFormIntMat
        brw_orbits.g                # T-3d: 4 orbit reps + BRW-action on H^3 coords
        centraliser_cache.g         # T-4: cache resolutions + Bockstein images
        tests/
            test_d8.g
            test_e_plus_2.g
            test_e_plus_3.g
    run_e_plus_3_kernel.g           # A-3a end-to-end driver (replaces run_e_plus_3_per_gen.g)
    transgression_kernel.g          # unchanged, kept as regression baseline
```

Public API:

```gap
# Boolean coboundary test (T-1).
# C: centraliser group, c_g: function (h, k) -> Z/exp value, vec: H^3 coord vector,
# setup: SetupCohomology3 record (gives torsion + exponent).
IsCoboundary2Split(C, c_g, vec, setup) -> bool

# Cohomology class as integer vector (T-1 + T-2 extension).
# Returns coordinates of [c_g] in a fixed basis of H^2(C; Z/exp).
CohomologyClass2(C, c_g, vec, setup) -> List(Int)

# Full pipeline (T-1 + T-2 + T-3d + T-4 + A-3a).
TransgressionKernelExact(G) -> rec( kernel := <subgroup gens>, M := <int matrix>, ... )
```

## 5. Core algorithm (torsion-split coboundary test)

**Setup.** Let $G$ have $H^3(G; U(1)) \cong H^3(G; \mathbb Z/\exp) \cong \bigoplus_{i=1}^k \mathbb Z/d_i$ with $d_i \mid \exp$. The $k$ generators $e_1, \ldots, e_k$ are realised as standard cocycles via `StandardCocycleOf(setup, vec)`. A query is a pair `(vec, [g])` asking *is $c_g$ a $\mathbb Z/\exp$-coboundary on $C := C_G(g)$?*

**Dispatch.** Decompose `vec` over the torsion sublattices. Let $r := \exp / d_i$ be the reduction factor for the $i$-th generator's torsion. The class has order dividing $\exp / r = d_i$, and $c_g$ takes values in $r \cdot \mathbb Z/\exp \subset \mathbb Z/\exp$ (the order-$d_i$ subgroup). Hence $c_g = r \cdot c'_g$ with $c'_g \in \mathbb Z/d_i$.

**Path A (order $< \exp$, the common case).** When all non-zero coordinates of `vec` are at order-2 generators (so $d_i = 2$ uniformly across `vec`'s support — in particular any unit vector $e_i$ with $d_i = 2$, hence the 34 unit vectors $e_1, \ldots, e_{34}$ on $E_+(3)$ and the 9 unit vectors $e_1, \ldots, e_9$ on $E_+(2)$), $r = \exp / 2$ and $c'_g$ is a $\mathbb Z/2$-2-cocycle on $C$. From the SES
$$
0 \;\longrightarrow\; \mathbb Z/2 \;\xrightarrow{\,\cdot r\,}\; \mathbb Z/\exp \;\xrightarrow{\,\bmod\, 2\,}\; \mathbb Z/(\exp/2) \;\longrightarrow\; 0
$$
and its LES,
$$
[c_g] = 0 \text{ in } H^2(C; \mathbb Z/\exp)
\;\;\iff\;\;
[c'_g] \in \mathrm{image}\!\left(\beta : H^1(C; \mathbb Z/2) \to H^2(C; \mathbb Z/2)\right).
$$
This collapses to two cheap GF(2) sub-checks:

* **(B1)** Run `SolutionMat` over $\mathbb F_2$ on the boundary system $A \beta = c'_g$ ($A$ shape $|C|^2 \times |C|$). Spike-confirmed at 1 ms / 10 ms for $|C| = 64$ / $128$. If solvable, $[c'_g] = 0$, so trivially in $\mathrm{image}(\beta)$.
* **(B2)** Otherwise, project $c'_g$ to its class $[c'_g] \in H^2(C; \mathbb F_2)$ and test membership in $\mathrm{image}(\beta)$. Image is small ($\le 2^{\mathrm{rk}\,C^{\mathrm{ab}}}$) and depends only on the centraliser isomorphism type — cached once per type via T-4.

**Path B (order-$\exp$ generator touched).** When `vec[k] \neq 0` at the unique generator with $d_k = \exp$, no reduction is possible. Two implementation options:

1. HAP's bar-resolution `Cohomology(R, 2)` over $\mathbb Z/\exp$ — to be confirmed during T-1 implementation (T-1a question 4).
2. Augmented-$\mathbb Z$ `SolutionIntMat` baseline, scoped to one generator only, on a fresh GAP process so heap pressure from the path-A work doesn't accumulate. At 65 calls × minutes-per-call, total $\le$ 1 h — acceptable when scoped to one generator.

**Math correctness premises (open during implementation, tracked in #61).**

* P1 — for every `vec` with $d_i < \exp$ at all non-zero coordinates, the standard-cocycle output $c_g$ takes values in $r \cdot \mathbb Z/\exp$. Validation hook: empirical check on $E_+(2)$.
* P2 — HAP exposes the Bockstein $\beta = \mathrm{Sq}^1$ on $H^1$ in a way that lets us extract its image as an $\mathbb F_2$-subspace.
* P3 — HAP's `Cohomology(R, 2)` (or analogue) projects a 2-cocycle to coordinates in a fixed basis.
* P4 — HAP supports $\mathbb Z/\exp$ coefficients for the order-$\exp$ generator's coboundary check (else use the scoped augmented-$\mathbb Z$ fallback).

If any premise fails, the documented fallback is sufficient — none block design.

**Out-of-scope generalisation.** Groups whose $H^3$ has *mixed* sub-exponent torsion (e.g. $d_i \in \{2, 4\}$ with $\exp = 8$) would need additional path-A variants per torsion order. $E_+(2)$ ($d_i \in \{2, 8\}$) and $E_+(3)$ ($d_i \in \{2, 4\}$) both fit the simpler "all non-trivial $d_i$ are either 2 or $\exp$" pattern, so this rework targets that pattern only.

## 6. T-2, T-3d, T-4 integration

**T-2 — SNF wrapper.** Per-class $T_g$ returns the coordinate vector of $[c_g]$ in a basis of $H^2(C_g; \mathbb Z/\exp)$. Concatenated across $[g]$ and stacked over generators, this gives $M \in \mathrm{Mat}(k \times \sum_{[g]} k_{C_g}; \mathbb Z)$. $\ker \mathrm{Tr}$ is then the image of the source torsion lattice under `NormalFormIntMat(M, exp)`. Sub-second once $M$ is built.

**T-3d — BRW-orbit reduction.** The 65 conjugacy classes of $E_+(3)$ partition into 4 BRW-orbits. For each orbit $O$ pick one rep $g_O$, run T-1 on $g_O$, and pull back to other classes in $O$ via the $\mathrm{BRW}(3)$-action on $H^3(G; U(1))$ (a once-computed permutation-with-signs of the generator coordinates). Reduces inner-loop calls from $65 \times 35 = 2275$ to $4 \times 35 = 140$. The BRW-action matrix is computed by direct cocycle pullback (option 1 of §2.4 in the parallel-workstreams doc) and validated at $m = 2$ before reliance at $m = 3$.

**T-4 — centraliser caching.** The 65 centralisers fall into 4 isomorphism types per the §2.3 BRW-orbit table. Cache per type: HAP resolution `ResolutionFiniteGroup(C_type, 4)`, basis of $H^2(C_{\mathrm{type}}; \mathbb Z/2)$, the Bockstein-image subspace, and basis of $H^2(C_{\mathrm{type}}; \mathbb Z/\exp)$. Persisted to `computed/transgression/3/centraliser_cache.g` for resumption.

## 7. Test ladder

Cheap-to-expensive; each rung is a hard regression gate before moving to the next.

1. **D_8 unit (T-1 + T-2 sanity).** Existing `test_transgression_d8.g`. Full enumeration; pass = trivial kernel + per-class T-1 byte-identical to baseline. Wall: seconds.
2. **E_+(2) per-generator boolean regression (T-1 correctness).** Existing `test_transgression_per_gen_e2.g`. Per-class booleans byte-identical to on-disk record. Wall: seconds. Note: $\exp = 8$, so $r = 4$ for order-2 generators — exercises the parameterized path 1 generation before $E_+(3)$.
3. **E_+(2) ker Tr regression (T-2 math anchor).** Full §3 stack on $E_+(2)$. Pass = $\|\ker \mathrm{Tr}\| = 2048$ exactly (matches commit `9bffebb`). Wall: seconds-to-minutes. **If this passes, the math is right.**
4. **E_+(3) end-to-end (A-3a).** `run_e_plus_3_kernel.g` on `SmallGroup(128, 2326)`. Pass = explicit ker Tr subgroup, wall ≤ 1 h, peak RSS ≤ 8 GB.

## 8. Acceptance criteria

| Issue | Existing | Refined |
|---|---|---|
| T-1 (#10) | wall ≤ 0.1× baseline at $n=64$; D_8 + E_+(2) per-gen boolean regression | + peak RSS ≤ 8 GB on $E_+(3)$; + median per-call wall at $n=128$ ≤ 100 ms over 10 sample inputs (absolute, since the augmented-Z baseline at $n=128$ is not measurable in finite time on $E_+(3)$); + parameterized $r$ path tested on D_8 + E_+(2) + E_+(3) |
| T-1a (#61) | — | four documented answers (P1–P4) reflected in T-1 implementation |
| T-2 (#11) | (existing) | + reproduces $\|\ker \mathrm{Tr}(E_+(2))\| = 2048$ exactly |
| T-3d (#31) | (existing) | + BRW-action matrix validated against m=2 brute force before m=3 use |
| T-4 (#13) | (existing) | + cache hit on second $E_+(3)$ run gives ≥ 5× wall speedup |
| A-3a (#42) | wall ≤ 1 h; output at `computed/transgression/3/kernel.g` | + peak RSS ≤ 8 GB; + ker matches a 100-class direct-evaluation cross-check |

## 9. Implementation order

Three sequential PRs.

* **PR 1 — T-1 + T-2.** Math correctness, gated at rung 3 (E_+(2) ker = 2048). T-1a's four answers committed in this PR. ~3–4 days.
* **PR 2 — T-3d + T-4.** Performance, gated at re-running rungs 1–3 with reduction/cache on (booleans + ker identical to PR 1). ~2–3 days.
* **PR 3 — A-3a driver.** End-to-end script, gated at rung 4. ~half day. Closes #42 and #2.

Branching: `t1-solver-rework` off `main`, then `t3d-t4-perf` off the merged PR 1, then `a3a-driver` off the merged PR 2.

Sub-spikes during PR 1 (each $<$ 1 h):

1. Today's tiny GF(2) spike (✓ done).
2. HAP Bockstein spike — confirm `ModPCohomologyRing(D_8, *, 2)` exposes $\mathrm{Sq}^1 = \beta$. Closes T-1a question 2.
3. 2-divisibility spike on E_+(2) — confirm $c_g$ takes values in $\{0, 4\} \pmod 8$ for the 9 order-2 generators. Closes T-1a question 1.
