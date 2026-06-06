# D-VAN: Detecting-Family Vanishing Test for H³(E_+(m); U(1))

**Date:** 2026-05-15
**Workstream prefix:** D-VAN
**Status:** Design (this doc); see issue tree below for implementation tracking.

## Goal

Decide whether a 3-cocycle class `[ω] ∈ H³(E_+(m); U(1))` is trivial by
restricting to the AM04 detecting family `F = {E, D_8}` instead of
computing the full kernel of the transgression map on `H³(E_+(m); U(1))`.

The injectivity of

```
res : H³(E_+(m); U(1)) → H³(E; U(1)) ⊕ H³(D_8; U(1))
```

is the key theorem (AM04 §IV.4-§IV.5 (specifically Thm 4.3 + Thm 5.6) +
Quillen 1971 essential-ideal argument: the essential ideal of
`H*(E_+(m); F_2)` starts in degree `2m`, so degree 3 is clear for all
m ≥ 2). For our application (Keller's question "is `[ω] = 0`?") this
means the test reduces to two cheap subgroup checks:
`|E| = 2^{m+1} ≤ 256` for m ≤ 7 and `|D_8| = 8` always.

The citation chain in detail: Adem–Milgram framework (§IV.4-§IV.5) →
Quillen 1971 Thm 5.10 (explicit H*(E_+(m); F_2)) → Harada–Kono 1987
Thm 1.1 (integer A(k) summand) → UCT for U(1) coefficients. See R-1
(`docs/superpowers/research/2026-05-17-detecting-family-literature.md`)
for the full synthesis.

## Motivation

The full kernel-of-Tr computation requires `ResolutionFiniteGroup(E_+(m), 4)`
and the per-generator transgression sweep (A-3a / A-5b machinery). For
the Keller question we don't need the full kernel — we only need to
know whether a specific `ω` lies in it. The detecting-family test does
that in seconds at any m, without touching the resolution at m = 7.

## Scope

Three public deliverables, two-phase rollout.

### Public API

```gap
# Core test.
ResIsTrivialOnDetectingFamily(m, omega_vec) -> rec(
    trivial   : bool,
    res_E_vec : coordinate vector in H³(E;   U(1)),  mod torsion_E
    res_D8_vec: coordinate vector in H³(D_8; U(1)),  mod torsion_D8
    f_E       : function(g1, g2, g3) -> Z/exp_E,    bar 3-cocycle on E
    f_D8      : function(g1, g2, g3) -> Z/exp_D8,   bar 3-cocycle on D_8
    source    : "hap" | "quillen"
);

# Keller-namespace wrapper.
KellerTwistIsTrivial(m, omega_vec) -> bool;

# S-entry dispatcher.
KellerSEntry(m, omega_vec, i, j) -> matrix entry;
    # trivial twist     -> S0Entry(m, i, j)  (closed form via existing V-2)
    # non-trivial twist -> SKellerEntry(m, omega_vec, i, j)  (K-2 adapter)
```

### Two-phase rollout

**Phase 1 — HAP-based, m ∈ {2, 3, 5}.** Restriction matrices via HAP on
`G = E_+(m)`'s resolution. Empirical anchors: every unit basis vector
of `H³(E_+(m); U(1))` reports `trivial = false` (by AM04+Quillen
injectivity of restriction); zero classes report `trivial = true`. (An
earlier draft said "matches HAP per-generator kernel-of-Tr"; that
framing is a math conflation between `ker(Tr)` and the detecting-family
restriction kernel — see the 2026-06-06 audit at
`extraspecial_orbifolds/docs/superpowers/research/2026-06-06-ker-tr-detecting-family-audit.md`.)
Ships first; independent of Q-int.

**Phase 2 — Quillen-based, m = 7.** Restriction matrices computed
analytically from the canonical Quillen presentation (`quillen_canonical_presentation.g`,
Q-2a / issue #133): pull back along `E ↪ G` and `D_8 ↪ G` at the
F_2-cohomology level, then lift to `H⁴(Z)` via the Bockstein spectral
sequence using `quillen_bockstein.g` (Q-int A1 / PR #139). Cross-validated
against Phase 1 at m = 2, 3, 5; delivers the m = 7 unlock. Gated on Q-int
A2/A3 (issue #136).

### Input convention

`omega_vec` accepts either:

- A hom-basis coordinate vector of length `Length(UCT.hombasis)` (e.g. 10
  for m = 2, 35 for m = 3), or
- A raw R-basis cocycle vector of length `R!.dimension(3)`.

Dispatch by length, matching the V-4a-fixed convention in
`fsi_wrapper.g::FSI_LiftIfHom` (which uses `UCT.cocyclebasis`, NOT the
mis-shaped `UCT.lift`).

### Out of scope

- **D-INV** (cohomology-level inverse for full kernel reconstruction at
  m = 7). Forward-referenced at issue #140; depends on D-VAN + Q-int
  A2/A3 + A-5b.
- Generalisation beyond extraspecial 2-groups of plus type.
- Computing the image of `res` (which we don't need — vanishing
  testing only requires evaluating `res` on a specific input, not
  inverting it).

## Architecture

### File layout

```
extraspecial_orbifolds/scripts/
  quillen_detecting_subgroup.g          # existing — keep as-is, used as input
  detecting_family_restriction.g        # NEW: restriction-matrix builders
  detecting_family_vanish.g             # NEW: ResIsTrivialOnDetectingFamily
  keller/                                # NEW directory if not present
    keller_twist_is_trivial.g           # NEW: Keller-namespace wrapper
    keller_s_entry.g                    # NEW: S-entry dispatcher
  tests/
    test_detecting_family_restriction.g # NEW
    test_detecting_family_vanish.g      # NEW
    test_keller_s_entry.g               # NEW
    test_detecting_family_phase2_xcheck.g  # NEW (deferred, Phase 2)
```

### `detecting_family_restriction.g`

Builds and caches restriction matrices per `(m, source)`. The HAP path
(Phase 1) uses `EquivariantChainMap` to lift the inclusion `E ↪ G` to a
chain map between HAP resolutions, then pulls back cocycle representatives
to obtain a linear map on H³-coordinates. The Quillen path (Phase 2)
substitutes variables in the canonical Quillen presentation directly
(pull-back along the inclusion of generating sets), bypassing HAP at G.

```gap
BuildRestrictionMatrices := function(m, source)
    # source ∈ {"hap", "quillen"}. Returns rec(
    #   m, source,
    #   res_E       : Matrix mapping H³(G; U(1)) -> H³(E;   U(1))
    #   res_D8      : Matrix mapping H³(G; U(1)) -> H³(D_8; U(1))
    #   torsion_G, torsion_E, torsion_D8,
    #   exp_G,     exp_E,     exp_D8,
    #   H_E, H_D8                  # the GAP subgroups
    # ).
    # Cached per (m, source) at module level in _DETF_CACHE.
end;
```

For Phase 1, the matrix entries are computed once and stored as the
representative of the cohomology-level restriction. The matrix is over
Z mod (the appropriate torsion), so its application is integer linear
algebra. For Phase 2, the same matrix is computed analytically; the cache
record's `source` field discriminates the path used.

### `detecting_family_vanish.g`

```gap
ResIsTrivialOnDetectingFamily := function(m, omega_vec)
    # 1. Build (or fetch from cache) restriction matrices via
    #    BuildRestrictionMatrices(m, source) where source is chosen
    #    based on m: "hap" for m ≤ 5, "quillen" for m = 7. (Caller
    #    can override via an optional second arg if needed.)
    # 2. Normalise omega_vec to hom-basis form via FSI_LiftIfHom
    #    convention.
    # 3. res_E_vec  := (res_E  * omega_vec) mod torsion_E
    #    res_D8_vec := (res_D8 * omega_vec) mod torsion_D8
    # 4. trivial := IsZeroVector(res_E_vec) and IsZeroVector(res_D8_vec)
    # 5. Construct callable cocycles f_E, f_D8 by lifting the
    #    coordinate vectors via E's and D_8's UCT.cocyclebasis (mirrors
    #    StandardCocycleOf from transgression_kernel.g but on the
    #    smaller groups).
    # 6. Return the rec.
end;
```

### Data flow

```
ω_vec ──┐
        │
        ├──> ResIsTrivialOnDetectingFamily(m, ω_vec)
        │      │
        │      ├──> BuildRestrictionMatrices(m, source)    (cached)
        │      │      │
        │      │      ├──> Phase 1 (m ≤ 5): HAP UCT on G, E, D_8
        │      │      │     + EquivariantChainMap pullbacks
        │      │      │
        │      │      └──> Phase 2 (m = 7): Quillen presentation
        │      │             pull-back at F_2 level + Bockstein lift
        │      │             (gated on Q-int A2/A3, issue #136)
        │      │
        │      ├──> v_E  = res_E  * ω_vec  mod torsion_E
        │      ├──> v_D8 = res_D8 * ω_vec  mod torsion_D8
        │      ├──> f_E, f_D8 from HAP StandardCocycle on E, D_8
        │      └──> trivial := (v_E = 0) ∧ (v_D8 = 0)
        │
        └──> KellerTwistIsTrivial ──> KellerSEntry dispatches to S⁰ or S^ω
```

### Caching

`BuildRestrictionMatrices(m, source)` is the only HAP-touching step at
m ≤ 5; cached per `(m, source)` in a script-level `_DETF_CACHE` record so
repeated calls across many `ω_vec`s reuse the matrix. The cache is the
"compute once, query many" engine that makes Keller-sweep workflows
tractable.

### Error handling

- **At m = 7 with Phase 2 not yet shipped:** `BuildRestrictionMatrices(7, "quillen")`
  errors with a clear message if `QuillenH3StructureAvailable(7) = false`
  (i.e. Q-int A2/A3 hasn't landed).
- **Approach A's "HAP-only at m = 7" trap is explicitly NOT supported.**
  `BuildRestrictionMatrices(7, "hap")` errors rather than silently
  invoking `ResolutionFiniteGroup(E_+(7), 4)` (which OOMs).
- **Unexpected `omega_vec` length:** error via `FSI_LiftIfHom`'s existing
  length-mismatch path.
- **Subgroup construction failure** (e.g. `MaximalElementaryAbelian_E_plus`
  finds no rank-(m+1) subgroup): error propagated from
  `quillen_detecting_subgroup.g`.

## Test ladder

### Anchored ground-truth cases

| Rung | Group       | Anchor                                                | What it proves                                                                                                |
| ---- | ----------- | ----------------------------------------------------- | ------------------------------------------------------------------------------------------------------------- |
| 1    | D_8 (m=1)   | `_QH3S_TORSION_TABLE.m1 = [2, 2, 4]`                 | D-VAN degenerates correctly: detecting family `= {D_8}` itself; sanity check.                                |
| 2    | E_+(2)      | torsion `[(Z/2)^9, Z/8]` from HAP UCT                 | Every unit basis vector reports `trivial=false`; Z/8 generator's D_8 row is non-zero. (Originally framed as "matches HAP kernel" — withdrawn 2026-06-06 audit.) |
| 3    | E_+(3)      | torsion `[(Z/2)^34, Z/4]` from HAP UCT                | Every unit basis vector reports `trivial=false`; Q_8 catches `2 * e_{order-4 gen}`. |
| 4    | E_+(5)      | torsion from `kernel.g` (only its `torsion` field is used; `in_kernel_gens` is NOT a verdict oracle) | Every unit basis vector reports `trivial=false`; half-vector for the Z/4 generator likewise. |
| 5    | E_+(7)      | (no ground truth; Phase 2 produces it)                | Phase 2 verdict on chosen ω; m = 7 unlock delivered.                                                          |

### Phase 1 acceptance gates

> **AUDIT NOTE (2026-06-06):** The original Gate 1A formulation as
> `e_i ∈ ker(Tr) ⟺ ResIsTrivialOnDetectingFamily(m, e_i).trivial` is
> a **math conflation** between `ker(Tr)` (kernel of transgression to
> centraliser 2-cocycles) and the detecting-family restriction kernel
> (which is `{0}` by AM04+Quillen). The biconditional is false in
> general — at `m=3`, `ker(Tr) = full H^3` while every unit gen is
> non-zero in `H^3` so D-VAN must return `trivial = false` on every
> one of them. See `extraspecial_orbifolds/docs/superpowers/research/
> 2026-06-06-ker-tr-detecting-family-audit.md` for the audit.
>
> The actually-shipped test (`tests/test_detecting_family_vanish.g`
> Tasks 2.4, 3.1) uses the corrected gate below (Gate 1A revised).
> Gate 1E (m=5 anchor) is similarly revised.

- **Gate 1A (revised).** For m = 2 and m = 3, every unit basis vector
  `e_i` is a non-zero class in `H^3(E_+(m); U(1))`, so the
  detecting-family restriction is non-zero on it (AM04+Quillen
  injectivity at degree 3 ≥ 2m-1). Therefore
  `ResIsTrivialOnDetectingFamily(m, e_i).trivial = false` for every
  unit basis vector. (10 + 35 = 45 cases.)
- **Gate 1B.** For m = 2, the Z/8 generator (order-8 invariant factor) is
  correctly identified as non-trivial when its restriction to D_8 is
  non-trivial — the case where elementary-abelian-only would fail.
- **Gate 1C.** `KellerSEntry(m, ω=0, i, j) = S0Entry(m, i, j)` for all
  `(i, j)` at m = 2.
- **Gate 1D.** `KellerSEntry(m, ω, i, j) = SKellerEntry(m, ω, i, j)` for
  one chosen non-trivial ω at m = 3.
- **Gate 1E (revised, self-contained).** Per-generator vanishing at m = 5
  is a 165/165 `trivial = false` sweep on the unit basis (analog of
  Gate 1A at m=3). It does NOT depend on A-5b's `kernel.g`.

### Phase 2 acceptance gates (separate PR after Q-int A2/A3)

- **Gate 2A.** Phase 2 restriction matrices agree byte-for-byte with Phase 1
  matrices at m = 2, 3, 5 (independent of `ω`).
- **Gate 2B.** D-VAN at m = 7 runs in under 60 seconds wall, including
  matrix build.
- **Gate 2C.** Phase 2 m = 7 verdict on a chosen non-trivial `ω` (e.g. unit
  basis vector under Q-int A2's torsion table) is internally consistent:
  restrictions produce non-zero vectors, dispatcher routes to SKeller.

### Test files mapped to gates

```
tests/test_detecting_family_restriction.g
  - Restriction-matrix shape sanity (m = 2, 3)
  - Gate 1A m = 2 (10 cases)
  - Gate 1A m = 3 (35 cases; fast subset + full subset under a flag)
  - Gate 1B Z/8 witness explicit

tests/test_detecting_family_vanish.g
  - Restriction-matrix -> vanishing-test composition
  - FSI_LiftIfHom dispatch on both length conventions
  - Cocycle-output f_E and f_D8 satisfy the bar 3-cocycle equation on
    a few witness triples

tests/test_keller_s_entry.g
  - Gate 1C: trivial-twist S = S⁰ for all (i, j) at m = 2
  - Gate 1D: non-trivial-twist S = SKeller for chosen ω at m = 3

tests/test_detecting_family_phase2_xcheck.g  (Phase 2)
  - Gate 2A: Phase 2 matrices = Phase 1 matrices at m = 2, 3, 5
  - Gate 2B: timing budget at m = 7
  - Gate 2C: m = 7 internal consistency
```

## Risk register

1. **AM04 §IV.4-§IV.5 injectivity could fail empirically.** Gate 1A *is* the
   empirical test. Probability we expect divergence: zero (Quillen 1971's
   essential-ideal argument is rock-solid for our range), but Gate 1A is
   the fact-check.
2. **EquivariantChainMap performance at m = 5.** Building the Phase 1
   restriction matrix could be slow (HAP resolution at m = 5 took 9 min;
   restriction map adds work). Mitigation: cache per `(m, source)` at
   module level; one-time cost amortised across all queries.
3. **Multiple D_8 sections.** `D8Section_E_plus(m)` picks `candidates[1]`.
   Different conjugates give different *coordinate vectors* but the
   `trivial` verdict is class-invariant. Mitigation: pin to whichever
   `D8Section_E_plus` returns; document; add internal smoke test that
   two different D_8-section choices give identical `trivial` verdicts on
   the m = 2 anchor set.
4. **Phase 2 chicken-and-egg.** Phase 2 needs Q-int A2/A3 (analytical H³
   structure for m = 7) to even define the restriction-matrix columns.
   Mitigation: gate cleanly; the Phase 2 PR opens only after Q-int A2/A3
   ships; the spec's existence of Phase 1 means D-VAN delivers Keller
   value through m = 5 immediately regardless.

## Issue decomposition

### Workstream tree

| Issue ID | Title                                                              | Workstream     | Type             | Depends on                          | Acceptance                              |
| -------- | ------------------------------------------------------------------ | -------------- | ---------------- | ----------------------------------- | --------------------------------------- |
| D-VAN-1  | EPIC: detecting-family vanishing test                              | D-VAN          | epic             | —                                   | All children closed                     |
| D-VAN-2  | Phase 1 — `BuildRestrictionMatrices(m, "hap")` builder             | D-VAN, Phase 1 | code, math       | quillen_detecting_subgroup.g (done) | Matrix shape correct m = 2, 3; cached  |
| D-VAN-3  | Phase 1 — `ResIsTrivialOnDetectingFamily` + FSI_LiftIfHom input     | D-VAN, Phase 1 | code             | D-VAN-2                             | Gate 1A m = 2, Gate 1B                 |
| D-VAN-4  | Phase 1 — m = 3 anchor extension                                   | D-VAN, Phase 1 | regression       | D-VAN-3                             | Gate 1A m = 3                          |
| D-VAN-5  | `KellerTwistIsTrivial` wrapper                                     | D-VAN, K-EPIC  | code             | D-VAN-3                             | Smoke tests m = 2, 3                   |
| D-VAN-6  | `KellerSEntry` dispatcher                                          | D-VAN, K-EPIC  | code             | D-VAN-5, K-2 (#39), V-2 (#34)       | Gates 1C, 1D                            |
| D-VAN-7  | m = 5 anchor                                                       | D-VAN, Phase 1 | regression       | A-5b (#47)                          | Gate 1E                                 |
| D-VAN-8  | Phase 2 — `BuildRestrictionMatrices(m, "quillen")`                  | D-VAN, Phase 2 | code, math       | Q-int A2/A3 (#136)                  | Gate 2A                                 |
| D-VAN-9  | Phase 2 — m = 7 unlock + timing budget                             | D-VAN, Phase 2 | code             | D-VAN-8                             | Gates 2B, 2C                            |

### Sequencing

```
Phase 1
  D-VAN-2 ──> D-VAN-3 ──> D-VAN-4
                 │
                 └──> D-VAN-5 ──> D-VAN-6

  D-VAN-7 (m = 5 anchor) — waits on A-5b (#47), independent of the rest

Phase 2 (gated on Q-int A2/A3, issue #136)
  Q-int A2/A3 ──> D-VAN-8 ──> D-VAN-9
```

### Estimated effort

- Phase 1: 3–4 sessions across D-VAN-2 through D-VAN-6.
- D-VAN-7: half-session once A-5b ships.
- Phase 2: 2–3 sessions after Q-int A2/A3.
- **Total: 6–8 sessions across two phases.**

## Interactions with other workstreams

- **A-5b (#47)** — independent of D-VAN's critical path; only D-VAN-7
  (the m = 5 anchor) waits on it.
- **Q-int A2/A3 (#136)** — Phase 2 gated entirely on this. Can run in
  parallel with Phase 1.
- **K-2 (#39), V-2 (#34)** — both closed; D-VAN-6 calls them directly.
- **Q-int A1 (`quillen_bockstein.g`, PR #139, just landed)** — Phase 2
  uses the Bockstein machinery here for the F_2 → H⁴(Z) lift.
- **D-INV (#140, brainstorm reminder)** — downstream; reuses D-VAN's
  restriction-matrix builders.

## References

- AM04 = A. Adem, R. Milgram, *Cohomology of Finite Groups*, 2nd ed.,
  Springer, 2004.
  - V.6.5 (general detecting-family injectivity)
  - §IV.4 Def 4.2, Thm 4.3 ("Groups with Cohomology Detected by
    Abelian Subgroups") + §IV.5 Thm 5.6 (F-isomorphism); the
    essential-ideal argument for extraspecial 2-groups is then
    Quillen 1971 Thm 5.10 (see R-1 synthesis at
    `docs/superpowers/research/2026-05-17-detecting-family-literature.md`).
- D. Quillen, *The mod 2 cohomology rings of extra-special 2-groups and
  the spinor groups*, Math. Ann. 194 (1971), 197–212. (Essential ideal
  starts in degree `2m`.)
- `extraspecial_orbifolds/scripts/quillen_detecting_subgroup.g` —
  existing infrastructure (`MaximalElementaryAbelian_E_plus`,
  `D8Section_E_plus`, `UnitCircleCohomologyDetectingFull`).
- `extraspecial_orbifolds/scripts/quillen_canonical_presentation.g` —
  Q-2a canonical Quillen presentation (issue #133, merged in PR #133).
- `extraspecial_orbifolds/scripts/quillen_bockstein.g` — Q-int A1
  Bockstein action (issue #136, PR #139).
- `extraspecial_orbifolds/scripts/fsi_wrapper.g` — `FSI_LiftIfHom`
  convention (V-4a fix, PR #135).
- `docs/superpowers/plans/2026-05-15-quillen-integration.md` — Q-int
  roadmap; D-VAN Phase 2 dovetails with Stage A2/A3.
- Issue #140 — D-INV brainstorm reminder.
