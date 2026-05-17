# K-4b m = 5 verdict — Keller's question at the Barnes–Wall orbifold

**TEMPLATE STATUS:** Fill in the bracketed `[...]` fields after the
K-4b m = 5 production run completes (`run_k4b_m5.sh`). Once filled,
rename this file from `TEMPLATE-k4b-m5-verdict.md` to
`YYYY-MM-DD-k4b-m5-verdict.md` (matching the `docs/superpowers/research/`
date convention) and commit.

**Date:** [YYYY-MM-DD — fill in run date]
**Issue:** K-4b (the production-run sibling of #200 / K-4a)
**Status:** [draft | final]
**Parent EPIC:** #187 (K-4)
**Sibling phases:** K-4a (m = 3 anchor + pipeline, #200, #201),
                    K-4c (m = 7 production — to be filed)
**Spec:** [`docs/superpowers/specs/2026-05-17-k4b-m5-production-spec.md`](../specs/2026-05-17-k4b-m5-production-spec.md)
**Reproduce:** `./extraspecial_orbifolds/scripts/run_k4b_m5.sh`

## Section 1: Verdict

**Verdict:** [trivial | non-trivial | incomplete]

The K-4a Phase 2 pipeline run on E_+(5) returns the following
detecting-family classification of α = α_KRR (the 3-cocycle obtained
from the Barnes–Wall lattice's KRR projector at m = 5):

| Subgroup branch | Result key | Value | Trivial reference |
|---|---|---|---|
| E (max elementary abelian, rank 6) | `E_class.is_coboundary` | `[true / false]` | `true` |
| D_8 (pinned section) | `D8_class.class_idx` | `[1..22]` | `1` |
| Q_8 (pinned section) | `Q8_class.class_idx` | `[1..8]` | `1` |

**Conjunction:** `RESULT.trivial = [true | false | fail]`,
`RESULT.verdict = "[trivial | non-trivial | incomplete]"`.

Wall-clock time: `[NNN.N s]` (per `RESULT.timing.wall_seconds`).

## Section 2: Per-subgroup classes (detail)

### Section 2.1: E branch (max elementary abelian)

[Describe E_class result.

- `is_abelian = true` (by construction).
- `is_coboundary = [true | false]`.
- If `is_coboundary = false`: identify the non-trivial coordinate
  via the `match` record — which Aut(E) orbit of H^3(E; U(1))?
  Note that H^3((Z/2)^6; U(1)) ≅ (Z/2)^20 ⊕ (Z/2)^15 ⊕ (Z/2)^6 ⊕ Z/2
  (cup-products of degree 1, 1+2, 1+1+1, 2+1 generators in
  H^*((Z/2)^6; F_2); cross-check against A-3a output).
- Match diagnostic: `match.ok = [true | false]`,
  `match.matchings_count = [N]`. Aut(E)-orbit at `pi = [...]`.]

### Section 2.2: D_8 branch

[Describe D8_class result.

- `class_idx = [k]` ∈ `[1..22]`. Trivial: k = 1.
- The k-th storage class of `modular_data/8/3/k.txt` corresponds to
  the H^3(D_8; U(1)) orbit `[orbit-vector]` (look up via
  `modular_data/8/3/3-cocycles.txt`, line k).
- All matches: `D8_class.all_matches = [...]` (length should be 1
  for an unambiguous classification; >1 indicates a degenerate
  modular-data class in 8/3 storage — investigate).]

### Section 2.3: Q_8 branch

[Describe Q8_class result.

- `class_idx = [k]` ∈ `[1..8]`. Trivial: k = 1.
- The k-th storage class of `modular_data/8/4/k.txt` corresponds to
  the H^3(Q_8; U(1)) orbit `[orbit-vector]` (look up via
  `modular_data/8/4/3-cocycles.txt`).
- All matches: `Q8_class.all_matches = [...]`.
- Q_8's role: catches the cyclic A(4) summand of H^3(E_+(m); U(1))
  that D_8 alone cannot detect at m ≥ 3 (see
  `docs/superpowers/research/2026-05-17-d8-vs-q8-detection.md`).]

## Section 3: Cross-validation against D-VAN

Cross-check via `k4b_xcheck_d_van.g`:

```
[paste single-line summary: CONSISTENT | MULTIPLE | INCONSISTENT
 | TRIVIAL-AXIS OK | TRIVIAL-AXIS INCONCLUSIVE | TRIVIAL-AXIS DISAGREE]
```

**Strategy used:** [A (full restriction-inversion) |
                    B (trivial-axis fallback)]

[If B: note that the fallback only validates the trivial-axis case.
 For non-trivial verdicts, strategy A's `_DVAN_InvertRestriction`
 implementation is required to provide a real cross-check — see the
 helper docstring in `k4b_xcheck_d_van.g` for what's needed, and
 file a follow-up issue if non-trivial.]

[If A: report which candidate orbit(s) were found and whether the
 cardinality matched (1 for consistent, 0 for inconsistent, >1 for
 injectivity gap).]

## Section 4: Confidence assessment

### Section 4.1: Anchor agreement at m = 3

K-4a-T7 (the m = 3 anchor regression test in
`tests/test_k4a_classify.g`) is `[GREEN | RED]` as of `[date]`. The
m = 3 case reproduces Keller's verified-trivial baseline through the
full K4aClassify pipeline. This gives upstream confidence in K-4b's
classification logic at m = 5.

### Section 4.2: Cross-validation outcome

[Restate Section 3 in confidence terms.

- TRIVIAL-AXIS OK: ✅ low-risk consistent trivial verdict.
- TRIVIAL-AXIS INCONCLUSIVE: ⚠ K-4b says non-trivial; cross-check
  cannot confirm without strategy (A); confidence depends on the
  internal coherence of the K-4b branches alone.
- CONSISTENT (A): ✅ definitive — single ω orbit identified.
- MULTIPLE (A): ⚠ injectivity gap — see R-1 follow-up.
- INCONSISTENT (A): ✗ blocks publication — file diagnostic issue.]

### Section 4.3: Caveats from the K-4a risk register

[Review the K-4a Phase 2 spec's risk register
(`docs/superpowers/specs/2026-05-17-k4a-phase2-implementation-spec.md`)
and note which risks are still open or relevant to this run.

Specifically, address:

- σ-vs-conj(σ) ambiguity in K-4a-T5b: cross-mitigated by m = 3
  anchor passing.
- Detecting-family injectivity gap (R-1, #193): is the {E, D_8, Q_8}
  family established as injective at m = 5 specifically, or only at
  m = 3? Cite the R-1 verdict
  (`docs/superpowers/research/2026-05-17-d8-vs-q8-detection.md`).
- BW lattice convention: any KRR sign / basis choice that could
  affect the m = 5 cocycle's class identifier?]

### Section 4.4: Spectral-source caveat

K4aClassify(m) by default uses the "untwisted baseline" spectral
source (`RESULT.spectral_data.source = "untwisted_baseline"`) rather
than `BuildKRRSpectralCharactersSparse(m)`. At m = 3 with Keller's
verified α = 0, the two are observationally identical. At m = 5,
if α turns out non-trivial, the untwisted baseline may not be the
right input; cross-check by re-running with the sparse spectral
source explicitly (modify `K4aClassify` to thread
`use_spectral := true` if/when that path is wired up).

## Section 5: Implications for Keller's conjecture at m = 5

### Section 5.1: The trivial case (`verdict = "trivial"`)

[If `verdict = "trivial"`: this answers Keller's open question
**affirmatively at m = 5** — the orbifold VOA module category
`Vec_{E_+(5)}^α` arising from the Barnes–Wall lattice is the
**untwisted** doubled-extraspecial fusion category, and the
orbifold of the BW(5) lattice VOA by E_+(5) gives a module category
equivalent to `Rep(Z(Vec_{E_+(5)}))`.

This generalises the m = 3 anchor result to m = 5 and provides
moderate evidence for the m = 7 case (K-4c) and the conjecture in
full generality.]

### Section 5.2: The non-trivial case (`verdict = "non-trivial"`)

[If `verdict = "non-trivial"`: this answers Keller's open question
**negatively at m = 5** and identifies the specific cohomology class.

The non-trivial branch is one of:
- E non-trivial: the elementary-abelian restriction of α is
  non-trivial → α has a non-vanishing component in the (Z/2)^k
  detecting summand at low ranks.
- D_8 non-trivial: the dihedral restriction is non-trivial → α has
  a non-vanishing A(2) component.
- Q_8 non-trivial: the quaternionic restriction is non-trivial → α
  has a non-vanishing A(4) component.

Report which branch fires and what storage class it lands in. This
identifies α up to the {E, D_8, Q_8}-detection equivalence; if R-1
shows injectivity at m = 5, this identifies α uniquely up to Aut.]

### Section 5.3: Reporting decision

[Decision: report m = 5 result in the methodology paper (W-1)?

Options:
- Report standalone if the verdict is strong (trivial) and the
  cross-check is at strategy-(A) confidence.
- Hold until m = 7 (K-4c) also lands if the m = 5 verdict is
  non-trivial — combined with m = 7 it tells a more complete story.
- Hold pending injectivity confirmation (R-1) at m = 5 specifically
  if the m = 5 verdict is non-trivial AND strategy (A) is
  unavailable.

Decision: [report | hold]. Reason: [...].]

## Section 6: Reproducibility

- **Driver:** `extraspecial_orbifolds/scripts/run_k4b_m5.sh`
- **Cross-check:** `extraspecial_orbifolds/scripts/k4b_xcheck_d_van.g`
- **Log file:** `extraspecial_orbifolds/perf/raw/k4b/k4b_m5_[TIMESTAMP].log`
- **Result file:** `extraspecial_orbifolds/scripts/k4b_m5_result.g`
  (binds `RESULT` on `Read`)
- **GAP version:** `[X.Y.Z]` (record `Print(GAPInfo.Version);`)
- **HAP version:** `[X.Y.Z]` (record `Print(InstalledPackageVersion("hap"));`)
- **Commit:** `[git rev-parse HEAD]`
- **Run start:** `[YYYY-MM-DDTHH:MM:SSZ]` (UTC, from the log)
- **Run end:** `[YYYY-MM-DDTHH:MM:SSZ]`

## Section 7: Follow-ups

[Enumerate any follow-up issues this run surfaces:

- K-4c m = 7 production (file once K-4b ships, regardless of verdict).
- `_DVAN_InvertRestriction` implementation if not done by now —
  required for non-trivial verdicts.
- Any unexpected modular-data class index (e.g. a D_8 result with
  `all_matches = [j, k]` for j ≠ k indicating duplicate stored
  classes — file as a modular_data hygiene bug).
- Any K-4a risk-register risk that this run elevated to a confirmed
  problem (file as its own issue).]
