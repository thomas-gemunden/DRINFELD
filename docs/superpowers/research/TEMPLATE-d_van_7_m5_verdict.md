# D-VAN-7 m = 5 verdict — D-VAN matches A-5b empirical kernel

**TEMPLATE STATUS:** Fill in the bracketed `[...]` fields after the
D-VAN-7 m = 5 production run completes (`run_d_van_7_m5.sh`). Once
filled, rename this file from `TEMPLATE-d_van_7_m5_verdict.md` to
`YYYY-MM-DD-d_van_7_m5_verdict.md` (matching the
`docs/superpowers/research/` date convention) and commit.

**Date:** [YYYY-MM-DD — fill in run date]
**Issue:** #148 (D-VAN-7)
**Status:** [draft | final]
**Parent EPIC:** #142 (D-VAN-1)
**Sibling phases:** D-VAN-3..6 (Phase 1 m ∈ {2, 3}; #144 .. #147),
                    D-VAN-8/9 (Phase 2 m = 7, Quillen; gated on #136),
                    K-4b (sibling K-4a-m=5 production scaffold, #189 / PR #227)
**Spec:** [`docs/superpowers/specs/2026-05-15-detecting-family-vanishing-test-design.md`](../specs/2026-05-15-detecting-family-vanishing-test-design.md)
**Reproduce:** `./extraspecial_orbifolds/scripts/run_d_van_7_m5.sh`

## Section 1: Verdict

**Verdict:** [agree | disagree]

D-VAN-7 sweeps every one of the 165 hom-basis unit generators of
H³(E_+(5); U(1)), computes `ResIsTrivialOnDetectingFamily(5, e_i)` for
each, and compares the result against A-5b's HAP-derived
`computed/transgression/5/kernel.g`. The verdict aggregates:

| Check | Result key | Value | Trivial reference |
|---|---|---|---|
| Per-generator sweep (165 unit gens) | `agree_per_gen` | `[true / false]` per i ∈ [1..165] | all `true` |
| Half-vector test (2 · e_{exp_index}) | `half_vec.agree` | `[true / false]` | `true` |
| Aggregate | `verdict` | `[agree / disagree]` | `agree` |

**Conjunction:** D-VAN's verdict for each unit generator e_i matches
A-5b's HAP-derived `(i in in_kernel_gens)` exactly when the algebraic
restriction is faithful — i.e. when the AM04+Quillen+Harada–Kono
injectivity (R-1) holds in practice on E_+(5)'s ker(Tr) structure.

| Field | Value |
|---|---|
| `RESULT.verdict` | `"[agree / disagree]"` |
| `#mismatches` | `[N]` (of 165) |
| `half_vec.dvan` | `[true / false]` |
| `half_vec.hap` | `[true / false]` |
| `half_vec.agree` | `[true / false]` |

[Wall-clock time: `[NNN.N s]`, primarily HAP resolution build for
E_+(5) (~10 min cold, per A-5a / #138) plus 165 cheap restriction-
matrix multiplications and half-vector test.]

## Section 2: Per-generator detail

[Describe per-generator results.

### Section 2.1: Expected outcome under Keller's conjecture

A-5b's m = 5 kernel structure (read off from `kernel.g`):
- `torsion = [insert torsion vector from kernel.g]` (length 165)
- `in_kernel_gens = [insert from kernel.g]`
- `exp_index = [insert]`
- `half_vec_in_kernel = [insert]`

Under Keller's α = 0 conjecture at m = 5, A-5b's `in_kernel_gens` is
expected to be `[1..165]` (full H³ in ker(Tr), as at m = 3) and
`half_vec_in_kernel = true`. D-VAN at every unit generator would then
report `trivial = true` (each e_i is a non-zero class in H³ but its
restriction to the detecting family vanishes — same pattern as m = 3,
see Task 3.1 of test_detecting_family_vanish.g for the corrected
framing).

### Section 2.2: Actual outcome

[Report what was actually found:

- All 165 generators in ker / a subset?
- D-VAN agrees on all / disagrees on which indices?
- For disagreements: which `(i, dvan, hap)` triples?
- Half-vector outcome.

If D-VAN disagrees with A-5b: the mismatch is the empirical witness.
List the witness centraliser(s) reported by A-5b vs the restriction
witness from D-VAN — D-VAN's `r.res_EA_vec_list`, `r.res_D8_vec`,
`r.res_Q8_vec` localise where the non-vanishing happens.]

### Section 2.3: Half-vector (2 · e_{exp_index})

[Report whether D-VAN and A-5b agree on the order-4 / order-exp
half-vector. The half-vector is the most delicate generator to detect
because at m ≥ 3 only the Q_8 detecting summand catches 2 · A(4)_gen
(D_8 alone misses it; cf. R-1 d8-vs-q8-detection.md, #153). A
mismatch here would indicate either:

- a Q_8-section selection issue in BuildRestrictionMatrices(5), or
- an A-5b half-vec test issue.

Both are documented as known-risk regions in the design.]

## Section 3: Cross-validation against K-4b

Cross-check via `d_van_7_xcheck_k4a.g` (consumes both
`computed/d_van_7/m5_result.g` and
`extraspecial_orbifolds/scripts/k4b_m5_result.g`):

```
[paste single-line summary: CONSISTENT | INCONSISTENT |
 INCONCLUSIVE | BLOCKED-D-VAN-7 | BLOCKED-K-4B]
```

### Section 3.1: Joint trivial-axis check

[If CONSISTENT (both pipelines report trivial):

This is the strongest available cross-validation at m = 5 pre-Phase-2.
K-4b's KRR-based classifier confirms α_KRR is detected-trivial; D-VAN's
algebraic-restriction pipeline confirms agreement with A-5b's HAP-
derived kernel-of-Tr structure on every unit generator.

The two pipelines share no implementation code (D-VAN routes through
HAP chain maps on E_+(m); K-4b routes through the KRR projector and
modular_data storage). Their joint trivial verdict is observationally
independent.]

### Section 3.2: Disagreement triage

[If INCONSISTENT:

The decision matrix in `d_van_7_xcheck_k4a.g` enumerates the four
disagreement cases. Identify which fired:

- K-4b trivial, D-VAN-7 disagree → either detecting-family injectivity
  gap (R-1, #193) at m = 5 specifically, or D-VAN implementation bug.
- K-4b non-trivial, D-VAN-7 agree → either K-4b classifier misroute
  (T5b σ-vs-conj(σ) ambiguity, T4b ε extraction) or A-5b empirical
  kernel incomplete (mixed-combination Stage-2 verification deferred).
- K-4b non-trivial, D-VAN-7 disagree → potentially CONSISTENT
  non-trivial if D-VAN's mismatches localise on the same α_KRR
  coordinates K-4b detects. Requires strategy-(A) inversion stub in
  `k4b_xcheck_d_van.g` to confirm.

File a diagnostic issue. Block W-1's m = 5 publication.]

## Section 4: Confidence assessment

### Section 4.1: Anchor agreement at m = 2, m = 3

D-VAN's m = 2 and m = 3 anchors (Tasks 2.4 and 3.1 in
`test_detecting_family_vanish.g`) are [GREEN | RED] as of [date]. The
m = 3 case in particular establishes the framework's correctness when
ker(Tr) = full H³ (Keller's "every class is in ker(Tr) yet only the
zero class is trivial in H^3" subtlety).

### Section 4.2: A-5b's kernel-completeness caveat

A-5b's `kernel.g` records the kernel as a STRUCTURAL basis (`basis_summary`
plus 165 in/out boolean flags + half-vec test) under the assumption that
no further non-obvious mixed combinations exist. Stage-2 enumeration is
deferred (per `scripts/tests/test_run_e_plus_5_kernel.g` notes). If
D-VAN reports `trivial = true` on a class that A-5b's `in_kernel_gens`
flags as out-of-kernel, the witness is a kernel-completeness gap on
A-5b's side — file as A-5b follow-up, not a D-VAN bug.

### Section 4.3: Detecting-family injectivity at m = 5

R-1 (`docs/superpowers/research/2026-05-17-detecting-family-literature.md`)
establishes injectivity of res: H³(E_+(m); U(1)) → H³(E; U(1)) ⊕
H³(D_8; U(1)) ⊕ H³(Q_8; U(1)) at all m ≥ 2 via AM04 §IV.4-§IV.5 +
Quillen 1971 + Harada–Kono 1987. The proof goes through degree-by-
degree in the F_2-cohomology spectral sequence; m = 5 is in scope.

[If D-VAN at m = 5 confirms A-5b's kernel structure to the last
generator, this constitutes the strongest computational verification of
the detecting family's m = 5 injectivity available pre-Phase-2.]

### Section 4.4: Caveats from D-VAN's known limitations

- D-VAN's input convention is hom-basis coords (length k_G = 165 at
  m = 5), not raw K^3-cocycle coords. Cocycle-form input is
  deferred — see `NormaliseOmegaToHomBasis` in
  `detecting_family_vanish.g`. The driver passes hom-basis vectors
  exclusively, so this is N/A for D-VAN-7 itself, but downstream
  callers that go through cocycle form must convert.

- D-VAN's D_8 section is one specific conjugacy class rep; Task 2.7
  in `test_detecting_family_vanish.g` confirms invariance under
  D_8-section choice at m = 2. The same invariance should hold at
  m = 5 by the same argument; not re-verified here.

## Section 5: Implications for Keller's conjecture at m = 5

### Section 5.1: The agree case (`verdict = "agree"`)

[If `verdict = "agree"`:

D-VAN's algebraic-restriction pipeline reproduces A-5b's empirical
ker(Tr) structure across every unit generator of H³(E_+(5); U(1))
plus the half-vector test. Combined with K-4b's CONSISTENT verdict
(if applicable), this answers Keller's open question
**affirmatively at m = 5**:

The orbifold VOA module category arising from the Barnes-Wall lattice
at m = 5 is the untwisted doubled-extraspecial fusion category, and
the orbifold of the BW(5) lattice VOA by E_+(5) gives a module
category equivalent to Rep(Z(Vec_{E_+(5)})).

This closes D-VAN Phase 1 (Gates 1A m ∈ {2, 3}, plus the m = 5
empirical anchor — Gate 1E) and provides moderate evidence for the
m = 7 case (D-VAN-8/9, Phase 2 Quillen, gated on Q-int A2/A3 #136).]

### Section 5.2: The disagree case (`verdict = "disagree"`)

[If `verdict = "disagree"`:

The mismatch is the empirical witness. Triage:

- Localise via D-VAN's per-generator `r.res_EA_vec_list`,
  `r.res_D8_vec`, `r.res_Q8_vec`: which detecting subgroup catches
  the disagreement? Which centraliser does A-5b's witness point at?
- Check whether the mismatch correlates with A-5b's
  `half_vec_in_kernel` axis (Q_8-detection of the cyclic A(4)
  summand) — that's the m ≥ 3 detection gap that #153 closed for
  D-VAN; an analogous gap on A-5b's empirical side would surface
  here.
- File diagnostic issue. Block W-1's m = 5 publication on the
  triage outcome.]

### Section 5.3: Reporting decision

[Decision: report m = 5 D-VAN-7 result in the methodology paper (W-1)?

Options:
- Report standalone if the verdict is "agree" and K-4b cross-check
  is CONSISTENT.
- Hold pending K-4b if K-4b's `run_k4b_m5.sh` hasn't shipped yet
  (gated on #200 + #220).
- Hold pending injectivity confirmation (R-1 m = 5 specifically) if
  the verdict is "disagree" — D-VAN's injectivity claim is what we
  rely on for the agree-implies-trivial direction.

Decision: [report | hold]. Reason: [...].]

## Section 6: Reproducibility

- **Driver:** `extraspecial_orbifolds/scripts/run_d_van_7_m5.sh`
- **Cross-check:** `extraspecial_orbifolds/scripts/d_van_7_xcheck_k4a.g`
- **Log file:** `extraspecial_orbifolds/perf/raw/d_van_7/d_van_7_m5_[TIMESTAMP].log`
- **Result file:** `computed/d_van_7/m5_result.g`
  (returns a `rec` when read via `ReadAsFunction(...)()`)
- **Upstream input:** `computed/transgression/5/kernel.g` (A-5b, #47)
- **Sibling input:** `extraspecial_orbifolds/scripts/k4b_m5_result.g` (K-4b, #189)
- **GAP version:** `[X.Y.Z]` (record `Print(GAPInfo.Version);`)
- **HAP version:** `[X.Y.Z]` (record `Print(InstalledPackageVersion("hap"));`)
- **Commit:** `[git rev-parse HEAD]`
- **Run start:** `[YYYY-MM-DDTHH:MM:SSZ]` (UTC, from the log)
- **Run end:** `[YYYY-MM-DDTHH:MM:SSZ]`

## Section 7: Follow-ups

[Enumerate any follow-up issues this run surfaces:

- D-VAN-8/9 m = 7 production (file once D-VAN-7 ships and Q-int A2/A3
  #136 lands).
- A-5b kernel-completeness Stage-2 verification (mixed-combination
  enumeration) if D-VAN's verdict reveals a kernel basis gap.
- K-4b strategy-(A) `_DVAN_InvertRestriction` implementation if the
  cross-check needed it (non-trivial verdict).
- Detecting-family m = 5 injectivity follow-up (R-1, #193) if any
  non-trivial behaviour surfaces.
- Any unexpected D_8-section or Q_8-section variability — file as a
  D-VAN hygiene bug.]
