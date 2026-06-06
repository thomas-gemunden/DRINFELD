# Audit: ker(Tr) vs detecting-family kernel conflation

**Date:** 2026-06-06
**Issue:** K-4b m=7 #449 audit (pre-cleanup for production)
**Status:** complete — Sections 2 corrections applied; load-bearing Section 3 corrections applied
**Branch:** `audit-ker-tr-detecting-family-conflation`

## Background

Two structurally different kernels both sit inside `H^3(E_+(m); U(1))`:

- **`ker(Tr)`** — kernel of the transgression
  `Tr : H^3(G; U(1)) -> ⊕_g H^2(C_G(g); U(1))`.
  Computed by the A-5b workstream (`run_e_plus_m_kernel_hap.g`,
  `transgression_matrix*.g`); persisted at
  `computed/transgression/<m>/kernel.g`. At `m=5` it is a pure
  `(Z/2)^52` subgroup of the ambient `(Z/2)^164 ⊕ Z/4` — size
  `2^52`.

- **Detecting-family kernel** — kernel of the restriction
  `res : H^3(G; U(1)) -> ⊕_H H^3(H; U(1))` where
  `H ∈ {EA, D_8, Q_8}` (the AM04 + Quillen detecting family). By
  AM04 IV.4-IV.5 + Quillen 1971 essential ideal in degree 2m, this
  restriction is **injective** on `H^3` at every `m ≥ 2`, so this
  kernel is `{0}` (the zero class only).

**These are kernels of different maps.** `ker(Tr)` can be large
(non-zero `H^3` classes whose centraliser-cocycle obstructions all
vanish). The detecting-family kernel is trivial (the only class
that restricts to zero on every member of `{EA, D_8, Q_8}` is the
zero class itself).

**Empirical proof of the gap:** at `m=2`, the `Z/8` generator
`e_{exp_idx}` is NOT in `ker(Tr)` (its image under Tr is non-zero).
At `m=3`, A-3a found `ker(Tr) = full H^3`, so every basis vector
`e_i` is in `ker(Tr)` yet none is the zero class in `H^3`.
The PR-417 withdrawal (`ed5cc4a`) demonstrated the gap empirically:
running `ResIsTrivialOnDetectingFamily(5, v)` on each of the 52
basis vectors of `ker(Tr)(E_+(5))` returned **55 FAIL / 0 PASS**
(the test was wrong; the math is fine).

## Section 1 — Legitimate references (no action)

Count: **47 of 62** matches for "ker(Tr) / kerTr / transgression
kernel" in `*.g`/`*.md`/`*.sh` (excluding `.claude/worktrees/`).
These are:

- `solver/transgression_matrix_reduced.g`, `solver/snf_wrapper.g`,
  `transgression_kernel.g`, `transgression_per_generator.g`,
  `transgression_matrix.g`, `transgression_resume.g`,
  `run_e_plus_*kernel*.g`, `test_transgression_*.g` — the kernel
  computation pipeline itself; legitimately about `ker(Tr)`.
- `computed/transgression/<m>/kernel.g` headers — correctly describe
  themselves as `ker(Tr)` data.
- `tests/test_detecting_family_vanish.g` Tasks 2.4/3.1 — explicit
  warning AGAINST the conflation; explains why the comparison is wrong.
- `tests/test_keller_s_entry.g` — explicit reframing comment about
  `ker(Tr) = full H^3` at `m=3` not implying triviality.

## Section 2 — Confirmed conflations (corrections applied)

### 2.1 `extraspecial_orbifolds/scripts/d_van_7_xcheck_k4a.g`

Entire harness is predicated on:
> "D-VAN-7 verdict = 'agree' iff every D-VAN trivial bit matches
> A-5b's `in_kernel_gens`"

This compares `r.trivial` (D-VAN: does `ω` restrict to zero on
`{EA, D_8, Q_8}`? — `true ⟺ ω = 0` in `H^3`) against
`(i in in_kernel_gens)` (A-5b: is `e_i ∈ ker(Tr)`?). The two flags
need not agree — at `m=3`, `in_kernel_gens = [1..35]` (every basis
vector is in `ker(Tr)`) while D-VAN reports `trivial = false` on
every basis vector (each is a non-zero class in `H^3`).

**Action:** flagged as broken cross-validation. The whole file is a
dead end and should not be run as written. A correct cross-validation
between D-VAN-7 and K-4b's m=5 verdict is what `k4b_xcheck_d_van.g`
already implements (trivial-trivial axis only; no ker(Tr) involvement).
Patched the comment block to mark the harness as **WITHDRAWN — math
conflation**; pointed readers to the corrected framing.

### 2.2 `extraspecial_orbifolds/scripts/run_d_van_7_m5.sh`

Same conflation: the driver sweeps 165 unit generators and writes
`hap_in_kernel`, `agree_per_gen`, `mismatches` records into
`computed/d_van_7/m5_result.g`, all under the assumption that
`r.trivial` should agree with `(i in in_kernel_gens)`.

**Action:** patched the script's header / docstring to mark it as
**WITHDRAWN — math conflation**. The script itself is left runnable
(it doesn't crash, just produces meaningless agreement statistics)
but the header now clearly states the output is not a meaningful
cross-validation.

### 2.3 `docs/superpowers/research/TEMPLATE-d_van_7_m5_verdict.md`

Template was set up to record the conflated comparison. Repeats the
false equivalence in §4.1, §4.2 ("A-5b's `in_kernel_gens` is expected
to be `[1..165]` (full H³ in ker(Tr), as at m = 3) ... D-VAN at every
unit generator would then report `trivial = true`").

**Action:** patched the template to document the conflation and mark
the file as a historical record of a withdrawn approach. The accurate
D-VAN sweep (each unit generator is a non-zero class in `H^3` so
D-VAN must report `trivial = false`) is what
`test_detecting_family_vanish.g` Task 3.1 already does at `m=3`; the
m=5 analog is the obvious extension once a D-VAN m=5 anchor is run.

### 2.4 `docs/superpowers/specs/2026-05-15-detecting-family-vanishing-test-design.md`

Gate 1A as literally written (line 233):

> `e_i ∈ ker(Tr) ⟺ ResIsTrivialOnDetectingFamily(m, e_i).trivial`

This biconditional is **mathematically wrong**. The correct gate at
`m ∈ {2, 3, 5}` is: every unit basis vector `e_i` is a non-zero class
in `H^3(E_+(m); U(1))`, so `ResIsTrivialOnDetectingFamily(m, e_i)`
must return `trivial = false`. This is what
`tests/test_detecting_family_vanish.g` Tasks 2.4 and 3.1 actually do
(see lines 60-90 of that file for the correct framing).

**Action:** patched the spec doc's Gate 1A definition to the
corrected form (`e_i ≠ 0` in `H^3` ⟹ `trivial = false`) and added a
warning paragraph about the conflation.

### 2.5 `docs/superpowers/plans/2026-05-15-detecting-family-vanishing-phase1.md`

The Phase-1 plan's Tasks 2.4, 3.1, 6.2 specify code that does:

```gap
in_hap_ker := i in in_kernel_gens_m3;
r := ResIsTrivialOnDetectingFamily(3, e_i);
if r.trivial <> in_hap_ker then
    Add(mismatches, ...);
fi;
```

This is the bad pattern. The actual test file
(`tests/test_detecting_family_vanish.g`) was corrected in PR #150/#156
to remove this pattern (see Task 3.1 comments lines 234-242, which
explicitly explain why the original plan was wrong).

**Action:** annotated the plan doc's tasks 2.4, 3.1, 6.2 with a
"WITHDRAWN — see test file Task 3.1 corrected framing" notice. The
plan is historical; we do not edit the task bodies because they're
in code-block form and rerunning them as written would fail.

### 2.6 `writeup/methodology.md` lines 117, 249, 557

The methodology paper states (line 557, abridged):

> "(i) D-VAN m = 5 Gate 1E, which sweeps the 165 basis vectors and
> confirms triviality on each; the kernel ground truth pins which
> basis vectors should be reported `trivial` by
> `ResIsTrivialOnDetectingFamily(5, e_i)` (the 52 kernel generators
> plus their integer span...)"

This conflates `ker(Tr)` with "what D-VAN reports `trivial`". D-VAN
reports `trivial = true` iff `[ω] = 0` in `H^3`, not iff
`ω ∈ ker(Tr)`. Of the 52 kernel generators, ALL are non-zero classes
in `H^3` (since `H^3` injects into the detecting family). D-VAN
should report `trivial = false` on every one of them. Similarly for
lines 117, 249, 254.

**Action:** patched the three locations. The corrected text states:
"the kernel-of-Tr computation gives an independent fact about the
class group structure; the D-VAN sweep at `m=5` tests injectivity of
restriction to `{EA, D_8, Q_8}` on each basis vector independently
(expected outcome: `trivial = false` on every non-zero basis vector,
by AM04 + Quillen injectivity)."

### 2.7 `writeup/section_4_applications.md` lines 386-398, 429, 433

Section 4.3.4 lists "verdict-vs-kernel agreement" as the success
criterion for D-VAN-7 at m=5. This is the same conflation.

**Action:** patched 4.3.4 to clarify that D-VAN-7's success is the
35/35 (or 165/165) `trivial = false` on basis vectors, NOT
agreement with `kernel.g`.

### 2.8 `writeup/section_5_conclusions.md` lines 248-255

"The kernel-of-Tr ground truth at m = 5 is what D-VAN cross-checks
against on the basis sweep."

**Action:** patched to: "D-VAN m=5 anchor exercises injectivity of
restriction at scale; it does not cross-check against
`ker(Tr)`."

### 2.9 `writeup/section_6_results_tables.md` line 87 footnote (line 109-110)

Table caption says A-5b output is "ground truth for D-VAN-7 #148."

**Action:** patched the footnote to read "feeds D-VAN-7 #148 only as
shared input dimension data (torsion vector); D-VAN-7 does NOT use
`in_kernel_gens` as a verdict cross-check."

### 2.10 `writeup/note_k4_mult0_normalization_rationale.md` lines 302-308

This file makes the *correct* one-direction statement:
> "K-4a verdict triviality on detecting family ⟹ ω = 0 in H^3 ⟹
>  ω ∈ ker(Tr) for the corresponding cocycle class."

That direction is true: `0 ∈ ker(Tr)`. But the conclusion
"the two pipelines should agree if both are correct" overstates the
relationship — they ALWAYS agree at the trivial axis (both
correctly identify `0 ↦ trivial`), but anywhere else they're
testing different properties. Not strictly a math error but the
phrasing oversells the cross-validation.

**Action:** patched to clarify the direction-of-implication.

### 2.11 `writeup/appendix_reproducibility.md` line 420

"D-VAN m = 5 anchor (Gate 1E) is separately gated on the A-5b
kernel-of-Tr ground truth at m = 5."

Gate 1E does NOT need A-5b output to function (it tests injectivity
of restriction; that's a self-contained check). The dependency listed
here is the misframed one.

**Action:** patched to "Gate 1E (D-VAN m=5 self-contained anchor)"
with no A-5b dependency claim.

### 2.12 `/Users/thomasgemunden/Projects/group_cohomology/CLAUDE.md` line 83

The active-workstream table says:
> "D-VAN m=5 anchor (#148) | Cross-validate detecting family vs A-5b
> m=5 `kernel.g` | `tests/test_dvan_m5_anchor_vs_kernel.g`"

The test file was withdrawn (`ed5cc4a`) for being a math conflation.
The workstream description repeats the misframing.

**Action:** patched the CLAUDE.md row to mark the workstream as
**closed/withdrawn** (math conflation; D-VAN m=5 is now a
self-contained injectivity sweep on 165 basis vectors).

## Section 3 — Ambiguous language (corrections only where load-bearing)

These items use "kernel" or "agree with HAP" in ways that could be
read either way but don't actively assert the false equivalence.
Listed here as follow-up; only fixed if the ambiguity is being
acted on now.

### 3.1 Variable name `hap_in_kernel` / `agree_per_gen` in `run_d_van_7_m5.sh`

The variable encodes `(i in ker_data.in_kernel_gens)` and is
written to `m5_result.g`. The name is fine on its face (membership
in HAP-computed `ker(Tr)`), but the *use* of comparing it against
`r.trivial` is wrong (Section 2.2).

**Action:** patched in 2.2 (whole driver flagged).

### 3.2 "Anchor" terminology in `writeup/methodology.md`

"Empirical anchor" is used both for:
- the test `r.trivial = false` on each unit generator (correct), and
- "matches HAP per-generator vanishing on 10 generators" (conflated).

**Action:** patched in 2.6.

### 3.3 `Gate 1A` definition shape (spec doc line 233)

Patched in 2.4.

### 3.4 README front-matter

`DRINFELD/README.md` does not mention either kernel — no action.
The umbrella `/Users/thomasgemunden/Projects/group_cohomology/CLAUDE.md`
is the one to patch (2.12).

## Section 4 — Cross-validation claims: math soundness check

The audit re-examined every test that compares D-VAN against any
`computed/transgression/<m>/kernel.g` data:

### 4.1 `tests/test_detecting_family_vanish.g` Task 2.4 (m=2)

**Verdict: mathematically sound.** Despite loading `ker_vecs`, the
gate is `IsEmpty(trivial_unit_gens_m2)` — "no unit generator is
trivial". The loaded `ker_vecs` is only used in Task 2.5 to confirm
the `Z/8` generator is NOT in `ker(Tr)` (and *then* assert D-VAN
flags it as non-trivial, which is consistent with the Z/8 generator
being non-zero in `H^3`). No false equivalence is asserted.

### 4.2 `tests/test_detecting_family_vanish.g` Task 3.1 (m=3)

**Verdict: mathematically sound.** The gate is again
`IsEmpty(trivial_unit_gens_m3)` — D-VAN reports `trivial = false`
on every unit generator. `in_kernel_gens` is not used as a verdict
oracle; only as context data for `exp_index`/`torsion`.

### 4.3 `tests/test_keller_s_entry.g` Gate 1D

**Verdict: mathematically sound.** The comment explicitly notes:
"At `m=3`, `ker(Tr) = full H^3`, so `in_kernel_gens = [1..35]` and
every `e_i` is BOTH in `ker(Tr)` AND a non-zero cohomology class.
D-VAN tests the latter."

### 4.4 The withdrawn `test_dvan_m5_anchor_vs_kernel.g`

Removed in commit `ed5cc4a` after returning 55 FAIL / 0 PASS. Not
re-introduced.

### 4.5 `d_van_7_xcheck_k4a.g` + `run_d_van_7_m5.sh`

**Verdict: mathematically unsound (Section 2.1, 2.2).** Patched.

## What is genuinely shared utility between the two pipelines

- `BuildRestrictionMatrices(m, source)` in `detecting_family_restriction.g`
  — D-VAN's primary builder; loads HAP resolutions for the same `G`
  that `transgression_kernel.g` uses, but the restriction matrices
  themselves are NOT used by the kernel-of-Tr computation.
- `SetupCohomology3` and `StandardCocycleOf` in `transgression_kernel.g`
  — shared utility code (`transgression_kernel.g` is poorly named:
  the FILE has both the kernel computation AND general H³ utilities).
  Use by `detecting_family_restriction.g` is fine.

## Follow-ups

- **Issue (followup)**: rename `transgression_kernel.g`'s utility
  exports to a separate file (e.g. `h3_utilities.g`) so callers
  don't have to import the kernel-computation module to use
  `SetupCohomology3`. Not done in this audit (would touch >20
  imports).
- **D-VAN m=5 self-contained anchor**: re-design (issue #148 needs
  rewording). The 165/165 `trivial = false` sweep is the right
  test; it doesn't need `kernel.g`.
- **K-4b m=7 #449 production**: this audit was a precondition.
  Cleared.
