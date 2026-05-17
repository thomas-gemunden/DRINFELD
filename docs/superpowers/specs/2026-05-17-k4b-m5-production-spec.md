# K-4b: m = 5 production run of the K-4a pipeline

**Date:** 2026-05-17
**Workstream prefix:** K-4b
**Status:** Design (this doc); awaits K-4a Phase 2 completion.
**Parent EPIC:** #187 (K-4)
**Sibling phases:** K-4a (m = 3 anchor + pipeline), K-4c (m = 7 production)
**Depends on:** K-4a Phase 2 (#194, #197, #198, #199, #200, #201) all merged and #201 (m = 3 anchor) green.

## Goal

Produce a definitive verdict on Keller's question for the Barnes–Wall lattice orbifold at m = 5: does the resulting 3-cocycle `[α] ∈ H³(E_+(5); U(1))` vanish?

The verdict from this workstream is one of:

- **trivial** — `K4aClassify(5).verdict = "trivial"`, all three detecting-subgroup checks return the trivial class. Combined with D-VAN-7 (#... once filed) agreement, this answers Keller's open question affirmatively at m = 5.
- **non-trivial** — at least one detecting-subgroup check returns a non-trivial class. Combined with D-VAN-7 agreement, this answers Keller's question negatively at m = 5 and identifies the specific cohomology class.
- **inconsistent** — K-4b and D-VAN-7 disagree. Triggers diagnostic workflow (#152 or sibling); blocks publication.

## Scope

This is **not a research/coding task** — all the heavy lifting is in K-4a Phase 2. K-4b is the orchestration + interpretation layer.

Three deliverables:

### 1. Driver script

`extraspecial_orbifolds/scripts/k4b_run_m5.sh`:

```bash
#!/usr/bin/env bash
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR"

LOG_DIR="${K4B_LOG_DIR:-../perf/raw/k4b}"
mkdir -p "$LOG_DIR"
LOG="$LOG_DIR/k4b_m5_$(date +%Y%m%d_%H%M%S).log"

echo "K-4b m=5 run started $(date -u +%FT%TZ)" | tee "$LOG"
ulimit -v $((96 * 1024 * 1024))  # 96 GB virtual memory cap

gap -q -b -c '
    Read("k4a_classify.g");
    result := K4aClassify(5);
    PrintTo("k4b_m5_result.g",
        "# K-4b m=5 result (auto-generated)\n",
        "RESULT := ", result, ";\n");
    Print("K-4b m=5 verdict: ", result.verdict, "\n");
    Print("  E   class: ", result.E_class, "\n");
    Print("  D_8 class: ", result.D8_class, "\n");
    Print("  Q_8 class: ", result.Q8_class, "\n");
    QUIT;
' 2>&1 | tee -a "$LOG"

echo "K-4b m=5 run ended $(date -u +%FT%TZ)" | tee -a "$LOG"
```

Persists the result record to `k4b_m5_result.g` (loadable in a fresh GAP session for downstream consumers).

### 2. Cross-validation harness

`extraspecial_orbifolds/scripts/k4b_xcheck_d_van.g`:

```gap
# K-4b cross-validation against D-VAN at m = 5.
#
# K-4b's verdict (from KRR lattice via CGR §5.2) and D-VAN's verdict
# (from algebraic restriction of a ω-vector) must agree at m = 5.

# 1. Load K-4b result.
Read("k4b_m5_result.g");      # binds RESULT

# 2. Load D-VAN result. For m = 5 we don't have an explicit ω-vector
#    from KRR — that's the whole point of K-4b. So D-VAN's role here
#    is verifying that K-4b's *classification* is consistent with the
#    structure of H³(E_+(5); U(1)).
#
#    Specifically: K-4b reports E_class, D8_class, Q8_class as
#    cohomology-class identifiers. D-VAN can enumerate H³ classes
#    and confirm there exists a consistent ω that has these three
#    restrictions. If yes, K-4b is consistent. If no, contradiction.

Read("detecting_family_vanish.g");

# 3. Determine which ω ∈ H³(E_+(5); U(1)) would have these restrictions.
#    Use the inverse direction of D-VAN's restriction matrices:
#       given Res(ω) = (res_E, res_D8, res_Q8),
#       solve for the H³ orbit that ω lies in.
#    The system is over-determined (3 subgroups, one ω), so solvability
#    is itself a check.
candidate_omega_orbits := _DVAN_InvertRestriction(5,
    RESULT.E_class, RESULT.D8_class, RESULT.Q8_class);

if Length(candidate_omega_orbits) = 0 then
    Print("INCONSISTENT: no ω has the K-4b restrictions.\n");
    Print("Diagnostic: check K-4a-T5b's σ phase, or T4b's ε extraction.\n");
elif Length(candidate_omega_orbits) > 1 then
    Print("MULTIPLE: ", Length(candidate_omega_orbits), " ω orbits match.\n");
    Print("Indicates injectivity gap in {E, D_8, Q_8} — see #193.\n");
else
    Print("CONSISTENT: unique ω orbit matches K-4b's restrictions.\n");
    Print("Specifically: orbit ", candidate_omega_orbits[1], " of H³(E_+(5); U(1)).\n");
fi;

QUIT;
```

This depends on a `_DVAN_InvertRestriction` helper that doesn't exist yet. If D-VAN can be coaxed to do this inversion, file as `K-4b-T2`; else fall back to the simpler check `D-VAN(ω = 0).trivial = (K-4b verdict = "trivial")`.

### 3. Interpretation note

`docs/superpowers/research/2026-XX-XX-k4b-m5-verdict.md`:

A short markdown note (written AFTER the run completes) summarising:

- The K-4b verdict at m = 5.
- The corresponding interpretation for Keller's question.
- Confidence assessment based on (a) anchor agreement at m = 3, (b) cross-validation outcome, (c) any caveats from K-4a's risk register.
- Whether the m = 5 result should be reported in a paper (cite the methodology paper W-1) or held until m = 7 (K-4c) also lands.

## Compute budget

`BuildKRREpsilonData(5)` is the dominant cost. From `test_defect_rep_optim.g` data:

- m = 3: 3 ms/entry, total ~ minutes.
- m = 5: 3 ms/entry (per measurement in #47 follow-up), total ~ tens of minutes.
- m = 7: 73 ms/entry, total ~ hours.

The downstream classifier work (T5a/T5b/T1/T2/T3) at m = 5 operates on subgroups of order ≤ 64 (E) or 8 (D_8/Q_8), so adds at most minutes.

**Estimated total**: K-4b m = 5 run completes in **~30-60 minutes** on a workstation with 96 GB cap. No new infrastructure needed beyond K-4a Phase 2.

## Acceptance criteria

1. K-4a Phase 2 fully merged and #201 (m = 3 anchor regression) is green.
2. `k4b_run_m5.sh` produces a result file with a non-`fail` verdict (i.e., the run completed).
3. `k4b_xcheck_d_van.g` reports `CONSISTENT`.
4. Interpretation note committed to `docs/superpowers/research/`.
5. K-4 EPIC (#187) updated with the m = 5 verdict.

## Risks

### High: K-4a Phase 2 doesn't ship

Tracking dependency: T4a (#196) determines feasibility. If T4a concludes ε_a is not extractable cleanly from KRR data, K-4b is blocked indefinitely.

Mitigation: T4a is being worked in parallel; risk reviewed when T4a's research note lands.

### Medium: m = 5 ε extraction performance

K-4a-T4b is implemented at m = 3 + tested at m = 5, 7. Performance has been measured for the intertwiner pipeline itself (3 ms/entry at m = 5); the ε extraction wrapper around it should be similar. If it's not, optimisation is needed before K-4b ships.

### Medium: σ phase convention

K-4a-T5b has a noted σ-vs-conj(σ) ambiguity (CGR (5.20) writes σ\*). The m = 3 anchor (T7) catches this if it's wrong. K-4b runs after T7 passes, so this risk is upstream-mitigated.

### Low: detecting family injectivity gap

If R-1 (#193) concludes {E, D_8, Q_8} doesn't actually detect at H³ (counter to AM04 + Pham 2000 evidence), K-4b's "trivial" verdict only proves the restriction is trivial, not that α itself is trivial. Could need additional detecting subgroups.

Mitigation: R-1 is in flight. If verdict comes back with a gap, file follow-up to expand the family.

## What K-4b does NOT do

- Compute H³(E_+(5); U(1)) directly (that's A-5b, the kernel-of-transgression workstream — currently #47 closed, but a follow-up may exist tracking the latest run).
- Compute the modular data of `Z(Vec_{E_+(5)}^{α_KRR})` in full (that's K-4c if needed, but our detecting-family approach avoids it).
- Resolve K-4a-T4a's research question (that's K-4a-T4a itself, #196).
- Run automatically — this is an explicit human-triggered run after Phase 2 lands.

## Out of scope

- m = 7 production run (K-4c, file once K-4b ships).
- Generalisation to non-CT twists.
- Statistical confidence quantification (the verdict is a deterministic yes/no, modulo bugs).

## Issues to file (after K-4a Phase 2 lands)

- **[K-4b-T1]** Driver + cross-validation harness (`k4b_run_m5.sh`, `k4b_xcheck_d_van.g`).
- **[K-4b-T2]** Interpretation note (depends on T1 completing).
- **[K-4b-T3]** `_DVAN_InvertRestriction` helper (or fallback strategy if D-VAN can't invert cleanly).
