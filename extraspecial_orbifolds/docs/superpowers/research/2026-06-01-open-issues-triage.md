# Open Issues Triage — 2026-06-01

## Summary

- **34 open issues** as of `2026-06-01T22:46Z` (after PR #395 merged).
- **9 candidates for closure** (closed-by-merge, stale, or umbrella with all children closed). See "Recommended closures".
- **25 active issues**, categorised by workstream below.
- **Top blocker chain**: A-5b m=5 `kernel.g` land → unblocks #148, #189, #280, and W-EPIC m=5 results row.

## Recommended closures

Each one-line justification states the closure type and evidence. **Closures are recommendations only — no issues were closed in this PR.**

| Issue | Type | Justification |
|---|---|---|
| **#391** Structural P16 fix: reduce Path Z matvec at m=5/m=7 | closed-by-merge | Approach A (#392), Approach B (#393), and A+B combine (#394) all merged into main. The "Acceptance" criteria (design doc, implementation plan, PR stack) are all met. Issue body still says OPEN; needs manual close. |
| **#109** [P-EPIC] Profile + performance optimisation of merged code | umbrella-all-children-closed | All listed children #110-#116 + #70 are CLOSED. The EPIC's own description says "closes when every leaf issue in the workstream closes" — that condition is met. |
| **#185** [b2-4 perf] ResolutionFiniteGroup(E_+(3), 6) OOM blocks m=3 Pontryagin anchor | stale | The downstream parent #164 (Q-int B2-4 m=3 anchor) is CLOSED. The b2-4 anchor it was blocking no longer needs this resolution. Per #187 K-4 EPIC body: "This makes #137 (low-mem HAP for E_+(7)) and #185 (b2-4 OOM) **not on the critical path**" — confirmed. |
| **#177** [A-5b perf] Vectorisation + batching opportunities in m=5 kernel sweep | stale | Round-2 patches R2-1..R2-3 all landed (#184, #233, #235, #246, #258, #260, #262, #265, #267, #268, #269, #270, etc.). The perf-audit-tier-1/2/3 work (#381-#389) and Path Z structural fix (#391/#392/#393/#394) supersede this. |
| **#280** [A-7 perf-4''] re-run m=5 anchor verification after A-5b completes | NEEDS-REVIEW (likely stale) | The perf-4'' M_stack compression branch the issue tracks is from May 2026; the A-5b production has since converged on a different perf stack (#381-#394). Issue says "Wait for A-5b" — A-5b's `kernel.g` is now imminent. Probably either re-target to the current branch or close. Recommend user-review before closing. |
| **#166** [Q-int B2-6] m=7 production: Quillen-route kernel.g for E_+(7) | NEEDS-REVIEW (likely stale) | Says "blocked by #165 (driver complete)" — #165 was CLOSED 2026-05-19. The parent #137 it was meant to close is CLOSED 2026-05-19. The Quillen-route m=7 path appears to have been deprecated in favour of the LHS-HAP route (#252) plus the D-VAN/B2 sister issues (#311/#312). User should confirm whether this issue should be re-scoped to track ongoing m=7 production, or closed and a new one filed for the LHS-HAP-route m=7 production. |
| **#140** [D-INV] Brainstorm: cohomology-level inverse of detecting-family restriction | NEEDS-REVIEW (probably stale) | Issue body explicitly says "Brainstorm placeholder" and "Do NOT start implementation". Listed prerequisites: D-VAN merged (yes, via #361/#379), Q-int A2+A3 (yes, via #133), A-5b shipped (imminent). The brainstorm has been deferred for ~6 weeks while the K-4 / D-VAN paths matured. Either it's time to brainstorm or the alternative paths have made D-INV moot. User-review. |
| **#154** [D-VAN-MATH] Quillen-stratification analysis: minimal complete detecting family | NEEDS-REVIEW (superseded) | The actionable theoretical content was answered by PR #310 (#154 follow-up for m=2/3, closed) and PR #314 (closed-form bound, closed). The remaining open math (m=5/7 minimum slack) is implicitly covered by #311/#312. User can either close #154 with pointer to #310/#314 or rescope. |
| **#1, #2, #3, #4, #5, #6, #7** | umbrella-EPICs | These are the W-EPIC/A-EPIC/V-EPIC/T-EPIC/Q-EPIC/K-EPIC/X-EPIC umbrellas. They're permanently open until "every leaf issue in the workstream closes" per their own descriptions. Practical guidance: NOT recommended for closure now, but worth a periodic review since the current open issues are mostly in m=7 / writeup territory. |

**Net**: 4 high-confidence closures (#391, #109, #185, #177) + 5 NEEDS-REVIEW (#280, #166, #140, #154, plus #187 K-4 EPIC and #142 D-VAN-1 EPIC as below).

## Active issues by workstream

### A-5b m=5 (#47 parent — already CLOSED)

The `[A-5b]` workstream-name lives on as "in-flight m=5 production" even though the issue #47 itself is CLOSED (2026-05-16). The current run is PID 87863 with A+B+combine engaged (per task context). Kernel result `|ker Tr(E_+(5))| = 2^52` is known from PID 81247's Step 3.

| Issue | Status | Notes |
|---|---|---|
| **#369** Memory footprint reduction options at m=5/m=7 | active | Options A-F listed; A (free `.table_gf2`) and D (slice fail-column) most relevant. Not yet implemented. Drives the "fit in 30-40 GB without swap" goal. |
| #177 | recommend close | Superseded by #381-#394 (see above). |
| #280 | NEEDS-REVIEW | Likely stale, see above. |

### D-VAN m=7 (#290 parent + #379, #380)

| Issue | Status | Notes |
|---|---|---|
| **#290** [D-VAN m=7] Extend Lagrangian enumeration for E_+(7) | active (umbrella) | Code landed via #361 (8-EA family) and #379 (F_2-first greedy). Acceptance criteria #1-#4 partially met; #3 (all 454 generators report `trivial=false`) is what #362 covers. Could be closed once #362 ships. |
| **#362** Per-generator sweep — certify 454 generators detected by the 8-EA family | active | Direct follow-up to PR #361. Cheap once Y_full built (~0.5-1d work + few hours wall). The remaining piece of #290 acceptance. |
| **#308** Resolution + per-EA chain-map at m=7 scale (HAP side) | active | Three phases: Phase A (LHS resolution wired into BuildRestrictionMatrices, code path #252 ready), Phase B (per-EA chain-map at scale — options B1/B2/B3 still pending), Phase C (end-to-end). Real work remaining. |
| **#311** Route C polynomial bridge extended to m=7 (via HAP) | active | Sister of #312 (B2b). Dependency on slack-trimming at m=7 (covered by #154 follow-ups). Without slack, full 9.8M EA path needs streaming. |
| **#312** Symbolic Quillen-presentation polynomial bridge at m=7 (bypass HAP) | active | Sister of #311 (B2a). The omega -> Quillen-coefficient conversion is the open algorithmic question. |

**D-VAN m=7 production status**: code landed (#379, #380, #361); a fresh m=7 production rerun is the next milestone per CLAUDE.md workstream-table.

### K-4a / K-4b / K-4c (#187 K-4 EPIC)

| Issue | Status | Notes |
|---|---|---|
| **#187** [K-4 EPIC] | NEEDS-REVIEW (likely close) | K-4a children all closed; K-4c (#190) closed; only K-4b (#189) remains open. EPIC could be left open until #189 closes, OR rescoped. |
| **#189** [K-4b] Restrict S^Keller to detecting family + compare to S^0\|_H | active, blocked by A-5b kernel.g | Acceptance: m=5 verdict (whether all three restrictions match). Needs the m=5 kernel result that A-5b is producing. Anchor at m=3 still pending too. |
| **#378** [K-4a] Lift K4aClassify m=5 cap; #236 has landed | active | Mechanical cap-lift (1-2 days). Unblocks K4aClassify(7) for omega=0 case. E branch at m=7 stays blocked behind a different issue (NEEDS-CHECK whether #377 closure cleared it — see below). |

**Note on #378's blocker dependency**: #377 was CLOSED 2026-06-01. So the lattice_source E branch at m=7 is now unblocked. Issue #378's body still mentions it as "blocked separately by #377" — update the body to reflect #377 has shipped, then proceed with the cap-lift.

### Q-int (Quillen integer Bockstein extensions)

| Issue | Status | Notes |
|---|---|---|
| #166 | recommend close (NEEDS-REVIEW) | #165 (driver) closed, #137 (parent) closed; Quillen-route m=7 production seems superseded by the LHS-HAP route. |

No other Q-int issues are open. The Q-int A1/A4/B2-1..B2-5 children are all closed.

### W (paper writing) — #7 W-EPIC

| Issue | Status | Notes |
|---|---|---|
| **#7** [W-EPIC] Methodology paper / writeup synthesis | active (umbrella) | No open W-* leaves currently. EPIC will progress as workstreams produce results to write up. |

No leaf W-* issues are currently open. The writeup arrival schedule is implicitly: A-5b kernel.g lands -> m=5 results row -> K-4b m=5 verdict -> m=7 production.

### Other / uncategorised

| Issue | Status | Notes |
|---|---|---|
| **#264** [V-5c #257 follow-up] Open items after small-m list-based engine | active | m=2 didn't finish in 5-min wall; m=3 not run; m=2 acceptance test still on the to-do. Modest perf-fix work + cross-validation. Low priority unless V-5c at m=2/3 is needed for the writeup. |
| **#142** [D-VAN-1 EPIC] | active (umbrella) | Only #148 remains open as a child. Could be closed once #148 ships. |
| **#148** [D-VAN-7] m=5 anchor: D-VAN matches A-5b empirical kernel | active, blocked by A-5b kernel.g | The last D-VAN Phase 1 leaf. Closes #142 EPIC. |
| **#271** [A-7 perf EPIC] | active (umbrella, mostly historical) | All perf-1..perf-5 children closed. perf-6 (#286) is the only open child. The EPIC itself could close when #286 closes (or #286 is closed as deferred). |
| **#272** [A-7 dist EPIC] Distributed-computing infrastructure | active (forward-looking) | Sub-tasks dist-1..dist-6 not yet started. Companion to #271, gated on m=7 perf landing. Long-horizon. |
| **#286** [A-7 perf-6] Compile codebase via gac for m=7 | deferred | Explicitly deferred per the issue body. Will revisit "for m=7 production". |
| **#45** [A-3d] E_+(3) Tier-3 \|Aut(N, T)\| cross-validation | low-priority backlog | Long-standing backlog; not on critical path. |
| **#48** [A-5c] E_+(5) Tier-4 driver (Quillen route) | conditional/deferred | "Blocked on DP-II HAP failed" — DP-II went HAP-succeeded (A-5b is the production line). This issue is effectively never going to run. Recommend close as won't-fix or rescope. NEEDS-REVIEW. |
| **#49** [A-5d] E_+(5) Tier-3 on subset | low-priority backlog | Multi-day Tier-3 compute. Not on the K-4 critical path. |
| **#51** [A-7b] E_+(7) Tier-1/5 candidate-elimination loop | conditional, future | Conditional on `ker != 0` at m=7. Real but distant. |

## Blocker chains

Reading right-to-left: target -> who's blocked -> on what.

1. **A-5b m=5 `kernel.g` (in flight, PID 87863)** blocks:
   - #148 (D-VAN-7 m=5 anchor)
   - #189 (K-4b restrict S^Keller, m=5 verdict)
   - #280 (perf-4'' re-run m=5 anchor)
   - W-EPIC m=5 results row (no specific issue)

2. **#236 (Gauss-sum stub, CLOSED 2026-05-17)** no longer blocks anything. #378 still references it as blocker — body needs updating.

3. **#377 (D-VAN m=7 EA generator persistence, CLOSED 2026-06-01)** unblocked:
   - K-4a m=7 lattice_source E branch (the gating note in #378's body is now outdated).

4. **m=7 production rerun (per CLAUDE.md workstream-table, code landed via #379/#380)** would unblock:
   - #362 (per-generator sweep at m=7 — needs Y_i matrices from a fresh m=7 run)
   - downstream K-4 m=7 verdict (#187 EPIC closure)

5. **D-VAN m=7 HAP side (#308 Phase A + B + C)** blocks:
   - #311 (Route C bridge at m=7), via Phase A's `ResolutionFiniteSubgroup(R_G_LHS, H)` adapter question
   - K-4c at m=7 (closed #190, but the LhS-resolution path still has open ends)

## Suggested next steps after A-5b lands `kernel.g`

In rough priority order:

1. **Close #391**. Verify the A+B+combine PR (#394) actually closes the issue body's acceptance, then close.
2. **Run #148 (D-VAN-7 m=5 anchor)**. With `kernel.g` available, this is a few hours wall + a few hours coding. Closes D-VAN Phase 1 (#142).
3. **Run #189 K-4b at m=5**. With `kernel.g` + KRR's m=5 spectral data already produced, this is the final piece of K-4 EPIC #187 at m=5.
4. **#378 cap lift**. 1-2 days, mechanical; updates body to reflect #236/#377 both closed.
5. **Close #109 P-EPIC**. All children closed; mark complete.
6. **Close #185 (b2-4 perf OOM)**. The downstream anchor is closed; this issue is stale.
7. **Close #177 (A-5b perf vectorisation)**. Superseded by #381-#394.
8. **Re-target or close #280**. Either the perf-4'' branch should be brought up to current main and run, or close it as superseded.
9. **#362 per-generator sweep at m=7**. With #379/#380 landed, this is the next D-VAN m=7 milestone. Estimated 0.5-1 day implementation + a few hours wall.
10. **Re-scope or close #166** (Quillen-route m=7 production). The route appears deprecated in favour of LHS-HAP + Route C.
11. **Revisit #154 / #140**. D-VAN-MATH and D-INV brainstorm placeholders — either start the work or close.
12. **#308 Phase A m=5 spike**. The `ResolutionFiniteSubgroup(R_G_LHS, H)` adapter question is the gating risk for D-VAN m=7 HAP-side; an m=5 cross-check would de-risk it cheaply.

## Notes / caveats

- The user asked me NOT to close any issues; this report only surfaces candidates.
- "NEEDS-REVIEW" tags mean I couldn't confirm closure from issue+PR text alone (often because the body's "acceptance" criteria are ambiguous after several months of upstream evolution).
- I did not exhaustively audit every closed issue from the past 60 days; the focus was on confirming references and identifying obvious orphan/parent relationships.
- PR #394 did not auto-close #391 (verified via `gh issue view 391 --json state`) — the GitHub linking was not configured. This is the model case of an issue that needs a manual `gh issue close` after merge.
