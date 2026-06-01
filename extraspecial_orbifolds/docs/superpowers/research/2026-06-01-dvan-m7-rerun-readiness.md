# D-VAN m=7 production rerun readiness brief

**Date**: 2026-06-01
**Issue**: #397
**Branch**: `dvan-m7-rerun-readiness-397`
**Parent context**: PRs #379 (F_2-first greedy + incremental RREF, issues #343+#347) and #380 (`ea_generators` persistence, issue #377), both merged 2026-06-01 (`12cdf17`, `3c4731a`).
**Status**: ready to launch on user signal. All anchors pass; no blockers. A-5b m=5 (PID 87863) still in flight — see launch protocol §7.

## Bottom line

1. **Anchors all pass** with the current code (post-#379 + #380). m=2/m=3 cold walls 110 ms / 3.4 s on HAP source; m=2/m=3 LHS source 183 ms / 3.6 s. Bit-for-bit witness reproduction matches PR #310 references. PR #379's F_2-first/incremental RREF refactor did NOT regress the m=2/m=3 cases. (Pass 1 of the rework runs only inside `_DETF_TrimmedFamily_m7_streaming`, which is m=7-only by dispatch.)

2. **`ea_generators` persistence (#380) works end-to-end**. Verified via runtime smoke test by invoking the m=7 streaming code at m=3 (`opts.m := 3`): result contains both `ea_generators` and `ea_generators_sorted`, each a list of pc-group element tuples (e.g. `[f7, f1*f5, f2*f6, f3]`) reproducible across reruns. `LoadDVANEAFamily(m)` is wired correctly to read these and return reconstructed `Subgroup(G, gen_tuple)` lists.

3. **Launch command** (with A-5b m=5 currently running; see §7 protocol):

   ```bash
   cd /Users/thomasgemunden/Projects/group_cohomology/DRINFELD/extraspecial_orbifolds/scripts
   nohup /opt/homebrew/bin/gap -o 16g -q -b -c \
     'TRIMMED_RUN_M7 := true;; TRIMMED_M7_SEED := 42;; TRIMMED_M7_SAMPLE_SIZE := 1000;; \
      Read("tests/test_dvan_trimmed_family.g"); QUIT;' \
     > /tmp/dvan_m7_rerun_$(date +%Y%m%d_%H%M%S).log 2>&1 &
   ```

   This exercises the same m=7 path as the previous PR #290 run via the test suite's T8 branch. **Caveat**: the test suite does not persist `result.g` to disk; see §5 for the persistence gap.

4. **Estimated wall**: 10-60 min (down from PR #290's 9.3 h, courtesy of #379's F_2-first/incremental-RREF rework). **Estimated peak memory**: 1-2 GB heap (`-o 16g` is generous).

5. **PERSISTENCE GAP**: no scripted persister exists for `dvan_min_family/m7/result.g`. The previous m=7 result was hand-written into commit `7b7fbbb` (PR #290 / issue #361). The fresh rerun will populate `r7` in-session but the operator must explicitly persist the lightweight fields (see §5).

## 1. Anchor verification (task §1)

Ran `gap -q -b tests/test_dvan_trimmed_family.g` from
`extraspecial_orbifolds/scripts/` with the current `dvan-m7-rerun-readiness-397`
checkout (off `origin/main` @ `e9681d8`). Output:

```
--- T3: m=2 anchor (PR #310 witness {2, 3, 5}) ---
  m=2 wall: 110 ms (cold)
  r2.ea_count = 3 (PR #310 minimum): PASS
  r2.family_size = 5: PASS
  r2.locally_tight = true: PASS
  r2 sorted chosen = [2, 3, 5]: PASS
  r2 chosen (greedy order) = [3, 2, 5]: PASS

--- T4: m=3 anchor (PR #310 witness {4, 6, 7, 11, 16, 22}) ---
  m=3 wall: 3439 ms (cold)
  r3.ea_count = 6 (PR #310 minimum): PASS
  r3.family_size = 8: PASS
  r3 sorted chosen = [4, 6, 7, 11, 16, 22]: PASS
  r3 chosen (greedy order) = [4, 6, 11, 22, 7, 16]: PASS
  r3 greedy kernel sequence matches PR #310: PASS

--- T5: caching second m=3 call ---
  m=3 wall (warm cache): 388 ms

--- T7: LHS-path cross-validation ---
  m=2 LHS wall: 183 ms — PASS
  m=3 LHS wall: 3631 ms — PASS

=== test_dvan_trimmed_family: PASS ===
```

All assertions pass. The greedy-witness and kernel-reduction sequences
match PR #310's bit-for-bit anchors. Conclusion: PR #379's F_2-first
greedy + incremental RREF rework does NOT regress m=2/m=3 (which makes
sense — the rework lives entirely inside
`_DETF_TrimmedFamily_m7_streaming`, dispatched only when `source = "lhs"
and m = 7`).

## 2. EA-generators persistence sanity check (task §3)

### What #380 actually changed

PR #380 added `ea_generators` and `ea_generators_sorted` fields ONLY to
the result rec returned by `_DETF_TrimmedFamily_m7_streaming`
(`detecting_family_restriction.g` line 2112). The non-streaming
`_DETF_TrimmedFamily` (used at m ∈ {2, 3, 5} both via "hap" and "lhs")
does NOT populate these fields — the eager path uses
`data.H_EA_list[ea_chosen[i]]` directly and indices ARE reproducible
there (deterministic max-EA enumeration via `_DETF_AllMaxEAsIn`). So
"sanity-check at m=3" needs to invoke the streaming path's `opts.m :=
3` override (line 1706-1710) rather than the default m=3 path.

### Runtime verification

```
gap -q -b -c 'Read("detecting_family_restriction.g"); \
  r := _DETF_TrimmedFamily_m7_streaming(rec(m := 3, sample_size := 30, \
    verbose := false, seed := 42)); ...'
```

Output:

```
m=3
ea_count=6
final_ker=1
locally_tight=true
has ea_generators=true
ea_generators length=6
has ea_generators_sorted=true
first ea_generators[1] sample=[ f7, f1*f5, f2*f6, f3 ]
```

`ea_generators[1]` is a list of pc-group products of `E_+(3)`'s
generators (here `f7` is the central element z; `f1*f5`, `f2*f6`,
`f3` span a rank-3 EA over F_2). Reconstructing via `Subgroup(G,
ea_generators[i])` gives back the EA subgroup deterministically across
reruns.

Note: `ea_count = 6` here exactly matches the m=3 PR #310 minimum, even
though this was run via the streaming path with `sample_size = 30`. At
m=3 the total number of max EAs is 30 so the sample is exhaustive.

### Persistence-test status

`tests/test_dvan_m7_ea_generator_persist.g` (run via absolute path
because it requires `INPUT_FILENAME()`):

```
T1. LoadDVANEAFamily(99) -> fail: ok
T2. LoadDVANEAFamily(7) -> fail (current result.g lacks ea_generators): ok
    [confirms PR #361's result.g is pre-#380, lacks the field]
T3. Source contains 'ea_generators :=' field: ok
T3. Source contains 'sample_basis_tuples[j]' reference: ok

Passes: 7, Failures: 0
```

T2 specifically anchors the fact that the currently-persisted
`computed/dvan_min_family/m7/result.g` is pre-#380 — and that the
production rerun is needed to populate the field.

## 3. m=7 launch prerequisites (task §2)

### Required on-disk prerequisites

None. The m=7 D-VAN path builds everything in-session:

- `_DETF_BuildSetupG_LHS(7)` calls `LHSResolutionEPlus(7, 4)` (not 5;
  D-VAN passes max_n=4 per `detecting_family_restriction.g:451-453`,
  saving ~14× over the m=7 LHS resolution time in CLAUDE.md). Cold
  wall ~63 s; heap ~130 MB. Cached per-session.
- `_DETF_LagrangiansViaWitt_streaming` is purely combinatorial; no
  HAP calls. Walks all 9 845 550 type-+ Lagrangians in V = (F_2)^14.
- Per-sample `RestrictionMatrixViaHAP` builds use the LHS R_E_lhs;
  each one is ~0.7 s post-#329 (`_FastGroupCohomologyFunctor` +
  `SolutionMat` rational solve). For sample_size = 1000 this is
  ~700 s ~ 12 min.

Disk checked:
- `extraspecial_orbifolds/computed/E_plus_7/`: contains
  `manifest.g` (structural T-vector) and `structural/manifest.g` only.
  No precomputed LHS resolution on disk (not needed; built in-session).
- `extraspecial_orbifolds/computed/dvan_min_family/m7/result.g`: present
  but **pre-#380** (PR #361 output; lacks `ea_generators`, has the
  short-form `greedy_log` `[rec(ea, ker), ...]` not the post-#379
  `[rec(ea, ker, pass, gain), ...]`).

### Stale outputs that might interfere

- `dvan_min_family/m7/result.g` (pre-#380): if the launcher simply
  reads then overwrites, no problem. If the launcher decides "result.g
  exists, skip" (no current code does this — neither the test path nor
  any persister), it would skip the rerun. **Recommendation**: rename
  or move the existing file before launch (e.g.,
  `result_pre380_pr361.g`) so the rerun output replaces it cleanly and
  the pre-#380 verdict remains for diffing.

### Estimated wall + memory

| Component | Cold wall | Memory |
|---|---|---|
| `LHSResolutionEPlus(7, 4)` | ~63 s | ~130 MB |
| D_8 + Q_8 restriction matrices | ~few seconds | included |
| Witt streaming + reservoir sample (1000 of 9 845 550) | ~few minutes | tiny |
| Per-sample restriction matrices (1000 × ~0.7 s) | ~12 min | grows to ~1-2 GB |
| Pass 1 F_2-first greedy (#379) | seconds | tiny |
| Pass 2 single integer SNF | minutes | bounded |
| Pass 3 fallback (only if Pass 2's ker > 1) | minutes-hours | bounded |
| Drop-one verification | minutes | bounded |
| **TOTAL** (with Pass 3 not firing) | **~15-30 min** | **~2 GB peak** |
| **TOTAL** (Pass 3 fires) | **30-90 min** | **~2 GB peak** |

The PR #379 commit message states "Expected wall at m=7: minutes instead
of ~9 hours" (vs PR #290's 33 483 s). At m=7 H^3 = (Z/2)^454 ⊕ Z/4 is
overwhelmingly F_2 torsion, so Pass 1's F_2-first saturation should hit
ker = 4 or 1 immediately and Pass 2 is a single SNF closing the
residual Z/4 (if any). If the Pass 1 + Pass 2 combination already gives
ker = 1, Pass 3 doesn't fire.

`-o 16g` heap cap is consistent with `tests/test_dvan_trimmed_family.g`
T8's documented invocation. Could probably run with `-o 8g`; `-o 16g`
gives headroom against the integer-SNF on the chosen-stack at Pass 2.

### Expected output files

ONE file: `extraspecial_orbifolds/computed/dvan_min_family/m7/result.g`
(or whatever the operator names it post-rerun).

`tests/test_dvan_trimmed_family.g` T8 does NOT persist — it only prints
`r7` to stdout. The previous PR #290 / #361 commit message says the
output was "Persisted to extraspecial_orbifolds/computed/
dvan_min_family/m7/result.g", but the file itself shows hand-formatted
GAP code with only a subset of `r7`'s fields (m, greedy_log,
family_size, final_ker, locally_tight, drop_one_kers, sample_size,
wall_seconds, source). The persistence appears to have been manual.

## 4. Known risks / open concerns

### Sample randomness (intrinsic to streaming-greedy)

The 1000-Lagrangian reservoir sample picks from 9 845 550 Lagrangians
via Mersenne-Twister with seed (default 42 per T8). **Seed 42
reproduces bit-for-bit across runs** on the same GAP build (probed
locally). Different seed → different chosen family, but `final_ker =
1, locally_tight = true` should hold for ANY sufficiently-large
sample. PR #290's run with seed (unknown — pre-deterministic) produced
the 8-EA family `[1, 2, 3, 6, 10, 12, 122, 765]`.

### Pass 3 fallback risk

If Pass 1 (F_2-first) and Pass 2 (integer SNF cleanup) jointly leave
`curr_ker > 1`, Pass 3 enters a top-K + integer-SNF batch loop
(`detecting_family_restriction.g:2009-2078`). Pass 3 has a "stuck"
exit when no top-K candidate reduces the kernel — in which case the
returned result has `final_ker > 1` and `locally_tight = false`.

If this fires, the response is to **rerun with larger `sample_size`**
(e.g. 5000 or 10000). The wall scales roughly linearly in
`sample_size`. At sample_size = 5000, expect ~75 min instead of ~15
min, still under 2 h.

### Issue #329 chain-map perf (CLAUDE.md memory note "blocked")

CLAUDE.md memory references issue #329 as a "blocked" m=7 chain-map
perf issue. Reading the code: PR #329 actually LANDED (
`_FastGroupCohomologyFunctor` at `detecting_family_restriction.g:151`,
"Issue #329 (further speedup)" comments throughout the SolutionMat
path). The memory note is stale — likely from before the PR merged.
The 0.7 s per-EA chain map is the post-#329 figure.

The CLAUDE.md memory file `reference_hap_and_workstream_history.md`
should be updated post-rerun to reflect that #329 is closed and the
per-EA chain map is ~0.7 s. **Not a blocker for the rerun.**

### `data` field bloat in the result

The streaming function returns a result rec that includes
`data := <BuildRestrictionMatrices-style rec>`, which itself contains
the per-EA HAP contexts and restriction matrices. PrintTo-ing the full
`r7` would write a multi-MB or multi-GB file. The previous PR #361
result.g intentionally persists only the small fields (the operator
must reproduce this selective-field write). See §5.

### CLAUDE.md "14 min" cost estimate

CLAUDE.md states: "Per CLAUDE.md, the LHS resolution itself is ~14
min / 500 MB". This refers to `LHSResolutionEPlus(7, 5)` used by
`run_e_plus_7_lhs.g` for A-7a's transgression driver. The D-VAN m=7
path uses `LHSResolutionEPlus(7, 4)` (~63 s, ~130 MB), per
`_DETF_BuildSetupG_LHS:451-453`. The 14 min figure in the task
description is for the A-7a workflow, not D-VAN.

### "Logging gap" risk per CLAUDE.md

CLAUDE.md "When a run goes silent" note: the m=7 streaming driver
emits progress lines every 500 000 Lagrangians (line 1820-1823) and
every 100 per-sample restriction matrix builds (line 1849-1853). These
are well below the 1 s / iteration threshold; logging is adequate.

The F_2-first Pass 1 logs every 5 steps (line 1973-1978); at expected
~6-30 Pass-1 picks this is OK. Pass 2 is a single SNF — log entry
1989-1991 emits one line before + one after. Pass 3 entries log per
super-step (line 2065-2068).

No silent-stretches expected longer than ~30 s.

## 5. Persistence gap — proposed operator protocol

The test-suite T8 path prints `r7` to stdout but does NOT persist. The
previous PR #290 / #361 result.g was hand-written. To avoid a repeat,
proposed protocol post-rerun:

1. Capture the rerun stdout to a log file (the launch command in §0
   already does this via `> /tmp/dvan_m7_rerun_*.log`).
2. After the run completes, in a follow-up GAP session, persist the
   selected fields via `OutputTextFile + SetPrintFormattingStatus(...,
   false)` to avoid the PrintTo autowrap hazard (CLAUDE.md §Caveats).
   Required selective fields:

   ```gap
   # In the rerun session, AFTER r7 lands:
   stream := OutputTextFile(
     "computed/dvan_min_family/m7/result.g", false);
   SetPrintFormattingStatus(stream, false);
   PrintTo(stream, "# D-VAN m=7 minimum detecting family\n");
   PrintTo(stream, "# Built post-#379 (F_2-first) + post-#380 ",
                   "(ea_generators).\n");
   PrintTo(stream, "dvan_m7_result := rec(\n");
   PrintTo(stream, "    m                        := ", r7.m, ",\n");
   PrintTo(stream, "    source                   := \"", r7.source,
                   "\",\n");
   PrintTo(stream, "    ea_indices_chosen        := ",
                   r7.ea_indices_chosen, ",\n");
   PrintTo(stream, "    ea_indices_chosen_sorted := ",
                   r7.ea_indices_chosen_sorted, ",\n");
   PrintTo(stream, "    ea_generators            := ",
                   r7.ea_generators, ",\n");
   PrintTo(stream, "    ea_generators_sorted     := ",
                   r7.ea_generators_sorted, ",\n");
   PrintTo(stream, "    include_D8               := ", r7.include_D8,
                   ",\n");
   PrintTo(stream, "    include_Q8               := ", r7.include_Q8,
                   ",\n");
   PrintTo(stream, "    final_ker                := ", r7.final_ker,
                   ",\n");
   PrintTo(stream, "    ea_count                 := ", r7.ea_count,
                   ",\n");
   PrintTo(stream, "    family_size              := ", r7.family_size,
                   ",\n");
   PrintTo(stream, "    locally_tight            := ",
                   r7.locally_tight, ",\n");
   PrintTo(stream, "    drop_one_kers            := ",
                   r7.drop_one_kers, ",\n");
   PrintTo(stream, "    walltime_ms              := ",
                   r7.walltime_ms, ",\n");
   PrintTo(stream, "    sample_size              := ", r7.sample_size,
                   ",\n");
   PrintTo(stream, "    total_lagrangians        := ",
                   r7.total_lagrangians, ",\n");
   # greedy_log entries are small enough to inline.
   PrintTo(stream, "    greedy_log               := ", r7.greedy_log,
                   "\n");
   PrintTo(stream, ");;\n");
   CloseStream(stream);
   ```

   Critically, omit `r7.data` (HAP contexts + restriction matrices —
   would inflate the file by O(GB)).

3. Run `LoadDVANEAFamily(7)` immediately after to confirm round-trip:

   ```gap
   Read("k4a_classify.g");
   subgroups := LoadDVANEAFamily(7);
   if subgroups = fail then
     Error("post-rerun: LoadDVANEAFamily(7) still returns fail");
   fi;
   ```

4. Commit the result.g + log; close issue #397 referencing the rerun
   wall + chosen family.

**Recommendation**: bundle steps 1-3 into a wrapper driver
`scripts/run_dvan_m7_production.g` in a follow-up PR. Out of scope for
this readiness brief (no code changes per task constraints).

## 6. Expected chosen family

We do NOT predict an exact family because the streaming-greedy at m=7
samples 1000 of 9 845 550 Lagrangians; the result depends on the RNG
seed.

What we DO predict (with high confidence):

- `final_ker = 1` (joint restriction injective).
- `locally_tight = true` (each EA needed).
- `ea_count` likely in [6, 12] range. PR #290's run with the pre-#379
  greedy gave 8 EAs; the F_2-first greedy may pick slightly more or
  fewer depending on how the F_2 plateau aligns with Z/4 torsion.
- `family_size = ea_count + 2` (D_8 + Q_8 both present at m=7).
- `total_lagrangians = 9 845 550` (full Witt enumeration always
  completes; only the sample is random).
- `wall_seconds < 5 400` (90 min), almost certainly under 30 min.

The PR #318 M-binom conjecture predicts 30 EAs at m=7, which would
suggest the 1000-sample is too small. The PR #290 run's 8-EA verdict
already refuted that prediction (sample greedy is upper-bounded by
the true minimum). The fresh rerun will reconfirm the upper bound,
likely in the 6-12 range.

## 7. Suggested launch protocol

### Current state of competing workloads

- **A-5b m=5 production**: PID 87863 (re-launch of the workload
  noted in CLAUDE.md as PID 79240). CPU: 99%, RES: ~26 GB. Step 4
  cross-check stuck on per-vec wall (issue #387).
- **Host memory**: 64 GB total, ~38 GB headroom currently.

### Compatibility analysis

D-VAN m=7 needs ~2 GB peak (`-o 16g` capped). A-5b uses ~26 GB.
**Side-by-side is comfortable**:
- 26 + 16 = 42 GB < 64 GB physical; no swap pressure.
- A-5b is CPU-bound on a single thread; D-VAN m=7 is also single-thread
  GAP. On an 8+ core Mac (M2 Max per `hap_lhs_resolution.g:75`) the
  two won't contend for CPU.

### Recommendation: run side-by-side

Killing A-5b first would lose ~16 minutes of computation (per current
ps output `16:15.41` user time on PID 87863). It is sufficiently
mid-flight that interrupting is costly; restart would re-do the
expensive Step 1 setup (post-#383 the cache load itself was 2h).

D-VAN m=7 at ~15-30 min wall will complete before A-5b makes
material new progress (A-5b's stuck per-vec wall in #387 is on the
order of hours).

**Decision tree**:

- **If A-5b m=5 is making progress that the user wants to preserve**:
  launch D-VAN m=7 side-by-side. Expected completion ~30 min wall;
  no impact on A-5b throughput beyond memory pressure (negligible)
  and shared LLVM-libomp-style page-cache contention (probably
  unmeasurable on this workload).

- **If A-5b m=5 is stalled per #387 (which CLAUDE.md describes as
  "stuck on per-vec wall")**: the user may want to kill it anyway
  and look at the stall before relaunching. In that case, launch
  D-VAN m=7 first (30 min) then dig into A-5b.

- **If the user wants maximum throughput on D-VAN m=7**: kill A-5b
  first. Saves zero wall on the m=7 path (no CPU contention) but
  removes the ~26 GB heap competitor.

**Default proposal**: run side-by-side, do not interrupt A-5b. The
~15-30 min D-VAN m=7 rerun is short enough that the cost-of-waiting
is small.

### Launch checklist

1. Confirm A-5b PID + memory before launch (verify no other
   competing job has spun up).
2. Optionally rename the existing `result.g` to
   `result_pre380_pr361.g` for clean diffing.
3. Issue the launch command in §0.5. Capture PID via the shell.
4. Tail `/tmp/dvan_m7_rerun_*.log` for the "LHS resolution + UCT"
   line, then for the "streaming Witt enumeration" line, then for
   the "building 1000 per-sample restriction matrices" progress
   lines (every 100 matrices).
5. On completion (test summary line `=== test_dvan_trimmed_family:
   PASS ===` or `... FAIL ...`), persist `r7` via the §5 protocol.
6. Verify `LoadDVANEAFamily(7)` round-trips.
7. Commit + close #397.

## 8. References

- PR #379 `7e15413`: F_2-first greedy + incremental RREF state.
- PR #380 `2b7bb18`: ea_generators persistence + LoadDVANEAFamily.
- PR #290 / #361 `7b7fbbb`: previous m=7 production result.
- `extraspecial_orbifolds/scripts/detecting_family_restriction.g`:
  - L. 441-468 `_DETF_BuildSetupG_LHS`.
  - L. 1685-2131 `_DETF_TrimmedFamily_m7_streaming`.
  - L. 2103-2129 result rec construction with `ea_generators` at L. 2112.
- `extraspecial_orbifolds/scripts/k4a_classify.g`:
  - L. 280-319 `LoadDVANEAFamily(m)`.
- `extraspecial_orbifolds/scripts/tests/test_dvan_trimmed_family.g`:
  - T3/T4 m=2/m=3 anchors; T7 LHS cross-validation; T8 m=7 reachability.
- `extraspecial_orbifolds/scripts/tests/test_dvan_m7_ea_generator_persist.g`:
  - T1/T2/T3 persistence checks.
- `extraspecial_orbifolds/docs/superpowers/research/2026-05-20-minimal-detecting-family.md`:
  the math context (k_min(2) = 5, k_min(3) = 8, m=5/m=7 open).
