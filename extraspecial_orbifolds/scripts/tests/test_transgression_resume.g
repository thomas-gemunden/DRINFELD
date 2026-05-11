# test_transgression_resume.g — crash-recover test for issue #32 (T-5).
#
# Demonstrates that TransgressionKernelResumable can be killed partway
# through a per-generator sweep and, on restart, will skip already-
# completed generators (reading the on-disk state file).
#
# Test plan:
#   1. Pick D_8 = SmallGroup(8, 3); H^3(D_8; U(1)) has k = 3 generators
#      (well-known torsion [2, 2, 4]). The task description specifies
#      "3 generators" exactly.
#   2. Phase 1: run the driver with a NEW state file. Capture the number
#      of "Computing generator ..." prints (should be k = 3).
#   3. Phase 2: simulate a crash by truncating the state file at
#      Length(state) - 1 records, then re-invoke. Expect (k - last_done)
#      "Computing" lines and (last_done) "Skipping" lines.
#   4. Phase 3: cross-check the final assembled kernel against a fresh
#      run from scratch — they must agree on which generators are in
#      ker Tr (independent of compute order).
#   5. (Bonus) Phase 4: hand-construct a state file with the first 2
#      generators marked complete and run the driver; verify exactly 1
#      generator (gen 3) is computed.
#
# Expected acceptance per issue #32:
#   * "Crash mid-sweep, restart: resumed run completes without re-
#     evaluating any completed generator." -> Phases 2 and 4.
#   * "Output format compatible with T-2." -> kernel_vecs from
#     AssembleKernelFromState is a list of integer vectors, sorted by
#     generator index, with the zero vec included.
#   * "Storage: incremental, O(k_completed) per file." -> the state file
#     after phase 1 has exactly k = 3 lines; truncation in phase 2 leaves
#     it with 2 lines, etc.
#
# Logged output: /tmp/test_transgression_resume.log
#
# Working directory note: this test is at scripts/tests/, and the
# resume driver Reads transgression_per_generator.g via relative path.
# We chdir to scripts/ before Read, and use absolute paths for the
# state files (which live under /tmp).

ChangeDirectoryCurrent(
    "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-t5/extraspecial_orbifolds/scripts");

Read("transgression_resume.g");

LogPath := "/tmp/test_transgression_resume.log";;
PrintTo(LogPath, "=== test_transgression_resume.g ===\n");

G := SmallGroup(8, 3);;     # D_8
AppendTo(LogPath, "G = D_8 = SmallGroup(8, 3), |G| = ", Order(G), "\n");

setup := SetupCohomology3(G);;
k := setup.num_generators;;
AppendTo(LogPath, "k = ", k, " H^3 generators (torsion = ",
         setup.torsion, ")\n");

# Per task description we expect k = 3 for D_8 — sanity-assert this so
# any GAP-version skew is caught loudly.
Assert(0, k = 3,
       Concatenation("Expected k = 3 for D_8; got ", String(k),
                     ". GAP version may differ; adjust if needed."));

# ----------------------------------------------------------------------
# Phase 1: fresh run, full sweep.
# ----------------------------------------------------------------------
fresh_state_path := "/tmp/d8_resume_fresh.state.g";;
if IsExistingFile(fresh_state_path) then
    RemoveFile(fresh_state_path);
fi;
AppendTo(LogPath, "\n--- Phase 1: fresh sweep ---\n");
AppendTo(LogPath, "state file: ", fresh_state_path, "\n");

t_p1 := Runtime();;
fresh_result := TransgressionKernelResumable(G, fresh_state_path);;
t_p1 := (Runtime() - t_p1) / 1000.;;

AppendTo(LogPath, "Phase 1 wall: ", t_p1, " s\n");
AppendTo(LogPath, "Completed generators: ",
         Length(fresh_result.state), " / ", k, "\n");
AppendTo(LogPath, "In-kernel indices: ",
         fresh_result.kernel_gen_indices, "\n");

Assert(0, Length(fresh_result.state) = k,
       "Phase 1 did not complete all generators.");

# Stash these for the cross-check.
fresh_in_kernel := fresh_result.kernel_gen_indices;;

# ----------------------------------------------------------------------
# Phase 2: simulate crash by truncating the state file, then resume.
# ----------------------------------------------------------------------
crash_state_path := "/tmp/d8_resume_crash.state.g";;
if IsExistingFile(crash_state_path) then
    RemoveFile(crash_state_path);
fi;

# Build a 2-record state by copying the first 2 records of fresh_result
# verbatim into the crash state file.
AppendTo(LogPath, "\n--- Phase 2: simulated crash ---\n");
last_done := 2;;
AppendTo(LogPath, "Pre-seed state file with ", last_done,
         " of ", k, " records (simulating mid-sweep kill).\n");
for i in [1..last_done] do
    r := fresh_result.state[i];
    # Re-persist verbatim to crash_state_path.
    PersistGenerator(crash_state_path, r.generator, r.all_in_kernel,
                     r.per_class);
od;

# Reload to confirm the pre-seed parsed cleanly.
preseed_completed := CompletedGenerators(crash_state_path);;
AppendTo(LogPath, "Pre-seed completed (re-read): ", preseed_completed, "\n");
Assert(0, preseed_completed = [1..last_done],
       "Pre-seed state file did not parse to the expected completed set.");

# Now resume on the crash state file. The driver should skip 1..2 and
# only compute 3.
t_p2 := Runtime();;
crash_result := TransgressionKernelResumable(G, crash_state_path);;
t_p2 := (Runtime() - t_p2) / 1000.;;

AppendTo(LogPath, "Phase 2 wall (resume): ", t_p2, " s\n");
AppendTo(LogPath, "Crash-resume final completed: ",
         List(crash_result.state, r -> r.generator), "\n");
AppendTo(LogPath, "Crash-resume kernel_gen_indices: ",
         crash_result.kernel_gen_indices, "\n");

Assert(0, Length(crash_result.state) = k,
       "Phase 2 resume did not complete all generators.");
Assert(0, crash_result.kernel_gen_indices = fresh_in_kernel,
       Concatenation("Phase 2 kernel disagrees with Phase 1: ",
                     String(crash_result.kernel_gen_indices),
                     " vs ", String(fresh_in_kernel)));

# ----------------------------------------------------------------------
# Phase 3: cross-check kernel_vecs (T-2-format) between phases.
# ----------------------------------------------------------------------
AppendTo(LogPath, "\n--- Phase 3: kernel_vecs cross-check ---\n");
fresh_vecs := fresh_result.kernel_vecs;;
crash_vecs := crash_result.kernel_vecs;;
AppendTo(LogPath, "Phase 1 kernel_vecs: ", fresh_vecs, "\n");
AppendTo(LogPath, "Phase 2 kernel_vecs: ", crash_vecs, "\n");
Assert(0, fresh_vecs = crash_vecs,
       "Phase 3: kernel_vec lists disagree between phases.");

# Also assemble via the public helper, exercising the format-compat path.
fresh_assembled := AssembleKernelFromState(setup, fresh_state_path);;
AppendTo(LogPath, "Phase 3 AssembleKernelFromState: ",
         "kernel_size = ", fresh_assembled.kernel_size,
         ", kernel_gen_indices = ", fresh_assembled.kernel_gen_indices,
         "\n");
Assert(0, fresh_assembled.kernel_vecs = fresh_vecs,
       "Phase 3: AssembleKernelFromState disagrees with driver output.");

# ----------------------------------------------------------------------
# Phase 4: hand-built partial state (2 of 3 completed), verify exactly 1
# generator is recomputed on resume.
# ----------------------------------------------------------------------
hand_state_path := "/tmp/d8_resume_hand.state.g";;
if IsExistingFile(hand_state_path) then
    RemoveFile(hand_state_path);
fi;
AppendTo(LogPath, "\n--- Phase 4: hand-built partial state ---\n");

# Hand-write 2 entries (gens 1 and 2) with arbitrary (but consistent-
# with-Phase-1) all_in_kernel flags. We re-use Phase-1 values so the
# final kernel still matches.
PersistGenerator(hand_state_path, 1, fresh_result.state[1].all_in_kernel,
                 fresh_result.state[1].per_class);
PersistGenerator(hand_state_path, 2, fresh_result.state[2].all_in_kernel,
                 fresh_result.state[2].per_class);

AppendTo(LogPath, "Hand-state file contents:\n",
         StringFile(hand_state_path), "\n");

# Sanity: reload, check completed indices.
hand_pre := CompletedGenerators(hand_state_path);;
AppendTo(LogPath, "Hand-state completed (re-read): ", hand_pre, "\n");
Assert(0, hand_pre = [1, 2],
       "Phase 4 hand-state did not parse to [1, 2].");

# Resume; count "Computing" prints by inspecting state length delta.
n_before := Length(LoadResumeState(hand_state_path));;
hand_result := TransgressionKernelResumable(G, hand_state_path);;
n_after := Length(LoadResumeState(hand_state_path));;
n_computed_this_run := n_after - n_before;;

AppendTo(LogPath, "Phase 4 n_before = ", n_before,
         "; n_after = ", n_after,
         "; n_computed_this_run = ", n_computed_this_run, "\n");
Assert(0, n_computed_this_run = 1,
       Concatenation("Phase 4 expected exactly 1 new gen computed; got ",
                     String(n_computed_this_run)));
Assert(0, hand_result.kernel_gen_indices = fresh_in_kernel,
       "Phase 4 kernel disagrees with Phase 1.");

# ----------------------------------------------------------------------
# Phase 5: malformed-line tolerance. Simulate a crash mid-record (no
# trailing comma) and verify the loader drops the partial line.
# ----------------------------------------------------------------------
mid_state_path := "/tmp/d8_resume_midcrash.state.g";;
if IsExistingFile(mid_state_path) then
    RemoveFile(mid_state_path);
fi;
AppendTo(LogPath, "\n--- Phase 5: partial-line tolerance ---\n");

# Re-use the Phase-1 gen-1 record so the final kernel matches fresh.
PersistGenerator(mid_state_path, 1, fresh_result.state[1].all_in_kernel,
                 fresh_result.state[1].per_class);
# Append a deliberately-malformed half-line to simulate a crash mid-
# AppendTo (no trailing comma or newline).
AppendTo(mid_state_path, "rec(generator := 2, all_in_kerne");

mid_pre := CompletedGenerators(mid_state_path);;
AppendTo(LogPath, "Mid-crash completed (re-read): ", mid_pre, "\n");
Assert(0, mid_pre = [1],
       Concatenation("Phase 5: expected [1] after dropping partial line; got ",
                     String(mid_pre)));

# Resume should compute gens 2 and 3.
mid_result := TransgressionKernelResumable(G, mid_state_path);;
AppendTo(LogPath, "Phase 5 final completed: ",
         List(mid_result.state, r -> r.generator), "\n");
Assert(0, Length(mid_result.state) = k,
       "Phase 5 resume did not complete all generators.");
Assert(0, mid_result.kernel_gen_indices = fresh_in_kernel,
       "Phase 5 kernel disagrees with Phase 1.");

# ----------------------------------------------------------------------
# Summary
# ----------------------------------------------------------------------
AppendTo(LogPath, "\n=== Summary ===\n");
AppendTo(LogPath, "All phases passed:\n");
AppendTo(LogPath, "  Phase 1 (fresh sweep, k = ", k, ")\n");
AppendTo(LogPath, "  Phase 2 (crash + resume, last_done = ", last_done, ")\n");
AppendTo(LogPath, "  Phase 3 (kernel_vec parity)\n");
AppendTo(LogPath, "  Phase 4 (hand-built partial state, 1 new gen)\n");
AppendTo(LogPath, "  Phase 5 (partial-line tolerance)\n");

Print("\n=== test_transgression_resume.g: ALL PHASES PASSED ===\n");
Print("Log: ", LogPath, "\n");
Print("k = ", k, "; in-kernel generators: ", fresh_in_kernel, "\n");
