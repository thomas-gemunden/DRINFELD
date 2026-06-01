# transgression_resume.g — resumable per-generator transgression sweep.
#
# Wraps the per-generator transgression test (TestGenerator from
# transgression_per_generator.g, or PerGeneratorTransgressionBRW from
# transgression_per_generator_brw.g) with crash-safe incremental
# persistence:
#
#   * After each generator completes, its result is appended to a state
#     file on disk before moving to the next generator.
#   * On restart, LoadResumeState reads the partial state file and the
#     driver skips any generator whose record is already present.
#
# Acceptance (issue #32):
#   * Crash mid-sweep, restart: resumed run completes without re-evaluating
#     any completed generator.
#   * Output format compatible with T-2 (kernel_vecs files in
#     computed/transgression/<m>/...): once the sweep finishes, the state
#     file can be loaded as a list of records, and AssembleKernelFromState
#     converts that into a kernel-vec list (one e_i per in-kernel gen,
#     plus the zero vec).
#   * Storage: incremental, O(k_completed) entries per file.
#
# State file format (incremental append-safe):
#
#   File contents on disk: a sequence of `rec(...),\n` lines, optionally
#   followed by a trailing list-close. The driver writes one record per
#   completed generator with three fields:
#       generator       — H^3 generator index, 1..k.
#       all_in_kernel   — true iff every c_g for that e_i is a coboundary.
#       per_class       — list of booleans (one per conjugacy class)
#                         indicating whether c_g for e_i is a 2-coboundary.
#                         May be omitted (set to fail) for compactness.
#       timestamp       — DateTimeString() at completion.
#
#   LoadResumeState wraps the on-disk bytes with `local L; L := [` ...
#   `]; return L;` and uses InputTextString + Read to parse, tolerating a
#   trailing comma (always present in append-only mode) and avoiding the
#   need to ever rewrite earlier lines. This way the state file is robust
#   to mid-record crashes — a partially-written final `rec(...)` line is
#   simply dropped by the parser via the recovery shim, and the prior
#   well-formed lines load cleanly. (We additionally truncate any
#   trailing partial line on load; see ParseStateFile.)
#
# Why not just `ReadAsFunction`? The natural GAP-source layout is
#   `local L; L := [ rec(...), rec(...), ... ]; return L;` — but this is
#   not append-safe: every append would need to rewrite the closing
#   bracket. The InputTextString approach below avoids that.
#
# Usage:
#
#   Read("transgression_resume.g");
#   G := SmallGroup(8, 3);;  # D_8 = E_+(1)
#   state_file := "/tmp/d8_resume_state.g";;
#   result := TransgressionKernelResumable(G, state_file);
#
# Crash recovery:
#
#   1. Run sweep, kill GAP partway (e.g. after 2 of 3 generators).
#   2. Inspect state_file: contains 2 `rec(...),` lines.
#   3. Re-Read this file, re-call TransgressionKernelResumable(G, state_file).
#   4. Output: "Skipping generator 1 (already done)", "Skipping generator
#      2 (already done)", "Computing generator 3..." — only gen 3 is
#      recomputed.
#
# Files this Reads:
#   - transgression_per_generator.g (for SetupCohomology3, TestGenerator)
#   - transgression_kernel.g (transitively, for IsCoboundary2 etc.)

if not IsBound(TestGenerator) then
    Read("transgression_per_generator.g");
fi;


# ----------------------------------------------------------------------
# Persistence helpers
# ----------------------------------------------------------------------

# PersistGenerator: append one completed-generator record to `state_file`.
# Uses AppendTo so a crash during the write leaves at worst a malformed
# final line, recoverable by the load-shim (see ParseStateFile).
#
# We deliberately do NOT enclose the entries in `[ ... ]` on write —
# the brackets are added at load time. This keeps appends O(1).
#
# Crash-safety detail: before appending, we check the existing file for
# a trailing newline. If the previous append crashed mid-write leaving
# a partial line without a newline, the next append would otherwise
# glue our new record onto the partial line and produce a malformed
# (but `,`-terminated, hence not droppable) line. By forcing a leading
# newline when the file doesn't end in one, the partial line stays its
# own line and is dropped cleanly by ParseStateFile.
PersistGenerator := function(state_file, gen_idx, all_in_kernel, per_class)
    local per_class_str, existing, needs_newline;
    if per_class = fail then
        per_class_str := "fail";
    else
        per_class_str := String(per_class);
    fi;
    needs_newline := false;
    if IsExistingFile(state_file) then
        existing := StringFile(state_file);
        if existing <> fail and Length(existing) > 0
                and existing[Length(existing)] <> '\n' then
            needs_newline := true;
        fi;
    fi;
    if needs_newline then
        AppendTo(state_file, "\n");
    fi;
    AppendTo(state_file,
             Concatenation("rec(generator := ", String(gen_idx),
                           ", all_in_kernel := ", String(all_in_kernel),
                           ", per_class := ", per_class_str,
                           ", timestamp := \"runtime-", String(Runtime()),
                           "\"),\n"));
end;;


# ParseStateFile: read the raw bytes of `state_file` (a sequence of
# `rec(...),\n` lines) and return the parsed list of records.
#
# Drops any line that doesn't look like a complete record terminator —
# i.e. that doesn't start with "rec(" and end with ",". This filtering
# is the recovery shim that handles partial writes anywhere in the
# file (not just at EOF), as can happen if a crash leaves a partial
# line that a later append glued to.
#
# We wrap the surviving lines in `return [ ... ];` and pass the result
# through ReadAsFunction (on an InputTextString stream), then call the
# returned closure to get the list. A trailing comma inside `[ ... ]`
# is allowed by GAP's parser.
#
# Returns: list of records (possibly empty if file is missing/empty/
# all-malformed).
ParseStateFile := function(state_file)
    local bytes, lines, good, ln, n, content, stream, fn, unwrapped;
    if not IsExistingFile(state_file) then
        return [];
    fi;
    bytes := StringFile(state_file);
    if bytes = fail or Length(bytes) = 0 then
        return [];
    fi;
    # GAP's AppendTo auto-wraps long lines with backslash-newline. Undo it.
    unwrapped := ReplacedString(bytes, "\\\n", "");
    lines := SplitString(unwrapped, "\n");
    good := [];
    for ln in lines do
        n := Length(ln);
        if n >= 5 and ln[n] = ','
                and ln{[1..4]} = "rec(" then
            Add(good, ln);
        fi;
    od;
    if IsEmpty(good) then
        return [];
    fi;
    content := Concatenation("return [ ",
                  Concatenation(List(good,
                      ln -> Concatenation(ln, "\n"))),
                  " ];");
    stream := InputTextString(content);
    fn := ReadAsFunction(stream);
    if fn = fail then
        Error("ParseStateFile: failed to parse surviving lines from ",
              state_file);
    fi;
    return fn();
end;;


# LoadResumeState: thin alias for ParseStateFile that also enforces
# uniqueness (in case of duplicate generator entries, the latest record
# wins). Returns a list of records, sorted by .generator.
LoadResumeState := function(state_file)
    local raw, dedup, r, gen_to_rec, gen_idx;
    raw := ParseStateFile(state_file);
    # Dedup: keep last record per generator index.
    gen_to_rec := rec();
    for r in raw do
        gen_to_rec.(String(r.generator)) := r;
    od;
    dedup := [];
    for gen_idx in RecNames(gen_to_rec) do
        Add(dedup, gen_to_rec.(gen_idx));
    od;
    Sort(dedup, function(a, b) return a.generator < b.generator; end);
    return dedup;
end;;


# CompletedGenerators: convenience accessor — returns the sorted set of
# generator indices already in `state_file`.
CompletedGenerators := function(state_file)
    return Set(LoadResumeState(state_file), r -> r.generator);
end;;


# ----------------------------------------------------------------------
# Driver: resumable per-generator sweep
# ----------------------------------------------------------------------
#
# TransgressionKernelResumable(G, state_file [, use_brw])
#
#   G          : the group (e.g. SmallGroup(8, 3) for D_8).
#   state_file : absolute path. If it exists, generators with records
#                in the file are skipped on this invocation.
#   use_brw    : optional bool. If true and EmGroup(m)-shaped, route per-
#                generator via PerGeneratorTransgressionBRW for speed.
#                Default false (use baseline TestGenerator). The state
#                file format is independent of which path was used to
#                produce a given record.
#
# Returns rec(state, kernel_gen_indices, kernel_vecs, k):
#
#   state               — full list of records from state_file post-run.
#   kernel_gen_indices  — list of i in [1..k] with all_in_kernel = true.
#   kernel_vecs         — list of e_i (unit vectors) for each in-kernel
#                         generator, plus the zero vector. NOTE: this is
#                         NOT the full kernel of Tr in general (which is
#                         the span of the in-kernel generators, possibly
#                         with non-trivial torsion-respecting linear
#                         combinations from generators whose torsion > 2).
#                         For a precise kernel computation, use
#                         TransgressionKernelExact (T-2). This field is
#                         only the "obvious" sub-kernel from individual
#                         generators.
#   k                   — number of H^3 generators.
TransgressionKernelResumable := function(arg)
    local G, state_file, use_brw, setup, classes, k,
          completed_idx, i, gen_result, all_in_kernel, per_class, t_gen,
          state, kernel_gen_indices, zero_vec, e_i, kernel_vecs, BRW_OK;

    G := arg[1];
    state_file := arg[2];
    if Length(arg) >= 3 then
        use_brw := arg[3];
    else
        use_brw := false;
    fi;

    # Optional BRW path needs the per-generator-brw file.
    BRW_OK := use_brw and IsBound(PerGeneratorTransgressionBRW);
    if use_brw and not BRW_OK then
        Print("TransgressionKernelResumable: use_brw=true but ",
              "PerGeneratorTransgressionBRW unbound; falling back ",
              "to baseline TestGenerator.\n");
        use_brw := false;
    fi;

    setup := SetupCohomology3(G);
    classes := ConjugacyClasses(G);
    k := setup.num_generators;

    completed_idx := Set(LoadResumeState(state_file), r -> r.generator);

    Print("\n");
    if IsBoundGlobal("_LogPhase") then
        _LogPhase("transgression-resume",
                  "=== TransgressionKernelResumable ===");
    else
        Print("=== TransgressionKernelResumable ===\n");
    fi;
    Print("Group: ", StructureDescription(G), " (|G| = ", Order(G), ")\n");
    Print("State file: ", state_file, "\n");
    Print("k = ", k, " H^3 generators (torsion = ", setup.torsion, ")\n");
    Print("Already completed: ", Length(completed_idx), " / ", k,
          "  ", completed_idx, "\n");
    if use_brw then
        Print("Using BRW-amortised per-generator path.\n");
    else
        Print("Using baseline TestGenerator path.\n");
    fi;

    # Iterate the remaining generators.
    for i in [1..k] do
        if i in completed_idx then
            Print("Skipping generator ", i, " (already done)\n");
            continue;
        fi;
        Print("Computing generator ", i, "... ");
        t_gen := Runtime();
        if use_brw then
            gen_result := PerGeneratorTransgressionBRW(G, i);
            # gen_result.per_class is already a list of booleans, but the
            # baseline shape uses [j, |C_g|, bool] tuples. We store the
            # booleans verbatim; downstream readers should accept either.
            per_class := gen_result.per_class;
            all_in_kernel := gen_result.all_in_kernel;
        else
            gen_result := TestGenerator(setup, i, classes);
            # gen_result.per_class is a list of [j, |C_g|, bool] tuples.
            # Project to booleans for the persisted record (compact form).
            per_class := List(gen_result.per_class, p -> p[3]);
            all_in_kernel := gen_result.all_in_kernel;
        fi;
        PersistGenerator(state_file, i, all_in_kernel, per_class);
        Print(If_(all_in_kernel, "IN", "NOT"), " kernel  (",
              (Runtime() - t_gen) / 1000., " s)\n");
    od;

    # Final assembly: re-read the state file, project to kernel-gen
    # indices and minimal kernel-vec list.
    state := LoadResumeState(state_file);
    kernel_gen_indices := List(Filtered(state, r -> r.all_in_kernel),
                                r -> r.generator);
    zero_vec := List([1..k], j -> 0);
    kernel_vecs := [zero_vec];
    for i in kernel_gen_indices do
        e_i := List([1..k], j -> 0);
        e_i[i] := 1;
        Add(kernel_vecs, e_i);
    od;
    Print("\nSweep complete.\n");
    Print("  In-kernel generators: ", Length(kernel_gen_indices),
          " / ", k, "  ", kernel_gen_indices, "\n");

    return rec(state := state,
               kernel_gen_indices := kernel_gen_indices,
               kernel_vecs := kernel_vecs,
               k := k);
end;;


# ----------------------------------------------------------------------
# Output-format compatibility: assemble a T-2-style kernel-vec record
# from a completed state file.
# ----------------------------------------------------------------------
#
# AssembleKernelFromState(setup, state_file)
#
# Returns a record with the same shape as
# computed/transgression/<m>/kernel.g but only the per-generator slice
# of the kernel (not the full linear-combination span). For T-2-style
# full-kernel output, prefer TransgressionKernelExact.
AssembleKernelFromState := function(setup, state_file)
    local state, kernel_gen_indices, zero_vec, kernel_vecs, e_i, i, k;
    state := LoadResumeState(state_file);
    kernel_gen_indices := List(Filtered(state, r -> r.all_in_kernel),
                                r -> r.generator);
    k := setup.num_generators;
    zero_vec := List([1..k], j -> 0);
    kernel_vecs := [zero_vec];
    for i in kernel_gen_indices do
        e_i := List([1..k], j -> 0);
        e_i[i] := 1;
        Add(kernel_vecs, e_i);
    od;
    return rec(torsion := setup.torsion,
               exponent := setup.exponent,
               kernel_size := Length(kernel_vecs),
               kernel_vecs := kernel_vecs,
               kernel_gen_indices := kernel_gen_indices,
               note := Concatenation("Per-generator sub-kernel only; ",
                                     "see TransgressionKernelExact for ",
                                     "the full kernel of Tr."));
end;;
