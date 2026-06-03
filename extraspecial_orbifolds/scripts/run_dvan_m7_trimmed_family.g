# run_dvan_m7_trimmed_family.g — production driver for D-VAN m=7
# minimum detecting family. Issue #427.
#
# Calls _DETF_TrimmedFamily(7, ...) and persists the result to
# computed/dvan_min_family/m7/result.g with the `ea_generators` field
# populated (PR #380 / issue #377 schema). The previous m=7 result
# committed via PR #361 (2026-05-24) predates that schema and lacks the
# field, so `LoadDVANEAFamily(7)` returns `fail` and K-4a at m=7 falls
# back to a mathematically insufficient single-EA E-branch path.
#
# At m=7, `_DETF_TrimmedFamily` dispatches to the streaming + sampling
# variant `_DETF_TrimmedFamily_m7_streaming` (only the m=7 path samples
# from the 9 845 550 Lagrangians; m in {2, 3, 5} go through the eager
# path). The streaming function builds and returns a result rec that
# includes `ea_generators` and `ea_generators_sorted` — pc-element
# tuples that reconstruct each chosen EA subgroup via Subgroup(G, gens).
#
# Usage (background, with redirected stdout/stderr per CLAUDE.md):
#
#   cd extraspecial_orbifolds/scripts
#   nohup /opt/homebrew/bin/gap -q -b -o 16g -c \
#     'Read("run_dvan_m7_trimmed_family.g"); QUIT;' \
#     > /tmp/run_dvan_m7_$(date -u +%Y%m%d_%H%M%S).log 2>&1 &
#
# Tunables (set as globals before Read):
#   DVAN_M7_SAMPLE_SIZE : K = number of sampled Lagrangians (default 1000).
#   DVAN_M7_SEED        : RNG seed for reservoir sampling (default
#                         unset; uses GAP's GlobalMersenneTwister).
#   DVAN_M7_VERBOSE     : pass through to _DETF_TrimmedFamily (default true).
#
# Expected wall: ~2-3 h on top of PR #379's F_2-first greedy at
# sample_size = 1000 (the most recent in-flight rerun PID 2819 wall was
# 2h 14m). Peak heap ~2 GB (the -o 16g cap is generous).
#
# Output:
#   ../computed/dvan_min_family/m7/result.g
#
# Format: top-level `dvan_m7_result := rec(...);;`, written via
# OutputTextFile + SetPrintFormattingStatus(stream, false) to avoid
# the PrintTo autowrap hazard (#43, #46).
#
# Verified after-write: re-Read the file, assert
# `dvan_m7_result.ea_generators` is bound with the expected length.

Read("solver/logging_util.g");
Read("detecting_family_restriction.g");

# --- tunables -----------------------------------------------------------

if not IsBoundGlobal("DVAN_M7_SAMPLE_SIZE") then
    DVAN_M7_SAMPLE_SIZE := 1000;
fi;
if not IsBoundGlobal("DVAN_M7_VERBOSE") then
    DVAN_M7_VERBOSE := true;
fi;

_LogPhase("dvan-m7-driver", "=== run_dvan_m7_trimmed_family.g ===");
_LogPhase("dvan-m7-driver", "DVAN_M7_SAMPLE_SIZE = ", DVAN_M7_SAMPLE_SIZE);
if IsBoundGlobal("DVAN_M7_SEED") then
    _LogPhase("dvan-m7-driver", "DVAN_M7_SEED = ", DVAN_M7_SEED);
else
    _LogPhase("dvan-m7-driver",
              "DVAN_M7_SEED unset (using GlobalMersenneTwister)");
fi;

# Build the opts rec. Only include `seed` when the user provided one;
# otherwise let the streaming driver default to GlobalMersenneTwister.
dvan_m7_opts := rec(
    source      := "lhs",
    sample_size := DVAN_M7_SAMPLE_SIZE,
    verbose     := DVAN_M7_VERBOSE);
if IsBoundGlobal("DVAN_M7_SEED") then
    dvan_m7_opts.seed := DVAN_M7_SEED;
fi;

# --- run ----------------------------------------------------------------

_LogPhase("dvan-m7-driver", "Calling _DETF_TrimmedFamily(7, opts) ...");
t_run := Runtime();;
result := _DETF_TrimmedFamily(7, dvan_m7_opts);;
wall_total := (Runtime() - t_run) / 1000.0;;

_LogPhase("dvan-m7-driver",
          "TrimmedFamily(7) returned after ", wall_total, " s");
_LogPhase("dvan-m7-driver",
          "  result.ea_count      = ", result.ea_count);
_LogPhase("dvan-m7-driver",
          "  result.final_ker     = ", result.final_ker);
_LogPhase("dvan-m7-driver",
          "  result.locally_tight = ", result.locally_tight);
_LogPhase("dvan-m7-driver",
          "  result.family_size   = ", result.family_size);

if not IsBound(result.ea_generators) then
    Error("run_dvan_m7_trimmed_family.g: result lacks ea_generators ",
          "field; _DETF_TrimmedFamily_m7_streaming must be updated.");
fi;
_LogPhase("dvan-m7-driver",
          "  |result.ea_generators| = ", Length(result.ea_generators));

# --- persist ------------------------------------------------------------
#
# Selective field copy: omit `data` (the full BuildRestrictionMatrices-
# style rec, which carries the per-EA HAP contexts and restriction
# matrices; persisting it would produce a multi-MB to multi-GB file).
# Mirror PR #361 / the §5 protocol in the rerun-readiness brief
# (2026-06-01-dvan-m7-rerun-readiness.md).

result_to_persist := rec(
    m                        := result.m,
    source                   := result.source,
    ea_indices_chosen        := result.ea_indices_chosen,
    ea_indices_chosen_sorted := result.ea_indices_chosen_sorted,
    ea_generators            := result.ea_generators,
    ea_generators_sorted     := result.ea_generators_sorted,
    include_D8               := result.include_D8,
    include_Q8               := result.include_Q8,
    final_ker                := result.final_ker,
    ea_count                 := result.ea_count,
    family_size              := result.family_size,
    greedy_log               := result.greedy_log,
    locally_tight            := result.locally_tight,
    drop_one_kers            := result.drop_one_kers,
    walltime_ms              := result.walltime_ms,
    sample_size              := result.sample_size,
    total_lagrangians        := result.total_lagrangians
);;

out_path := "../computed/dvan_min_family/m7/result.g";;
_LogPhase("dvan-m7-driver", "Writing to ", out_path);

stream := OutputTextFile(out_path, false);;
SetPrintFormattingStatus(stream, false);
PrintTo(stream, "# D-VAN m=7 minimum detecting family.\n");
PrintTo(stream, "# Generated by run_dvan_m7_trimmed_family.g ",
                "(issue #427).\n");
PrintTo(stream, "# Wall: ", wall_total, " s.\n");
PrintTo(stream, "# Schema includes ea_generators (PR #380 / issue #377):\n");
PrintTo(stream, "#   dvan_m7_result.ea_generators is a list of pc-element\n");
PrintTo(stream, "#   tuples reconstructing each chosen EA subgroup via\n");
PrintTo(stream, "#   Subgroup(G, gens) against G = setup_G.group from\n");
PrintTo(stream, "#   _DETF_BuildSetupG_LHS(7).\n");
PrintTo(stream, "dvan_m7_result := ", result_to_persist, ";;\n");
CloseStream(stream);

_LogPhase("dvan-m7-driver", "Wrote ", out_path);

# --- post-write verification --------------------------------------------
#
# Re-read the file and assert `dvan_m7_result.ea_generators` is bound
# with the expected length. Guards against any PrintTo autowrap or
# silent-truncation regression.

_LogPhase("dvan-m7-driver", "Verifying post-write readability");
if IsBoundGlobal("dvan_m7_result") then
    UnbindGlobal("dvan_m7_result");
fi;
Read(out_path);
if not IsBoundGlobal("dvan_m7_result") then
    Error("run_dvan_m7_trimmed_family.g: post-write Read failed to ",
          "bind dvan_m7_result");
fi;
if not IsBound(dvan_m7_result.ea_generators) then
    Error("run_dvan_m7_trimmed_family.g: post-write result lacks ",
          "ea_generators (PrintTo may have stripped or truncated it?)");
fi;
if Length(dvan_m7_result.ea_generators) <> result.ea_count then
    Error("run_dvan_m7_trimmed_family.g: post-write |ea_generators| = ",
          Length(dvan_m7_result.ea_generators), " <> ea_count = ",
          result.ea_count);
fi;
_LogPhase("dvan-m7-driver",
          "Post-write verification PASS. |ea_generators| = ",
          Length(dvan_m7_result.ea_generators));
_LogPhase("dvan-m7-driver", "=== DRIVER DONE ===");
