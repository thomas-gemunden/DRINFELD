# test_k4a_dvan_fast_path.g
#
# Tests the D-VAN fast-path skip in K4aClassify introduced in issue
# #426. The fast-path is gated by opts.skip_dvan_fast_path (default
# false: enabled).
#
# Test cases:
#
#   T1. omega = 0 (default opts): fast-path does NOT fire because we
#       pre-skip on _K4A_OmegaIsZero. The result rec has NO
#       dvan_fast_path field. Verdict = "trivial" (Keller alpha = 0).
#
#   T2. For unit generators e_i at m = 2: K4aClassify with fast-path
#       enabled vs disabled returns the same verdict string. Because
#       each unit generator is a non-zero class in H^3, the fast-path
#       observes is_trivial = false and falls through to the full
#       pipeline -- verdicts must match. (Capped at i in {1, 9} for
#       wall-time budget; full sweep gated by FULL=1.)
#
#   T3. Known-trivial-coordinate omega ([2, 0, ..., 0] at m = 2 is
#       the zero class since torsion_G[1] = 2): fast-path triggers,
#       returns dvan_fast_path = true and verdict = "trivial" in
#       under 30 s wall.
#
#   T4. skip_dvan_fast_path := true forces the full pipeline.
#       Verifies the result rec does NOT carry dvan_fast_path = true.
#
# Run from extraspecial_orbifolds/scripts/:
#   gap -q -b tests/test_k4a_dvan_fast_path.g

# ---- Test bookkeeping --------------------------------------------------

T_PASSES   := 0;;
T_FAILURES := [];;

TAssertEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
        T_PASSES := T_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Print("         expected: ", expected, "\n");
        Print("         got:      ", got, "\n");
        Add(T_FAILURES, label);
    fi;
end;;

TAssertTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
        T_PASSES := T_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Add(T_FAILURES, label);
    fi;
end;;

# ---- Locate worktree, scripts, sibling files ---------------------------

T_SELF := INPUT_FILENAME();;
if T_SELF = fail or T_SELF = "stream" then
    Error("test_k4a_dvan_fast_path.g: INPUT_FILENAME() unavailable; ",
          "Read the file by its absolute path.");
fi;
T_SELFDIR := T_SELF{[1..Length(T_SELF)
                      - Length("/test_k4a_dvan_fast_path.g")]};;
T_SCRIPTSDIR := T_SELFDIR{
    [1..Length(T_SELFDIR) - Length("/tests")]};;
T_WT_ROOT := T_SCRIPTSDIR{
    [1..Length(T_SCRIPTSDIR) - Length("/extraspecial_orbifolds/scripts")]};;

# ---- Load deps ---------------------------------------------------------
# Mirror test_k4a_classify_lattice_source.g's load order.

Read(Concatenation(T_WT_ROOT, "/src/modular_data.g"));
TAssertTrue("LoadModularData bound", IsBound(LoadModularData));

Read(Concatenation(T_SCRIPTSDIR, "/untwisted_modular_data.g"));
Read(Concatenation(T_SCRIPTSDIR, "/krr_projector.g"));
Read(Concatenation(T_SCRIPTSDIR, "/build_krr_intertwiner_data.g"));
Read(Concatenation(T_SCRIPTSDIR, "/k4a_classify.g"));
TAssertTrue("K4aClassify bound", IsBound(K4aClassify));

# ---- modular_data symlink + chdir --------------------------------------

T_MD_ROOT := fail;;
for T_CAND in
    [ Concatenation(T_WT_ROOT, "/../modular_data"),
      "/Users/thomasgemunden/Projects/group_cohomology/modular_data" ] do
    if T_MD_ROOT = fail
       and IsExistingFile(Concatenation(T_CAND, "/8/4/1.txt")) then
        T_MD_ROOT := T_CAND;
    fi;
od;
if T_MD_ROOT = fail then
    Error("test_k4a_dvan_fast_path.g: cannot locate modular_data tree.");
fi;
T_LINKDIR := Concatenation(T_SELFDIR, "/k4a/dvan_fast_path");;
if not IsExistingFile(T_LINKDIR) then
    Exec(Concatenation("mkdir -p '", T_LINKDIR, "'"));
fi;
T_LINKPATH := Concatenation(T_LINKDIR, "/Modular_Data");;
if not IsExistingFile(T_LINKPATH) then
    Exec(Concatenation("ln -s '", T_MD_ROOT, "' '",
                       T_LINKPATH, "'"));
fi;
ChangeDirectoryCurrent(T_LINKDIR);

# ---- T1: omega = 0 -> fast-path does NOT fire --------------------------

Print("\n=================================================================\n");
Print("T1: omega = 0 (default opts) -- fast-path skipped via _K4A_OmegaIsZero\n");
Print("=================================================================\n");

T1_T0 := Runtime();;
T1_RES := K4aClassify(2);;
T1_WALL := (Runtime() - T1_T0) / 1000.0;;

Print("\n  T1 wall time: ", T1_WALL, " s\n");

TAssertTrue("T1: K4aClassify(2) returned a record", IsRecord(T1_RES));
TAssertEqual("T1: verdict = 'trivial' (Keller alpha = 0 at m = 2)",
             T1_RES.verdict, "trivial");
TAssertTrue("T1: NO dvan_fast_path field on result (omega = 0 skipped)",
            not IsBound(T1_RES.dvan_fast_path));
TAssertTrue("T1: full-pipeline E_class has modular_ct",
            IsBound(T1_RES.E_class.modular_ct));

# ---- T2: unit generators e_i at m=2 give the same verdict either way ---

Print("\n=================================================================\n");
Print("T2: unit generators e_i agree under fast-path on vs off (m=2)\n");
Print("=================================================================\n");

T2_FULL_ENV := IO_getenv("FULL");;
T2_FULL := T2_FULL_ENV <> fail and T2_FULL_ENV = "1";;
if T2_FULL then
    T2_INDICES := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
else
    T2_INDICES := [1, 9];
fi;
Print("  T2 iterations: ", T2_INDICES, " (set FULL=1 for the full sweep)\n");

for T2_I in T2_INDICES do
    T2_E_I := List([1..10], j -> If_(j = T2_I, 1, 0));
    Print("\n  -- e_", T2_I, " (unit generator) --\n");
    T2_T0 := Runtime();
    T2_FP := K4aClassify(2, rec(lattice_source := true,
                                  omega_vec := T2_E_I));
    T2_W_FP := (Runtime() - T2_T0) / 1000.0;
    Print("    fast-path-on wall:  ", T2_W_FP, " s, verdict = ",
          T2_FP.verdict, "\n");
    T2_T0 := Runtime();
    T2_NO := K4aClassify(2, rec(lattice_source := true,
                                  omega_vec := T2_E_I,
                                  skip_dvan_fast_path := true));
    T2_W_NO := (Runtime() - T2_T0) / 1000.0;
    Print("    fast-path-off wall: ", T2_W_NO, " s, verdict = ",
          T2_NO.verdict, "\n");
    TAssertEqual(
        Concatenation("T2: verdict matches at e_", String(T2_I),
                       " (fast-on vs fast-off)"),
        T2_FP.verdict, T2_NO.verdict);
    TAssertTrue(
        Concatenation("T2: skip_dvan_fast_path=true at e_", String(T2_I),
                       " has NO dvan_fast_path field"),
        not IsBound(T2_NO.dvan_fast_path));
od;

# ---- T3: known-trivial coordinate omega -> fast-path triggers ----------
# torsion_G at m=2 = [2,2,2,2,2,2,2,2,2,8] -> [2, 0, ..., 0] is the
# zero class (2*e_1 = 0 mod torsion_G[1] = 2).

Print("\n=================================================================\n");
Print("T3: known-trivial omega = [2,0,...,0] -- fast-path triggers\n");
Print("=================================================================\n");

T3_OMEGA := List([1..10], j -> If_(j = 1, 2, 0));;
T3_T0 := Runtime();;
T3_RES := K4aClassify(2, rec(lattice_source := true,
                              omega_vec := T3_OMEGA));;
T3_WALL := (Runtime() - T3_T0) / 1000.0;;

Print("\n  T3 wall time: ", T3_WALL, " s\n");

TAssertTrue("T3: K4aClassify(2, [2,0,...,0]) returned a record",
            IsRecord(T3_RES));
TAssertTrue("T3: dvan_fast_path = true on top-level result",
            IsBound(T3_RES.dvan_fast_path)
            and T3_RES.dvan_fast_path = true);
TAssertEqual("T3: is_coboundary = true", T3_RES.is_coboundary, true);
TAssertEqual("T3: verdict = 'trivial'", T3_RES.verdict, "trivial");
TAssertEqual("T3: trivial = true", T3_RES.trivial, true);
TAssertEqual("T3: E_class.is_coboundary = true",
             T3_RES.E_class.is_coboundary, true);
TAssertEqual("T3: D8_class.class_idx = 1",
             T3_RES.D8_class.class_idx, 1);
TAssertEqual("T3: Q8_class.class_idx = 1",
             T3_RES.Q8_class.class_idx, 1);
TAssertTrue("T3: E_class has dvan_fast_path flag",
            IsBound(T3_RES.E_class.dvan_fast_path)
            and T3_RES.E_class.dvan_fast_path = true);
TAssertTrue("T3: D8_class has dvan_fast_path flag",
            IsBound(T3_RES.D8_class.dvan_fast_path)
            and T3_RES.D8_class.dvan_fast_path = true);
TAssertTrue("T3: Q8_class has dvan_fast_path flag",
            IsBound(T3_RES.Q8_class.dvan_fast_path)
            and T3_RES.Q8_class.dvan_fast_path = true);
TAssertEqual("T3: spectral_data.source = 'dvan_fast_path'",
             T3_RES.spectral_data.source, "dvan_fast_path");
TAssertEqual("T3: spectral_data.spectral_call_skipped = true",
             T3_RES.spectral_data.spectral_call_skipped, true);
TAssertTrue("T3: dvan_wall_s is a non-negative float",
            IsBound(T3_RES.dvan_wall_s) and T3_RES.dvan_wall_s >= 0.0);
TAssertTrue("T3: timing.dvan_fast_path present",
            IsBound(T3_RES.timing.dvan_fast_path));
TAssertTrue(Concatenation("T3: wall < 30 s (got ", String(T3_WALL), ")"),
            T3_WALL < 30.0);

# ---- T4: skip_dvan_fast_path = true forces full pipeline ---------------

Print("\n=================================================================\n");
Print("T4: skip_dvan_fast_path = true on the same omega forces full pipeline\n");
Print("=================================================================\n");

T4_T0 := Runtime();;
T4_RES := K4aClassify(2, rec(lattice_source := true,
                              omega_vec := T3_OMEGA,
                              skip_dvan_fast_path := true));;
T4_WALL := (Runtime() - T4_T0) / 1000.0;;

Print("\n  T4 wall time: ", T4_WALL, " s\n");

TAssertTrue("T4: K4aClassify(2, [2,...], skip=true) returned a record",
            IsRecord(T4_RES));
TAssertTrue("T4: NO dvan_fast_path on top-level result (full pipeline)",
            not IsBound(T4_RES.dvan_fast_path));
TAssertEqual("T4: opts.skip_dvan_fast_path retained as true",
             T4_RES.opts.skip_dvan_fast_path, true);
TAssertTrue("T4: spectral_data.source != 'dvan_fast_path'",
            T4_RES.spectral_data.source <> "dvan_fast_path");
TAssertTrue("T4: full-pipeline E_class has modular_ct",
            IsBound(T4_RES.E_class.modular_ct));

# Sanity: at omega = zero-class (just expressed non-canonically), the
# full pipeline at lattice_source = true is also expected to give
# verdict = "trivial". Cross-check.
TAssertEqual("T4: full-pipeline verdict matches fast-path on trivial omega",
             T4_RES.verdict, T3_RES.verdict);

# ---- Summary ----------------------------------------------------------

Print("\n=================================================================\n");
Print("Summary: ", T_PASSES, " passes, ", Length(T_FAILURES), " failures.\n");
Print("=================================================================\n");
if Length(T_FAILURES) > 0 then
    Print("\nFailures:\n");
    for T_F in T_FAILURES do
        Print("  - ", T_F, "\n");
    od;
    Print("\nFAIL test_k4a_dvan_fast_path\n");
    QuitGap(1);
fi;
Print("\nPASS test_k4a_dvan_fast_path\n");
QuitGap(0);
