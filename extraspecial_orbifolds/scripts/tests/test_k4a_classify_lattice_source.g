# test_k4a_classify_lattice_source.g
#
# Tests the K4aClassify opts.lattice_source = true path added in
# #316 (K-4a follow-ups). The acceptance criterion is:
#
#   K4aClassify(m, rec(lattice_source := true))   at omega = 0
#   produces the SAME verdict as the default K4aClassify(m).
#
# This is the K-3-style cross-validation that the dispatch text
# explicitly calls out: at omega = 0 the KR-bridge path
# (BuildKRRIntertwinerData) is numerically equivalent to the
# untwisted-baseline path (BuildIntertwinerDataUntwisted), so verdicts
# must agree. Routing K-4a through the lattice path is the prerequisite
# for omega-twisted K-4 verdicts (which require V-1's `EpsilonOmegaPhase`
# already wired into BuildKRRIntertwinerData; see test_epsilon_omega_phase.g).
#
# Run:
#   gap -q -b .../tests/test_k4a_classify_lattice_source.g

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
    Error("test_k4a_classify_lattice_source.g: INPUT_FILENAME() unavailable; ",
          "Read the file by its absolute path.");
fi;
T_SELFDIR := T_SELF{[1..Length(T_SELF)
                      - Length("/test_k4a_classify_lattice_source.g")]};;
T_SCRIPTSDIR := T_SELFDIR{
    [1..Length(T_SELFDIR) - Length("/tests")]};;
T_WT_ROOT := T_SCRIPTSDIR{
    [1..Length(T_SCRIPTSDIR) - Length("/extraspecial_orbifolds/scripts")]};;

# ---- Load deps ---------------------------------------------------------
# Same prep as test_k4a_classify.g: load modular_data.g first so that
# LoadModularData is bound, then k4a_classify.g, then the build_krr
# bridge.

Read(Concatenation(T_WT_ROOT, "/src/modular_data.g"));
TAssertTrue("LoadModularData bound", IsBound(LoadModularData));

Read(Concatenation(T_SCRIPTSDIR, "/untwisted_modular_data.g"));
Read(Concatenation(T_SCRIPTSDIR, "/krr_projector.g"));
Read(Concatenation(T_SCRIPTSDIR, "/build_krr_intertwiner_data.g"));
TAssertTrue("BuildKRRIntertwinerData bound (pre-K4a load)",
            IsBound(BuildKRRIntertwinerData));

Read(Concatenation(T_SCRIPTSDIR, "/k4a_classify.g"));
TAssertTrue("K4aClassify bound", IsBound(K4aClassify));

# ---- modular_data symlink + chdir, same as test_k4a_classify.g --------

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
    Error("test_k4a_classify_lattice_source.g: cannot locate modular_data tree.");
fi;
T_LINKDIR := Concatenation(T_SELFDIR, "/k4a/lattice_source");;
if not IsExistingFile(T_LINKDIR) then
    Exec(Concatenation("mkdir -p '", T_LINKDIR, "'"));
fi;
T_LINKPATH := Concatenation(T_LINKDIR, "/Modular_Data");;
if not IsExistingFile(T_LINKPATH) then
    Exec(Concatenation("ln -s '", T_MD_ROOT, "' '",
                       T_LINKPATH, "'"));
fi;
ChangeDirectoryCurrent(T_LINKDIR);

# ---- T1: m = 2 — opts.lattice_source = true gives the same verdict ----

Print("\n=================================================================\n");
Print("T1: m = 2, lattice_source = true vs default\n");
Print("=================================================================\n");

T1_DEFAULT := K4aClassify(2);;
T1_LATTICE := K4aClassify(2, rec(lattice_source := true));;

TAssertEqual("T1a: default verdict = lattice verdict (m = 2)",
             T1_LATTICE.verdict, T1_DEFAULT.verdict);
TAssertEqual("T1b: default trivial = lattice trivial (m = 2)",
             T1_LATTICE.trivial, T1_DEFAULT.trivial);
TAssertEqual("T1c: default E.is_coboundary = lattice E.is_coboundary",
             T1_LATTICE.E_class.is_coboundary,
             T1_DEFAULT.E_class.is_coboundary);
TAssertEqual("T1d: default D8.class_idx = lattice D8.class_idx",
             T1_LATTICE.D8_class.class_idx,
             T1_DEFAULT.D8_class.class_idx);
TAssertEqual("T1e: default Q8.class_idx = lattice Q8.class_idx",
             T1_LATTICE.Q8_class.class_idx,
             T1_DEFAULT.Q8_class.class_idx);
TAssertEqual("T1f: lattice verdict = 'trivial' (Keller alpha = 0 at m=2)",
             T1_LATTICE.verdict, "trivial");
TAssertTrue("T1g: lattice opts record retained on result",
            IsBound(T1_LATTICE.opts)
            and T1_LATTICE.opts.lattice_source = true);
TAssertTrue("T1h: default opts.lattice_source = false",
            IsBound(T1_DEFAULT.opts)
            and T1_DEFAULT.opts.lattice_source = false);

# ---- T2: spectral_source forwarding sanity ----------------------------

Print("\n=================================================================\n");
Print("T2: spectral_source = lite is the default when lattice_source = true\n");
Print("=================================================================\n");

T2_LATTICE_LITE := K4aClassify(2, rec(lattice_source := true,
                                       spectral_source := "lite"));;
TAssertEqual("T2: explicit spectral_source = lite agrees with default",
             T2_LATTICE_LITE.verdict, T1_LATTICE.verdict);

# ---- T3: omega_vec = fail without lattice_source errors ---------------

Print("\n=================================================================\n");
Print("T3: omega_vec is rejected when lattice_source = false (with error)\n");
Print("=================================================================\n");

T3_SAVE := BreakOnError;;
BreakOnError := false;;
T3_OUT := CALL_WITH_CATCH(K4aClassify,
                          [2, rec(lattice_source := false,
                                    omega_vec := [0, 0, 0, 0, 0, 0])]);;
BreakOnError := T3_SAVE;;
TAssertEqual("T3: omega_vec without lattice_source errored (caught)",
             T3_OUT[1], false);

# ---- T4: m = 3 cross-validation (the canonical anchor) ----------------
# This is the high-confidence test: K-4a-T7's m=3 anchor must hold
# under the lattice-source path at omega = 0. We skip if FAST=1
# (m=3 lattice path traverses the full E_+(3) for three branches,
# ~10x cost of the m=2 case).

T4_FAST := false;;
T4_FAST_ENV := IO_getenv("FAST");
if T4_FAST_ENV <> fail and T4_FAST_ENV = "1" then
    T4_FAST := true;
fi;
if not T4_FAST then
    Print("\n=================================================================\n");
    Print("T4: m = 3, lattice_source = true vs default (FAST=0 only)\n");
    Print("=================================================================\n");
    T4_DEFAULT := K4aClassify(3);;
    T4_LATTICE := K4aClassify(3, rec(lattice_source := true));;
    TAssertEqual("T4: default verdict = lattice verdict (m = 3)",
                 T4_LATTICE.verdict, T4_DEFAULT.verdict);
    TAssertEqual("T4: lattice verdict = 'trivial' at m = 3 (K-4a-T7 anchor)",
                 T4_LATTICE.verdict, "trivial");
else
    Print("\n[SKIP] T4 (m=3 cross-validation) — FAST=1.\n");
fi;

# ---- Summary ----------------------------------------------------------

Print("\n=================================================================\n");
Print("Summary: ", T_PASSES, " passes, ", Length(T_FAILURES), " failures.\n");
Print("=================================================================\n");
if Length(T_FAILURES) > 0 then
    Print("\nFailures:\n");
    for T_F in T_FAILURES do
        Print("  - ", T_F, "\n");
    od;
    Error("test_k4a_classify_lattice_source.g: ",
          Length(T_FAILURES), "/", T_PASSES + Length(T_FAILURES),
          " assertions failed.");
fi;
Print("\nPASS test_k4a_classify_lattice_source\n");
