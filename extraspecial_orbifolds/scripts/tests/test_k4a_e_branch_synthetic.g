# test_k4a_e_branch_synthetic.g - K-4a E-branch synthetic test (#424).
#
# Verifies the abelian-branch (E-branch) classifier path of K-4a can
# distinguish trivial from non-trivial twists when fed SYNTHETIC twisted
# modular data of an elementary abelian (EA) subgroup of E_+(m).
#
# For each m in {2, 3, 5} (m=7 gated, default off):
#   1. Get EA := MaximalElementaryAbelian_E_plus(m).subgroup
#      (|EA| = 2^(m+1) = 8, 16, 64 for m = 2, 3, 5).
#   2. setup_ea := SetupCohomology3(EA)
#      (abelian path -> ResolutionAbelianGroup, num_generators bound).
#   3. For omega_vec = zero vector AND for omega_vec = e_i (i-th unit
#      vector), 1 <= i <= test_count:
#        a. omega_cocycle := StandardCocycleOf(setup_ea, omega_vec).
#        b. val := Gcd(Gcd(omega_vec), setup_ea.exponent);
#           expon := setup_ea.exponent / val.
#        c. modular_ct := ComputeModularData(EA, omega_cocycle, val, expon).
#        d. modular_untwisted := ComputeUntwistedModularData(EA).
#        e. match := JointPermutationMatcher(
#                       modular_untwisted.S, modular_untwisted.T,
#                       modular_ct.S, modular_ct.T).
#        f. Assert:
#             omega_vec = 0   -> match.ok = true  (anchor; ground truth).
#             omega_vec = e_i -> match.ok = false (twist DOES change MD
#                                                  on an EA).
#
# Math premise: for an abelian group A, twisting Z(Vec_A) by any
# non-trivial 3-cocycle alpha changes the modular data (no S/T-relabeling
# can identify Z(Vec^alpha_A) with Z(Vec_A) when [alpha] != 0). This is
# the foundation of the E-branch detection in K-4a: an abelian H^3
# generator is detected as non-trivial iff the H-level twisted modular
# data fails to be untwisted-permutation-equivalent.
#
# Configurable counts:
#   K4A_E_BRANCH_M2_TEST_COUNT  (default 10, full sweep of m=2 EA).
#   K4A_E_BRANCH_M3_TEST_COUNT  (default 20).
#   K4A_E_BRANCH_M5_TEST_COUNT  (default 5, smoke).
#   K4A_E_BRANCH_M7_TEST_COUNT  (default 0, gated; |EA|=256 makes
#                                ComputeModularData O((|EA|*N)^2) slow).
#
# Each count caps at setup_ea.num_generators.
#
# Usage:
#   gap -q -b /Users/.../tests/test_k4a_e_branch_synthetic.g
#
#   # Custom counts:
#   gap -q -b -c 'K4A_E_BRANCH_M2_TEST_COUNT := 10; \
#                 K4A_E_BRANCH_M3_TEST_COUNT := 0; \
#                 K4A_E_BRANCH_M5_TEST_COUNT := 0; \
#                 Read("tests/test_k4a_e_branch_synthetic.g");'
#
# Exit 0 on all GREEN, 1 on any RED.

# ---- Locate worktree, scripts dir --------------------------------------

_TKE_SELF := INPUT_FILENAME();;
if _TKE_SELF = fail or _TKE_SELF = "stream" then
    Error("test_k4a_e_branch_synthetic.g: INPUT_FILENAME() unavailable; ",
          "Read the file by its absolute path.");
fi;
if Length(_TKE_SELF) > 0 and _TKE_SELF[1] <> '/' then
    _TKE_SELF := Filename(DirectoryCurrent(), _TKE_SELF);
fi;
_TKE_SELFDIR := _TKE_SELF{
    [1..Length(_TKE_SELF) - Length("/test_k4a_e_branch_synthetic.g")]};;
_TKE_SCRIPTSDIR := _TKE_SELFDIR{
    [1..Length(_TKE_SELFDIR) - Length("/tests")]};;
_TKE_WT_ROOT := _TKE_SCRIPTSDIR{
    [1..Length(_TKE_SCRIPTSDIR) - Length("/extraspecial_orbifolds/scripts")]};;

# transgression_kernel.g does an unconditional Read of
# "../../src/modular_data.g" using a relative path (legacy fallback when
# loaded by relative path). Chdir to scripts/ before reading deps so
# that fallback path resolves correctly.
ChangeDirectoryCurrent(_TKE_SCRIPTSDIR);

# ---- Load dependencies -------------------------------------------------

Read(Concatenation(_TKE_WT_ROOT, "/src/modular_data.g"));
Read(Concatenation(_TKE_SCRIPTSDIR, "/untwisted_modular_data.g"));
Read(Concatenation(_TKE_SCRIPTSDIR, "/quillen_detecting_subgroup.g"));
Read(Concatenation(_TKE_SCRIPTSDIR, "/transgression_kernel.g"));
Read(Concatenation(_TKE_SCRIPTSDIR, "/joint_permutation_matcher.g"));

# ---- Configurable per-m test counts ------------------------------------

if not IsBoundGlobal("K4A_E_BRANCH_M2_TEST_COUNT") then
    K4A_E_BRANCH_M2_TEST_COUNT := 10;
fi;
if not IsBoundGlobal("K4A_E_BRANCH_M3_TEST_COUNT") then
    K4A_E_BRANCH_M3_TEST_COUNT := 20;
fi;
if not IsBoundGlobal("K4A_E_BRANCH_M5_TEST_COUNT") then
    K4A_E_BRANCH_M5_TEST_COUNT := 5;
fi;
if not IsBoundGlobal("K4A_E_BRANCH_M7_TEST_COUNT") then
    K4A_E_BRANCH_M7_TEST_COUNT := 0;
fi;

_TKE_COUNTS := rec(
    m2 := K4A_E_BRANCH_M2_TEST_COUNT,
    m3 := K4A_E_BRANCH_M3_TEST_COUNT,
    m5 := K4A_E_BRANCH_M5_TEST_COUNT,
    m7 := K4A_E_BRANCH_M7_TEST_COUNT
);;

# ---- Per-m runner ------------------------------------------------------

_TKE_RunForM := function(m, test_count_req)
    local ea_rec, EA, setup_ea, k, test_count, results, t0_m,
          omega_vec_zero, anchor_res, i, omega_vec, t0_i, omega_cocycle,
          val, expon, modular_ct, modular_untwisted, match, wall_i,
          this_pass, this_fail, want_ok, label, wall_m,
          n_pass, n_fail, num_tests;

    Print("\n=================================================================\n");
    Print("=== m = ", m, " : E-branch synthetic test ===\n");
    Print("=================================================================\n");

    if test_count_req <= 0 then
        Print("  [skipped] test count = ", test_count_req, " for m=", m, "\n");
        return rec(m := m, pass := 0, fail := 0, total := 0,
                    wall := 0.0, skipped := true);
    fi;

    t0_m := Runtime();
    ea_rec := MaximalElementaryAbelian_E_plus(m);
    EA := ea_rec.subgroup;
    Print("  |EA(m=", m, ")| = ", Order(EA),
          " (rank ", ea_rec.rank, ")\n");

    setup_ea := SetupCohomology3(EA);
    k := setup_ea.num_generators;
    Print("  setup_ea.num_generators = ", k,
          ", exponent = ", setup_ea.exponent,
          ", num_h3_classes = ", setup_ea.num_h3_classes, "\n");

    test_count := Minimum(test_count_req, k);
    if test_count < test_count_req then
        Print("  [note] requested ", test_count_req,
              " unit vectors, but EA has only ", k, " H^3 generators; ",
              "capping at ", test_count, "\n");
    fi;

    n_pass := 0;
    n_fail := 0;
    results := [];

    # ---- omega = 0 anchor ----
    omega_vec_zero := ListWithIdenticalEntries(k, 0);
    t0_i := Runtime();
    omega_cocycle := StandardCocycleOf(setup_ea, omega_vec_zero);
    val := Gcd(Gcd(omega_vec_zero), setup_ea.exponent);
    expon := setup_ea.exponent / val;
    modular_ct := ComputeModularData(EA, omega_cocycle, val, expon);
    modular_untwisted := ComputeUntwistedModularData(EA);
    match := JointPermutationMatcher(
                modular_untwisted.S, modular_untwisted.T,
                modular_ct.S, modular_ct.T);
    wall_i := (Runtime() - t0_i) / 1000.;
    if match.ok = true then
        n_pass := n_pass + 1;
        Print("  PASS: m=", m, " omega=0 anchor -> matcher.ok = true ",
              "(wall ", wall_i, " s)\n");
    else
        n_fail := n_fail + 1;
        Print("  FAIL: m=", m, " omega=0 anchor -> matcher.ok = ",
              match.ok, " (expected true!) wall ", wall_i, " s\n");
        if IsBound(match.reason) then
            Print("        reason: ", match.reason, "\n");
        fi;
    fi;
    Add(results, rec(label := "anchor", i := 0,
                     ok := match.ok, want := true, wall := wall_i));

    # ---- e_i unit vectors ----
    for i in [1..test_count] do
        omega_vec := ListWithIdenticalEntries(k, 0);
        omega_vec[i] := 1;
        t0_i := Runtime();
        omega_cocycle := StandardCocycleOf(setup_ea, omega_vec);
        val := Gcd(Gcd(omega_vec), setup_ea.exponent);
        expon := setup_ea.exponent / val;
        modular_ct := ComputeModularData(EA, omega_cocycle, val, expon);
        modular_untwisted := ComputeUntwistedModularData(EA);
        match := JointPermutationMatcher(
                    modular_untwisted.S, modular_untwisted.T,
                    modular_ct.S, modular_ct.T);
        wall_i := (Runtime() - t0_i) / 1000.;
        # For a non-zero e_i on an abelian group, the twisted modular
        # data must NOT match the untwisted one (matcher.ok = false).
        want_ok := false;
        if match.ok = want_ok then
            n_pass := n_pass + 1;
            Print("  PASS: m=", m, " e_", i, "/", test_count,
                  " -> matcher.ok = false (wall ", wall_i, " s)\n");
        else
            n_fail := n_fail + 1;
            Print("  FAIL: m=", m, " e_", i, "/", test_count,
                  " -> matcher.ok = ", match.ok,
                  " (expected false!) wall ", wall_i, " s\n");
        fi;
        Add(results, rec(label := Concatenation("e_", String(i)),
                         i := i,
                         ok := match.ok, want := want_ok,
                         wall := wall_i));
    od;

    wall_m := (Runtime() - t0_m) / 1000.;
    num_tests := 1 + test_count;
    Print("  --- m=", m, " summary: ", n_pass, "/", num_tests,
          " pass, ", n_fail, "/", num_tests, " fail, wall ",
          wall_m, " s ---\n");
    return rec(m := m, pass := n_pass, fail := n_fail,
                total := num_tests, wall := wall_m,
                skipped := false, results := results);
end;;

# ---- Main run ----------------------------------------------------------

Print("=================================================================\n");
Print("test_k4a_e_branch_synthetic.g (K-4a E-branch synthetic, #424)\n");
Print("=================================================================\n");
Print("config: m2=", _TKE_COUNTS.m2,
      ", m3=", _TKE_COUNTS.m3,
      ", m5=", _TKE_COUNTS.m5,
      ", m7=", _TKE_COUNTS.m7, " unit vectors per m\n");

_TKE_T_TOTAL := Runtime();;
_TKE_PER_M_RESULTS := [];;

Add(_TKE_PER_M_RESULTS, _TKE_RunForM(2, _TKE_COUNTS.m2));
Add(_TKE_PER_M_RESULTS, _TKE_RunForM(3, _TKE_COUNTS.m3));
Add(_TKE_PER_M_RESULTS, _TKE_RunForM(5, _TKE_COUNTS.m5));
if _TKE_COUNTS.m7 > 0 then
    Add(_TKE_PER_M_RESULTS, _TKE_RunForM(7, _TKE_COUNTS.m7));
fi;

_TKE_WALL_TOTAL := (Runtime() - _TKE_T_TOTAL) / 1000.;;

# ---- Final summary ----

Print("\n=================================================================\n");
Print("FINAL SUMMARY\n");
Print("=================================================================\n");

_TKE_TOTAL_PASS := 0;;
_TKE_TOTAL_FAIL := 0;;
_TKE_TOTAL_RUN  := 0;;
for _TKE_R in _TKE_PER_M_RESULTS do
    if _TKE_R.skipped then
        Print("  m=", _TKE_R.m, ": SKIPPED (count = 0)\n");
    else
        Print("  m=", _TKE_R.m, ": ", _TKE_R.pass, "/", _TKE_R.total,
              " pass, ", _TKE_R.fail, "/", _TKE_R.total, " fail, wall ",
              _TKE_R.wall, " s\n");
        _TKE_TOTAL_PASS := _TKE_TOTAL_PASS + _TKE_R.pass;
        _TKE_TOTAL_FAIL := _TKE_TOTAL_FAIL + _TKE_R.fail;
        _TKE_TOTAL_RUN  := _TKE_TOTAL_RUN  + _TKE_R.total;
    fi;
od;
Print("\nTotal: ", _TKE_TOTAL_PASS, "/", _TKE_TOTAL_RUN,
      " pass, ", _TKE_TOTAL_FAIL, "/", _TKE_TOTAL_RUN,
      " fail, wall ", _TKE_WALL_TOTAL, " s\n");

if _TKE_TOTAL_FAIL = 0 and _TKE_TOTAL_RUN > 0 then
    Print("\n[GREEN] test_k4a_e_branch_synthetic\n");
    QuitGap(0);
elif _TKE_TOTAL_RUN = 0 then
    Print("\n[SKIPPED] All m's had count = 0 (nothing tested)\n");
    QuitGap(1);
else
    Print("\n[RED] test_k4a_e_branch_synthetic\n");
    Print("Failure detail:\n");
    for _TKE_R in _TKE_PER_M_RESULTS do
        if not _TKE_R.skipped then
            for _TKE_F in _TKE_R.results do
                if _TKE_F.ok <> _TKE_F.want then
                    Print("  m=", _TKE_R.m, " ", _TKE_F.label,
                          ": got matcher.ok = ", _TKE_F.ok,
                          ", expected ", _TKE_F.want, "\n");
                fi;
            od;
        fi;
    od;
    QuitGap(1);
fi;
