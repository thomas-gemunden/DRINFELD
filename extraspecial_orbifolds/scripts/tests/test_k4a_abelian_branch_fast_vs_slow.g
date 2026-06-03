# test_k4a_abelian_branch_fast_vs_slow.g — issue #434 cross-validation.
#
# For each m in {2, 3} verify that
#
#     ClassifyAbelianBranchFast(EA, omega_cocycle, expon).is_coboundary
#   = JointPermutationMatcher(untwisted MD, ComputeModularData(EA, ...)).ok
#
# for omega_vec ∈ {0, e_1, e_2, ..., e_N} where N caps at
# K4A_FAST_VS_SLOW_M${m}_COUNT (defaults 10 / 0; m=5/m=7 deferred).
#
# Math: for abelian A and ω : A^3 → Z/N, [ω] is modular-data-trivial iff
# q_ω(a) := ω(a, a, a) ≡ 0 AND b_ω(a, b) := q_ω(a*b) - q_ω(a) - q_ω(b) ≡ 0
# (both mod N). The slow path builds the full S+T modular data and matches
# against the untwisted one; the fast path skips S and decides via (q, b).
# Cross-validation here confirms the two paths agree on the binary
# coboundary verdict for every ω in the sweep.
#
# Configurable counts:
#   K4A_FAST_VS_SLOW_M2_COUNT  (default 10)
#   K4A_FAST_VS_SLOW_M3_COUNT  (default 0 — gated; flip to 20 after m=2 GREEN
#                               AND the m=7 production rerun has completed)
#
# Usage:
#   gap -q -b -c 'K4A_FAST_VS_SLOW_M2_COUNT := 10;
#                 K4A_FAST_VS_SLOW_M3_COUNT := 0;
#                 Read("tests/test_k4a_abelian_branch_fast_vs_slow.g");
#                 QUIT;'
#
# Exit 0 on all GREEN, 1 on any RED.

# ---- Locate worktree, scripts dir --------------------------------------

_K4AFVS_SELF := INPUT_FILENAME();;
if _K4AFVS_SELF = fail or _K4AFVS_SELF = "stream" then
    Error("test_k4a_abelian_branch_fast_vs_slow.g: INPUT_FILENAME() ",
          "unavailable; Read the file by its absolute path.");
fi;
if Length(_K4AFVS_SELF) > 0 and _K4AFVS_SELF[1] <> '/' then
    _K4AFVS_SELF := Filename(DirectoryCurrent(), _K4AFVS_SELF);
fi;
_K4AFVS_SELFDIR := _K4AFVS_SELF{
    [1..Length(_K4AFVS_SELF) - Length("/test_k4a_abelian_branch_fast_vs_slow.g")]};;
_K4AFVS_SCRIPTSDIR := _K4AFVS_SELFDIR{
    [1..Length(_K4AFVS_SELFDIR) - Length("/tests")]};;
_K4AFVS_WT_ROOT := _K4AFVS_SCRIPTSDIR{
    [1..Length(_K4AFVS_SCRIPTSDIR) - Length("/extraspecial_orbifolds/scripts")]};;

# transgression_kernel.g has relative `Read` siblings; chdir first.
ChangeDirectoryCurrent(_K4AFVS_SCRIPTSDIR);

# ---- Load dependencies -------------------------------------------------

Read(Concatenation(_K4AFVS_WT_ROOT, "/src/modular_data.g"));
Read(Concatenation(_K4AFVS_SCRIPTSDIR, "/untwisted_modular_data.g"));
Read(Concatenation(_K4AFVS_SCRIPTSDIR, "/quillen_detecting_subgroup.g"));
Read(Concatenation(_K4AFVS_SCRIPTSDIR, "/transgression_kernel.g"));
Read(Concatenation(_K4AFVS_SCRIPTSDIR, "/joint_permutation_matcher.g"));
Read(Concatenation(_K4AFVS_SCRIPTSDIR, "/abelian_branch_fast.g"));

# ---- Configurable per-m test counts ------------------------------------

if not IsBoundGlobal("K4A_FAST_VS_SLOW_M2_COUNT") then
    K4A_FAST_VS_SLOW_M2_COUNT := 10;
fi;
if not IsBoundGlobal("K4A_FAST_VS_SLOW_M3_COUNT") then
    K4A_FAST_VS_SLOW_M3_COUNT := 0;
fi;

_K4AFVS_COUNTS := rec(
    m2 := K4A_FAST_VS_SLOW_M2_COUNT,
    m3 := K4A_FAST_VS_SLOW_M3_COUNT
);;

# ---- Per-m runner ------------------------------------------------------

_K4AFVS_RunForM := function(m, test_count_req)
    local ea_rec, EA, setup_ea, k, test_count, results, t0_m, wall_m,
          omega_vec_zero, i, omega_vec, t0_i, omega_cocycle, val, expon,
          modular_ct, modular_untwisted, match, slow_ok, slow_coboundary,
          fast_res, fast_coboundary, agree, wall_slow, wall_fast,
          n_pass, n_fail, num_tests, label, t_slow_0, t_fast_0;

    Print("\n=================================================================\n");
    Print("=== m = ", m, " : fast q+b vs slow ComputeModularData ===\n");
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

    t_slow_0 := Runtime();
    modular_ct := ComputeModularData(EA, omega_cocycle, val, expon);
    modular_untwisted := ComputeUntwistedModularData(EA);
    match := JointPermutationMatcher(
                modular_untwisted.S, modular_untwisted.T,
                modular_ct.S, modular_ct.T);
    wall_slow := (Runtime() - t_slow_0) / 1000.;
    slow_coboundary := match.ok;

    t_fast_0 := Runtime();
    fast_res := ClassifyAbelianBranchFast(EA, omega_cocycle, expon);
    wall_fast := (Runtime() - t_fast_0) / 1000.;
    fast_coboundary := fast_res.is_coboundary;

    agree := slow_coboundary = fast_coboundary;
    if agree and fast_coboundary = true then
        n_pass := n_pass + 1;
        Print("  PASS: m=", m, " omega=0 anchor -> ",
              "slow.coboundary = fast.coboundary = true (slow ",
              wall_slow, " s, fast ", wall_fast, " s)\n");
    else
        n_fail := n_fail + 1;
        Print("  FAIL: m=", m, " omega=0 anchor -> slow.coboundary = ",
              slow_coboundary, ", fast.coboundary = ", fast_coboundary,
              " (expected both true)\n");
    fi;
    Add(results, rec(label := "anchor", i := 0,
                     slow := slow_coboundary, fast := fast_coboundary,
                     agree := agree,
                     wall_slow := wall_slow, wall_fast := wall_fast));

    # ---- e_i unit vectors ----
    for i in [1..test_count] do
        omega_vec := ListWithIdenticalEntries(k, 0);
        omega_vec[i] := 1;

        omega_cocycle := StandardCocycleOf(setup_ea, omega_vec);
        val := Gcd(Gcd(omega_vec), setup_ea.exponent);
        expon := setup_ea.exponent / val;

        t_slow_0 := Runtime();
        modular_ct := ComputeModularData(EA, omega_cocycle, val, expon);
        modular_untwisted := ComputeUntwistedModularData(EA);
        match := JointPermutationMatcher(
                    modular_untwisted.S, modular_untwisted.T,
                    modular_ct.S, modular_ct.T);
        wall_slow := (Runtime() - t_slow_0) / 1000.;
        slow_coboundary := match.ok;

        t_fast_0 := Runtime();
        fast_res := ClassifyAbelianBranchFast(EA, omega_cocycle, expon);
        wall_fast := (Runtime() - t_fast_0) / 1000.;
        fast_coboundary := fast_res.is_coboundary;

        agree := slow_coboundary = fast_coboundary;
        if agree then
            n_pass := n_pass + 1;
            Print("  PASS: m=", m, " e_", i, "/", test_count,
                  " -> slow=fast=", slow_coboundary,
                  " (slow ", wall_slow, " s, fast ", wall_fast, " s)\n");
        else
            n_fail := n_fail + 1;
            Print("  FAIL: m=", m, " e_", i, "/", test_count,
                  " -> slow.coboundary = ", slow_coboundary,
                  ", fast.coboundary = ", fast_coboundary,
                  " (slow ", wall_slow, " s, fast ", wall_fast, " s)\n");
            Print("        DISAGREEMENT — fast path verdict differs from slow path.\n");
            Print("        is_q_trivial = ", fast_res.is_q_trivial,
                  ", is_b_trivial = ", fast_res.is_b_trivial, "\n");
        fi;
        Add(results, rec(label := Concatenation("e_", String(i)),
                         i := i,
                         slow := slow_coboundary, fast := fast_coboundary,
                         agree := agree,
                         wall_slow := wall_slow, wall_fast := wall_fast));
    od;

    wall_m := (Runtime() - t0_m) / 1000.;
    num_tests := 1 + test_count;
    Print("  --- m=", m, " summary: ", n_pass, "/", num_tests,
          " agree, ", n_fail, "/", num_tests, " disagree, wall ",
          wall_m, " s ---\n");
    return rec(m := m, pass := n_pass, fail := n_fail,
               total := num_tests, wall := wall_m,
               skipped := false, results := results);
end;;

# ---- Main run ----------------------------------------------------------

Print("=================================================================\n");
Print("test_k4a_abelian_branch_fast_vs_slow.g (#434)\n");
Print("=================================================================\n");
Print("config: m2=", _K4AFVS_COUNTS.m2,
      ", m3=", _K4AFVS_COUNTS.m3, " unit vectors per m\n");

_K4AFVS_T_TOTAL := Runtime();;
_K4AFVS_PER_M_RESULTS := [];;

Add(_K4AFVS_PER_M_RESULTS, _K4AFVS_RunForM(2, _K4AFVS_COUNTS.m2));
Add(_K4AFVS_PER_M_RESULTS, _K4AFVS_RunForM(3, _K4AFVS_COUNTS.m3));

_K4AFVS_WALL_TOTAL := (Runtime() - _K4AFVS_T_TOTAL) / 1000.;;

# ---- Final summary ----

Print("\n=================================================================\n");
Print("FINAL SUMMARY\n");
Print("=================================================================\n");

_K4AFVS_TOTAL_PASS := 0;;
_K4AFVS_TOTAL_FAIL := 0;;
_K4AFVS_TOTAL_RUN  := 0;;

for _K4AFVS_R in _K4AFVS_PER_M_RESULTS do
    if _K4AFVS_R.skipped then
        Print("  m=", _K4AFVS_R.m, ": SKIPPED (count = 0)\n");
    else
        Print("  m=", _K4AFVS_R.m, ": ", _K4AFVS_R.pass, "/",
              _K4AFVS_R.total, " agree, ", _K4AFVS_R.fail,
              " disagree, wall ", _K4AFVS_R.wall, " s\n");
        _K4AFVS_TOTAL_PASS := _K4AFVS_TOTAL_PASS + _K4AFVS_R.pass;
        _K4AFVS_TOTAL_FAIL := _K4AFVS_TOTAL_FAIL + _K4AFVS_R.fail;
        _K4AFVS_TOTAL_RUN  := _K4AFVS_TOTAL_RUN  + _K4AFVS_R.total;
    fi;
od;
Print("\nTotal: ", _K4AFVS_TOTAL_PASS, "/", _K4AFVS_TOTAL_RUN,
      " agree, ", _K4AFVS_TOTAL_FAIL, " disagree\n");
Print("Total wall: ", _K4AFVS_WALL_TOTAL, " s\n");

if _K4AFVS_TOTAL_FAIL = 0 and _K4AFVS_TOTAL_RUN > 0 then
    Print("\n[GREEN] test_k4a_abelian_branch_fast_vs_slow\n");
    QuitGap(0);
elif _K4AFVS_TOTAL_RUN = 0 then
    Print("\n[SKIPPED] All m's had count = 0 (nothing tested)\n");
    QuitGap(1);
else
    Print("\n[RED] test_k4a_abelian_branch_fast_vs_slow\n");
    QuitGap(1);
fi;
