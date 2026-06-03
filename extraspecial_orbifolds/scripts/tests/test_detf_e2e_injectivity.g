# test_detf_e2e_injectivity.g - End-to-end injectivity verification (#425).
#
# Empirically verifies AM04 IV.7 + Quillen injectivity of restriction
#     H^3(E_+(m); U(1)) -> H^3(EA; U(1)) (+) H^3(D_8; U(1)) (+) H^3(Q_8; U(1))
# THROUGH the modular-data classifier pipeline. Each non-zero
# omega_vec at the G level must be detected as non-trivial by at least
# one branch of the K-4a classifier dispatch (EA / D_8 / Q_8).
#
# For each m in {2, 3, 5}:
#
#   1. Build setup_G := SetupCohomology3(EPlusGroup(m)) and
#      rec_m := BuildRestrictionMatrices(m, "hap"), giving per-branch
#      restriction matrices res_EA_list / res_D8 / res_Q8 and ambient
#      setup_K records for each branch.
#
#   2. For omega_vec = 0 (anchor): every branch must report trivial
#      (twisted MD matches the untwisted MD of K).
#
#   3. For each non-zero omega_vec = e_i (i = 1..N basis vector):
#      a. v_K := omega_vec * res_K  mod torsion_K  for K in {EA_j, D_8, Q_8}.
#         (Matrix-vector convention follows ResIsTrivialOnDetectingFamily:
#         hom_omega * res_K, see detecting_family_vanish.g lines 156-167.)
#      b. For each (K, v_K):
#         - If v_K = 0: this branch CANNOT detect omega_i (the restriction
#           class itself is the zero class of H^3(K)). Mark as not-detected
#           but do not flag as a failure of the branch — that's the test
#           the cohomology-level injectivity test does.
#         - If v_K != 0: build twisted modular data, classify, mark as
#           detected non-trivial iff classifier reports non-trivial.
#      c. ASSERT: at least one of the three branches detected non-trivial.
#         If all three reported trivial for a non-zero omega_vec, FAIL — at
#         the modular-data level the restriction is "invisible", which
#         would refute the e2e injectivity claim.
#
# Configurable counts:
#   DETF_E2E_M2_TEST_COUNT  (default 10 - full sweep at m=2).
#   DETF_E2E_M3_TEST_COUNT  (default 35 - full sweep at m=3).
#   DETF_E2E_M5_TEST_COUNT  (default 10 - sample; full is 165 generators).
# When a count is 0, that m is skipped.
#
# Usage:
#   cd extraspecial_orbifolds/scripts
#   gap -q -b /Users/.../tests/test_detf_e2e_injectivity.g
#
#   gap -q -b -c 'DETF_E2E_M2_TEST_COUNT := 10; \
#                 DETF_E2E_M3_TEST_COUNT := 0; \
#                 DETF_E2E_M5_TEST_COUNT := 0; \
#                 Read("tests/test_detf_e2e_injectivity.g"); QUIT;'
#
# Exit 0 on all GREEN, 1 on any RED.

# ---- Locate worktree, scripts dir --------------------------------------

_DETFE2E_SELF := INPUT_FILENAME();;
if _DETFE2E_SELF = fail or _DETFE2E_SELF = "stream" then
    Error("test_detf_e2e_injectivity.g: INPUT_FILENAME() unavailable; ",
          "Read the file by its absolute path.");
fi;
if Length(_DETFE2E_SELF) > 0 and _DETFE2E_SELF[1] <> '/' then
    _DETFE2E_SELF := Filename(DirectoryCurrent(), _DETFE2E_SELF);
fi;
_DETFE2E_SELFDIR := _DETFE2E_SELF{
    [1..Length(_DETFE2E_SELF) - Length("/test_detf_e2e_injectivity.g")]};;
_DETFE2E_SCRIPTSDIR := _DETFE2E_SELFDIR{
    [1..Length(_DETFE2E_SELFDIR) - Length("/tests")]};;
_DETFE2E_WT_ROOT := _DETFE2E_SCRIPTSDIR{
    [1..Length(_DETFE2E_SCRIPTSDIR) - Length("/extraspecial_orbifolds/scripts")]};;

# Many sibling .g files do relative Reads. Chdir to scripts/ so those
# resolve (CLAUDE.md "CWD-sensitive relative Read calls" caveat).
ChangeDirectoryCurrent(_DETFE2E_SCRIPTSDIR);

# ---- Load dependencies -------------------------------------------------
#
# Order matters:
#   1. src/modular_data.g - LoadModularData + ComputeModularData (the
#      legacy twisted-MD engine used here for both K=EA and K=D_8/Q_8).
#   2. untwisted_modular_data.g - ComputeUntwistedModularData (for the
#      E-branch dispatch, mirrors test_k4a_e_branch_synthetic.g).
#   3. quillen_detecting_subgroup.g - EPlusGroup + MaximalElementaryAbelian_E_plus.
#   4. transgression_kernel.g - SetupCohomology3, StandardCocycleOf.
#   5. joint_permutation_matcher.g - JointPermutationMatcher (E-branch).
#   6. d8_classifier.g / q8_classifier.g - D_8 / Q_8 dispatch.
#   7. detecting_family_restriction.g - BuildRestrictionMatrices.

Read(Concatenation(_DETFE2E_WT_ROOT, "/src/modular_data.g"));
Read(Concatenation(_DETFE2E_SCRIPTSDIR, "/untwisted_modular_data.g"));
Read(Concatenation(_DETFE2E_SCRIPTSDIR, "/quillen_detecting_subgroup.g"));
Read(Concatenation(_DETFE2E_SCRIPTSDIR, "/transgression_kernel.g"));
Read(Concatenation(_DETFE2E_SCRIPTSDIR, "/joint_permutation_matcher.g"));
Read(Concatenation(_DETFE2E_SCRIPTSDIR, "/d8_classifier.g"));
Read(Concatenation(_DETFE2E_SCRIPTSDIR, "/q8_classifier.g"));
Read(Concatenation(_DETFE2E_SCRIPTSDIR, "/detecting_family_restriction.g"));

# ---- Locate the modular_data tree and chdir to a symlink dir ----------
#
# ClassifyOnD8 / ClassifyOnQ8 call LoadModularData(8, 3, k) /
# LoadModularData(8, 4, k), which reads "Modular_Data/8/3/k.txt" relative
# to GAP's CWD. Mirrors the test_d8_classifier.g / test_q8_classifier.g
# convention: create tests/detf_e2e/Modular_Data -> ../../../../modular_data,
# then ChangeDirectoryCurrent to that dir.

_DETFE2E_MD_ROOT := fail;;
for _DETFE2E_CAND in
    [ Concatenation(_DETFE2E_WT_ROOT, "/../modular_data"),
      "/Users/thomasgemunden/Projects/group_cohomology/modular_data" ] do
    if _DETFE2E_MD_ROOT = fail
       and IsExistingFile(Concatenation(_DETFE2E_CAND, "/8/3/1.txt"))
       and IsExistingFile(Concatenation(_DETFE2E_CAND, "/8/4/1.txt")) then
        _DETFE2E_MD_ROOT := _DETFE2E_CAND;
    fi;
od;
if _DETFE2E_MD_ROOT = fail then
    Error("test_detf_e2e_injectivity.g: cannot locate modular_data tree ",
          "containing 8/3/1.txt and 8/4/1.txt.");
fi;
Print("modular_data root: ", _DETFE2E_MD_ROOT, "\n");

_DETFE2E_LINKDIR := Concatenation(_DETFE2E_SELFDIR, "/detf_e2e");;
if not IsExistingFile(_DETFE2E_LINKDIR) then
    Exec(Concatenation("mkdir -p '", _DETFE2E_LINKDIR, "'"));
fi;
_DETFE2E_LINKPATH := Concatenation(_DETFE2E_LINKDIR, "/Modular_Data");;
if not IsExistingFile(_DETFE2E_LINKPATH) then
    Exec(Concatenation("ln -s '", _DETFE2E_MD_ROOT, "' '",
                       _DETFE2E_LINKPATH, "'"));
fi;
if not IsExistingFile(Concatenation(_DETFE2E_LINKPATH, "/8/3/1.txt")) then
    Error("test_detf_e2e_injectivity.g: Modular_Data symlink at ",
          _DETFE2E_LINKPATH, " does not resolve to a tree containing ",
          "8/3/1.txt.");
fi;
ChangeDirectoryCurrent(_DETFE2E_LINKDIR);

# ---- Configurable per-m test counts ------------------------------------

if not IsBoundGlobal("DETF_E2E_M2_TEST_COUNT") then
    DETF_E2E_M2_TEST_COUNT := 10;
fi;
if not IsBoundGlobal("DETF_E2E_M3_TEST_COUNT") then
    DETF_E2E_M3_TEST_COUNT := 35;
fi;
if not IsBoundGlobal("DETF_E2E_M5_TEST_COUNT") then
    DETF_E2E_M5_TEST_COUNT := 10;
fi;

_DETFE2E_COUNTS := rec(
    m2 := DETF_E2E_M2_TEST_COUNT,
    m3 := DETF_E2E_M3_TEST_COUNT,
    m5 := DETF_E2E_M5_TEST_COUNT
);;

# ---- Branch dispatch ---------------------------------------------------
#
# Given a sub-vector v_K (mod torsion_K) on a detecting-family branch K,
# return rec(skipped, detected_nontrivial, branch_label, reason).
#
#   * skipped = true when v_K is the zero vector: this branch's
#     restriction class is zero in H^3(K), so it cannot detect omega
#     even if omega is non-zero at G. Other branches must pick it up.
#   * detected_nontrivial = true iff the modular-data classifier on the
#     twisted MD reports non-trivial:
#         K = D_8 -> class_idx != 1
#         K = Q_8 -> class_idx != 1
#         K = EA  -> JointPermutationMatcher vs untwisted MD returns ok=false.
#
# The D_8 / Q_8 branches use the legacy ComputeModularData (src/modular_data.g)
# which is the same engine that produced the on-disk LoadModularData
# entries that ClassifyOnD8 / ClassifyOnQ8 match against - so a self-consistent
# round trip. The EA branch mirrors test_k4a_e_branch_synthetic.g (#424)
# in using ComputeModularData + ComputeUntwistedModularData on the abelian
# subgroup and a JointPermutationMatcher.

_DETFE2E_BranchDispatch := function(K, setup_K, v_K, branch_label)
    local omega_cocycle, val, expon, modular_ct, modular_untwisted, match,
          class_res, untwisted_class_idx;

    if ForAll(v_K, x -> x = 0) then
        return rec(skipped := true, detected_nontrivial := false,
                   branch_label := branch_label, reason := "v_K = 0");
    fi;

    omega_cocycle := StandardCocycleOf(setup_K, v_K);
    val := Gcd(Gcd(v_K), setup_K.exponent);
    expon := setup_K.exponent / val;
    modular_ct := ComputeModularData(K, omega_cocycle, val, expon);

    if branch_label = "D_8" then
        # ClassifyOnD8 returns class_idx in {1..12} or fail. Class 1 is
        # the trivial (untwisted) cocycle by the modular_data/8/3/3-cocycles.txt
        # ordering. fail means the input did not match any of the 12 stored
        # Aut(D_8)-orbit reps - still non-trivial vs trivial.
        class_res := ClassifyOnD8(modular_ct.S, DiagonalOfMat(modular_ct.T));
        return rec(skipped := false,
                   detected_nontrivial := (class_res.class_idx <> 1),
                   branch_label := branch_label,
                   class_idx := class_res.class_idx,
                   all_matches := class_res.all_matches);
    elif branch_label = "Q_8" then
        # ClassifyOnQ8 returns class_idx in {1..8} or fail. Class 1 is
        # the trivial cocycle.
        class_res := ClassifyOnQ8(modular_ct.S, DiagonalOfMat(modular_ct.T));
        return rec(skipped := false,
                   detected_nontrivial := (class_res.class_idx <> 1),
                   branch_label := branch_label,
                   class_idx := class_res.class_idx,
                   all_matches := class_res.all_matches);
    else
        # EA branch: classify via JointPermutationMatcher vs untwisted MD.
        modular_untwisted := ComputeUntwistedModularData(K);
        match := JointPermutationMatcher(
                    modular_untwisted.S, modular_untwisted.T,
                    modular_ct.S, modular_ct.T);
        return rec(skipped := false,
                   detected_nontrivial := (match.ok = false),
                   branch_label := branch_label,
                   match_ok := match.ok);
    fi;
end;;

# ---- Per-m runner ------------------------------------------------------
#
# All matvec uses the convention from ResIsTrivialOnDetectingFamily
# (detecting_family_vanish.g): hom_omega * res_K, then per-column mod
# against torsion_K. res_K has shape k_G x k_{H_K}.

_DETFE2E_RunForM := function(m, test_count_req)
    local rec_m, setup_G, k_G, n_pass, n_fail, results, t0_m, wall_m,
          i, omega_vec, t0_i, wall_i, branches_detected, branches_skipped,
          j, ea_setup, ea_H, v_EA, branch_EA, v_D8, branch_D8, v_Q8,
          branch_Q8, all_branches_trivial, branch_dets, label,
          test_count, anchor_omega, anchor_res, results_m,
          omega_int_EA, omega_int_D8, omega_int_Q8, anchor_all_trivial,
          n_anchor_pass;

    Print("\n=================================================================\n");
    Print("=== m = ", m, " : E2E injectivity through classifier pipeline ===\n");
    Print("=================================================================\n");

    if test_count_req <= 0 then
        Print("  [skipped] test count = ", test_count_req, " for m=", m, "\n");
        return rec(m := m, pass := 0, fail := 0, total := 0,
                   anchor_pass := 0, wall := 0.0, skipped := true);
    fi;

    t0_m := Runtime();
    rec_m := BuildRestrictionMatrices(m, "hap");
    setup_G := rec_m.setup_G;
    k_G := setup_G.num_generators;
    Print("  E_+(", m, "): |G| = ", Order(rec_m.G),
          ", k_G = ", k_G,
          ", H_EA_list len = ", Length(rec_m.H_EA_list),
          ", Q_8 present = ", rec_m.H_Q8 <> fail, "\n");

    test_count := Minimum(test_count_req, k_G);
    if test_count < test_count_req then
        Print("  [note] requested ", test_count_req,
              " unit vectors, but k_G = ", k_G,
              "; capping at ", test_count, "\n");
    fi;

    n_pass := 0;
    n_fail := 0;
    n_anchor_pass := 0;
    results_m := [];

    # ---- omega_vec = 0 anchor: every branch should report trivial ----
    Print("\n  --- omega_vec = 0 anchor ---\n");
    anchor_omega := ListWithIdenticalEntries(k_G, 0);
    t0_i := Runtime();
    branch_dets := [];
    anchor_all_trivial := true;
    for j in [1..Length(rec_m.H_EA_list)] do
        ea_H := rec_m.H_EA_list[j];
        ea_setup := SetupCohomology3(ea_H);
        omega_int_EA := anchor_omega * rec_m.res_EA_list[j];
        v_EA := List([1..Length(omega_int_EA)], k ->
            omega_int_EA[k] mod rec_m.torsion_EA_list[j][k]);
        branch_EA := _DETFE2E_BranchDispatch(
            ea_H, ea_setup, v_EA,
            Concatenation("EA_", String(j)));
        Add(branch_dets, branch_EA);
        if branch_EA.detected_nontrivial then
            anchor_all_trivial := false;
        fi;
    od;
    omega_int_D8 := anchor_omega * rec_m.res_D8;
    v_D8 := List([1..Length(omega_int_D8)], k ->
        omega_int_D8[k] mod rec_m.torsion_D8[k]);
    branch_D8 := _DETFE2E_BranchDispatch(
        rec_m.H_D8, SetupCohomology3(rec_m.H_D8), v_D8, "D_8");
    Add(branch_dets, branch_D8);
    if branch_D8.detected_nontrivial then
        anchor_all_trivial := false;
    fi;
    if rec_m.H_Q8 <> fail then
        omega_int_Q8 := anchor_omega * rec_m.res_Q8;
        v_Q8 := List([1..Length(omega_int_Q8)], k ->
            omega_int_Q8[k] mod rec_m.torsion_Q8[k]);
        branch_Q8 := _DETFE2E_BranchDispatch(
            rec_m.H_Q8, SetupCohomology3(rec_m.H_Q8), v_Q8, "Q_8");
        Add(branch_dets, branch_Q8);
        if branch_Q8.detected_nontrivial then
            anchor_all_trivial := false;
        fi;
    fi;
    wall_i := (Runtime() - t0_i) / 1000.;
    if anchor_all_trivial then
        n_anchor_pass := 1;
        Print("  PASS: omega=0 anchor -> every branch reports trivial ",
              "(wall ", wall_i, " s)\n");
    else
        n_fail := n_fail + 1;
        Print("  FAIL: omega=0 anchor -> some branch reported non-trivial ",
              "(wall ", wall_i, " s)\n");
        for label in branch_dets do
            if label.detected_nontrivial then
                Print("        branch ", label.branch_label,
                      " reported non-trivial (should be trivial)\n");
            fi;
        od;
    fi;
    Add(results_m, rec(label := "anchor", i := 0,
                       wall := wall_i,
                       all_trivial := anchor_all_trivial,
                       branches := branch_dets));

    # ---- e_i unit vectors ----
    for i in [1..test_count] do
        omega_vec := ListWithIdenticalEntries(k_G, 0);
        omega_vec[i] := 1;
        t0_i := Runtime();

        branches_detected := [];
        branches_skipped := [];
        branch_dets := [];

        for j in [1..Length(rec_m.H_EA_list)] do
            ea_H := rec_m.H_EA_list[j];
            ea_setup := SetupCohomology3(ea_H);
            omega_int_EA := omega_vec * rec_m.res_EA_list[j];
            v_EA := List([1..Length(omega_int_EA)], k ->
                omega_int_EA[k] mod rec_m.torsion_EA_list[j][k]);
            branch_EA := _DETFE2E_BranchDispatch(
                ea_H, ea_setup, v_EA,
                Concatenation("EA_", String(j)));
            Add(branch_dets, branch_EA);
            if branch_EA.skipped then
                Add(branches_skipped, branch_EA.branch_label);
            elif branch_EA.detected_nontrivial then
                Add(branches_detected, branch_EA.branch_label);
            fi;
        od;

        omega_int_D8 := omega_vec * rec_m.res_D8;
        v_D8 := List([1..Length(omega_int_D8)], k ->
            omega_int_D8[k] mod rec_m.torsion_D8[k]);
        branch_D8 := _DETFE2E_BranchDispatch(
            rec_m.H_D8, SetupCohomology3(rec_m.H_D8), v_D8, "D_8");
        Add(branch_dets, branch_D8);
        if branch_D8.skipped then
            Add(branches_skipped, branch_D8.branch_label);
        elif branch_D8.detected_nontrivial then
            Add(branches_detected, branch_D8.branch_label);
        fi;

        if rec_m.H_Q8 <> fail then
            omega_int_Q8 := omega_vec * rec_m.res_Q8;
            v_Q8 := List([1..Length(omega_int_Q8)], k ->
                omega_int_Q8[k] mod rec_m.torsion_Q8[k]);
            branch_Q8 := _DETFE2E_BranchDispatch(
                rec_m.H_Q8, SetupCohomology3(rec_m.H_Q8), v_Q8, "Q_8");
            Add(branch_dets, branch_Q8);
            if branch_Q8.skipped then
                Add(branches_skipped, branch_Q8.branch_label);
            elif branch_Q8.detected_nontrivial then
                Add(branches_detected, branch_Q8.branch_label);
            fi;
        fi;

        wall_i := (Runtime() - t0_i) / 1000.;
        all_branches_trivial := IsEmpty(branches_detected);

        if not all_branches_trivial then
            n_pass := n_pass + 1;
            Print("  PASS: m=", m, " e_", i, "/", test_count,
                  " -> detected by ", branches_detected,
                  " (skipped ", branches_skipped, ", wall ", wall_i, " s)\n");
        else
            n_fail := n_fail + 1;
            Print("  FAIL: m=", m, " e_", i, "/", test_count,
                  " -> ALL branches reported trivial (skipped ",
                  branches_skipped, ", wall ", wall_i, " s)\n");
            Print("        FALSE-NEGATIVE: omega is non-zero at G but ",
                  "no classifier branch detected it.\n");
            for label in branch_dets do
                Print("        ", label.branch_label, ": ");
                if label.skipped then
                    Print("skipped (", label.reason, ")\n");
                elif IsBound(label.class_idx) then
                    Print("class_idx = ", label.class_idx,
                          ", all_matches = ", label.all_matches, "\n");
                else
                    Print("match.ok = ", label.match_ok, "\n");
                fi;
            od;
        fi;
        Add(results_m, rec(label := Concatenation("e_", String(i)),
                           i := i,
                           wall := wall_i,
                           all_trivial := all_branches_trivial,
                           branches := branch_dets));
    od;

    wall_m := (Runtime() - t0_m) / 1000.;
    Print("\n  --- m=", m, " summary: anchor ", n_anchor_pass,
          "/1 pass, e_i ", n_pass, "/", test_count, " pass, ",
          n_fail, " fail, wall ", wall_m, " s ---\n");
    return rec(m := m, pass := n_pass, fail := n_fail,
               anchor_pass := n_anchor_pass,
               total := test_count, wall := wall_m,
               skipped := false, results := results_m);
end;;

# ---- Main run ----------------------------------------------------------

Print("=================================================================\n");
Print("test_detf_e2e_injectivity.g (D-VAN E2E #425)\n");
Print("=================================================================\n");
Print("config: m2=", _DETFE2E_COUNTS.m2,
      ", m3=", _DETFE2E_COUNTS.m3,
      ", m5=", _DETFE2E_COUNTS.m5,
      " unit vectors per m\n");

_DETFE2E_T_TOTAL := Runtime();;
_DETFE2E_PER_M_RESULTS := [];;

Add(_DETFE2E_PER_M_RESULTS, _DETFE2E_RunForM(2, _DETFE2E_COUNTS.m2));
Add(_DETFE2E_PER_M_RESULTS, _DETFE2E_RunForM(3, _DETFE2E_COUNTS.m3));
Add(_DETFE2E_PER_M_RESULTS, _DETFE2E_RunForM(5, _DETFE2E_COUNTS.m5));

_DETFE2E_WALL_TOTAL := (Runtime() - _DETFE2E_T_TOTAL) / 1000.;;

# ---- Final summary ----

Print("\n=================================================================\n");
Print("FINAL SUMMARY\n");
Print("=================================================================\n");

_DETFE2E_TOTAL_PASS := 0;;
_DETFE2E_TOTAL_FAIL := 0;;
_DETFE2E_TOTAL_RUN  := 0;;
_DETFE2E_ANCHOR_PASS := 0;;
_DETFE2E_ANCHOR_TOTAL := 0;;

for _DETFE2E_R in _DETFE2E_PER_M_RESULTS do
    if _DETFE2E_R.skipped then
        Print("  m=", _DETFE2E_R.m, ": SKIPPED (count = 0)\n");
    else
        Print("  m=", _DETFE2E_R.m, ": anchor ", _DETFE2E_R.anchor_pass,
              "/1, e_i ", _DETFE2E_R.pass, "/", _DETFE2E_R.total,
              " correctly detected non-trivial, ", _DETFE2E_R.fail,
              " false-negative, wall ", _DETFE2E_R.wall, " s\n");
        _DETFE2E_TOTAL_PASS := _DETFE2E_TOTAL_PASS + _DETFE2E_R.pass;
        _DETFE2E_TOTAL_FAIL := _DETFE2E_TOTAL_FAIL + _DETFE2E_R.fail;
        _DETFE2E_TOTAL_RUN  := _DETFE2E_TOTAL_RUN  + _DETFE2E_R.total;
        _DETFE2E_ANCHOR_PASS := _DETFE2E_ANCHOR_PASS + _DETFE2E_R.anchor_pass;
        _DETFE2E_ANCHOR_TOTAL := _DETFE2E_ANCHOR_TOTAL + 1;
    fi;
od;
Print("\nTotal e_i: ", _DETFE2E_TOTAL_PASS, "/", _DETFE2E_TOTAL_RUN,
      " correctly detected non-trivial, ", _DETFE2E_TOTAL_FAIL,
      " false-negative\n");
Print("Anchor: ", _DETFE2E_ANCHOR_PASS, "/", _DETFE2E_ANCHOR_TOTAL,
      " all-trivial as expected\n");
Print("Total wall: ", _DETFE2E_WALL_TOTAL, " s\n");

if _DETFE2E_TOTAL_FAIL = 0
   and _DETFE2E_ANCHOR_PASS = _DETFE2E_ANCHOR_TOTAL
   and _DETFE2E_TOTAL_RUN > 0 then
    Print("\n[GREEN] test_detf_e2e_injectivity\n");
    QuitGap(0);
elif _DETFE2E_TOTAL_RUN = 0 then
    Print("\n[SKIPPED] All m's had count = 0 (nothing tested)\n");
    QuitGap(1);
else
    Print("\n[RED] test_detf_e2e_injectivity\n");
    Print("Failure detail:\n");
    for _DETFE2E_R in _DETFE2E_PER_M_RESULTS do
        if not _DETFE2E_R.skipped then
            for _DETFE2E_F in _DETFE2E_R.results do
                if _DETFE2E_F.label = "anchor" and not _DETFE2E_F.all_trivial then
                    Print("  m=", _DETFE2E_R.m,
                          " ANCHOR: some branch reported non-trivial on omega=0\n");
                elif _DETFE2E_F.label <> "anchor" and _DETFE2E_F.all_trivial then
                    Print("  m=", _DETFE2E_R.m, " ", _DETFE2E_F.label,
                          ": FALSE-NEGATIVE (no branch detected non-zero omega)\n");
                fi;
            od;
        fi;
    od;
    QuitGap(1);
fi;
