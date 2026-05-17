# test_hap_lhs_resolution.g — regression for `hap_lhs_resolution.g`.
#
# Issue #238 (Q-int C-2). Cross-validates the LHS-perturbed resolution
# against the direct `ResolutionFiniteGroup(E_+(m), n)` at small m,
# and (opt-in) probes the m=7 build for memory + cohomology agreement
# with the Harada-Kono prediction.
#
# # Test plan.
#
# 1. m=2 full cross-check (default, ~seconds).
#    - LHS R built to degree 5; direct R built to degree 5.
#    - Hard assert: H^n(LHS) == H^n(direct) for n ∈ {2, 3, 4}.
#    - Known reference (Harada-Kono / direct measurement):
#         H^2 = (Z/2)^4, H^3 = (Z/2)^5, H^4 = (Z/2)^9 ⊕ Z/8.
#      (m=2 has Z/8 not Z/4 because m=2 is the "A(8) = Z/8" boundary
#       case of the Harada-Kono pattern.)
#
# 2. m=3 cross-check (default, ~seconds).
#    - LHS R built to degree 5; direct R built to degree 4 only.
#    - At m=3, direct ResolutionFiniteGroup(G, 5) OOMs even at 16 GB
#      heap (this is the symptom blocking #238 at larger m). So the
#      direct route can only cover up to degree 4 → H^n for n ≤ 3.
#    - Hard assert: H^n(LHS) == H^n(direct) for n ∈ {2, 3}.
#    - Soft check (best-effort): LHS H^4 matches Harada-Kono
#      "(Z/2)^{34} ⊕ Z/4" — useful as a self-consistency probe even
#      without a direct cross-check.
#
# 3. m=7 build probe (opt-in via EPLUS7_RUN := true).
#    - Build LHSResolutionEPlus(7, 5), record peak heap.
#    - Compute Cohomology(R, 3) and Cohomology(R, 4).
#    - Compare H^4 against Harada-Kono "(Z/2)^{454} ⊕ Z/4".
#    - Default-off because the m=7 build runs in minutes (~5-10 for
#      R_E to deg 5) and Cohomology(R_E, 4) costs additional minutes.
#      The test scaffolding records both timings so the budget can be
#      revisited.
#    - Note on the spec: issue #238 acceptance says "Cohomology(R, 3)
#      matches (Z/2)^{454} ⊕ Z/4". That refers to H^3(G; U(1)). Via
#      UCT, H^3(G; U(1)) ≅ H^4(G; Z) for finite G, and HAP's
#      Cohomology(HomToIntegers(R), n) returns H^n(G; Z). So the
#      literal acceptance test is on integer H^4, not H^3 — verified
#      at m ∈ {3, 4} where H^4 follows Harada-Kono (Z/2)^{N} ⊕ Z/4
#      with N(3)=34, N(4)=83.
#
# # Running.
#
#   gap -o 4g -q -b tests/test_hap_lhs_resolution.g            # default tasks 1-2
#   gap -o 16g -c 'EPLUS7_RUN := true;;' \
#       -q -b tests/test_hap_lhs_resolution.g                  # all tasks (~minutes)
#
# A failing acceptance prints "test_hap_lhs_resolution: FAIL (N
# failures)" with a per-task breakdown; a zero-failure run prints
# "test_hap_lhs_resolution: ALL PASS".

BreakOnError := false;;

LoadPackage("hap");

Read("hap_lhs_resolution.g");

Print("\n=== test_hap_lhs_resolution.g (issue #238) ===\n");

testFailures := [];;
If_loc := function(c, a, b) if c then return a; else return b; fi; end;;
AssertOrLog := function(label, cond)
    Print("  ", label, ": ", If_loc(cond, "PASS", "FAIL"), "\n");
    if not cond then Add(testFailures, label); fi;
end;;

# Compute H^n robustly. Returns rec(ok := bool, value := list, error := str).
# Catches errors (typically `reached the pre-set memory limit`) so the
# m=3 direct comparison can degrade gracefully under heap pressure.
ComputeHnSafe := function(R, n)
    local C, captured;
    C := HomToIntegers(R);
    captured := CALL_WITH_CATCH(Cohomology, [C, n]);
    if captured[1] then
        return rec(ok := true, value := captured[2], error := "");
    fi;
    return rec(ok := false, value := fail,
               error := String(captured[2]));
end;;

# Wall-clock seconds since Unix epoch.
WallClockSec := function()
    return Float(NanosecondsSinceEpoch()) / 1.0e9;
end;;

# Build a direct ResolutionFiniteGroup(E_+(m), max_n) safely.
BuildDirectSafe := function(m, max_n)
    local G, captured;
    G := ExtraspecialGroup(2^(2*m + 1), "+");
    captured := CALL_WITH_CATCH(ResolutionFiniteGroup, [G, max_n]);
    if captured[1] then
        return rec(ok := true, R := captured[2], error := "");
    fi;
    return rec(ok := false, R := fail,
               error := String(captured[2]));
end;;

# ---------------------------------------------------------------------
# Task 1: m = 2 full cross-check.
# ---------------------------------------------------------------------

Print("\n--- Task 1: m=2 full cross-check (n ∈ {2, 3, 4}) ---\n");

m := 2;
G2 := ExtraspecialGroup(2^(2*m + 1), "+");
Print("  |E_+(", m, ")| = ", Order(G2), "\n");

t0 := WallClockSec();
det_lhs_2 := LHSResolutionEPlusDetailed(2, 5);;
R_lhs_2 := det_lhs_2.R_E;;
t_lhs_2 := WallClockSec() - t0;
Print("  LHS build time: ", t_lhs_2, " s\n");

t0 := WallClockSec();
direct_2 := BuildDirectSafe(2, 5);;
t_dir_2 := WallClockSec() - t0;
if not direct_2.ok then
    Print("  Direct build FAILED (heap?): ", direct_2.error, "\n");
    AssertOrLog("m=2 direct ResolutionFiniteGroup builds", false);
else
    Print("  Direct build time: ", t_dir_2, " s\n");
    R_dir_2 := direct_2.R;
    for n in [2, 3, 4] do
        r_lhs := ComputeHnSafe(R_lhs_2, n);
        r_dir := ComputeHnSafe(R_dir_2, n);
        if r_lhs.ok and r_dir.ok then
            match := r_lhs.value = r_dir.value;
            Print("  m=2, H^", n, ": LHS = ", r_lhs.value,
                  " ; direct = ", r_dir.value, " ; match = ", match,
                  "\n");
            AssertOrLog(Concatenation("m=2 H^", String(n),
                                      " LHS == direct"),
                        match);
        else
            Print("  m=2, H^", n, ": LHS.ok = ", r_lhs.ok,
                  ", direct.ok = ", r_dir.ok, "\n");
            AssertOrLog(Concatenation("m=2 H^", String(n),
                                      " both routes succeeded"), false);
        fi;
    od;
fi;

# ---------------------------------------------------------------------
# Task 2: m = 3 cross-check at n ∈ {2, 3} + soft check H^4 vs H-K.
# ---------------------------------------------------------------------

Print("\n--- Task 2: m=3 cross-check (n ∈ {2, 3}, plus H^4 H-K) ---\n");

m := 3;
G3 := ExtraspecialGroup(2^(2*m + 1), "+");
Print("  |E_+(", m, ")| = ", Order(G3), "\n");

t0 := WallClockSec();
det_lhs_3 := LHSResolutionEPlusDetailed(3, 5);;
R_lhs_3 := det_lhs_3.R_E;;
t_lhs_3 := WallClockSec() - t0;
Print("  LHS build time: ", t_lhs_3, " s\n");

# Direct route at m=3 deg 4 (= one less, to compare H^2, H^3 only;
# deg 5 OOMs).
t0 := WallClockSec();
direct_3 := BuildDirectSafe(3, 4);;
t_dir_3 := WallClockSec() - t0;
if not direct_3.ok then
    Print("  Direct n=4 build FAILED (heap?): ", direct_3.error, "\n");
    AssertOrLog("m=3 direct ResolutionFiniteGroup(G, 4) builds", false);
else
    Print("  Direct build (n=4) time: ", t_dir_3, " s\n");
    R_dir_3 := direct_3.R;
    for n in [2, 3] do
        r_lhs := ComputeHnSafe(R_lhs_3, n);
        r_dir := ComputeHnSafe(R_dir_3, n);
        if r_lhs.ok and r_dir.ok then
            match := r_lhs.value = r_dir.value;
            Print("  m=3, H^", n, ": LHS = ", r_lhs.value,
                  " ; direct = ", r_dir.value, " ; match = ", match,
                  "\n");
            AssertOrLog(Concatenation("m=3 H^", String(n),
                                      " LHS == direct"),
                        match);
        else
            Print("  m=3, H^", n, ": LHS.ok = ", r_lhs.ok,
                  ", direct.ok = ", r_dir.ok, "\n");
            AssertOrLog(Concatenation("m=3 H^", String(n),
                                      " both routes succeeded"), false);
        fi;
    od;
fi;

# Soft check: LHS H^4 at m=3 should match H-K (Z/2)^{34} ⊕ Z/4.
Print("\n  Self-consistency: LHS H^4 at m=3 vs Harada-Kono.\n");
r_h4 := ComputeHnSafe(R_lhs_3, 4);;
if r_h4.ok then
    Print("  H^4(LHS m=3) = ", r_h4.value, "\n");
    Print("    Length = ", Length(r_h4.value), "\n");
    n_z2 := Length(Filtered(r_h4.value, x -> x = 2));
    n_z4 := Length(Filtered(r_h4.value, x -> x = 4));
    n_other := Length(Filtered(r_h4.value, x -> not x in [2, 4]));
    Print("    Z/2 count = ", n_z2, ", Z/4 count = ", n_z4,
          ", other = ", n_other, "\n");
    # Harada-Kono prediction at m=3: H^4(E_+(3); Z) = (Z/2)^{34} ⊕ Z/4.
    AssertOrLog("m=3 H^4 == (Z/2)^{34} ⊕ Z/4 (Harada-Kono)",
                n_z2 = 34 and n_z4 = 1 and n_other = 0);
else
    Print("  H^4(LHS m=3) FAILED: ", r_h4.error, "\n");
    AssertOrLog("m=3 H^4 LHS computation succeeded", false);
fi;

# ---------------------------------------------------------------------
# Task 3: m = 7 build probe (opt-in via EPLUS7_RUN).
# ---------------------------------------------------------------------

run_m7 := IsBoundGlobal("EPLUS7_RUN") and ValueGlobal("EPLUS7_RUN") = true;;

if run_m7 then
    Print("\n--- Task 3: m=7 build + H^4 probe (EPLUS7_RUN = true) ---\n");

    t0 := WallClockSec();
    det_lhs_7 := LHSResolutionEPlusDetailed(7, 5);;
    R_lhs_7 := det_lhs_7.R_E;;
    t_lhs_7 := WallClockSec() - t0;
    Print("  m=7 LHS build: ", t_lhs_7, " s\n");
    Print("  m=7 R_V dims (0..5) = ",
          List([0..5], d -> det_lhs_7.R_V!.dimension(d)), "\n");
    Print("  m=7 R_E dims (0..5) = ",
          List([0..5], d -> R_lhs_7!.dimension(d)), "\n");
    Print("  m=7 heap after build: ", det_lhs_7.heap_after_LHS_mb,
          " MB\n");

    AssertOrLog("m=7 LHS build completes without OOM", true);
    AssertOrLog("m=7 heap after build < 32 GB",
                det_lhs_7.heap_after_LHS_mb >= 0
                and det_lhs_7.heap_after_LHS_mb < 32768.0);

    # H^3 sanity probe.
    Print("\n  m=7 computing H^3...\n");
    t0 := WallClockSec();
    r7_h3 := ComputeHnSafe(R_lhs_7, 3);;
    t_h3_7 := WallClockSec() - t0;
    Print("  m=7 H^3 computation: ", t_h3_7, " s\n");
    if r7_h3.ok then
        Print("  m=7 H^3 length = ", Length(r7_h3.value), "\n");
        Print("  m=7 H^3 distinct orders = ", Set(r7_h3.value), "\n");
    else
        Print("  m=7 H^3 FAILED: ", r7_h3.error, "\n");
        AssertOrLog("m=7 H^3 computation succeeded", false);
    fi;

    # H^4 (Harada-Kono check).
    Print("\n  m=7 computing H^4...\n");
    t0 := WallClockSec();
    r7_h4 := ComputeHnSafe(R_lhs_7, 4);;
    t_h4_7 := WallClockSec() - t0;
    Print("  m=7 H^4 computation: ", t_h4_7, " s\n");
    if r7_h4.ok then
        Print("  m=7 H^4 length = ", Length(r7_h4.value), "\n");
        n_z2 := Length(Filtered(r7_h4.value, x -> x = 2));
        n_z4 := Length(Filtered(r7_h4.value, x -> x = 4));
        n_other := Length(Filtered(r7_h4.value, x -> not x in [2, 4]));
        Print("    Z/2 count = ", n_z2, ", Z/4 count = ", n_z4,
              ", other = ", n_other, "\n");
        # Harada-Kono prediction at m=7 (per Q-int A2 #136):
        # H^4(E_+(7); Z) = (Z/2)^{454} ⊕ Z/4.
        AssertOrLog("m=7 H^4 == (Z/2)^{454} ⊕ Z/4 (Harada-Kono)",
                    n_z2 = 454 and n_z4 = 1 and n_other = 0);
    else
        Print("  m=7 H^4 FAILED: ", r7_h4.error, "\n");
        AssertOrLog("m=7 H^4 computation succeeded", false);
    fi;
else
    Print("\n--- Task 3: m=7 build SKIPPED ---\n");
    Print("  Re-run with `gap -o 16g -c 'EPLUS7_RUN := true;;' ",
          "-q -b tests/test_hap_lhs_resolution.g`\n");
fi;

# ---------------------------------------------------------------------
# Summary.
# ---------------------------------------------------------------------

Print("\n=== Summary ===\n");
if IsEmpty(testFailures) then
    Print("test_hap_lhs_resolution: ALL PASS\n");
else
    Print("test_hap_lhs_resolution: FAIL (",
          Length(testFailures), " failures)\n");
    for f in testFailures do Print("  - ", f, "\n"); od;
fi;
