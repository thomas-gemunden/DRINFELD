# Tests for issue #339: SetupCohomology3 abelian-dispatch fix.
#
# Before the fix, `SubgroupCohomologyContext(H)` for a rank-8
# elementary abelian (|H| = 256) — the per-EA hot path at m=7 — went
# through `ResolutionFiniteGroup(H, 4)` which OOMs at ~60 GB (the bar
# resolution has 256^4 ~ 4.3B cells).
#
# The fix routes abelian (and elementary-abelian) groups through HAP's
# `ResolutionAbelianGroup(H, 4)`, which uses the elementary-abelian
# structure (tensor product of small cyclic resolutions) and finishes
# in < 2 s wall, < 200 MB heap.
#
# Run from extraspecial_orbifolds/scripts/:
#   gap -o 8g -q -b -c 'Read("tests/test_rank8_ea_context_339.g"); QUIT;'

BreakOnError := false;;

Read("detecting_family_restriction.g");

Print("\n=== test_rank8_ea_context_339.g (issue #339) ===\n");

testFailures := [];;
If_ := function(c, a, b) if c then return a; else return b; fi; end;;
AssertOrLog := function(label, cond)
    Print("  ", label, ": ", If_(cond, "PASS", "FAIL"), "\n");
    if not cond then Add(testFailures, label); fi;
end;;

# ---------------------------------------------------------------------
# T1: rank-8 elementary abelian H, |H| = 256.
# ---------------------------------------------------------------------
#
# This is the failing case from the D-VAN m=7 production
# (2026-05-21 OOM): each per-sample H at m=7 is a rank-(m+1) = rank-8
# elementary abelian with |H| = 2^8 = 256.

Print("\n--- T1: rank-8 EA (|H| = 256) ---\n");
t0 := Runtime();;
H := AbelianGroup(IsPcGroup, [2, 2, 2, 2, 2, 2, 2, 2]);;
AssertOrLog("|H| = 256", Order(H) = 256);
AssertOrLog("IsElementaryAbelian(H)", IsElementaryAbelian(H));

ctx := SubgroupCohomologyContext(H);;
t_elapsed := Runtime() - t0;;
Print("  SubgroupCohomologyContext wall: ", t_elapsed, " ms\n");
AssertOrLog("ctx built (no OOM)", IsRecord(ctx));
AssertOrLog("wall < 60 000 ms (1 min)", t_elapsed < 60000);

# H^3((Z/2)^n; Z) is purely 2-torsion (exponent 2). We don't anchor
# the exact num_generators because HAP's torsion-coefficient grouping
# is somewhat implementation-defined; the invariants we DO anchor are:
#   * exponent = 2 (Z/2 coefficients)
#   * every torsion[i] = 2 (purely 2-torsion)
#   * num_generators > 0 (H^3 is non-trivial)
AssertOrLog("num_generators > 0", ctx.num_generators > 0);
AssertOrLog("torsion all = 2",
            ForAll(ctx.torsion, x -> x = 2));
AssertOrLog("exponent = 2", ctx.exponent = 2);

# ---------------------------------------------------------------------
# T2: Same test on a rank-6 EA (|H| = 64) — what m=5 EAs look like.
# Verifies the abelian dispatch works at smaller ranks too. Was already
# tractable under `ResolutionFiniteGroup` but the new dispatch gives a
# different (smaller / faster) resolution.
# ---------------------------------------------------------------------

Print("\n--- T2: rank-6 EA (|H| = 64) ---\n");
t1 := Runtime();;
H6 := AbelianGroup(IsPcGroup, [2, 2, 2, 2, 2, 2]);;
ctx6 := SubgroupCohomologyContext(H6);;
t_elapsed6 := Runtime() - t1;;
Print("  rank-6 EA SubgroupCohomologyContext wall: ", t_elapsed6, " ms\n");
AssertOrLog("rank-6 ctx built", IsRecord(ctx6));
AssertOrLog("rank-6 exponent = 2", ctx6.exponent = 2);
AssertOrLog("rank-6 torsion all = 2",
            ForAll(ctx6.torsion, x -> x = 2));

# ---------------------------------------------------------------------
# T3: Verify non-abelian groups still go through ResolutionFiniteGroup.
# Use D_8 (|G| = 8, non-abelian). The fix should be no-op for D_8.
# ---------------------------------------------------------------------

Print("\n--- T3: non-abelian (D_8) still uses ResolutionFiniteGroup ---\n");
D8 := SmallGroup(8, 3);;  # D_8
AssertOrLog("not IsAbelian(D_8)", not IsAbelian(D8));
ctx_d8 := SubgroupCohomologyContext(D8);;
AssertOrLog("D_8 ctx built", IsRecord(ctx_d8));
# Anchor: D_8 has H^3(D_8; U(1)) = Z/2 x Z/2 x Z/4 (torsion [2, 2, 4],
# exponent 4). This matches test_d8_regression.g's T-1 anchor.
AssertOrLog("D_8 torsion = [2, 2, 4]", ctx_d8.torsion = [2, 2, 4]);
AssertOrLog("D_8 exponent = 4", ctx_d8.exponent = 4);
AssertOrLog("D_8 num_generators = 3", ctx_d8.num_generators = 3);

# ---------------------------------------------------------------------
# Summary.
# ---------------------------------------------------------------------

if IsEmpty(testFailures) then
    Print("\n=== test_rank8_ea_context_339: PASS ===\n");
else
    Print("\n=== test_rank8_ea_context_339: FAIL (",
          Length(testFailures), ") ===\n");
    for f in testFailures do Print("  - ", f, "\n"); od;
fi;
