# test_gac_compile_smoke.g — verify gac-compiled abelian_branch_fast.so
# matches the interpreted version on a small synthetic example
# (issue #286).
#
# Usage:
#   cd extraspecial_orbifolds/scripts
#   ./compile_codebase.sh
#   gap -q -b tests/test_gac_compile_smoke.g

failures := 0;;

Read("load_compiled.g");

if not IsBoundGlobal("ClassifyAbelianBranchFast") then
    Print("[smoke] T1 FAIL: ClassifyAbelianBranchFast not bound after ",
          "load_compiled.g\n");
    QuitGap(1);
fi;
Print("[smoke] T1 PASS: ClassifyAbelianBranchFast bound\n");

H := AbelianGroup([2, 2, 2]);;
omega_trivial := function(a, b, c) return 0; end;;

res := ClassifyAbelianBranchFast(H, omega_trivial, 2);;
if res.is_coboundary <> true then
    Print("[smoke] T2 FAIL: trivial omega should give is_coboundary=true; ",
          "got ", res.is_coboundary, "\n");
    failures := failures + 1;
elif res.method <> "abelian_branch_fast_q_b" then
    Print("[smoke] T2 FAIL: method field mismatch: ", res.method, "\n");
    failures := failures + 1;
elif not IsInt(res.wall_ms) then
    Print("[smoke] T2 FAIL: wall_ms not an integer: ", res.wall_ms, "\n");
    failures := failures + 1;
else
    Print("[smoke] T2 PASS: trivial omega returns is_coboundary=true ",
          "(wall_ms=", res.wall_ms, ")\n");
fi;

ones_q := List([1..Length(res.q_omega)], i -> 0);;
if res.q_omega <> ones_q then
    Print("[smoke] T3 FAIL: q_omega for trivial cocycle should be all 0; ",
          "got ", res.q_omega, "\n");
    failures := failures + 1;
else
    Print("[smoke] T3 PASS: q_omega = ", Length(res.q_omega), " zeros\n");
fi;

# T4: mod2_solver.so + transgression_kernel.so are bound after load.
Print("[smoke] T4: mod2_solver + transgression_kernel binding\n");
for fn_name in ["BoundaryMatrixGF2", "IsCoboundary2Mod2",
                "IsCoboundary2Mod2WithLift", "IsCoboundary2Mod2Vec",
                "SetupCohomology3", "StandardCocycleOf", "IsCoboundary2"] do
    if not IsBoundGlobal(fn_name) then
        Print("[smoke] T4 FAIL: ", fn_name, " not bound\n");
        failures := failures + 1;
    fi;
od;
if failures = 0 then
    Print("[smoke] T4 PASS: all 7 mod2_solver/transgression_kernel functions bound\n");
fi;

# T5: BoundaryMatrixGF2 on D_8 returns a sensible matrix shape.
Print("[smoke] T5: BoundaryMatrixGF2 on D_8 sanity\n");
D8 := DihedralGroup(8);;
A := BoundaryMatrixGF2(D8);;
if Length(A) <> 64 then  # |D_8|^2 = 8^2 = 64 rows
    Print("[smoke] T5 FAIL: BoundaryMatrixGF2(D_8) has ", Length(A),
          " rows; expected 64\n");
    failures := failures + 1;
elif Length(A[1]) <> 8 then  # |D_8| = 8 columns
    Print("[smoke] T5 FAIL: BoundaryMatrixGF2(D_8) has ", Length(A[1]),
          " cols; expected 8\n");
    failures := failures + 1;
else
    Print("[smoke] T5 PASS: BoundaryMatrixGF2(D_8) shape 64x8\n");
fi;

if failures = 0 then
    Print("\ntest_gac_compile_smoke: ALL PASS\n");
    QuitGap(0);
else
    Print("\ntest_gac_compile_smoke: ", failures, " FAILURE(S)\n");
    QuitGap(1);
fi;
