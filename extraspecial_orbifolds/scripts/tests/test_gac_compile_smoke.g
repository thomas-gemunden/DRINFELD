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

if failures = 0 then
    Print("\ntest_gac_compile_smoke: ALL PASS\n");
    QuitGap(0);
else
    Print("\ntest_gac_compile_smoke: ", failures, " FAILURE(S)\n");
    QuitGap(1);
fi;
