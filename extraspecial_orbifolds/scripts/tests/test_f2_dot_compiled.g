# test_f2_dot_compiled.g — issue #408 / PR #402 A-K4-1.
#
# Validates that the compiled `F2_Dot` and `F2_QuadDot` overrides in
# defect_rep_minus_id_optim.g produce bit-identical results to the
# original interpreted-loop versions in defect_rep_minus_id.g.

Read("defect_rep_minus_id.g");

# Capture the original interpreted-loop F2_Dot / F2_QuadDot semantics
# before optim.g overrides them. Use local lambdas to inline the loops.
LoopDot := function(u, v)
    local s, i;
    s := 0;
    for i in [1..Length(u)] do s := s + u[i] * v[i]; od;
    return s mod 2;
end;;

LoopQuadDot := function(u, Q, v)
    local n, s, i, j;
    n := Length(u);
    s := 0;
    for i in [1..n] do
        for j in [1..n] do s := s + u[i] * Q[i][j] * v[j]; od;
    od;
    return s mod 2;
end;;

# Load the overrides.
Read("defect_rep_minus_id_optim.g");

failures := 0;;
for trial in [1..40] do
    n := Random([2, 4, 8, 16, 32, 64]);
    u := List([1..n], i -> Random([0, 1]));
    v := List([1..n], i -> Random([0, 1]));
    Q := List([1..n], i -> List([1..n], j -> Random([0, 1])));
    if F2_Dot(u, v) <> LoopDot(u, v) then
        Print("FAIL: F2_Dot trial ", trial, " (n=", n, ")\n");
        failures := failures + 1;
    fi;
    if F2_QuadDot(u, Q, v) <> LoopQuadDot(u, Q, v) then
        Print("FAIL: F2_QuadDot trial ", trial, " (n=", n, ")\n");
        failures := failures + 1;
    fi;
od;

# Edge cases.
if F2_Dot([], []) <> 0 then
    Print("FAIL: F2_Dot empty\n");
    failures := failures + 1;
fi;
if F2_QuadDot([], [], []) <> 0 then
    Print("FAIL: F2_QuadDot empty\n");
    failures := failures + 1;
fi;
# Even-sum case: should give 0 mod 2.
if F2_Dot([1, 1, 1, 1], [1, 1, 1, 1]) <> 0 then
    Print("FAIL: F2_Dot all-ones (sum=4 mod 2 = 0)\n");
    failures := failures + 1;
fi;

if failures = 0 then
    Print("test_f2_dot_compiled: ALL PASS (40 random + 3 edge cases)\n");
    QuitGap(0);
else
    Print("test_f2_dot_compiled: ", failures, " FAILURE(S)\n");
    QuitGap(1);
fi;
