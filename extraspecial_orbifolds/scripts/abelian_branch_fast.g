# abelian_branch_fast.g — fast q_ω + b_ω abelian-branch classifier (#434).
#
# For abelian H, [ω] in H^3(H; U(1)) is modular-data-trivial iff
# q_ω ≡ 0 AND b_ω ≡ 0 (mod N, the cocycle's coefficient exponent), where
#
#     q_ω(a)    = ω(a, a, a) mod N                                 (quadratic)
#     b_ω(a, b) = q_ω(a*b) - q_ω(a) - q_ω(b) mod N                 (polarisation)
#
# This skips the O(|H|^4) S-matrix build of ComputeModularData. Direct
# cocycle evaluation: O(|H|) for q, O(|H|^2) for b.
#
# Implementation: Option 3 per the issue #434 comment — direct cocycle
# evaluation, no partial-S, no ComputeModularData calls.
#
# Used by the K-4a production classifier (k4a_classify.g) when
# `_K4A_USE_FAST_ABELIAN_BRANCH = true`, and by the e2e injectivity test
# `tests/test_detf_e2e_injectivity.g` when `DETF_E2E_FAST_ABELIAN = true`.


DeclareGlobalFunction("ClassifyAbelianBranchFast");

InstallGlobalFunction(ClassifyAbelianBranchFast, function(H, omega_cocycle, modulus)
    local elems, n, q, b, i, j, ab, q_a, q_b, q_ab,
          is_q_trivial, is_b_trivial, is_trivial, t0, row;
    t0 := Runtime();
    elems := AsList(H);
    n := Length(elems);
    q := List(elems, a -> omega_cocycle(a, a, a) mod modulus);
    b := EmptyPlist(n);
    for i in [1..n] do
        row := EmptyPlist(n);
        q_a := q[i];
        for j in [1..n] do
            ab := elems[i] * elems[j];
            q_b := q[j];
            q_ab := q[Position(elems, ab)];
            row[j] := (q_ab - q_a - q_b) mod modulus;
        od;
        b[i] := row;
    od;
    is_q_trivial := ForAll(q, x -> x = 0);
    is_b_trivial := ForAll(b, r -> ForAll(r, x -> x = 0));
    is_trivial := is_q_trivial and is_b_trivial;
    return rec(
        is_abelian     := true,
        is_coboundary  := is_trivial,
        q_omega        := q,
        b_omega        := b,
        is_q_trivial   := is_q_trivial,
        is_b_trivial   := is_b_trivial,
        wall_ms        := Runtime() - t0,
        method         := "abelian_branch_fast_q_b"
    );
end);

if IsBoundGlobal("_LogStamped") then
    _LogStamped("Loaded abelian_branch_fast.g (#434).");
else
    Print("Loaded abelian_branch_fast.g (#434).\n");
fi;
