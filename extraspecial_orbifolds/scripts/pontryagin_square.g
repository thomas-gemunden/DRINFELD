# pontryagin_square.g — Steenrod's cochain-level Pontryagin square.
#
# Issue #161 (Q-int B2-2). Spec:
# docs/superpowers/specs/2026-05-15-path3-pontryagin-square-design.md
#
# Formula (Brumfiel-Morgan 1973 Topology 12:105-122, Lemma 3.5(b),
# specialised to the closed case with no relative boundary terms):
#
#     P(α)(g₁, ..., g_{2n}) = (α̃ ∪ α̃)(...) + (δα̃ ∪₁ α̃)(...)   mod 4
#
# where
#   - α is an F_2-valued n-cocycle (n = 2 for our H^4(G; Z/4) use case);
#   - α̃ is its set-theoretic integer lift (values in {0, 1} ⊂ Z);
#   - δα̃ is the integer coboundary, valued in 2Z (since α is an F_2
#     cocycle);
#   - ∪ is the ordinary cup product, ∪₁ the Steenrod cup-1 product
#     (from #160).
#
# Cocycle verification (over Z, evaluated mod 4):
#   δ(α̃ ∪ α̃)     = δα̃ ∪ α̃ − α̃ ∪ δα̃
#   δ(δα̃ ∪₁ α̃) = (δα̃ ∪₁ δα̃) + (δα̃ ∪ α̃) + (α̃ ∪ δα̃)
#                  (Leibniz rule for ∪₁, using δδα̃ = 0)
#   Sum         = 2(δα̃ ∪ α̃) + (δα̃ ∪₁ δα̃)
# Both summands are in 4Z (each ∪ factor in 2Z), so δ[P(α)] ≡ 0 mod 4.
#
# The output is a Z/4-valued 2n-cocycle. For n=2 it is a 4-cocycle.
#
# References:
#   - Steenrod, N. "Products of cocycles and extensions of mappings",
#     Ann. Math. 48 (1947), 290–320.
#   - Brumfiel, G. & Morgan, J. "Quadratic functions, the index modulo
#     8, and a Z/4-Hirzebruch formula", Topology 12 (1973), 105–122.
#     Local copy: docs/main.pdf.

if not IsBoundGlobal("SteenrodCup1") then
    Read("steenrod_cup1.g");
fi;

# PontryaginSquare(α, n)
#
# α: a callable G^n -> F_2 (or {0, 1} ⊂ Z) representing an n-cocycle.
# n: positive integer, the degree of α (n=2 is the case used by #137 /
#    A-5c-Z4 / Path 3).
#
# Returns a callable G^{2n} -> Z/4 representing P(α) ∈ H^{2n}(G; Z/4).
PontryaginSquare := function(alpha, n)
    local cup_aa, d_alpha, cup1_da_a;
    if not (IsInt(n) and n >= 1) then
        Error("PontryaginSquare: n must be a positive integer, got ", n);
    fi;
    cup_aa     := BarCup(alpha, n, alpha, n);              # G^{2n} -> Z
    d_alpha    := BarCoboundary(alpha, n);                 # G^{n+1} -> Z
    cup1_da_a  := SteenrodCup1(d_alpha, n + 1, alpha, n);  # G^{2n} -> Z
    return function(arg)
        local args;
        args := arg;
        if Length(args) <> 2 * n then
            Error("PontryaginSquare cochain: expected ", 2*n,
                  " args, got ", Length(args));
        fi;
        return (CallFuncList(cup_aa,    args)
              + CallFuncList(cup1_da_a, args)) mod 4;
    end;
end;;

# Verify the bar 2n-cocycle equation for a Z/4-valued cochain f on G.
# Returns rec(violations, total). Used as the #161 acceptance test.
VerifyBar2nCocycleEquationMod4 := function(G, f, n)
    local elts, total, violations, args, val, i, sign, sub_args;
    elts := AsList(G);
    total := 0;
    violations := 0;
    for args in Tuples(elts, 2 * n + 1) do
        # (df)(g_1, ..., g_{2n+1})
        # = f(g_2, ..., g_{2n+1})
        # + sum_{i=1}^{2n} (-1)^i f(g_1, ..., g_i*g_{i+1}, ..., g_{2n+1})
        # + (-1)^{2n+1} f(g_1, ..., g_{2n}).
        val := CallFuncList(f, args{[2..2*n+1]});
        for i in [1..2*n] do
            if IsEvenInt(i) then sign := 1; else sign := -1; fi;
            sub_args := Concatenation(
                args{[1..i-1]},
                [args[i] * args[i+1]],
                args{[i+2..2*n+1]});
            val := val + sign * CallFuncList(f, sub_args);
        od;
        # (-1)^{2n+1} = -1.
        val := val - CallFuncList(f, args{[1..2*n]});
        val := val mod 4;
        if val <> 0 then violations := violations + 1; fi;
        total := total + 1;
    od;
    return rec(violations := violations, total := total);
end;;

Print("Loaded pontryagin_square.g ",
      "(PontryaginSquare, VerifyBar2nCocycleEquationMod4).\n");
