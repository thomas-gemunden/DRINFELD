# steenrod_cup1.g — Steenrod cup-1 product on bar cochains.
#
# Issue #160 (Q-int B2-1). Spec:
# docs/superpowers/specs/2026-05-15-path3-pontryagin-square-design.md
#
# Background.
# The Steenrod ∪₁ product is a chain-level operation on cochains that
# measures the failure of the cup product to be (graded-)commutative
# at the cochain level. It is the second-order term in the Steenrod
# squares construction (Sq^1 is the Bockstein, Sq^i for i ≥ 1 are
# defined via ∪_{i-1}). The Steenrod 1947 paper "Products of cocycles
# and extensions of mappings", Ann. Math. 48, 290-320 is the original
# reference. We follow the inhomogeneous-bar-cochain conventions used
# elsewhere in this codebase.
#
# Formula (for the inhomogeneous bar resolution of a group G).
# For α a p-cochain and β a q-cochain, both on G with values in a
# commutative ring R, the cup-1 product α ∪₁ β is the (p+q-1)-cochain
#
#     (α ∪₁ β)(g_1, ..., g_{p+q-1}) =
#         sum_{i=0}^{p-1} (-1)^{i*(q-1)}
#             · α(g_1, ..., g_i,
#                 g_{i+1} * g_{i+2} * ... * g_{i+q},
#                 g_{i+q+1}, ..., g_{p+q-1})
#             · β(g_{i+1}, g_{i+2}, ..., g_{i+q}).
#
# Over F_2 the signs drop. Over Z (used inside Pontryagin square) the
# signs matter.
#
# Defining property (the "coboundary identity" — the cup-1 product
# interpolates between commuted cup products):
#
#     d(α ∪₁ β) = dα ∪₁ β + (-1)^p α ∪₁ dβ
#               + (-1)^{p*q} β ∪ α - α ∪ β.
#
# Over F_2 the last two terms become α ∪ β + β ∪ α. This identity is
# the acceptance test (TestBarCup1CoboundaryIdentity below).

If_ := function(c, a, b) if c then return a; else return b; fi; end;;

# Apply a callable to a list of arguments.
_SC1_Call := function(f, args)
    return CallFuncList(f, args);
end;;

# (α ∪₁ β)(g₁, ..., g_{p+q-1}) over a generic ring (caller is
# responsible for the ring; we just use integer +/- and multiplication
# on the values returned by alpha and beta).
#
# `alpha` is a callable taking p group elements.
# `beta`  is a callable taking q group elements.
# Returns a callable taking (p+q-1) group elements.
SteenrodCup1 := function(alpha, p, beta, q)
    if not (IsInt(p) and p >= 1) then
        Error("SteenrodCup1: p must be a positive integer, got ", p);
    fi;
    if not (IsInt(q) and q >= 1) then
        Error("SteenrodCup1: q must be a positive integer, got ", q);
    fi;
    return function(arg)
        local args, total, i, j, sign, prod, alpha_args, beta_args,
              expected_arity;
        args := arg;
        expected_arity := p + q - 1;
        if Length(args) <> expected_arity then
            Error("SteenrodCup1 cochain: expected ", expected_arity,
                  " args, got ", Length(args));
        fi;
        total := 0;
        for i in [0..p-1] do
            sign := If_(IsEvenInt(i * (q - 1)), 1, -1);
            # Product of the q middle elements args[i+1] * ... * args[i+q].
            prod := args[i+1];
            for j in [i+2..i+q] do prod := prod * args[j]; od;
            # α's args: take indices 1..i, then prod, then i+q+1..p+q-1.
            alpha_args := Concatenation(
                args{[1..i]}, [prod], args{[i+q+1..expected_arity]});
            beta_args := args{[i+1..i+q]};
            total := total + sign * _SC1_Call(alpha, alpha_args)
                                  * _SC1_Call(beta, beta_args);
        od;
        return total;
    end;
end;;

# Cup product on bar cochains (ordinary, not ∪₁):
#     (α ∪ β)(g_1, ..., g_{p+q}) = α(g_1, ..., g_p) · β(g_{p+1}, ..., g_{p+q}).
# Provided here for convenience and for the coboundary-identity test.
BarCup := function(alpha, p, beta, q)
    if not (IsInt(p) and p >= 1) then
        Error("BarCup: p must be a positive integer, got ", p);
    fi;
    if not (IsInt(q) and q >= 1) then
        Error("BarCup: q must be a positive integer, got ", q);
    fi;
    return function(arg)
        local args, expected_arity;
        args := arg;
        expected_arity := p + q;
        if Length(args) <> expected_arity then
            Error("BarCup cochain: expected ", expected_arity,
                  " args, got ", Length(args));
        fi;
        return _SC1_Call(alpha, args{[1..p]})
             * _SC1_Call(beta,  args{[p+1..p+q]});
    end;
end;;

# Bar coboundary of a cochain.
#     (dα)(g_1, ..., g_{p+1}) =
#         α(g_2, ..., g_{p+1})
#         + sum_{i=1}^{p} (-1)^i α(g_1, ..., g_i * g_{i+1}, ..., g_{p+1})
#         + (-1)^{p+1} α(g_1, ..., g_p).
BarCoboundary := function(alpha, p)
    return function(arg)
        local args, total, i, sign, sub_args;
        args := arg;
        if Length(args) <> p + 1 then
            Error("BarCoboundary cochain: expected ", p+1, " args, got ",
                  Length(args));
        fi;
        # Term 0: α(g_2, ..., g_{p+1}).
        total := _SC1_Call(alpha, args{[2..p+1]});
        # Terms 1..p: sign (-1)^i applied to product-collapse at index i.
        for i in [1..p] do
            sign := If_(IsEvenInt(i), 1, -1);
            sub_args := Concatenation(
                args{[1..i-1]},
                [args[i] * args[i+1]],
                args{[i+2..p+1]});
            total := total + sign * _SC1_Call(alpha, sub_args);
        od;
        # Term p+1: (-1)^{p+1} α(g_1, ..., g_p).
        if IsEvenInt(p + 1) then
            total := total + _SC1_Call(alpha, args{[1..p]});
        else
            total := total - _SC1_Call(alpha, args{[1..p]});
        fi;
        return total;
    end;
end;;

# Test the cup-1 coboundary identity over F_2 (signs drop).
# Given α a p-cochain and β a q-cochain on G, both F_2-valued, check
# d(α ∪₁ β) - dα ∪₁ β - α ∪₁ dβ - α ∪ β - β ∪ α  ≡ 0  (mod 2)
# on every (p+q)-tuple of elements of G. Returns the violation count.
TestBarCup1CoboundaryIdentity := function(G, alpha, p, beta, q)
    local elts, cup1_ab, dcup1_ab, da, db, da_cup1_b, a_cup1_db,
          ab_cup, ba_cup, n_viol, total, args, val;
    elts := AsList(G);
    cup1_ab := SteenrodCup1(alpha, p, beta, q);
    dcup1_ab := BarCoboundary(cup1_ab, p + q - 1);
    da := BarCoboundary(alpha, p);
    db := BarCoboundary(beta, q);
    da_cup1_b := SteenrodCup1(da, p + 1, beta, q);
    a_cup1_db := SteenrodCup1(alpha, p, db, q + 1);
    ab_cup := BarCup(alpha, p, beta, q);
    ba_cup := BarCup(beta, q, alpha, p);

    n_viol := 0;
    total := 0;
    for args in Tuples(elts, p + q) do
        val := (_SC1_Call(dcup1_ab, args)
              + _SC1_Call(da_cup1_b, args)
              + _SC1_Call(a_cup1_db, args)
              + _SC1_Call(ab_cup, args)
              + _SC1_Call(ba_cup, args)) mod 2;
        if val <> 0 then n_viol := n_viol + 1; fi;
        total := total + 1;
    od;
    return rec(violations := n_viol, total := total);
end;;

Print("Loaded steenrod_cup1.g ",
      "(SteenrodCup1, BarCup, BarCoboundary, TestBarCup1CoboundaryIdentity).\n");
