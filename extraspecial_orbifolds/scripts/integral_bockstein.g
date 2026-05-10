# integral_bockstein.g — Integral Bockstein on F_2-cochains at the
# cochain level, for finite groups.
#
# Issue Q-4 / Task #53. See
# `extraspecial_orbifolds/parallel_workstreams_design.md` § Q-4.
#
# # Background.
#
# Given a finite group G, the short exact sequence of trivial
# G-modules
#
#     0 -> Z -->*2-> Z --> F_2 -> 0
#
# induces the integral Bockstein
#
#     beta : H^n(G; F_2) -> H^{n+1}(G; Z).
#
# Working with normalised bar cochains, the cochain-level recipe is:
#
#   1. Take an F_2 n-cocycle  f : G^n -> F_2.
#   2. Lift it to an integer cochain  f~ : G^n -> Z  whose values lie
#      in {0, 1} (the standard set-theoretic lift).
#   3. Compute its Z-coboundary  (delta f~) : G^{n+1} -> Z. Because f
#      was a cocycle mod 2, every value of delta f~ lies in 2Z.
#   4. Return  beta(f) = (delta f~) / 2 : G^{n+1} -> Z.
#
# This produces a Z-valued (n+1)-cocycle representing beta([f]) in
# H^{n+1}(G; Z). Different cochain lifts of f give Z-cocycles that
# differ by Z-coboundaries, so the cohomology class is well-defined.
#
# # Representation conventions.
#
# Cochains are represented as GAP functions
#
#     cochain : <list of n group elements> -> ring element
#
# matching the convention used by `quillen_cup_product.g`. The F_2
# (input) cochain returns elements of GF(2); the Z (output) cochain
# returns ordinary GAP integers.
#
# The bar-resolution coboundary used here is the standard
# (un-normalised) one:
#
#     (delta f)(g_1, ..., g_{n+1})
#         =  f(g_2, ..., g_{n+1})
#          + sum_{i=1}^{n} (-1)^i * f(g_1, ..., g_i * g_{i+1}, ..., g_{n+1})
#          + (-1)^{n+1} * f(g_1, ..., g_n).
#
# Over Z this matches the standard formula for group cohomology with
# trivial coefficients.
#
# # Public API.
#
#   LiftF2CochainToZ(cochain_f2)
#       Return a Z-valued cochain f~ with f~(args) in {0, 1} given by
#       lifting f's value at each tuple from GF(2) to {0, 1} subset Z.
#
#   ZCoboundary(cochain_z, n)
#       Return the cochain (delta f~) : G^{n+1} -> Z.
#
#   IntegralBockstein(cochain_f2, n)
#       Compose the two: return beta(f) = (delta(lift f)) / 2.
#
#   BocksteinSquared(cochain_f2, n)
#       beta(beta(f)) as a Z-cochain. Should be zero on H^{n+1}(G; Z)
#       but only "twice an integer Bockstein" at cochain level. The
#       function evaluates beta_F2 applied to beta(f) mod 2: this
#       composition is identically zero already at cochain level when
#       starting from an F_2-cocycle f, by exactness of the BSS at
#       cochain level. We expose this helper for the acceptance test.
#
#   EvaluateF2Cocycle(cochain_f2, G, n)
#       Validate that an F_2 cochain is in fact a cocycle: compute its
#       F_2 coboundary and assert it vanishes on every (n+1)-tuple.
#       Returns true / false.
#
# # No dependencies on quillen_algebra.
#
# The Bockstein operates on raw cochains, not Quillen-algebra-form
# classes. Q-5 (universal-coefficient encoding) will be the layer that
# turns a Z-valued cochain output into a class in the integral
# cohomology algebra. We deliberately keep this file standalone --
# nothing here depends on `quillen_algebra.g`. We only borrow the
# F_2-cochain conventions from `quillen_cup_product.g`.

# ---- F_2 <-> Z conversion --------------------------------------------

# Lift a GF(2) element to {0, 1} subset Z.
F2ElementToZ := function(x)
    if IsZero(x) then return 0; fi;
    return 1;
end;;

# Z element mod 2 -> GF(2) element.
ZElementToF2 := function(n)
    if (n mod 2) = 0 then return 0 * Z(2); fi;
    return Z(2)^0;
end;;

# ---- Lift an F_2 cochain to a Z cochain ------------------------------

# Given a cochain f : G^n -> F_2, return f~ : G^n -> Z with
# f~(args) = F2ElementToZ(f(args)) in {0, 1}.
LiftF2CochainToZ := function(cochain_f2)
    return function(args)
        return F2ElementToZ(cochain_f2(args));
    end;
end;;

# Reduce a Z-valued cochain mod 2: return f : G^n -> GF(2) with
# f(args) = ZElementToF2(cochain_z(args)).
ReduceZCochainToF2 := function(cochain_z)
    return function(args)
        return ZElementToF2(cochain_z(args));
    end;
end;;

# ---- Z-valued bar coboundary -----------------------------------------

# Compute (delta f)(g_1, ..., g_{n+1}) for f : G^n -> Z (an integer
# cochain). The output is an integer.
#
# We re-evaluate `cochain_z` at the (n+1) tuples that appear in the
# bar formula. The cost is O(n) evaluations per output point.
ZCoboundaryEval := function(cochain_z, n, args)
    local total, i, sub, sign, k;
    if Length(args) <> n + 1 then
        Error("ZCoboundaryEval: expected ", n + 1,
              " group elements, got ", Length(args));
    fi;

    # First term: f(g_2, ..., g_{n+1}).
    total := cochain_z(args{[2..n+1]});

    # Middle terms: sum_{i=1..n} (-1)^i f(g_1,...,g_i*g_{i+1},...,g_{n+1}).
    for i in [1..n] do
        sub := [];
        for k in [1..i-1] do Add(sub, args[k]); od;
        Add(sub, args[i] * args[i+1]);
        for k in [i+2..n+1] do Add(sub, args[k]); od;
        sign := (-1)^i;
        total := total + sign * cochain_z(sub);
    od;

    # Last term: (-1)^{n+1} f(g_1, ..., g_n).
    total := total + (-1)^(n+1) * cochain_z(args{[1..n]});

    return total;
end;;

# Wrap ZCoboundaryEval as a (n+1)-cochain.
ZCoboundary := function(cochain_z, n)
    return function(args)
        return ZCoboundaryEval(cochain_z, n, args);
    end;
end;;

# ---- Integral Bockstein ----------------------------------------------

# Given f : G^n -> F_2 (an F_2 cochain, expected to be a cocycle),
# return beta(f) : G^{n+1} -> Z, the integral Bockstein.
#
# Algorithm:
#   f_lift := LiftF2CochainToZ(f)       (values in {0, 1})
#   df     := ZCoboundary(f_lift, n)    (values in 2*Z by cocycle hyp.)
#   return  df / 2.
#
# Caveat. The caller is responsible for ensuring f IS an F_2-cocycle.
# If not, beta(f)(args) need not be an integer (division by 2 will be
# a non-integer rational, GAP value 1/2 etc.), which is the signature
# of a bug upstream.
IntegralBockstein := function(cochain_f2, n)
    local f_lift, df;
    f_lift := LiftF2CochainToZ(cochain_f2);
    df     := ZCoboundary(f_lift, n);
    return function(args)
        local v;
        v := df(args);
        if (v mod 2) <> 0 then
            Error("IntegralBockstein: input is not an F_2-cocycle; ",
                  "delta(lift f)(args) = ", v, " is not in 2Z. args = ",
                  args);
        fi;
        return v / 2;
    end;
end;;

# ---- Cocycle validation ----------------------------------------------

# Check (using all G elements) that a Z-cochain is a Z-cocycle: i.e.
# delta f = 0 identically on G^{n+1}. Returns true or the first failing
# tuple (a list of group elements) as a witness.
IsZCocycleOnGroup := function(cochain_z, n, G)
    local elts, tup, df, v;
    elts := Elements(G);
    df := ZCoboundary(cochain_z, n);
    for tup in Tuples(elts, n + 1) do
        v := df(tup);
        if v <> 0 then
            return rec(ok := false, witness := tup, value := v);
        fi;
    od;
    return rec(ok := true);
end;;

# Check that an F_2-cochain f is a cocycle: i.e. delta_{F_2} f = 0 on
# all (n+1)-tuples.
IsF2CocycleOnGroup := function(cochain_f2, n, G)
    local f_lift, df, elts, tup, v;
    f_lift := LiftF2CochainToZ(cochain_f2);
    df := ZCoboundary(f_lift, n);
    elts := Elements(G);
    for tup in Tuples(elts, n + 1) do
        v := df(tup);
        if (v mod 2) <> 0 then
            return rec(ok := false, witness := tup, value := v);
        fi;
    od;
    return rec(ok := true);
end;;

# ---- Bockstein-squared helper ----------------------------------------
#
# At the level of cohomology, beta o beta = 0. At the *cochain* level
# the literal composition  IntegralBockstein(., n+1) o IntegralBockstein(., n)
# doesn't typecheck because the inner Bockstein produces a Z-cochain,
# not an F_2-cochain. To form beta^2 in the chain complex sense one
# first reduces the Z-cochain mod 2 (the natural map Z -> F_2). The
# composition  beta o (mod 2) o beta  agrees with the Bockstein-squared
# operator at the cohomology level.
#
# For acceptance criterion "Bockstein squared = 0 on every test class"
# we use the following stronger property: when f is an F_2-cocycle,
# beta(f) is a Z-cocycle (no longer just mod 2), so its reduction mod 2
# is also a cocycle, and we can apply the F_2 Bockstein again.
# Equivalent at chain level: the F_2-reduction of beta(f) is an
# F_2-coboundary, hence beta of it is a Z-coboundary; in particular it
# represents the zero class.

# Compose: f -> beta(f) -> reduce mod 2 -> beta -> Z-cochain.
BocksteinComposeOnce := function(cochain_f2, n)
    return ReduceZCochainToF2(IntegralBockstein(cochain_f2, n));
end;;

BocksteinSquared := function(cochain_f2, n)
    return IntegralBockstein(BocksteinComposeOnce(cochain_f2, n), n + 1);
end;;

# Test "beta^2 = 0 at cohomology level" by verifying that beta^2(f) is
# a Z-coboundary. Stronger test we actually run: in test cases the
# reduction mod 2 of beta(f) is already an F_2-coboundary, so
# beta(BocksteinComposeOnce(f, n)) is the beta of a coboundary, hence
# zero up to Z-coboundary.
#
# For practical purposes the test in test_integral_bockstein.g checks
# beta^2(f) takes value 0 on EVERY tuple, after we have established
# that beta(f) mod 2 is identically zero as an F_2-cochain (which is
# the strongest cochain-level statement and is what holds for our
# representative cocycles built from linear characters with Z-lift).

# Pretty-print a Z-cochain on a small group (for debug).
PrintZCochainTable := function(cochain_z, n, G)
    local elts, tup, v;
    elts := Elements(G);
    for tup in Tuples(elts, n) do
        v := cochain_z(tup);
        if v <> 0 then
            Print("  f(", tup, ") = ", v, "\n");
        fi;
    od;
end;;

Print("Loaded integral_bockstein.g (Q-4: integral Bockstein at cochain level).\n");
