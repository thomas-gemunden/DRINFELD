# bar_cocycle.g — Stage B Task B1: explicit bar 3-cocycles.
#
# Source: docs/superpowers/plans/2026-05-15-quillen-integration.md
#         (Stage B, Task B1: "Bar 3-cocycle for cup products").
#
# Goal: build closed-form bar 3-cocycles on a finite group G
# representing the F_2 cohomology generators that Quillen's Theorem
# 4.6 [Q4] supplies for E_+(m). The output is a callable
#     f : G^3 -> Z/q
# that satisfies the bar 3-cocycle equation
#     f(g_1, g_2, g_3) - f(g_0 g_1, g_2, g_3) + f(g_0, g_1 g_2, g_3)
#       - f(g_0, g_1, g_2 g_3) + f(g_0, g_1, g_2) = 0   (mod q)
# strictly, not just up to homotopy.
#
# This bypasses HAP's `StandardCocycle` -- which has the V-4a bug
# (1105/4096 violations on Q_8 ω≠0 mod 8) because HAP's Syzygy
# produces a chain map up to homotopy, not strictly.
#
# What this file exports (Stage B1):
#   * F2Hom1Class(G, abelianisation_coord)
#       Build a homomorphism G -> Z (= a class in H^1(G; F_2)).
#   * Cup1x1x1(x, y, z)
#       Cup product of three degree-1 classes; satisfies the bar
#       3-cocycle equation by construction.
#   * VerifyBar3CocycleEquation(G, f, q)
#       Brute-force check that f satisfies the bar equation on G x G x G x G.
#       Returns number of violations.
#
# Future (Stage B2): Bockstein lifts for Z/4, Z/8 classes via the
# Pontryagin square at the cochain level.

# Local ternary helper (used below).
If_ := function(c, a, b) if c then return a; else return b; fi; end;;

# ---------------------------------------------------------------------
# Bar 3-cocycle equation: brute-force check.
#
# The inhomogeneous bar 3-cocycle equation is
#     f(g_1, g_2, g_3) - f(g_0 g_1, g_2, g_3) + f(g_0, g_1 g_2, g_3)
#       - f(g_0, g_1, g_2 g_3) + f(g_0, g_1, g_2) = 0   (mod q)
# Returns the number of (g_0, g_1, g_2, g_3) quadruples on which this
# fails. Useful as the V-4a-style acceptance gate.
# ---------------------------------------------------------------------

VerifyBar3CocycleEquation := function(G, f, q)
    local elts, n_viol, g0, g1, g2, g3, val;
    elts := Elements(G);
    n_viol := 0;
    for g0 in elts do
        for g1 in elts do
            for g2 in elts do
                for g3 in elts do
                    val := (f(g1, g2, g3) - f(g0*g1, g2, g3)
                            + f(g0, g1*g2, g3) - f(g0, g1, g2*g3)
                            + f(g0, g1, g2)) mod q;
                    if val <> 0 then
                        n_viol := n_viol + 1;
                    fi;
                od;
            od;
        od;
    od;
    return n_viol;
end;;

# ---------------------------------------------------------------------
# H^1 class: a group homomorphism G -> F_2 = Z/2.
#
# Caller provides the F_2-images of a generating set of G as a list
# of 0/1 ints (in F_2). We build a GAP GroupHomomorphism and wrap it
# as an F_2-valued callable.
#
# Returns a function G -> Z (values 0 or 1).
# ---------------------------------------------------------------------

F2HomFromImages := function(G, gen_images_F2)
    local Z2, gens, hom_images, hom, lift;
    gens := GeneratorsOfGroup(G);
    if Length(gen_images_F2) <> Length(gens) then
        Error("F2HomFromImages: gen_images_F2 length ",
              Length(gen_images_F2), " must match GeneratorsOfGroup(G) ",
              "length ", Length(gens));
    fi;
    Z2 := CyclicGroup(IsPermGroup, 2);
    hom_images := List(gen_images_F2, x ->
        If_(x mod 2 = 0, Identity(Z2), GeneratorsOfGroup(Z2)[1]));
    hom := GroupHomomorphismByImages(G, Z2, gens, hom_images);
    if hom = fail then
        Error("F2HomFromImages: the given gen_images do not extend to a ",
              "homomorphism G -> F_2 (the kernel of [G, G] -> 0 ",
              "is violated for this assignment).");
    fi;
    lift := function(g)
        if Image(hom, g) = Identity(Z2) then return 0; else return 1; fi;
    end;
    return lift;
end;;

# ---------------------------------------------------------------------
# Cup product of three degree-1 classes.
#
# For x, y, z : G -> F_2 group homomorphisms (i.e., bar 1-cocycles),
# the cup product is the bar 3-cocycle
#     (x \cup y \cup z)(g_1, g_2, g_3) = x(g_1) * y(g_2) * z(g_3)  mod 2.
#
# The bar 3-cocycle equation is automatic: the algebraic check we did
# in /tmp/v4a_probe* (with x, y, z homs) shows that all five terms in
# the bar boundary cancel pairwise modulo 2.
# ---------------------------------------------------------------------

Cup1x1x1 := function(x, y, z)
    return function(g1, g2, g3)
        return (x(g1) * y(g2) * z(g3)) mod 2;
    end;
end;;

# ---------------------------------------------------------------------
# Next research milestone (Stage B2): Bockstein at the cochain level.
#
# H^3(E_+(m); F_2) contains classes that are NOT triple cup products
# of degree-1 classes -- e.g. for D_8 = E_+(1), the classes x_1·w and
# x_2·w where w in H^2 is the Bockstein image of a degree-1 class.
# To represent these as bar 3-cocycles we need:
#
#   1. The cochain-level Bockstein operation β: C^n(G; F_2) ->
#      C^{n+1}(G; F_2) computed via the short exact sequence
#         0 -> Z/2 -> Z/4 -> Z/2 -> 0.
#      Explicit formula: for f: G^n -> F_2 a 2-cocycle, lift to
#      f~: G^n -> Z/4, then β(f) = (1/2) δ f~ : G^{n+1} -> Z/2.
#
#   2. Pontryagin square or P_2 -> Z/4 lift for the order-4 generator
#      of H^4(D_8; Z) = H^3(D_8; U(1)).
#
# These are the math next steps. The cup-product machinery here is
# Stage B1's deliverable and is independently useful (it confirms the
# bar 3-cocycle equation can be satisfied strictly, validating the
# whole Stage B path -- bypassing the V-4a obstacle).
# ---------------------------------------------------------------------

Print("Loaded bar_cocycle.g (Stage B1: VerifyBar3CocycleEquation, ",
      "F2HomFromImages, Cup1x1x1).\n");
