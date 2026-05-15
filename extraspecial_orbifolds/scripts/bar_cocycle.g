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
# Stage B2: cochain-level Bockstein and related operations.
#
# The Bockstein β : H^n(G; F_2) -> H^{n+1}(G; F_2) is induced by the
# short exact sequence of coefficient groups
#     0 -> Z/2 -> Z/4 -> Z/2 -> 0.
#
# At the cochain level: given a cocycle f : G^n -> F_2 (values in
# {0, 1}), choose any lift f-tilde : G^n -> Z/4 with f-tilde(σ) ∈
# {0, 1} ⊂ Z/4. Then δ(f-tilde) takes values in 2 · Z/4 (since f is
# a Z/2-cocycle, so δf ≡ 0 mod 2), and we set
#     β(f)(σ) := (1/2) · δ(f-tilde)(σ)  mod 2.
#
# This gives a cocycle β(f) : G^{n+1} -> F_2 whose class in
# H^{n+1}(G; F_2) is the Bockstein image.
#
# Specialised formulas (derived in B2 research notes):
#   * β(x) = x ∪ x  for x ∈ H^1(G; F_2).
#   * β(x ∪ y) = x² · y + x · y²  for x, y ∈ H^1.  (β is a derivation
#     in F_2 cohomology.)
# These are all expressible as triple cup products, so for E_+(m)'s
# degree-3 F_2 cohomology (m ≥ 2: only deg-1 generators × Quillen
# relations), nothing beyond `Cup1x1x1` is needed.
#
# The genuine novelty at Stage B2 is for higher integer torsion:
# Z/4-valued bar 3-cocycles (the order-4 class in H^3(D_8; U(1)) and
# in H^3(E_+(3); U(1))) and Z/8-valued (H^3(E_+(2); U(1))). These
# come from the Pontryagin square P : H²(G; F_2) -> H⁴(G; Z/4) and
# its higher analogues; see Stage B2 follow-up tasks in the plan.

# ---------------------------------------------------------------------
# Cup product of two degree-1 classes.
#
# For x, y : G -> F_2 group homomorphisms (= bar 1-cocycles), the cup
# product (x ∪ y)(g_1, g_2) := x(g_1) · y(g_2) is a bar 2-cochain.
# It IS a bar 2-cocycle (the bar 2-cocycle equation δ(x∪y) = 0 mod 2
# reduces to bilinearity of x · y over the homomorphism property of
# x and y).
# ---------------------------------------------------------------------

Cup1x1 := function(x, y)
    return function(g1, g2)
        return (x(g1) * y(g2)) mod 2;
    end;
end;;

# ---------------------------------------------------------------------
# Bar 2-cocycle equation (brute-force check, mod q).
#
# δf(g_0, g_1, g_2) = f(g_1, g_2) - f(g_0 g_1, g_2)
#                    + f(g_0, g_1 g_2) - f(g_0, g_1)
# Returns the violation count on G × G × G.
# ---------------------------------------------------------------------

VerifyBar2CocycleEquation := function(G, f, q)
    local elts, n_viol, g0, g1, g2, val;
    elts := Elements(G);
    n_viol := 0;
    for g0 in elts do
        for g1 in elts do
            for g2 in elts do
                val := (f(g1, g2) - f(g0*g1, g2) + f(g0, g1*g2)
                        - f(g0, g1)) mod q;
                if val <> 0 then n_viol := n_viol + 1; fi;
            od;
        od;
    od;
    return n_viol;
end;;

# ---------------------------------------------------------------------
# Cochain-level Bockstein for a 2-cocycle f : G^2 -> F_2.
#
# Input: G a group; f a function G^2 -> {0, 1} (a Z/2-valued 2-cocycle
# of the bar complex).
#
# Output: a function G^3 -> {0, 1} (the Bockstein image, a Z/2-valued
# 3-cocycle).
#
# Algorithm: lift f to f-tilde : G^2 -> {0, 1} ⊂ Z (the trivial lift),
# compute δ(f-tilde) : G^3 -> Z (which by f being a F_2-cocycle has
# all values in {-2, 0, 2}), divide by 2, reduce mod 2.
# ---------------------------------------------------------------------

BocksteinAt2 := function(G, f)
    return function(g0, g1, g2)
        local delta_int;
        delta_int := f(g1, g2) - f(g0*g1, g2) + f(g0, g1*g2) - f(g0, g1);
        # delta_int ∈ {-2, 0, 2} when f is an F_2-cocycle. (1/2) δ mod 2:
        return (delta_int / 2) mod 2;
    end;
end;;

# ---------------------------------------------------------------------
# Cochain-level Bockstein for a 1-cocycle x : G -> F_2 (i.e. a hom).
#
# For a hom, β(x)(g_0, g_1) := (1/2)·(x(g_1) - x(g_0 g_1) + x(g_0)).
# Closed form: β(x) = x · x, i.e. (x ∪ x)(g_0, g_1) = x(g_0) · x(g_1).
# We expose this as a primitive in case callers want to use it as
# a 2-cocycle to compose further (e.g. cup with a degree-1 class).
# ---------------------------------------------------------------------

BocksteinAt1 := function(G, x)
    # = Cup1x1(x, x), but written via the Bockstein formula for clarity.
    return function(g0, g1)
        local delta_int;
        delta_int := x(g1) - x(g0*g1) + x(g0);
        return (delta_int / 2) mod 2;
    end;
end;;

# ---------------------------------------------------------------------
# Next research milestone (Stage B2 follow-up): Pontryagin square.
#
# For F_2-cohomology at H^3, the cup-product + Bockstein machinery
# here suffices (since β is a derivation and is expressible in cup
# products of degree-1 classes).
#
# The genuine novelty needed for the full Quillen integration is the
# Pontryagin square P : H²(G; F_2) -> H⁴(G; Z/4), which builds the
# Z/4-valued bar cocycles representing the order-4 generators of
# H⁴(G; Z) = H³(G; U(1)). For E_+(m):
#   * m = 1 (D_8): order-4 generator (1 class).
#   * m = 3: order-4 generator (1 class).
#   * m = 2: order-8 generator (1 class) -- requires the iterated
#     Bockstein (or higher Pontryagin construction).
#
# Implementation sketch (Steenrod's 1952 formula; see Brown
# "Cohomology of Groups" §V.6 for a treatment specialised to groups):
# For u : G^2 -> F_2 a 2-cocycle, the Pontryagin square is
#   P(u)(g_0, g_1, g_2, g_3) :=
#     u-tilde(g_0, g_1) · u-tilde(g_2, g_3)
#       + u-tilde(g_0, g_1·g_2) · u-tilde(g_2, g_3)
#       + lower-order correction terms involving ∪_1 products
# where u-tilde is the trivial {0, 1} ⊂ Z/4 lift. Reading this off
# gives P(u) : G^4 -> Z/4 satisfying the bar 4-cocycle equation
# mod 4. Under the deg-shift iso H^4(G; Z) ≅ H^3(G; U(1)) we then
# extract a bar 3-cocycle ω : G^3 -> Z/4.
#
# The shift G^4 -> G^3 corresponds to the connecting map of the
# coefficient SES 0 -> Z -> R -> U(1) -> 0; concretely it sets g_0
# to identity and reads off (g_1, g_2, g_3) -> P(u)(1, g_1, g_2, g_3)
# (or a similar normalised form). Verifying the bar 3-cocycle
# equation is the acceptance gate.
# ---------------------------------------------------------------------

Print("Loaded bar_cocycle.g (Stage B1+B2: cup products, ",
      "F_2 Bockstein, bar 2/3 cocycle equation verifiers).\n");
