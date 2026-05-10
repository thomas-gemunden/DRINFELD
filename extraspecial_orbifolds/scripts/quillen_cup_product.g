# quillen_cup_product.g — Bar-resolution cup product for mod-2 cohomology
# of finite groups.
#
# Issue Q-3 / Task #49. See `extraspecial_orbifolds/parallel_workstreams_design.md` § Q-3.
#
# # Background
#
# For a finite group G, the mod-2 cohomology H^*(G; F_2) is a graded
# F_2-algebra under the cup product. On the (normalised) bar
# resolution, the cup product of an n-cochain `a` and an m-cochain
# `b` is the (n+m)-cochain
#
#     (a ∪ b)(g_1, ..., g_{n+m})  =  a(g_1, ..., g_n) * b(g_{n+1}, ..., g_{n+m})
#
# where the multiplication is in F_2. In characteristic 2 the cup
# product is graded-commutative on cohomology (signs vanish).
#
# # Representation
#
# A "cochain" is represented here as a function `args -> F_2 element`
# where `args` is a list of group elements of length equal to the
# cochain degree. Internally we work with F_2 = GF(2) as GAP's prime
# field; elements are 0 * Z(2) or Z(2)^0 (= 1).
#
# A "cohomology class" coming from a free-resolution-style computation
# (e.g. HAP) is typically a homomorphism on the free Z-module of
# degree-n generators. To use the bar-resolution cup product on such
# data we need an evaluation function — see `EvaluateBarCochain` for
# the deg-1 case, where every homomorphism G -> F_2 factors through
# G^{ab}.
#
# # Public API
#
#   CupProductBarResolution(G, n, m)
#       Returns a function (cochain_a, cochain_b) -> cochain_{n+m}
#       implementing the Alexander–Whitney / bar formula above.
#
#   CupProductBarResolutionEval(cochain_a, n, cochain_b, m, args)
#       Convenience evaluator: directly compute (a ∪ b)(args).
#
#   EvaluateDeg1CochainFromHom(G, hom_to_F2, g)
#       Evaluate a deg-1 cochain specified as a hom G^{ab} -> F_2.
#
# These are intentionally minimal; the heavy lifting (going from a
# HAP cohomology basis to a list of bar cochains) is the caller's job.

# ---- Evaluation primitive --------------------------------------------

# Evaluate the (un-normalised) bar-resolution cup product (a ∪ b) on a
# tuple `args = [g_1, ..., g_{n+m}]`.
#
# `cochain_a` and `cochain_b` are GAP functions; their first argument is
# expected to be a *list* of group elements of length n and m
# respectively (this matches how HAP and the standard bar formulae are
# written). Return values are F_2 elements (0 or 1 in GF(2)).
CupProductBarResolutionEval := function(cochain_a, n, cochain_b, m, args)
    local va, vb, args_a, args_b;
    if Length(args) <> n + m then
        Error("CupProductBarResolutionEval: expected ", n + m,
              " group elements, got ", Length(args));
    fi;
    args_a := args{[1..n]};
    args_b := args{[n + 1..n + m]};
    va := cochain_a(args_a);
    vb := cochain_b(args_b);
    return va * vb;   # F_2 multiplication
end;;

# ---- Public constructor ----------------------------------------------

# Build the cup-product operator (n, m) -> ((a, b) -> a ∪ b).
#
# The output is a function taking two cochains (as evaluators) and
# returning a new cochain (an evaluator on (n+m)-tuples).
CupProductBarResolution := function(G, n, m)
    return function(cochain_a, cochain_b)
        return function(args)
            return CupProductBarResolutionEval(cochain_a, n, cochain_b, m, args);
        end;
    end;
end;;

# ---- Helpers for degree-1 cochains -----------------------------------
#
# Every degree-1 cohomology class over F_2 is a homomorphism
# G^{ab}/2 -> F_2. We provide a convenience wrapper to turn such a hom
# into a bar-cochain evaluator.

# Build a deg-1 cochain evaluator from a function (g -> GF(2)).
# The evaluator takes a length-1 list [g] and returns f(g).
Deg1CochainFromFunction := function(f)
    return function(args)
        if Length(args) <> 1 then
            Error("Deg1Cochain: expected length-1 args, got ", Length(args));
        fi;
        return f(args[1]);
    end;
end;;

# Build a deg-1 cochain evaluator from a GAP group hom phi : G -> A
# (any abelian group with elements convertible to F_2; e.g. CyclicGroup(2)).
# The caller supplies `to_f2`, a function A -> GF(2). This decouples us
# from any particular F_2 encoding.
Deg1CochainFromHom := function(phi, to_f2)
    return Deg1CochainFromFunction(g -> to_f2(Image(phi, g)));
end;;

# Helper: build a function g -> (i-th coordinate of phi(g) mod 2),
# where coordinates are with respect to `gens` (an independent abelian
# generating set of Image(phi)).
Deg1CoordinateFunction := function(phi, gens, i)
    return function(g)
        local exps, img, A;
        A := Image(phi);
        img := Image(phi, g);
        # Express img in terms of `gens`. IndependentGeneratorExponents
        # is the inverse of "evaluate exponent vector on gens" for an
        # abelian group built from IndependentGeneratorsOfAbelianGroup.
        exps := IndependentGeneratorExponents(A, img);
        return (exps[i] mod 2) * Z(2)^0;
    end;
end;;

# Convenience: build a list of deg-1 cochains, one per F_2-basis vector
# of Hom(G^{ab}/2, F_2).
#
# We compute G^{ab} via MaximalAbelianQuotient(G), then quotient by 2 and
# extract its F_2 dual. Each generator of the dual gives one cochain.
#
# Returns rec(cochains := <list of evaluators>,
#             dim       := <dimension of H^1(G; F_2)>).
Deg1CochainBasis := function(G)
    local phi, A, gens, hom_list, i;
    phi := MaximalAbelianQuotient(G);
    A   := Image(phi);
    # Generators of A as an abelian group: we use IndependentGeneratorsOfAbelianGroup
    # to get a clean direct-product decomposition.
    gens := IndependentGeneratorsOfAbelianGroup(A);
    # Only generators of EVEN order contribute to H^1(G; F_2); odd-order
    # generators die after tensoring with F_2.
    hom_list := [];
    for i in [1..Length(gens)] do
        if Order(gens[i]) mod 2 = 0 then
            # The i-th basis cochain sends gens[i] -> 1, other gens[j] -> 0.
            # Evaluate on g by writing phi(g) in coords on `gens` and reading
            # off the i-th coordinate mod 2.
            Add(hom_list, i);
        fi;
    od;

    return rec(
        phi      := phi,
        abquot   := A,
        gens     := gens,
        cochains := List(hom_list, i ->
            Deg1CochainFromFunction(
                Deg1CoordinateFunction(phi, gens, i))),
        indices  := hom_list,
        dim      := Length(hom_list)
    );
end;;

Print("Loaded quillen_cup_product.g (Q-3: bar-resolution cup product).\n");
