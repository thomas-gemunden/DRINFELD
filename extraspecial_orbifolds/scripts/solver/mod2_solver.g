# mod2_solver.g — GF(2) coboundary test.
#
# IsCoboundary2Mod2(H, c'_g) — given a finite group H and a function
#   c'_g : H × H -> Z/2 (or returning integers; we mod 2 internally),
# decide whether there exists beta : H -> Z/2 with
#   c'_g(h, k) = beta(h) - beta(hk) + beta(k)  (mod 2).
#
# Builds the boundary system A·beta = b over GF(2) and runs SolutionMat.
# Spike-confirmed at 1 ms / 10 ms for |H| = 64 / 128.

IsCoboundary2Mod2 := function(H, c)
    local elts, n, idx, A, b, i, j, ij, row, sol, zero, one;
    elts := AsList(H);
    n := Length(elts);
    idx := function(h) return Position(elts, h); end;
    zero := Zero(GF(2));
    one  := One(GF(2));

    # A: n^2 x n matrix over GF(2). Row (i, j) encodes
    #   beta(elts[i]) + beta(elts[i]*elts[j]) + beta(elts[j]) = c(elts[i], elts[j]).
    A := List([1..n*n], i -> List([1..n], j -> zero));
    b := List([1..n*n], i -> zero);
    for i in [1..n] do
        for j in [1..n] do
            row := (i - 1) * n + j;
            ij := idx(elts[i] * elts[j]);
            # +beta(i) + beta(j) - beta(ij), all mod 2 -> just sum.
            A[row][i]  := A[row][i]  + one;
            A[row][j]  := A[row][j]  + one;
            A[row][ij] := A[row][ij] + one;
            b[row]     := (c(elts[i], elts[j]) mod 2) * one;
        od;
    od;
    ConvertToMatrixRep(A, GF(2));
    ConvertToVectorRep(b, GF(2));

    # SolutionMat solves x * M = b. We have A * beta = b, equivalent to
    # beta * Transpose(A) = b. So:
    sol := SolutionMat(TransposedMat(A), b);
    return sol <> fail;
end;;

# BocksteinH1ToH2(C) — image of the connecting homomorphism
#   β : H^1(C; F_2) -> H^2(C; F_2)
# from the SES 0 -> F_2 -·²-> F_4 -> F_2 -> 0 (equivalently Sq^1).
#
# H^1(C; F_2) = Hom(C, F_2) = Hom(C^ab ⊗ F_2, F_2). For α in this Hom space,
# β(α) is the cup-square at degree 1 in F_2: β(α)(h, k) = α(h) · α(k).
#
# Returns a reduced F_2-basis of the image as a list of length-n² vectors,
# indexed compatibly with IsCoboundary2Mod2: vec[(i-1)*n + j] = α(elts[i])·α(elts[j])
# where elts := AsList(C). The basis is produced by BaseMat over GF(2).
#
# Construction of the F_2-functionals α: take phi := MaximalAbelianQuotient(C),
# pick independent abelian generators of Image(phi); for each generator whose
# order is even, the corresponding coordinate of IndependentGeneratorExponents,
# reduced mod 2, gives one α. Generators of odd order contribute no F_2
# functional (the mod-2 reduction kills them). So |hom_basis| equals the
# number of even-order elementary divisors of C^ab — i.e. the F_2-rank of
# C^ab / 2·C^ab = H^1(C; F_2).
BocksteinH1ToH2 := function(C)
    local elts, n, phi, GA, abgens, ab_orders, hom_basis, alpha_vals,
          k, ord, vecs, i, j, v, zero, one;
    elts := AsList(C);
    n := Length(elts);
    zero := Zero(GF(2));
    one  := One(GF(2));

    phi := MaximalAbelianQuotient(C);
    GA := Image(phi);
    abgens := IndependentGeneratorsOfAbelianGroup(GA);
    ab_orders := List(abgens, Order);

    # For each even-order independent generator, build α : C -> F_2 as a
    # length-n list of GF(2) values: α(elts[i]) = (k-th IGE coord of phi(elts[i])) mod 2.
    hom_basis := [];
    for k in [1..Length(abgens)] do
        ord := ab_orders[k];
        if ord mod 2 = 0 then
            alpha_vals := List(elts, g ->
                (IndependentGeneratorExponents(GA, Image(phi, g))[k] mod 2) * one);
            Add(hom_basis, alpha_vals);
        fi;
    od;

    # For each α, build β(α) as a length-n² vector with β(α)(i, j) = α(i)·α(j).
    vecs := [];
    for alpha_vals in hom_basis do
        v := List([1..n*n], i -> zero);
        for i in [1..n] do
            for j in [1..n] do
                v[(i - 1) * n + j] := alpha_vals[i] * alpha_vals[j];
            od;
        od;
        Add(vecs, v);
    od;

    if IsEmpty(vecs) then
        return [];
    fi;
    ConvertToMatrixRep(vecs, GF(2));
    return BaseMat(vecs);
end;;
