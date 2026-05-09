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
