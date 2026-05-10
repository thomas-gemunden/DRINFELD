# BRW(m) action on H^3(E_+(m); U(1)).
#
# For each generator y of BRW(m), the conjugation map
#     alpha_y : E_+(m) -> E_+(m),   g -> y * g * y^(-1)
# is an automorphism of E_+(m). Its pullback action on cohomology gives
# a linear map
#     alpha_y^* : H^3(E_+(m); U(1)) -> H^3(E_+(m); U(1)).
#
# H^3 has torsion structure [d_1, ..., d_k], so alpha_y^* is a k x k
# integer matrix M_y with the property that its j-th column lives in
# (Z/d_1) x ... x (Z/d_k). Stacking the M_y for the BRW(m) generators
# gives the image of BRW(m) -> Aut(H^3) = Aut(prod Z/d_i).
#
# Reference math: see issue #30. Implementation strategy follows the
# existing AutomorphismOrbits in src/modular_data.g, which uses
# HAP's EquivariantChainMap + GroupCohomologyFunctor to lift an
# Aut(E_+(m)) element to a matrix on the integer cycle basis. We
# package that into a per-H^3-generator coordinate matrix.
#
# Output: rec with field `matrices` (a list of k x k integer matrices,
# one per BRW generator), plus the H^3 setup data and BRW generators.
#
# Acceptance:
#   - For m = 2: matrices generate a subgroup of Aut(Z/2^9 x Z/8) of
#     order equal to |image of BRW(2)/E_+(2) -> Aut(H^3)|.  The image
#     of E_+(m) itself is trivial (inner automorphisms act trivially on
#     cohomology), so we expect the image to be a quotient of
#     O^+(2m, F_2) (order 72 for m=2).
#   - Torsion-mod constraints preserved: M_y[j][i] is well-defined mod
#     d_j given source coordinate is in Z/d_i.

if not IsBound(BRW) then
    Read("brw_construction.g");
fi;
if not IsBound(SetupCohomology3) then
    Read("transgression_kernel.g");
fi;

# ---------------------------------------------------------------------
# Cocycle-level action of a single E_+(m) automorphism.
#
# Given setup (from SetupCohomology3) and a GroupHomomorphism
# phi : E_+(m) -> E_+(m), compute the k x k integer matrix that
# represents alpha^* on H^3 in the UCT.hombasis basis.
#
# We follow GroupCohomologyFunctor: F = the matrix of phi on the
# adapted cycle basis of Z_3. autmat = TransposedMat(F) acts on hom
# vectors of length |ZZ| = Length(UCT.cyclebasis) over Z/exp by
# left multiplication. Then we express each phi^*(hombasis[i]) as
# a Z/exp-combination of {hombasis[1], ..., hombasis[k]}.
#
# Existence of the projection: the existing AutomorphismOrbits relies
# on `OrbitsDomain` over `NearAdditiveGroup(rcv(hombasis))`, so the
# orbit closure already lands literally in the integer-span of
# hombasis modulo exponent. We mirror that here by solving the linear
# system (hombasis_matrix | -exp * I) * x = image_vec over Z.
# ---------------------------------------------------------------------

H3MatrixOfAutomorphism := function(setup, phi)
    local R, K, UCT, exp, torsion, k, hombasis, hb_len,
          chainmap, gcf, F, autmat, M_y, i, image_vec, j,
          aug_matrix, sol, col_coeffs;

    R := setup.R;
    K := setup.K;
    UCT := setup.UCT;
    exp := setup.exponent;
    torsion := setup.torsion;
    k := setup.num_generators;
    hombasis := UCT.hombasis;
    hb_len := Length(hombasis[1]);

    # F = matrix of phi on adapted cycle basis. Row convention:
    # F[i] is the coordinate vector of phi_*(Z1[i]) in basis Z2,
    # so on row vectors of cycle coords, c_out (row) = c_in (row) * F.
    # Pullback on hom-cochains (also row vectors of length |ZZ|):
    #   phi^*(h) = h * F^T  (in row form) = F * h^T (in column form).
    # autmat := TransposedMat(F) so that phi^*(h) = h * autmat,
    # i.e. left-multiplication via "v^autmat" / row-times-matrix.
    # This matches the existing AutomorphismOrbits in src/modular_data.g.
    chainmap := TensorWithIntegers(EquivariantChainMap(R, R, phi));
    gcf := GroupCohomologyFunctor(K, K, chainmap, 3);
    F := gcf!.matrix;
    autmat := TransposedMat(F);

    # Pre-build the augmented matrix for projecting any image_vec onto
    # hombasis modulo exp. Rows = hombasis vectors, then exp * I_{hb_len}.
    # Solving x * aug_matrix = image_vec gives x[1..k] = hombasis coeffs
    # (with leftover x[k+1..k+hb_len] absorbed as mod-exp slack).
    aug_matrix := Concatenation(
        hombasis,
        List([1..hb_len], r -> List([1..hb_len], c ->
            If_(r = c, exp, 0))));

    # M_y has columns = coordinates of phi^*(hombasis[i]) in hombasis.
    M_y := NullMat(k, k);
    for i in [1..k] do
        # phi^*(hombasis[i]) viewed as a length-hb_len vector mod exp.
        # Use row * matrix: hombasis[i] is a row vector of length |ZZ|.
        image_vec := List(hombasis[i] * autmat, x -> x mod exp);
        sol := SolutionIntMat(aug_matrix, image_vec);
        if sol = fail then
            Error("H3MatrixOfAutomorphism: could not project image of ",
                  "hombasis[", i, "] onto hombasis. ",
                  "phi may not be an automorphism, or basis is wrong.");
        fi;
        col_coeffs := sol{[1..k]};
        for j in [1..k] do
            M_y[j][i] := col_coeffs[j] mod torsion[j];
        od;
    od;

    return M_y;
end;;

# ---------------------------------------------------------------------
# Build the GroupHomomorphism alpha_y : E_+(m) -> E_+(m) induced by
# conjugation by y, where y is a matrix in BRW(m) and E_+(m) is the
# matrix group EmGroup(m). Uses GroupHomomorphismByImages on the
# em-generators; this asserts that the images are again in em.
# ---------------------------------------------------------------------

ConjugationAutomorphism := function(em, y)
    local gens, images, phi;
    gens := GeneratorsOfGroup(em);
    images := List(gens, g -> y * g * y^(-1));
    # Use the checking variant so that bad y (not normalising em) raises
    # immediately. For BRW(m) generators this should never fail, but the
    # check is cheap relative to the chain-map cost downstream.
    phi := GroupHomomorphismByImages(em, em, gens, images);
    if phi = fail then
        Error("Conjugation by y does not yield an automorphism of E_+(m).");
    fi;
    return phi;
end;;

# ---------------------------------------------------------------------
# Aut(prod Z/d_i): the abelian-group automorphisms of the product of
# cyclic groups with orders torsion = [d_1, ..., d_k]. We use the
# concrete realisation as k x k integer matrices A with A[j][i] in
# Z/d_j and the well-defined-ness constraint: if d_i | d_j, then
# A[j][i] must be a multiple of d_j / gcd(d_i, d_j)... actually for
# Aut to act on prod Z/d_i, we just need the matrix to be invertible
# over the appropriate quotient. For our purposes (just acting),
# any matrix preserves the structure.
# ---------------------------------------------------------------------

# Verify that M is a well-defined endomorphism of prod Z/d_i: for each
# (j, i), M[j][i] is in Z/d_j and applying M to the i-th unit vector
# (which has order d_i) must give a vector whose j-th coordinate has
# order dividing d_i, i.e. M[j][i] * d_i ≡ 0 mod d_j, i.e.
# d_j | M[j][i] * d_i, i.e. M[j][i] * d_i mod d_j = 0.
IsValidH3Endomorphism := function(M, torsion)
    local k, j, i, val;
    k := Length(torsion);
    for j in [1..k] do
        for i in [1..k] do
            val := (M[j][i] * torsion[i]) mod torsion[j];
            if val <> 0 then return false; fi;
        od;
    od;
    return true;
end;;

# Action of an endomorphism matrix M on a coordinate vector v in
# prod Z/d_i: the result is again in prod Z/d_i.
ApplyH3Endomorphism := function(M, v, torsion)
    local k, result, j, i;
    k := Length(torsion);
    result := List([1..k], j -> 0);
    for j in [1..k] do
        for i in [1..k] do
            result[j] := result[j] + M[j][i] * v[i];
        od;
        result[j] := result[j] mod torsion[j];
    od;
    return result;
end;;

# Composition of two endomorphisms: (M1 . M2)[j][i] = sum_l M1[j][l] * M2[l][i],
# reduced mod torsion[j] for each j.
ComposeH3Endomorphism := function(M1, M2, torsion)
    local k, result, j, i, s, l;
    k := Length(torsion);
    result := NullMat(k, k);
    for j in [1..k] do
        for i in [1..k] do
            s := 0;
            for l in [1..k] do
                s := s + M1[j][l] * M2[l][i];
            od;
            result[j][i] := s mod torsion[j];
        od;
    od;
    return result;
end;;

# Identity endomorphism of prod Z/d_i.
IdH3Endomorphism := function(torsion)
    local k, M, i;
    k := Length(torsion);
    M := NullMat(k, k);
    for i in [1..k] do M[i][i] := 1; od;
    return M;
end;;

# Hash key for a matrix M with entries reduced mod torsion[j] in row j.
# Used for orbit / generated-subgroup enumeration without building an
# external group-theoretic object.
H3EndomorphismKey := function(M, torsion)
    local k, j, i, row, key;
    k := Length(torsion);
    key := [];
    for j in [1..k] do
        row := [];
        for i in [1..k] do
            Add(row, M[j][i] mod torsion[j]);
        od;
        Add(key, row);
    od;
    return key;
end;;

# Enumerate the subgroup of End(prod Z/d_i) generated by a list of
# matrices, by BFS closure under composition. Stops when no new
# matrix is generated; returns the list of matrix-keys (each a list of
# rows). The user can then compute |subgroup| = Length(closure).
GeneratedH3Subgroup := function(generators, torsion)
    local id, closure, queue, M, M2, M_new, key_new, k, max_size;
    id := IdH3Endomorphism(torsion);
    k := Length(torsion);
    closure := [id];
    queue := [id];
    # Safety guard: if torsion is small, |Aut(prod Z/d_i)| is bounded
    # by Product(d_i)^k. We cap exploration there.
    max_size := Product(torsion)^k;
    while not IsEmpty(queue) do
        M := Remove(queue, 1);
        for M2 in generators do
            M_new := ComposeH3Endomorphism(M, M2, torsion);
            key_new := H3EndomorphismKey(M_new, torsion);
            if not (key_new in List(closure, x -> H3EndomorphismKey(x, torsion))) then
                Add(closure, M_new);
                Add(queue, M_new);
                if Length(closure) >= max_size then
                    Error("GeneratedH3Subgroup: exceeded max_size=",
                          max_size, "; aborting.");
                fi;
            fi;
        od;
    od;
    return closure;
end;;

# Faster variant: keep sorted set of keys for fast (binary) membership.
GeneratedH3SubgroupFast := function(generators, torsion)
    local id, id_key, closure_keys, queue, M, M2, M_new, key_new, max_size;
    id := IdH3Endomorphism(torsion);
    id_key := H3EndomorphismKey(id, torsion);
    # SSortedList ensures binary-search semantics for `in`.
    closure_keys := SSortedList([id_key]);
    queue := [id];
    max_size := 10^7;
    while not IsEmpty(queue) do
        M := Remove(queue, 1);
        for M2 in generators do
            M_new := ComposeH3Endomorphism(M, M2, torsion);
            key_new := H3EndomorphismKey(M_new, torsion);
            if not (key_new in closure_keys) then
                AddSet(closure_keys, key_new);
                Add(queue, M_new);
                if Length(closure_keys) >= max_size then
                    Error("GeneratedH3SubgroupFast: exceeded max_size=",
                          max_size, "; aborting.");
                fi;
            fi;
        od;
    od;
    return closure_keys;
end;;

# ---------------------------------------------------------------------
# Main entry point: BRWH3Action(m).
#
# Returns a record with fields:
#   .m              : m
#   .em             : E_+(m)
#   .brw            : BRW(m)
#   .setup          : SetupCohomology3(em) record
#   .torsion        : H^3 torsion list (k entries)
#   .num_generators : k = Length(torsion)
#   .brw_gens       : GeneratorsOfGroup(brw)
#   .matrices       : list of k x k integer matrices M_y, one per
#                     BRW generator, with M_y[j][i] in Z/torsion[j].
#   .valid_endos    : list of booleans, per matrix, asserting that
#                     M_y is a well-defined endomorphism of prod Z/d_i.
# ---------------------------------------------------------------------

BRWH3Action := function(m)
    local em, brw, setup, torsion, k, brw_gens, matrices, i, y, phi,
          M_y, valid_endos;
    Assert(0, m >= 1, "m must be a positive integer");

    em := EmGroup(m);
    brw := BRW(m);

    setup := SetupCohomology3(em);
    torsion := setup.torsion;
    k := setup.num_generators;

    brw_gens := GeneratorsOfGroup(brw);
    matrices := [];
    valid_endos := [];
    for i in [1..Length(brw_gens)] do
        y := brw_gens[i];
        phi := ConjugationAutomorphism(em, y);
        M_y := H3MatrixOfAutomorphism(setup, phi);
        Add(matrices, M_y);
        Add(valid_endos, IsValidH3Endomorphism(M_y, torsion));
    od;

    return rec(
        m := m,
        em := em,
        brw := brw,
        setup := setup,
        torsion := torsion,
        num_generators := k,
        brw_gens := brw_gens,
        matrices := matrices,
        valid_endos := valid_endos
    );
end;;
