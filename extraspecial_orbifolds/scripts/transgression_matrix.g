# Tier 4 (§2.1 + §2.2 of transgression_improvements_design.md):
# Build the matrix of the transgression
#   Tr : H^3(G; U(1)) -> ⊕_{[g]} H^2(C_G(g); U(1))
# in fixed cohomology bases, then compute its kernel via Smith Normal Form.
#
# STATUS (2026-05-08): WIP.  The augmented system uses Gruen UCT.cocyclebasis
# at degree 2 as the H^2(C; U(1)) basis, but for E_+(2) generator e_10 the
# pipeline fails (project returns fail) because Gruen's cocyclebasis at n=2
# spans H^2(C; U(1)) = H_2(C; Z), which differs from H^2(C; Z/exp) when
# Tor(H^3(C; Z), Z/exp) is non-zero.  The basis needs to be extended with
# Tor-part generators before this can produce the full integer matrix.
#
# For E_+(2) the kernel of Tr was determined exactly by per-generator +
# brute-force on the only non-in-kernel cyclic factor; see
# `test_transgression_kernel_e2.g`.  That bypasses the basis issue.
# The full SNF approach here will return useful coords for groups where
# multiple generators have non-trivial transgression (e.g. E_+(3)).
#
# Pipeline
# --------
# Per H^3(G) generator e_i (i in 1..k):
#   1. Build omega_i := bar 3-cocycle from UCT.cocyclebasis[i].
#   2. For each conjugacy class g of G:
#      a. Compute c_g_i : C_G(g) x C_G(g) -> Z/exp via the slant formula
#            c_g_i(h1, h2) = omega_i(g, h1, h2) + omega_i(h1, h2, g)
#                             - omega_i(h1, g, h2).
#      b. Project [c_g_i] onto a basis of H^2(C_G(g); U(1)) using
#         per-class augmented system; coords = integer vector in
#         prod_l (Z / e_{g,l}).
#   3. Concatenate per-class coords -> row of M.
#
# Stack into matrix M (k rows, sum-of-H^2-ranks columns).  Kernel of Tr
# is the SNF kernel of [M ; -diag(col_torsion)].
#
# Important: relies on the corrected `StandardCocycleOf` (uses
# UCT.cocyclebasis, not `lift * vec`).
#
# This file requires the parent Read("transgression_kernel.g") so that
# SetupCohomology3, StandardCocycleOf, CGCocycleFunc are all defined
# with the corrected semantics.

Read("transgression_kernel.g");

# ---------------------------------------------------------------------
# Local patch of Gruen's UniversalCoefficientsTheorem so it works for
# arbitrary n (not just n=3).  Original hardcodes K!.dimension(3) on
# what should be K!.dimension(n).
# ---------------------------------------------------------------------
UniversalCoefficientsTheorem := function(K, n)
    local ZZ, B, r, C, D, m, homlist, r2, R1, C1, I, cocyclelist, hom, i;
    ZZ := NullspaceIntMat(TransposedMat(BoundaryMatrix(K, n)));
    if not Size(ZZ) > 0 then
        return rec(complex := K, cyclebasis := ZZ, cycletrans := [],
                   hombasis := [], cocyclebasis := [], torsion := [1],
                   exponent := 1, lift := []);
    fi;
    B := BaseIntMat(TransposedMat(BoundaryMatrix(K, n+1)));
    r := ComplementIntMatWithTransforms(ZZ, B);
    C := r!.fulltrans;
    D := r!.moduli;
    m := D[Size(D)];
    homlist := [];
    for i in [1..Size(D)] do
        if D[i] = 1 then continue; fi;
        hom := ListWithIdenticalEntries(Size(ZZ), 0);
        hom[i] := m / D[i];
        Add(homlist, hom);
    od;
    homlist := List(homlist, x -> ((C^(-1)) * x) mod m);
    r2 := ComplementIntMatWithTransforms(IdentityMat(K!.dimension(n)), ZZ);
    C1 := r2!.subtrans;
    R1 := r2!.fulltrans;
    I := Concatenation(IdentityMat(Size(ZZ)),
                       NullMat(K!.dimension(n) - Size(ZZ), Size(ZZ)));
    cocyclelist := List(homlist, x -> (R1^(-1) * (I * (C1 * x))) mod m);
    return rec(complex := K, cyclebasis := ZZ, cycletrans := C,
               hombasis := homlist, cocyclebasis := cocyclelist,
               torsion := Filtered(D, x -> not x = 1),
               exponent := m,
               lift := R1^(-1) * I * C1);
end;;

# ---------------------------------------------------------------------
# Per-centraliser projector setup.
# ---------------------------------------------------------------------
#
# For each centraliser C, builds the augmented integer system that
# decomposes a 2-cocycle c on C as
#     c(h1, h2) ≡ sum_l a_l * beta_l(h1, h2) + delta(gamma)(h1, h2)
#                                                       (mod exp)
# where {beta_l} is the basis of H^2(C; U(1)) given by Gruen's UCT
# (via cocyclebasis) and gamma is a 1-cochain.  Solving recovers
# a_l in Z/torsion[l].
#
# Returns a record with .torsion, .M_aug_T, .project, .basis_check.

SetupCentraliserH2 := function(C, exp)
    local elts, n, R, K, UCT_C, K2dim, basis_cocycles, r, basis_funcs,
          B_T, k, f_k, i, j, ij, idx_dict, M_aug_T, project, basis_check;
    elts := AsList(C);
    n := Length(elts);
    R := ResolutionFiniteGroup(C, 3);
    K := TensorWithIntegers(R);
    UCT_C := UniversalCoefficientsTheorem(K, 2);
    K2dim := R!.dimension(2);
    basis_cocycles := UCT_C.cocyclebasis;   # length-K2dim integer vectors
    r := Length(basis_cocycles);
    basis_funcs := List(basis_cocycles, v -> StandardCocycle(R, v, 2, exp));

    # Build B_T: (n*n) x r, B_T[(i-1)*n+j][l] = basis_funcs[l](elts[i], elts[j]) mod exp.
    B_T := List([1..n*n], i -> List([1..r], k -> 0));
    for k in [1..r] do
        f_k := basis_funcs[k];
        for i in [1..n] do
            for j in [1..n] do
                B_T[(i-1)*n + j][k] := f_k(elts[i], elts[j]) mod exp;
            od;
        od;
    od;

    # Augmented system: (r + n + n^2) x (n^2) matrix M_aug_T such that
    # solving x · M_aug_T = c_vec gives x = (a_l, gamma_p, w_q) with
    # the first r entries the basis-cocycle coordinates of c modulo exp.
    M_aug_T := [];
    # First r rows: basis cocycle values across all (i, j) pairs.
    for k in [1..r] do
        Add(M_aug_T, List([1..n*n], j -> B_T[j][k]));
    od;
    # Next n rows: gamma (coboundary) contributions.  Row r+p, column (i,j):
    # +1 if elts[p] = elts[i],  +1 if elts[p] = elts[j],  -1 if elts[p] = elts[i]*elts[j].
    for k in [1..n] do Add(M_aug_T, List([1..n*n], q -> 0)); od;
    # Audit (#258 follow-up): replace `Position(elts, elts[i]*elts[j])`
    # (O(n) per call, called twice per inner iteration → O(n^3) total)
    # with a NewDictionary lookup (O(1) per call → O(n^2) total).
    idx_dict := NewDictionary(elts[1], true, elts);
    for k in [1..n] do AddDictionary(idx_dict, elts[k], k); od;
    for i in [1..n] do
        for j in [1..n] do
            ij := LookupDictionary(idx_dict, elts[i] * elts[j]);
            M_aug_T[r + i][(i-1)*n + j] := M_aug_T[r + i][(i-1)*n + j] + 1;
            M_aug_T[r + j][(i-1)*n + j] := M_aug_T[r + j][(i-1)*n + j] + 1;
            M_aug_T[r + ij][(i-1)*n + j] := M_aug_T[r + ij][(i-1)*n + j] - 1;
        od;
    od;
    # Last n^2 rows: exp * I_{n^2} -- mod-exp slack.
    for k in [1..n*n] do
        Add(M_aug_T, List([1..n*n], q -> If_(q = k, exp, 0)));
    od;

    project := function(c_func)
        local c_vec, i, j, sol, a_coords, k;
        c_vec := List([1..n*n], q -> 0);
        for i in [1..n] do
            for j in [1..n] do
                c_vec[(i-1)*n + j] := c_func(elts[i], elts[j]) mod exp;
            od;
        od;
        sol := SolutionIntMat(M_aug_T, c_vec);
        if sol = fail then return fail; fi;
        a_coords := List([1..r], k -> sol[k] mod UCT_C.torsion[k]);
        return a_coords;
    end;

    # Sanity: each basis_funcs[k] should project to the k-th unit vector.
    basis_check := List([1..r], k -> project(basis_funcs[k]));

    return rec(C := C, exp := exp, elts := elts, n := n,
               R := R, UCT_C := UCT_C, K2dim := K2dim, r := r,
               basis_cocycles := basis_cocycles,
               torsion := UCT_C.torsion,
               M_aug_T := M_aug_T,
               project := project,
               basis_check := basis_check);
end;;

# ---------------------------------------------------------------------
# Build the transgression matrix.
# ---------------------------------------------------------------------

TransgressionMatrix := function(G, verbose)
    local setup_G, classes, k, n_classes, centralisers, h2_setups,
          col_torsions, col_offsets, total_cols, M, i, vec, omega, j,
          gRep, c_g, coords, c, t0, t1;

    setup_G := SetupCohomology3(G);
    k := setup_G.num_generators;
    if verbose then
        Print("\n=== Transgression matrix for ", StructureDescription(G), " ===\n");
        Print("|G| = ", Order(G), ";  H^3 torsion = ", setup_G.torsion,
              "; #generators = ", k, "\n");
    fi;

    classes := ConjugacyClasses(G);
    n_classes := Length(classes);
    if verbose then Print("# conjugacy classes: ", n_classes, "\n"); fi;

    if verbose then Print("\nSetting up H^2 projectors per centraliser...\n"); fi;
    centralisers := List(classes, cl -> Centralizer(G, Representative(cl)));
    h2_setups := [];
    for j in [1..n_classes] do
        if verbose then t0 := Runtime(); fi;
        c := SetupCentraliserH2(centralisers[j], setup_G.exponent);
        Add(h2_setups, c);
        if verbose then
            Print("  class ", j, "/", n_classes, ": |C|=", c.n,
                  ", K2dim=", c.K2dim, ", r=", c.r,
                  ", torsion=", c.torsion,
                  "  (", (Runtime() - t0)/1000., " s)\n");
        fi;
    od;

    col_torsions := Concatenation(List(h2_setups, s -> s.torsion));
    total_cols := Length(col_torsions);
    if verbose then Print("Total Tr-matrix columns: ", total_cols, "\n"); fi;
    col_offsets := [0];
    for j in [1..n_classes] do
        Add(col_offsets, col_offsets[j] + Length(h2_setups[j].torsion));
    od;

    M := List([1..k], i -> List([1..total_cols], j -> 0));
    if verbose then Print("\nFilling transgression matrix...\n"); fi;
    for i in [1..k] do
        if verbose then t0 := Runtime(); fi;
        vec := List([1..k], j -> If_(j = i, 1, 0));
        omega := StandardCocycleOf(setup_G, vec);
        for j in [1..n_classes] do
            gRep := Representative(classes[j]);
            c_g := CGCocycleFunc(omega, gRep);
            coords := h2_setups[j].project(c_g);
            if coords = fail then
                Error("project returned fail at generator i=", i,
                      ", class j=", j, ", |C|=", h2_setups[j].n);
            fi;
            for c in [1..Length(coords)] do
                M[i][col_offsets[j] + c] := coords[c];
            od;
        od;
        if verbose then
            t1 := Runtime();
            Print("  generator ", i, "/", k, ": ", (t1 - t0)/1000., " s\n");
        fi;
    od;

    return rec(setup_G := setup_G,
               classes := classes,
               h2_setups := h2_setups,
               col_torsions := col_torsions,
               col_offsets := col_offsets,
               row_torsion := setup_G.torsion,
               M := M);
end;;

# ---------------------------------------------------------------------
# Kernel computation via SNF.
# ---------------------------------------------------------------------
#
# We have M : (Z/d_1) x ... x (Z/d_k) -> (Z/e_1) x ... x (Z/e_c)
# where d = row_torsion (H^3 source), e = col_torsions (H^2 target).
#
# Kernel = { x in Z^k mod d : Mx ≡ 0 in Z^c mod e }
#        = ((Z^k -> Z^c, M) preimage of e * Z^c) / (d * Z^k)
#
# In row-vector form, x · M = y · diag(e) for y in Z^c.  So the integer
# left-kernel of (M | -diag(e)) (a (k+c) x c matrix when stacked
# vertically) projected onto first k coords, then quotiented by
# d-multiples, gives the kernel.

KernelOfTransgression := function(tm)
    local M, k, e, d, c, big, snf, kernel_rows, x_part,
          reduced_rows, snf_d, kernel_torsion, normal_diag;
    M := tm.M;
    k := Length(M);
    if k = 0 then
        return rec(kernel_size := 1, kernel_torsion := []);
    fi;
    c := Length(M[1]);
    d := tm.row_torsion;
    e := tm.col_torsions;

    # Form (k + c) x c integer matrix; want left null space.
    big := Concatenation(M,
        List([1..c], i -> List([1..c], j -> If_(i = j, -e[i], 0))));
    snf := NormalFormIntMat(big, 6);   # 6 = SNF + rowtrans

    # Rows of snf.rowtrans whose corresponding diagonal of snf.normal is
    # zero (for indices >= rank+1) form integer left null space.
    kernel_rows := List([snf.rank+1..k+c], i -> snf.rowtrans[i]);
    x_part := List(kernel_rows, row -> row{[1..k]});

    # Reduce x_part rows mod d-coordinates: kernel-of-Tr in Z/d^k.
    reduced_rows := Concatenation(x_part,
        List([1..k], i -> List([1..k], j -> If_(i = j, d[i], 0))));
    snf_d := NormalFormIntMat(reduced_rows, 6);
    normal_diag := DiagonalOfMat(snf_d.normal);
    kernel_torsion := Filtered(normal_diag, x -> x <> 1 and x <> 0);

    return rec(big := big,
               snf := snf,
               kernel_rows := kernel_rows,
               x_part := x_part,
               kernel_torsion := kernel_torsion,
               kernel_size := Product(kernel_torsion));
end;;
