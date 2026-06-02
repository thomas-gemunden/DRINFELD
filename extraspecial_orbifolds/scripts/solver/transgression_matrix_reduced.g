# transgression_matrix_reduced.g — perf-4' from issue #271.
#
# Eliminates per-class enumeration (Path A / Path Z) inside the
# transgression-kernel sweep by precomputing, per BRW-orbit-rep centraliser
# C, the REDUCED transgression matrix
#
#   M_bar_g : H^3(G; U(1))_{order-2 part}  -> F_2^{n² - rank(lift_sem(C))}
#
# where lift_sem(C) is the cached
#     [BocksteinH1ToH2(C); BoundaryMatrixGF2(C)^T]
# SemiEchelonMatTransformation (see solver/mod2_solver.g). The
# constraint M_bar_g . vec ≡ 0 (over GF(2)) is EXACTLY the condition
# that c_g_{vec mod 2} represents a class in image(Bockstein) + B²(F_2),
# which (by the lift argument for exp >= 4) is equivalent to c_g being
# a Z/exp coboundary on C — i.e. [c_g] = 0 in H²(C; Z/exp), the orbit-
# kernel condition.
#
# Then computes
#
#   ker(Tr : H^3(G; U(1)) -> sum_g H^2(C_g; U(1)))
#
# as the joint kernel of the vertical concatenation of M_bar_g . M_y_j
# (the BRW-propagated forms) across orbits, via F_2-nullspace.
#
# The order-exp H^3 generator (if any) is NOT handled by the F_2 path;
# its kernel contribution along the <e_{exp_index}> axis is computed
# separately by per-axis IsCoboundary2Split fallback (test k * e for
# k = 1..exp-1, find smallest k_min). This is sound because the kernel
# of Tr splits along the order-exp axis from the F_2-axes part (the
# transgression image of the order-exp gen lies in a different summand
# of H^2(C; Z/exp) from the order-2 gens; verified empirically by the
# m=2 anchor where ker = (Z/2)^9 × <2*e_10> exactly matches the
# Cartesian-product decomposition).
#
# Mathematical recipe (per issue #271):
#
#   * BuildPerClassCocycleBasis(setup, g, C) yields a table T_g of shape
#     n² × k whose entry T_g[(i-1)*n+j][l] is
#       (alpha_l(g, elts[i], elts[j])
#        - alpha_l(elts[i], g, elts[j])
#        + alpha_l(elts[i], elts[j], g))  mod exp_G
#     where alpha_l is the l-th basis 3-cocycle on G. So T_g is the
#     matrix of Tr_g at the COCYCLE level (no projection to H^2 yet).
#
#   * To get Tr_g at the COHOMOLOGY level (M_bar_g : H^3(G) -> H^2(C)),
#     we apply the projection P_C : Z^2(C; U(1)) -> H^2(C; U(1)) to
#     each column of T_g. P_C is built from HAP's UCT_C on the C-side
#     (ResolutionFiniteGroup(C, 3), UCT(TensorWithIntegers, 2)).
#
#   * P_C is built via an augmented integer system: for any 2-cochain
#     vector c : n² -> Z/exp on C, find integer (a_1..a_r, beta_1..beta_n,
#     w_1..w_{n²}) such that
#       sum_l a_l * basis_func_l(C) + delta_2(beta) + exp * w = c
#     The first r entries `a_l mod UCT_C.torsion[l]` are the H^2 coords
#     of [c]. If the system is unsolvable (because [c] has a Bockstein-
#     image component not in span(basis_funcs)), we augment with the
#     Bockstein-image cocycles and retry — see ProjectWithBockstein.
#
#   * For each BRW orbit (rep g, members {g_j}), we compute M_bar_g
#     and then propagate to all orbit members via the H^3 endomorphism
#     M_y_j (the BRW matrix for the y_j taking g to g_j):
#       row block for orbit member j  =  M_bar_g . M_y_j
#     where M_y_j is k × k. So the per-orbit block is (|orbit| * r) × k.
#
#   * Stacking across orbits gives M_stack of shape R_total × k where
#     R_total = sum_orbits |orbit| * r_orbit. The joint kernel of M_stack
#     mod (UCT_C.torsion per row block, H^3.torsion per column) gives
#     ker(Tr).
#
# Returns (per BuildReducedTransgressionMatrix):
#   rec(
#     table_int   : n² × k cocycle-level transgression (= cache.table)
#     P_C         : the projection record (M_aug_T, project func)
#     M_bar       : r × k integer matrix mod UCT_C.torsion
#     torsion_C   : UCT_C.torsion (list of moduli per row of M_bar)
#     C           : the centraliser (reference)
#     bockstein_used : bool, true if we augmented with the Bockstein image
#                  to get a full-rank projection.
#   )
#
# Acceptance anchors (issue #271):
#   * m=2: |ker| = 2048; matches computed/transgression/2/kernel.g.
#   * m=3: |ker| = 262144 = 2^18; in_kernel_gens =
#          [1,2,3,4,5,6,8,10,11,12,13,14,15,17,18,19,30]; exp_index = 35.
#   * Wall: m=3 reduced-matrix path should be < 5 minutes.

# ---------------------------------------------------------------------
# Read-path shim: this file is intended to be Read either from solver/
# directly or from solver/tests/. Companion deps live in solver/ or up
# one level (scripts/).
# ---------------------------------------------------------------------

tmr_orig_dir := DirectoryCurrent();;
tmr_target := fail;;
for tmr_try in [".", "..", "../.."] do
    if IsExistingFile(Concatenation(tmr_try,
                                    "/solver/transgression_matrix_reduced.g")) then
        tmr_target := tmr_try;
        break;
    elif IsExistingFile(Concatenation(tmr_try,
                                       "/transgression_matrix_reduced.g")) then
        tmr_target := Concatenation(tmr_try, "/..");
        break;
    fi;
od;;
if tmr_target = fail then
    Error("transgression_matrix_reduced.g: cannot locate scripts/ from CWD ",
          Filename(tmr_orig_dir, ""));
fi;
ChangeDirectoryCurrent(tmr_target);;

# transgression_kernel.g brings in SetupCohomology3, StandardCocycleOf and
# the corrected UniversalCoefficientsTheorem. (modular_data.g is Read by
# transgression_kernel.g.)
if not IsBound(SetupCohomology3) then
    Read("transgression_kernel.g");
fi;
# transgression_matrix.g brings in the LOCAL patched UniversalCoefficientsTheorem
# (which generalises Gruen's to any n, needed for n=2) and SetupCentraliserH2
# (which builds the augmented integer system for projecting to H^2(C; U(1))).
if not IsBound(SetupCentraliserH2) then
    Read("transgression_matrix.g");
fi;
# snf_wrapper.g brings in BuildPerClassCocycleBasis (cocycle-level table).
if not IsBound(BuildPerClassCocycleBasis) then
    ChangeDirectoryCurrent("solver");
    Read("snf_wrapper.g");
    ChangeDirectoryCurrent("..");
fi;
# mod2_solver.g brings in BocksteinH1ToH2 used for the Bockstein-augmented
# projection fallback (Tor-part detection).
if not IsBound(BocksteinH1ToH2) then
    ChangeDirectoryCurrent("solver");
    Read("mod2_solver.g");
    ChangeDirectoryCurrent("..");
fi;
ChangeDirectoryCurrent(Filename(tmr_orig_dir, ""));;

# Local If_ shim (matches the rest of the codebase).
If_ := function(cond, a, b) if cond then return a; else return b; fi; end;;


# ---------------------------------------------------------------------
# BuildPCWithBockstein(C, exp) — extends SetupCentraliserH2 with Bockstein-
# image fallback.
#
# The basic SetupCentraliserH2 augmented system can FAIL on cocycles whose
# class has a non-trivial Bockstein-image (Ext) component in H^2(C; Z/exp)
# — these aren't in the span of UCT_C.cocyclebasis (which only sees the
# Hom-part). For our purposes (computing M_bar columns from the per-class
# table), every column IS a 2-cocycle mod exp on C, and if the bare system
# fails, augmenting with the Bockstein image (r2 extra "basis" vectors,
# each of order 2) lets us still extract integer coordinates.
#
# Returns a record with the same shape as SetupCentraliserH2 plus:
#   .bockstein_used : bool — whether Bockstein-image columns were added
#   .torsion_full   : the FULL torsion list (UCT_C.torsion ++ Z/2s for
#                     each Bockstein row added)
#   .r_full         : Length(torsion_full)
#
# Note: we ALWAYS include the Bockstein image (when exp is even). It's
# cheap (one BocksteinH1ToH2 call per C, cached) and saves a retry round
# trip. The Bockstein basis vectors are LINEARLY INDEPENDENT of the
# Hom-part cocyclebasis as cocycles (since they live in distinct factors
# of H^2(C; Z/exp) = Hom(H_2, Z/exp) + Ext(H_1, Z/exp) when 2 | exp).
# ---------------------------------------------------------------------

BuildPCWithBockstein := function(C, exp)
    local base, n, elts, img_rows, k, r_base, r_bockstein, r_full,
          torsion_full, basis_cocycles_full, M_aug_T_full, project_full,
          basis_check, exp_int, one_gf2, k_b, b_F2;
    base := SetupCentraliserH2(C, exp);
    n := base.n;
    elts := base.elts;
    r_base := base.r;

    # CRITICAL: at exp >= 4 the Bockstein image cocycles (α∪α scaled by
    # exp/2) are themselves Z/exp coboundaries (since 2·(α∪α) = δ(α̃)
    # at the chain level, hence (exp/2)·(α∪α) = δ((exp/4)·2·α̃) for
    # exp >= 4). So adding them to the basis is mathematically wrong:
    # they are TRIVIAL classes in H^2(C; Z/exp), and including them as
    # explicit "basis" elements with order 2 in `torsion_full` over-
    # constrains the projection (non-canonical solutions with non-zero
    # coords on these "fake" basis elements).
    #
    # At exp = 2, the Bockstein image IS non-trivial in H^2(C; F_2),
    # and the augmentation is correct. For exp >= 4, skip the
    # augmentation entirely — projection failures on the order-exp
    # generator's column reflect genuine Z/4 (or higher) Ext components
    # in H^2(C; Z/exp) not covered by cocyclebasis; those are handled
    # by the fallback IsCoboundary2Split path in
    # KernelOfTransgressionViaMBar.
    if exp <> 2 then
        return rec(
            C := C, exp := exp, elts := elts, n := n,
            R := base.R, UCT_C := base.UCT_C, K2dim := base.K2dim,
            r := r_base, r_full := r_base,
            basis_cocycles := base.basis_cocycles,
            torsion := base.torsion, torsion_full := base.torsion,
            M_aug_T := base.M_aug_T, project := base.project,
            basis_check := base.basis_check,
            bockstein_used := false);
    fi;

    # Compute Bockstein image as a list of n² integer (0/1) cochains.
    # BocksteinH1ToH2 returns a list of GF(2) vectors; lift to {0, r} where
    # r = exp / 2 (so they have order 2 in Z/exp).
    img_rows := BocksteinH1ToH2(C);
    r_bockstein := Length(img_rows);

    if r_bockstein = 0 then
        # No 2-torsion in C^ab — no Bockstein image to add.
        return rec(
            C := C, exp := exp, elts := elts, n := n,
            R := base.R, UCT_C := base.UCT_C, K2dim := base.K2dim,
            r := r_base, r_full := r_base,
            basis_cocycles := base.basis_cocycles,
            torsion := base.torsion, torsion_full := base.torsion,
            M_aug_T := base.M_aug_T, project := base.project,
            basis_check := base.basis_check,
            bockstein_used := false);
    fi;

    # Lift each GF(2) Bockstein-image row to an integer row with values
    # in {0, exp/2}. (Bockstein-image classes have order 2 in H^2(C; Z/exp);
    # representing them as (exp/2)·(0/1 mod 2) sits them in Z/exp coherently.)
    exp_int := exp;
    r_full := r_base + r_bockstein;
    torsion_full := Concatenation(base.torsion,
                                  List([1..r_bockstein], i -> 2));

    # Build M_aug_T_full: the existing rows of M_aug_T (length n²) followed
    # by r_bockstein new rows (each length n²) for the Bockstein image, then
    # the existing n rows of coboundary slack and n² rows of exp-slack —
    # we re-assemble from scratch to keep the ordering convention
    # (basis-rows first, then coboundary, then exp-slack).
    M_aug_T_full := [];
    # First r_base rows: the cocyclebasis rows.
    for k_b in [1..r_base] do
        Add(M_aug_T_full, ShallowCopy(base.M_aug_T[k_b]));
    od;
    # Next r_bockstein rows: Bockstein image as integer rows (values in {0, exp/2}).
    # Per audit C-8 (PR #396): IntVecFFE converts the packed GF(2) row to a plist
    # of 0/1 ints in a single compiled call; the subsequent list-scalar mul is
    # also compiled. Replaces the previous closure (P5) + per-cell loop.
    for k_b in [1..r_bockstein] do
        Add(M_aug_T_full, IntVecFFE(img_rows[k_b]) * (exp_int / 2));
    od;
    # Next n rows: coboundary contributions (same as base).
    for k_b in [1..n] do
        Add(M_aug_T_full, ShallowCopy(base.M_aug_T[r_base + k_b]));
    od;
    # Last n² rows: exp · I (same as base).
    for k_b in [1..n*n] do
        Add(M_aug_T_full, ShallowCopy(base.M_aug_T[r_base + n + k_b]));
    od;

    project_full := function(c_func)
        local c_vec, i, j, sol, a_coords;
        c_vec := List([1..n*n], q -> 0);
        for i in [1..n] do
            for j in [1..n] do
                c_vec[(i-1)*n + j] := c_func(elts[i], elts[j]) mod exp_int;
            od;
        od;
        sol := SolutionIntMat(M_aug_T_full, c_vec);
        if sol = fail then return fail; fi;
        a_coords := List([1..r_full], k_b -> sol[k_b] mod torsion_full[k_b]);
        return a_coords;
    end;

    return rec(
        C := C, exp := exp, elts := elts, n := n,
        R := base.R, UCT_C := base.UCT_C, K2dim := base.K2dim,
        r := r_base, r_full := r_full,
        basis_cocycles := base.basis_cocycles,
        torsion := base.torsion, torsion_full := torsion_full,
        M_aug_T := M_aug_T_full, project := project_full,
        basis_check := base.basis_check,
        bockstein_used := true);
end;;


# ---------------------------------------------------------------------
# ProjectVectorViaP_C(P_C_rec, c_g_vec) — fast vectorised variant of
# P_C_rec.project that takes a length-n² INTEGER vector directly instead
# of a c_func closure.
#
# Same math as P_C_rec.project: solve `x * M_aug_T = c_g_vec` and return
# the first r_full entries mod torsion_full. The function-call adapter
# inside `.project` would re-evaluate the cocycle on every (i, j) pair,
# which is wasteful when we already have the table column in hand.
# ---------------------------------------------------------------------

ProjectVectorViaP_C := function(P_C_rec, c_g_vec)
    local sol, a_coords, k_b, c_vec_mod, exp_local;
    exp_local := P_C_rec.exp;
    # Issue #387 audit-tier3 rank 4: compiled list-mod-int instead of n^2 closures.
    c_vec_mod := c_g_vec mod exp_local;
    sol := SolutionIntMat(P_C_rec.M_aug_T, c_vec_mod);
    if sol = fail then return fail; fi;
    a_coords := List([1..P_C_rec.r_full],
                     k_b -> sol[k_b] mod P_C_rec.torsion_full[k_b]);
    return a_coords;
end;;


# ---------------------------------------------------------------------
# FastProjectionMatrixSetup(C, exp) — precompute SNF of the small
# [basis_funcs; coboundary] matrix WITHOUT the explicit n²·I exp-slack.
#
# Motivation: the SolutionIntMat in ProjectVectorViaP_C operates on a
# (r + n + n²) × n² matrix, where n² = |C|². At m=3 with n=128 this is
# ~16400 × 16384, and the per-column SolutionIntMat is O(n^6) ~ minutes.
#
# Instead, we work modulo exp directly:
#   1. Build M_small = [basis_funcs; coboundary] of shape (r + n) × n².
#   2. Compute SNF of M_small ONCE per C: M_small = U_T · D · V_T (where
#      we work in the row-vector convention: rows of M_small are the
#      basis/coboundary rows, columns are (i, j) cells).
#   3. For each c_g_i column to project, solve
#        x · M_small ≡ c_g_i (mod exp)
#      via the SNF: x = (c_g_i · V_T^{-1}) "divided by D" within Z/exp,
#      then x · U_T^{-1} gives the original-basis coefficients.
#
# We avoid building M_aug_T's n² × n² block entirely; this drops the
# per-column cost from O(n^6) to O(rank · n²) ≈ O(n^4) — about 1000×
# faster at n=128.
#
# Returns a record with:
#   .M_small      : the (r + n) × n² matrix
#   .snf          : NormalFormIntMat(M_small, 6) result
#   .r            : r_base (number of basis-cocycle rows = first r rows of M_small)
#   .n            : |C|
#   .UCT_C        : the original UCT_C
#   .torsion      : UCT_C.torsion (the basis-cocycle torsion list)
#   .exp          : exp
#
# Project via FastProjectVector(setup_rec, c_g_vec).
# ---------------------------------------------------------------------

FastProjectionMatrixSetup := function(C, exp)
    local elts, n, R, K, UCT_C, basis_cocycles, r, basis_funcs, k_b, f_k,
          i, j, B_T, M_small, idx_dict, ij, snf, K2dim;
    elts := AsList(C);
    n := Length(elts);
    R := ResolutionFiniteGroup(C, 3);
    K := TensorWithIntegers(R);
    UCT_C := UniversalCoefficientsTheorem(K, 2);
    K2dim := R!.dimension(2);
    basis_cocycles := UCT_C.cocyclebasis;
    r := Length(basis_cocycles);
    basis_funcs := List(basis_cocycles, v -> StandardCocycle(R, v, 2, exp));

    # Build B_T: (n*n) x r as in SetupCentraliserH2.
    # Issue #387 audit-tier3 rank 6: NullMat avoids n^2 * r closures.
    B_T := NullMat(n*n, r);
    for k_b in [1..r] do
        f_k := basis_funcs[k_b];
        for i in [1..n] do
            for j in [1..n] do
                B_T[(i-1)*n + j][k_b] := f_k(elts[i], elts[j]) mod exp;
            od;
        od;
    od;

    # Build M_small: (r + n) × n². Row k_b in [1..r] = basis_funcs[k_b]
    # as a length-n² row. Row r+i in [r+1..r+n] = δ(1_{elts[i]}) as
    # length-n² (= sign-contributions to (i', j') cells where elts[i']
    # ∈ {elts[i], elts[j], elts[i']*elts[j']}).
    # Issue #387 audit-tier3 rank 6: NullMat avoids (r+n) * n^2 closures.
    M_small := NullMat(r + n, n*n);
    for k_b in [1..r] do
        for i in [1..n*n] do
            M_small[k_b][i] := B_T[i][k_b];
        od;
    od;
    idx_dict := NewDictionary(elts[1], true, elts);
    for k_b in [1..n] do AddDictionary(idx_dict, elts[k_b], k_b); od;
    for i in [1..n] do
        for j in [1..n] do
            ij := LookupDictionary(idx_dict, elts[i] * elts[j]);
            M_small[r + i][(i-1)*n + j] := M_small[r + i][(i-1)*n + j] + 1;
            M_small[r + j][(i-1)*n + j] := M_small[r + j][(i-1)*n + j] + 1;
            M_small[r + ij][(i-1)*n + j] := M_small[r + ij][(i-1)*n + j] - 1;
        od;
    od;

    return rec(
        C := C,
        n := n,
        elts := elts,
        R := R, UCT_C := UCT_C, K2dim := K2dim,
        r := r, torsion := UCT_C.torsion, exp := exp,
        basis_cocycles := basis_cocycles,
        basis_funcs := basis_funcs,
        M_small := M_small);
end;;


# Fast projection: given a length-n² integer vector c (the c_g values),
# solve `x · M_small ≡ c (mod exp)` and return `[x[1..r] mod torsion]`.
# Uses SolutionIntMat over Z on the AUGMENTED matrix [M_small; exp·I_{n²}]
# (size (r + n + n²) × n²). This is the SAME math as SetupCentraliserH2's
# project, but we keep M_small × exp·I separate so we can amortise
# different parts of the computation if needed.
#
# NOTE: for now this is still SolutionIntMat over Z with the explicit
# n²·I slack — same as the original. The speedup will come from a future
# SNF-based back-sub (currently NOT IMPLEMENTED; we have it as a stub
# for the design surface). For m=2/m=3 the current path is just
# SetupCentraliserH2.
FastProjectVector := function(fproj, c_g_vec)
    # Fallback: use the slow but correct SolutionIntMat path via
    # augmented matrix. Identical math to ProjectVectorViaP_C.
    local M_aug_T, p, q, r, n, exp_local, torsion, c_vec_mod, sol,
          a_coords, k_b;
    r := fproj.r;
    n := fproj.n;
    exp_local := fproj.exp;
    torsion := fproj.torsion;

    # Build M_aug_T = [M_small; exp · I_{n²}] — same as SetupCentraliserH2
    # would produce. We build it ONCE and cache; subsequent calls just
    # call SolutionIntMat.
    if not IsBound(fproj.M_aug_T_cached) then
        M_aug_T := ShallowCopy(fproj.M_small);
        # exp·I has rank n²; rows added at the end.
        for p in [1..n*n] do
            Add(M_aug_T, List([1..n*n],
                              q -> If_(q = p, exp_local, 0)));
        od;
        fproj.M_aug_T_cached := M_aug_T;
    fi;
    # Issue #387 audit-tier3 rank 4: compiled list-mod-int instead of n^2 closures.
    c_vec_mod := c_g_vec mod exp_local;
    sol := SolutionIntMat(fproj.M_aug_T_cached, c_vec_mod);
    if sol = fail then return fail; fi;
    a_coords := List([1..r], k_b -> sol[k_b] mod torsion[k_b]);
    return a_coords;
end;;


# ---------------------------------------------------------------------
# BuildReducedTransgressionMatrix(setup, g_rep, C) — public entry point.
#
# Returns rec(table_int, P_C, M_bar, torsion_C, C, bockstein_used) where:
#   table_int   = BuildPerClassCocycleBasis(setup, g_rep, C).table
#                 (n² × k integer matrix; column i is c_{g_rep}_{e_i}
#                  as a length-n² vector indexed by (h_i, h_j) in AsList(C))
#   P_C         = the projection record (from BuildPCWithBockstein)
#   M_bar       = r × k integer matrix; entry M_bar[l][i] is the l-th
#                 H^2(C) coordinate of Tr_{g_rep}(e_i) modulo
#                 P_C.torsion_full[l]
#   torsion_C   = P_C.torsion_full
#   bockstein_used = bool from P_C
# ---------------------------------------------------------------------

# ---------------------------------------------------------------------
# BuildReducedTransgressionMatrixFast — GF(2)-only fast path.
#
# For order-2 H^3 generators e_i (h3_torsion[i] = 2): the c_g cocycle
# values are in {0, exp/2}, which after dividing by exp/2 gives an F_2
# cocycle c'_g. The condition [c_g] = 0 in H^2(C; Z/exp) is equivalent
# (for exp >= 4) to [c'_g] in image(β: H^1(F_2) -> H^2(F_2)) + B^2(F_2),
# which is the row-span of M_lift := [BocksteinH1ToH2(C); B^2(F_2)^T].
# (For exp = 2 the same is true with B^2(F_2) only, since image(β) is
# orthogonal to the kernel question. We use the same machinery either
# way via _GetLiftSemForC.)
#
# M_bar_F2's i-th column (for order-2 e_i) is the projection of c'_g_{e_i}
# to F_2^{n²} / span(M_lift); this is computed via the cached
# SemiEchelonMatTransformation in _GetLiftSemForC(C).batched, extracting
# the non-pivot-column entries of the back-sub residual.
#
# For the order-exp generator (h3_torsion[i] = exp): its column in M_bar
# is left UNPROJECTED (it's a Z/exp class possibly outside the Hom +
# Bockstein span). Tested via IsCoboundary2Split fallback in the kernel
# computation.
# ---------------------------------------------------------------------

BuildReducedTransgressionMatrixFast := function(setup, g_rep, C)
    local cache, table_int, k, h3_torsion, exp_local,
          lift_entry, lift_sem, lift_batched, pivot_cols, Y_full,
          rank, ncols, non_pivot_cols, r_quot, table_gf2, table_gf2_top_T,
          M_bar_F2, i, col_i_gf2, residual, one_gf2, zero_gf2,
          order_2_gens, fail_columns, l, r_local, cols_gf2,
          M_bar_gf2,
          # batched Step 1 locals
          B_cols, k_use, idx, residual_batch;

    cache := BuildPerClassCocycleBasis(setup, g_rep, C);
    table_int := cache.table;
    table_gf2 := cache.table_gf2;   # n² × k GF(2) precomputed in cache
    table_gf2_top_T := cache.table_gf2_top_T;   # column-major view (issue #391)
    exp_local := setup.exponent;
    h3_torsion := setup.torsion;
    k := setup.num_generators;
    one_gf2 := One(GF(2));
    zero_gf2 := Zero(GF(2));

    # Get the cached SemiEchelonMatTransformation of M_lift = [β image; B²].
    lift_entry := _GetLiftSemForC(C);
    lift_sem := lift_entry.sem;
    lift_batched := lift_entry.batched;
    rank := lift_batched.rank;
    ncols := lift_batched.ncols;   # = n*n
    pivot_cols := lift_batched.pivot_cols;
    Y_full := lift_batched.Y_full;
    # Non-pivot columns = [1..n²] \ pivot_cols. The projection to the
    # quotient extracts entries at these columns.
    non_pivot_cols := Difference([1..ncols], pivot_cols);
    r_quot := Length(non_pivot_cols);

    # Order-2 generator indices (which order-2 H^3 gens to project).
    order_2_gens := Filtered([1..k], i -> h3_torsion[i] = 2);

    # MEMORY FIX (issue #302): At m=5 r_quot can be 4M+. The previous
    # `List([1..r_quot], l -> List([1..k], i -> 0))` allocated an
    # r_quot × k INTEGER matrix (~5.5 GB at r=4M, k=165). We now build
    # the matrix one COLUMN at a time as GF(2) vectors, then transpose
    # to a r_quot × k compressed GF(2) matrix. Compressed GF(2) packing
    # makes the result ~80 MB instead of ~5.5 GB.
    #
    # We still return `M_bar` as a list of integer rows (0/1) for any
    # callers that need the explicit integer form (e.g. M_bar_F2[l][i]
    # indexing in legacy tests). At m=5, callers using the streaming
    # column path consume `M_bar_gf2` directly and ignore `M_bar`.
    # fail_columns: H^3 generators that need fallback. We mark ALL
    # non-order-2 generators (i.e. the order-exp generator) as fallback,
    # since this F_2 path only handles order-2 cocycles.
    fail_columns := Filtered([1..k], i -> h3_torsion[i] <> 2);

    # Step 1: compute, for each order-2 generator i, the i-th column of
    # M_bar as a length-r_quot GF(2) vector.
    #
    # Composition (PR #396 audit instance B-6): the previous version did
    # k separate AddRowVector-based back-subs against the same cached
    # `lift_sem` (one per order-2 generator). Each back-sub had ~99.7%
    # interpreter overhead per the live A-5b profile. The
    # cached `lift_batched` record already contains pre-built batched
    # artefacts (Y_full in RREF + pivot_cols) for exactly this scenario;
    # `_RowSpanResidualBatch(lift_batched, B)` computes the residual in
    # one compiled GF(2) matmul + matrix add for a whole batch of RHSes,
    # mirroring what `IsCoboundary2Mod2WithLiftVecBatch` does on the Path
    # A hot path.
    #
    # Build B as the stacked column matrix (k_use × n²): row idx in B is
    # column `order_2_gens[idx]` of table_gf2, which equals
    # cache.table_gf2_top_T[order_2_gens[idx]] — a packed-GF(2) vector.
    # The column-major view (table_gf2_top_T, populated by PR #391) avoids
    # the n²-element closure dispatch that the previous extraction used.
    k_use := Length(order_2_gens);
    cols_gf2 := List([1..k], i -> fail);
    if k_use > 0 then
        B_cols := EmptyPlist(k_use);
        for idx in [1..k_use] do
            i := order_2_gens[idx];
            # Column-major extraction: one ELM_LIST instead of a closure.
            # ShallowCopy because _RowSpanResidualBatch may mutate inputs
            # via in-place GF(2) ops in some code paths; conservative copy.
            Add(B_cols, ShallowCopy(table_gf2_top_T[i]));
        od;
        ConvertToMatrixRep(B_cols, GF(2));

        # One batched residual computation. At rank=0 the residual equals
        # B_cols itself (no constraints from lift_sem); _RowSpanResidualBatch
        # short-circuits this case internally and returns B unchanged.
        residual_batch := _RowSpanResidualBatch(lift_batched, B_cols);

        # Slice each residual row to non_pivot_cols → length r_quot
        # quotient-space vector. Compiled list-element-slice
        # (ELMS_GF2VEC) on a GF(2) row.
        for idx in [1..k_use] do
            i := order_2_gens[idx];
            col_i_gf2 := residual_batch[idx]{non_pivot_cols};
            ConvertToVectorRep(col_i_gf2, GF(2));
            cols_gf2[i] := col_i_gf2;
        od;
    fi;
    # Zero column for any non-order-2 generator (fail columns).
    for i in [1..k] do
        if cols_gf2[i] = fail then
            col_i_gf2 := ListWithIdenticalEntries(r_quot, zero_gf2);
            ConvertToVectorRep(col_i_gf2, GF(2));
            cols_gf2[i] := col_i_gf2;
        fi;
    od;

    # Step 2: transpose cols_gf2 (list of k length-r_quot GF(2) vectors)
    # to M_bar_gf2 (r_quot × k compressed GF(2) matrix). Build row by row.
    M_bar_gf2 := [];
    for l in [1..r_quot] do
        b := ListWithIdenticalEntries(k, zero_gf2);
        for i in [1..k] do
            b[i] := cols_gf2[i][l];
        od;
        ConvertToVectorRep(b, GF(2));
        Add(M_bar_gf2, b);
    od;
    if r_quot > 0 then
        ConvertToMatrixRep(M_bar_gf2, GF(2));
    fi;
    # Discard the per-column GF(2) vectors now that M_bar_gf2 owns the data.
    cols_gf2 := fail;

    # Build the legacy integer M_bar lazily ONLY if r_quot is small enough
    # that materialising it does not OOM. The streaming consumer below
    # uses M_bar_gf2 directly; legacy callers (m<=3) still get an int M_bar.
    # Threshold: r_quot * k > 4e6 cells (-> ~32 MB for ints) → skip.
    if r_quot * k <= 4 * 1000 * 1000 then
        M_bar_F2 := List([1..r_quot],
            l -> List([1..k], i -> If_(IsZero(M_bar_gf2[l][i]), 0, 1)));
    else
        # Too large; skip integer M_bar. Streaming path uses M_bar_gf2.
        M_bar_F2 := fail;
    fi;

    return rec(
        table_int     := table_int,
        P_C           := rec(r_full := r_quot,
                              torsion_full := List([1..r_quot], l -> 2)),
        M_bar         := M_bar_F2,
        M_bar_gf2     := M_bar_gf2,
        r_quot        := r_quot,
        torsion_C     := List([1..r_quot], l -> 2),
        C             := C,
        bockstein_used := false,
        cache         := cache,
        fail_columns  := fail_columns,
        order_2_gens  := order_2_gens);
end;;


BuildReducedTransgressionMatrix := function(setup, g_rep, C)
    local cache, P_C, table_int, k, r_full, M_bar, i, col_i, a_coords,
          exp_local, l, h3_torsion, order_2_gens, fail_columns,
          M_bar_order2;
    # Dispatch to the FAST GF(2)-based path. The order-exp generator
    # (if any) is left to fall back to IsCoboundary2Split per orbit,
    # which is recorded via fail_columns = [exp_index] in the caller.
    return BuildReducedTransgressionMatrixFast(setup, g_rep, C);
end;;


BuildReducedTransgressionMatrix_Slow := function(setup, g_rep, C)
    local cache, P_C, table_int, k, r_full, M_bar, i, col_i, a_coords,
          exp_local, l, h3_torsion, order_2_gens, fail_columns,
          M_bar_order2;
    cache := BuildPerClassCocycleBasis(setup, g_rep, C);
    table_int := cache.table;
    exp_local := setup.exponent;
    h3_torsion := setup.torsion;

    P_C := BuildPCWithBockstein(C, exp_local);
    r_full := P_C.r_full;
    k := setup.num_generators;

    # SCOPE NOTE (perf-4'): we project to H^2(C; Z/exp_G) only the
    # ORDER-2 generators of H^3(G; U(1)) (i.e. columns i with
    # h3_torsion[i] = 2). For order-2 generators, the cocycle c_g_{e_i}
    # takes values in {0, exp_G / 2}, which is covered by the
    # (cocyclebasis + Bockstein-image) augmented basis.
    #
    # The order-exp generator (h3_torsion[i] = exp_G) is handled
    # separately by the existing iterated-Bockstein Path-Z dispatch
    # (IsCoboundary2Z2k); its column in M_bar is left as zero and
    # the kernel computation only constrains the ORDER-2 columns.
    #
    # This is a sound restriction: if vec[order-exp generator] = 0,
    # the kernel question reduces entirely to the order-2 sublayer
    # (where M_bar . vec ≡ 0 mod row_torsion is the exact constraint).
    # For non-zero order-exp coordinate, the kernel intersects the
    # <e_order-exp> axis at a sub-cyclic subgroup, computable by
    # bisection: test k * e_{exp_index} for k = 1, 2, ..., exp - 1
    # via the existing per-class IsCoboundary2Split path.
    #
    # See KernelOfTransgressionViaMBar for the order-exp axis test
    # and the combined kernel assembly.
    order_2_gens := Filtered([1..k], i -> h3_torsion[i] = 2);

    M_bar := List([1..r_full], l -> List([1..k], i -> 0));
    fail_columns := [];
    # Try ALL columns of table_int (order-2 generators AND the order-exp
    # generator, if present). The order-exp column may fail projection due
    # to non-trivial Z/4 or Z/8 components in H^2(C; Z/exp_G); in that
    # case we record the column index for fallback. Order-2 columns
    # have c_g cocycle values in {0, exp/2}, which the Bockstein-augmented
    # basis ALWAYS spans (mod boundary + exp), so they typically succeed.
    for i in [1..k] do
        # Column i of table_int: the c_{g_rep}_{e_i} cocycle as a length-n²
        # vector. Get it by extracting column i from the table matrix.
        col_i := List(table_int, row -> row[i]);
        a_coords := ProjectVectorViaP_C(P_C, col_i);
        if a_coords = fail then
            # Projection failure: c_g has an H^2(C; Z/exp_G) class
            # outside (cocyclebasis + Bockstein-image) span. Record for
            # fallback. The caller will use IsCoboundary2Split per-class
            # for these (vec, orbit) combinations.
            Add(fail_columns, i);
            continue;
        fi;
        for l in [1..r_full] do
            M_bar[l][i] := a_coords[l];
        od;
    od;

    if not IsEmpty(fail_columns) then
        Print("    WARNING: ", Length(fail_columns),
              " columns failed projection on |C|=", Order(C), ": ",
              fail_columns,
              " (will fall back to IsCoboundary2Split for these).\n");
    fi;

    return rec(
        table_int     := table_int,
        P_C           := P_C,
        M_bar         := M_bar,
        torsion_C     := P_C.torsion_full,
        C             := C,
        bockstein_used := P_C.bockstein_used,
        cache         := cache,
        fail_columns  := fail_columns,
        order_2_gens  := order_2_gens);
end;;


# ---------------------------------------------------------------------
# Helpers for BRW-orbit propagation.
# ---------------------------------------------------------------------
#
# For an orbit with rep g and members {g_j = y_j . g}, the reduced
# transgression matrix at member g_j (computed via its own centraliser
# C_j) equals M_bar_g . M_y_j (up to isomorphism C_j ≅ C, which doesn't
# affect the kernel — the H^2 coordinates are different bases but the
# constraint M_bar_g . M_y_j . vec ≡ 0 mod torsion_C is the SAME kernel
# condition as M_bar_{g_j} . vec ≡ 0 mod torsion_{C_j}).
#
# So per orbit, the joint constraint is
#   M_bar_g . M_y_j . vec ≡ 0 mod torsion_C   for all j in orbit
# and stacking the |orbit| matrices gives the orbit's contribution
# to M_stack.

# ApplyH3MatrixToMatBar(M_bar, M_y, h3_torsion)
#   Compute M_bar . M_y as an r × k integer matrix, reducing each
#   ROW mod the H^2 torsion (since the M_bar rows are already mod
#   torsion_C, M_bar . M_y is well-defined mod torsion_C).
#
# WARNING (#302): at m=5 with r ~4M and k=165, the r × k allocation
# is ~5.5 GB of int memory. KEPT for legacy callers (tests at m<=3).
# Streaming consumers should use ColumnDispositionFromMBarGF2 below.
ApplyH3MatrixToMatBar := function(M_bar, M_y, torsion_C, h3_torsion)
    local r, k, result, l, i, s, j;
    r := Length(M_bar);
    if r = 0 then return []; fi;
    k := Length(M_bar[1]);
    result := List([1..r], l -> List([1..k], i -> 0));
    for l in [1..r] do
        for i in [1..k] do
            s := 0;
            for j in [1..k] do
                s := s + M_bar[l][j] * M_y[j][i];
            od;
            result[l][i] := s mod torsion_C[l];
        od;
    od;
    return result;
end;;


# UpdateColumnDispositionFromMBarGF2(M_bar_gf2, M_y, col_has_constraint)
#   Streaming alternative to ApplyH3MatrixToMatBar for the OOM site (#302).
#
#   M_bar_gf2: r × k compressed GF(2) matrix (the propagated M_bar mod 2).
#   M_y      : k × k INTEGER matrix (H^3 endomorphism mod h3_torsion).
#   col_has_constraint: BlistList of length k. On entry the bits for
#     columns already proven non-trivial. On return updated in place:
#     bit i set to true if column i of (M_bar_gf2 . M_y mod 2) has any
#     nonzero row.
#
# Math: for each column i of the result, we need
#   (M_bar_gf2 . M_y[:,i] mod 2) has a nonzero entry  ?
# We extract column i of M_y mod 2 as a GF(2) vector v, then check
# whether `M_bar_gf2 * v` (a length-r GF(2) vector) has any 1.
# If at least one 1: column i is constrained. We can therefore SKIP
# any column already marked constrained (avoids the GF(2) matvec for
# columns we already know about).
#
# Peak memory per call: O(r) bits for the GF(2) matvec result, which
# at r=4M is ~500 KB. The M_bar_gf2 matrix itself (~80 MB) is shared
# across all members of an orbit and freed after the orbit completes.
UpdateColumnDispositionFromMBarGF2 := function(M_bar_gf2, M_y,
                                                col_has_constraint)
    local k_dim, zero_gf2, one_gf2, r_local, i, j, v, prod, ok;
    if Length(M_bar_gf2) = 0 then
        return;
    fi;
    k_dim := Length(M_y);
    zero_gf2 := Zero(GF(2));
    one_gf2 := One(GF(2));
    r_local := Length(M_bar_gf2);

    for i in [1..k_dim] do
        # Skip columns already known to be constrained.
        if col_has_constraint[i] then continue; fi;
        # Build column i of M_y mod 2 as a GF(2) vector.
        v := List([1..k_dim], j -> If_(M_y[j][i] mod 2 = 0, zero_gf2, one_gf2));
        ConvertToVectorRep(v, GF(2));
        # Compute M_bar_gf2 * v over GF(2).
        prod := M_bar_gf2 * v;
        # If any entry of prod is nonzero, column i has a constraint.
        if not IsZero(prod) then
            col_has_constraint[i] := true;
        fi;
    od;
end;;


# UpdateColumnDispositionFromMBarGF2_Batch(M_bar_gf2, M_y, col_has_constraint)
#   Batched variant: builds M_y mod 2 RESTRICTED to currently-unconstrained
#   columns as a GF(2) matrix and multiplies M_bar_gf2 * M_y_gf2_unconstrained
#   in one shot, then checks each column for nonzero entries.
#
#   Use this when many columns are still unconstrained (early in the
#   sweep) — GF(2) matrix-matrix multiply is much faster than k matrix-
#   vector multiplies. Switch to the per-column variant once most
#   columns are settled.
#
#   Composition (PR #396 audit instance A-3): the previous version did a
#   full `M_bar_gf2 * M_y_gf2` over all k columns of M_y, even when most
#   were already marked constrained via col_has_constraint. The "switch
#   between batched and per-column" dispatcher amortised one win or the
#   other but never composed them. We now restrict M_y to its unconstrained
#   columns BEFORE the GF(2) matmul, so the compiled
#   PROD_GF2MAT_GF2MAT call's numRHS shrinks to |unconstrained|. At
#   later orbits, where most columns are already constrained, this is
#   strictly better than both the pre-A-3 batched path (which paid the
#   full O(r × k_dim) matmul cost) and the per-column path (which paid
#   |unconstrained| separate matvec calls).
#
#   Peak memory: O(r × |unconstrained|) GF(2) bits during the product,
#   bounded above by the previous ~80 MB at r=4M, k=165. At late orbits
#   where |unconstrained| is small, peak memory drops proportionally.
UpdateColumnDispositionFromMBarGF2_Batch := function(M_bar_gf2, M_y,
                                                      col_has_constraint)
    local k_dim, zero_gf2, one_gf2, r_local, unconstrained, k_un,
          M_y_gf2, j, i, row, prod_sliced, idx_u;
    if Length(M_bar_gf2) = 0 then
        return;
    fi;
    k_dim := Length(M_y);
    zero_gf2 := Zero(GF(2));
    one_gf2 := One(GF(2));
    r_local := Length(M_bar_gf2);

    # Identify currently-unconstrained columns. The matmul only needs to
    # examine these — already-constrained columns can never flip back.
    unconstrained := Filtered([1..k_dim], i -> not col_has_constraint[i]);
    k_un := Length(unconstrained);
    if k_un = 0 then
        return;
    fi;

    # Build M_y mod 2 RESTRICTED to the unconstrained columns as a GF(2)
    # matrix of shape k_dim × k_un. Each row is M_y[j]{unconstrained} mod 2
    # lifted into GF(2). We construct row-by-row so the resulting matrix
    # is in compressed GF(2) form for the compiled PROD_GF2MAT_GF2MAT call.
    M_y_gf2 := [];
    for j in [1..k_dim] do
        row := List(unconstrained,
                    i -> If_(M_y[j][i] mod 2 = 0, zero_gf2, one_gf2));
        ConvertToVectorRep(row, GF(2));
        Add(M_y_gf2, row);
    od;
    ConvertToMatrixRep(M_y_gf2, GF(2));

    # Compute M_bar_gf2 * M_y_gf2_unconstrained over GF(2): shape
    # (r_local × k_dim) × (k_dim × k_un) → (r_local × k_un). Peak
    # memory scales with |unconstrained| rather than k_dim.
    prod_sliced := M_bar_gf2 * M_y_gf2;

    # Inspect each column of the sliced product for nonzero entries.
    # idx_u indexes into `unconstrained` (and into the columns of prod_sliced);
    # unconstrained[idx_u] is the original column index in col_has_constraint.
    for idx_u in [1..k_un] do
        if not ForAll([1..r_local], j -> IsZero(prod_sliced[j][idx_u])) then
            col_has_constraint[unconstrained[idx_u]] := true;
        fi;
    od;
end;;


# H3MatrixForOrbitMember(start_idx, target_idx, parent, gen_used,
#                        h3_matrices, h3_torsion)
#   Build the k × k H^3 endomorphism matrix M_y such that y . classes[start]
#   = classes[target] under the BRW conjugacy action. This is the matrix
#   form of the same computation H3VecAtTarget does on a single vector,
#   but materialised as a full matrix so we can compose with M_bar
#   (which is r × k).
#
#   Algorithm: walk the Schreier path start -> ... -> target, applying
#   h3_matrices[gen_used[pos]] in forward order. The result acts on
#   column vectors v as (M_y * v) — same convention as
#   ApplyH3Endomorphism.
H3MatrixForOrbitMember := function(start_idx, target_idx, parent, gen_used,
                                    h3_matrices, h3_torsion)
    local path, pos, M_y, k_dim, k_step, M_step, prod, l, i, s, j;
    k_dim := Length(h3_torsion);
    if target_idx = start_idx then
        # Identity matrix mod torsion.
        return List([1..k_dim],
                    l -> List([1..k_dim], i -> If_(l = i, 1, 0)));
    fi;
    # Reconstruct path start_idx -> target_idx by walking parents.
    path := [target_idx];
    pos := target_idx;
    while parent[pos] <> start_idx do
        pos := parent[pos];
        if pos = -1 then
            Error("H3MatrixForOrbitMember: target ", target_idx,
                  " not reachable from start ", start_idx);
        fi;
        Add(path, pos);
    od;
    path := Reversed(path);
    # M_y starts as identity, then we LEFT-multiply by each h3_matrices step
    # in forward order: M_y -> h3_matrices[gen_used[path[1]]] . M_y -> ...
    # Equivalently, we want the composition order to match H3VecAtTarget:
    # vec -> h3_matrices[path[1]] . vec -> h3_matrices[path[2]] . (h3_matrices[path[1]] . vec) -> ...
    # So the final matrix on column vec is h3_matrices[path[end]] . ... . h3_matrices[path[1]].
    M_y := List([1..k_dim], l -> List([1..k_dim], i -> If_(l = i, 1, 0)));
    for pos in path do
        k_step := gen_used[pos];
        M_step := h3_matrices[k_step];
        # M_y_new = M_step . M_y, with each row mod h3_torsion[l].
        #
        # Issue #372 (F1): replace the interpreted k^3 triple loop with
        # compiled PROD_MAT_MAT_INT and a per-row mod pass. Same shape
        # as the wins in #370 / #371. At k=165, the triple loop was
        # ~4.5M interpreted ops per Schreier step times O(path_length *
        # orbit_size * axis_vecs) — the next dominant fail-column cost
        # after #371 cleared the IB closure dispatch.
        prod := M_step * M_y;
        # Issue #387 audit-tier3 rank 3: per-row closure dispatched k
        # times per Schreier step; compiled list-mod-int is a single C
        # call per row.
        for l in [1..k_dim] do
            prod[l] := prod[l] mod h3_torsion[l];
        od;
        M_y := prod;
    od;
    return M_y;
end;;


# ---------------------------------------------------------------------
# KernelOfTransgressionViaMBar — driver that builds M_bar per orbit rep,
# propagates via BRW, stacks vertically, and computes the joint kernel
# via SNF.
#
# Inputs:
#   setup        : SetupCohomology3(G) record
#   orbits_data  : list of rec(start_idx, orbit, parent, gen_used) from
#                  OrbitWithSchreierVec sweep (the conjugacy-class action
#                  of BRW). Same format produced by run_e_plus_m_kernel_hap.g.
#   classes      : ConjugacyClasses(G) (or equivalent list)
#   G            : the group
#   h3_matrices  : list of k×k H^3 endomorphism matrices (parallel to BRW
#                  generators); h3_matrices[i] acts on vec as
#                  ApplyH3Endomorphism(h3_matrices[i], vec, torsion).
#
# Returns rec(
#   kernel_size      : integer (Product of basis_orders)
#   in_kernel_gens   : list of unit-generator indices that are in ker
#                      (when M_bar . e_i ≡ 0); used for cross-check
#                      with the existing per-gen sweep output format.
#   exp_index        : Position(setup.torsion, setup.exponent)
#   half_in_kernel   : whether 2 * e_{exp_index} is in ker (for exp > 2)
#   kernel_basis_vecs: list of (basis_vec, order) records — the kernel
#                      decomposition similar to run_e_plus_m_kernel_hap.g's
#                      basis_summary
#   M_stack          : the stacked r_total × k integer matrix (mod
#                      torsion_stack per row, mod h3_torsion per col input)
#   row_torsion      : torsion list for the stacked rows
#   reduced_matrices : list of rec(orbit_start, M_bar_g, torsion_C) per orbit
# )
# ---------------------------------------------------------------------

KernelOfTransgressionViaMBar := function(setup, orbits_data, classes, G,
                                          h3_matrices)
    local k, h3_torsion, exp_local, exp_index, n_orbits,
          reduced_matrices, orb_info, rep, C, redmat, t_orb, t_propagate,
          M_stack, row_torsion, M_y_j, M_bar_propagated, l, i, r_o,
          t_kernel, in_kernel_gens, half_in_ker, half_vec, half_okay,
          kernel_basis_vecs, vec, target_idx, t_red, kernel_size,
          unit_e_i, j, mask, big, snf, kernel_rows, x_part, reduced_rows,
          snf_d, normal_diag, kernel_torsion, all_fail_columns,
          fc, fc_i, e_fc, cache_orbit, c_g_table_fc, ok, has_failures,
          fallback_in_ker, c_g_func, fallback_target_idx,
          fallback_vec_target, exp_axis_in_ker, t_test, c_g_table_exp,
          t_axis, exp_axis_k, exp_axis_vec, exp_axis_in_ker_k,
          M_y_j_exp, M_y_j_exp_T, vec_target_exp, all_orbit_ok, basis_orders, jj,
          col_has_constraint, total_rows, orbit_ckpt_path,
          completed_orbit_starts, ckpt_data, ckpt_stream, t_orbit_prop,
          M_bar_gf2_val, r_quot_val, cache_val, fail_columns_val;
    k := setup.num_generators;
    h3_torsion := setup.torsion;
    exp_local := setup.exponent;
    exp_index := Position(setup.torsion, exp_local);
    n_orbits := Length(orbits_data);

    Print("KernelOfTransgressionViaMBar: ", n_orbits, " BRW orbits, ",
          " k = ", k, " H^3 generators, exp = ", exp_local, "\n");

    # Step 1: build M_bar per orbit rep.
    reduced_matrices := [];
    t_red := Runtime();
    for j in [1..n_orbits] do
        orb_info := orbits_data[j];
        rep := Representative(classes[orb_info.start_idx]);
        C := Centralizer(G, rep);
        Print("  orbit ", j, "/", n_orbits, " (|C|=", Order(C),
              ", orbit size=", Length(orb_info.orbit),
              ", rep order=", Order(rep), ") ... ");
        t_orb := Runtime();
        if IsOne(rep) then
            # Identity class: c_g identically 0; M_bar_g is the zero
            # matrix. We still need to record SOMETHING with consistent
            # torsion shape — but a zero row contributes no constraints
            # to the kernel, so we just record an EMPTY M_bar (r=0).
            redmat := rec(
                table_int := [],
                P_C := rec(r_full := 0, torsion_full := []),
                M_bar := [],
                M_bar_gf2 := [],
                r_quot := 0,
                torsion_C := [],
                C := C,
                bockstein_used := false,
                cache := fail,
                fail_columns := [],
                order_2_gens := []);
            Print("identity (skipped, no constraints)  (",
                  (Runtime() - t_orb) / 1000., " s)\n");
        else
            redmat := BuildReducedTransgressionMatrix(setup, rep, C);
            Print("M_bar shape = ", redmat.r_quot, "x", k,
                  ", bockstein_used = ", redmat.bockstein_used,
                  "  (", (Runtime() - t_orb) / 1000., " s)\n");
        fi;
        # Issue #363: build the per-orbit record entry using real
        # `if/else` blocks rather than the strict-eval `If_` shim.
        # `If_` evaluates BOTH branches before dispatch, so the lazy
        # fallback `Length(redmat.M_bar)` (intended only when r_quot
        # is unbound) explodes when M_bar = fail. At m=5, the lazy-
        # integer-M_bar path in BuildReducedTransgressionMatrix
        # (lines 596-606) deliberately returns M_bar = fail when
        # r_quot * k > 4e6 cells; r_quot is always set.
        if IsBound(redmat.M_bar_gf2) then
            M_bar_gf2_val := redmat.M_bar_gf2;
        else
            M_bar_gf2_val := [];
        fi;
        if IsBound(redmat.r_quot) then
            r_quot_val := redmat.r_quot;
        elif IsList(redmat.M_bar) then
            r_quot_val := Length(redmat.M_bar);
        else
            r_quot_val := 0;
        fi;
        if IsBound(redmat.cache) then
            cache_val := redmat.cache;
        else
            cache_val := fail;
        fi;
        if IsBound(redmat.fail_columns) then
            fail_columns_val := redmat.fail_columns;
        else
            fail_columns_val := [];
        fi;
        Add(reduced_matrices, rec(
            orbit_start := orb_info.start_idx,
            M_bar       := redmat.M_bar,
            M_bar_gf2   := M_bar_gf2_val,
            r_quot      := r_quot_val,
            torsion_C   := redmat.torsion_C,
            C           := redmat.C,
            bockstein_used := redmat.bockstein_used,
            cache       := cache_val,
            fail_columns := fail_columns_val,
            orb_info    := orb_info));
    od;
    if IsBoundGlobal("_LogStamped") then
        _LogStamped("Per-orbit M_bar build wall: ",
                    (Runtime() - t_red) / 1000., " s");
    else
        Print("Per-orbit M_bar build wall: ",
              (Runtime() - t_red) / 1000., " s\n");
    fi;

    # Collect the UNION of fail_columns across orbits — these are H^3
    # generator indices whose c_g projection failed on at least one
    # orbit. We'll need to test their kernel contribution by per-orbit
    # fallback IsCoboundary2Split rather than via the M_stack linear
    # algebra.
    all_fail_columns := [];
    for j in [1..n_orbits] do
        for fc in reduced_matrices[j].fail_columns do
            if not (fc in all_fail_columns) then
                Add(all_fail_columns, fc);
            fi;
        od;
    od;
    Print("Union of fail_columns across orbits: ", all_fail_columns, "\n");

    # Step 2: propagate per-orbit M_bar to all orbit members via
    # BRW H^3 endomorphism matrices and accumulate per-column
    # constraint information.
    #
    # MEMORY FIX (#302): the previous implementation materialised
    # M_stack (R_total × k integers, with R_total ~ 4M+ at m=5),
    # consuming ~5.5 GB of integer memory and OOM-ing the run at
    # transgression_matrix_reduced.g:696. The new path streams the
    # propagation per orbit-member and only retains a boolean
    # `col_has_constraint[i]` saying whether column i of M_stack has
    # any nonzero row. That's the only information used by Step 3.
    #
    # For the half-vec check (Step 3b) we also track whether the
    # propagated rows of M_stack `dot half_vec mod 2` is identically
    # zero, which is automatic since half_vec[exp_index] = 2 and the
    # propagated rows are mod 2 — so 2*x mod 2 = 0 always. (See the
    # detailed comment in Step 3b.) Confirming this means we do not
    # need to keep any row data around at all.
    #
    # CHECKPOINTING (#302 Stage 1): after each orbit's contribution is
    # merged into col_has_constraint, we persist the bitvector to
    # `computed/transgression/<m>/orbit_partial.g`. Resumption skips
    # already-processed orbits (which can take hours each at m=5).
    t_propagate := Runtime();
    # col_has_constraint[i] = true iff some row of M_stack has a
    # nonzero value in column i. Initialised all-false.
    col_has_constraint := BlistList([1..k], []);
    # row_torsion stays available as a small accumulator (~few hundred
    # entries — only contains the FULL list when stored; with streaming
    # we just track Sum(orbit_size * r_o) and the per-orbit r_o values).
    row_torsion := [];   # kept for legacy result-record compat (small)
    total_rows := 0;

    # Checkpoint file: optional, controlled by global ORBIT_CHECKPOINT_PATH.
    if IsBoundGlobal("ORBIT_CHECKPOINT_PATH") then
        orbit_ckpt_path := ORBIT_CHECKPOINT_PATH;
    else
        orbit_ckpt_path := fail;
    fi;
    completed_orbit_starts := [];   # orbit.start_idx values already merged
    if orbit_ckpt_path <> fail and IsExistingFile(orbit_ckpt_path) then
        # Load previously persisted col_has_constraint + completed orbits.
        Print("Loading orbit checkpoint from ", orbit_ckpt_path, "...\n");
        ckpt_data := ReadAsFunction(orbit_ckpt_path)();
        if IsRecord(ckpt_data)
           and IsBound(ckpt_data.col_has_constraint)
           and IsBound(ckpt_data.completed_orbit_starts)
           and Length(ckpt_data.col_has_constraint) = k then
            for i in [1..k] do
                if ckpt_data.col_has_constraint[i] then
                    col_has_constraint[i] := true;
                fi;
            od;
            completed_orbit_starts := ckpt_data.completed_orbit_starts;
            if IsBound(ckpt_data.total_rows) then
                total_rows := ckpt_data.total_rows;
            fi;
            Print("  resumed: ", Length(completed_orbit_starts),
                  " orbits already merged, ",
                  Length(Filtered([1..k], i -> col_has_constraint[i])),
                  " columns already constrained\n");
        else
            Print("  checkpoint file present but malformed; ignoring.\n");
        fi;
    fi;

    for j in [1..n_orbits] do
        orb_info := reduced_matrices[j].orb_info;
        if reduced_matrices[j].r_quot = 0 then
            # Trivial orbit (identity class) — no constraints.
            continue;
        fi;
        if orb_info.start_idx in completed_orbit_starts then
            Print("  orbit ", j, "/", n_orbits, " (start ",
                  orb_info.start_idx, "): SKIPPED (resumed from checkpoint)\n");
            continue;
        fi;
        r_o := reduced_matrices[j].r_quot;
        # Per-orbit accumulator wall time.
        t_orbit_prop := Runtime();
        for target_idx in orb_info.orbit do
            M_y_j := H3MatrixForOrbitMember(
                orb_info.start_idx, target_idx,
                orb_info.parent, orb_info.gen_used,
                h3_matrices, h3_torsion);
            # MEMORY-SAFE streaming column-disposition update.
            # The batched variant uses ~80 MB peak GF(2) memory at m=5;
            # the per-column variant uses ~500 KB (slower per call but
            # short-circuits once columns settle). Heuristic: use the
            # per-column variant when most columns are already
            # constrained (saves the full matmul); use batched when
            # many columns are still open.
            if Length(reduced_matrices[j].M_bar_gf2) > 0
               and Length(Filtered([1..k], i -> not col_has_constraint[i]))
                   > k / 2 then
                UpdateColumnDispositionFromMBarGF2_Batch(
                    reduced_matrices[j].M_bar_gf2, M_y_j,
                    col_has_constraint);
            else
                UpdateColumnDispositionFromMBarGF2(
                    reduced_matrices[j].M_bar_gf2, M_y_j,
                    col_has_constraint);
            fi;
            total_rows := total_rows + r_o;
        od;
        Add(completed_orbit_starts, orb_info.start_idx);
        Print("  orbit ", j, "/", n_orbits, " merged (r_o=", r_o,
              ", members=", Length(orb_info.orbit), ", ",
              (Runtime() - t_orbit_prop) / 1000., " s, ",
              Length(Filtered([1..k], i -> col_has_constraint[i])),
              "/", k, " columns now constrained)\n");

        # Persist checkpoint after each orbit (small, ~few KB).
        if orbit_ckpt_path <> fail then
            ckpt_stream := OutputTextFile(orbit_ckpt_path, false);
            SetPrintFormattingStatus(ckpt_stream, false);
            PrintTo(ckpt_stream,
                "# Orbit-level checkpoint for KernelOfTransgressionViaMBar (#302).\n",
                "# Generated by transgression_matrix_reduced.g.\n",
                "return rec(\n",
                "    col_has_constraint := ",
                List([1..k], i -> col_has_constraint[i]), ",\n",
                "    completed_orbit_starts := ",
                completed_orbit_starts, ",\n",
                "    total_rows := ", total_rows, "\n",
                ");\n");
            CloseStream(ckpt_stream);
        fi;

        # Free per-orbit M_bar / M_bar_gf2 immediately to release
        # ~80 MB before the next orbit is built.
        reduced_matrices[j].M_bar := fail;
        reduced_matrices[j].M_bar_gf2 := fail;
    od;
    if IsBoundGlobal("_LogStamped") then
        _LogStamped("Propagation wall: ",
                    (Runtime() - t_propagate) / 1000., " s");
    else
        Print("Propagation wall: ",
              (Runtime() - t_propagate) / 1000., " s\n");
    fi;
    Print("Total propagated rows (M_stack height): ", total_rows, "\n");
    Print("Columns with constraints: ",
          Length(Filtered([1..k], i -> col_has_constraint[i])), " / ", k, "\n");
    # M_stack itself is not materialised; downstream consumers should
    # use col_has_constraint. We expose an EMPTY M_stack in the result
    # record for backward compatibility (callers may check Length only).
    M_stack := [];

    # Step 3: extract ker(Tr) from the column-disposition information.
    #
    # MEMORY FIX (#302): the original Step 3 iterated `M_stack[l][i] mod
    # row_torsion[l]` across all L × k entries. The streaming Step 2
    # already accumulated the equivalent column information into
    # `col_has_constraint`: column i has at least one nonzero row in
    # M_stack iff col_has_constraint[i] is true. So e_i is in
    # ker(Tr) iff col_has_constraint[i] is false (for order-2 generators
    # not in all_fail_columns).
    t_kernel := Runtime();
    if total_rows = 0 then
        # Trivial kernel: full H^3 (only identity-class orbits — degenerate).
        kernel_size := Product(h3_torsion);
        kernel_basis_vecs := List([1..k], i -> rec(
            generator_index := i,
            kind := Concatenation("e_", String(i)),
            order := h3_torsion[i],
            vec := List([1..k], j -> If_(j = i, 1, 0))));
        return rec(
            kernel_size      := kernel_size,
            in_kernel_gens   := [1..k],
            exp_index        := exp_index,
            half_in_kernel   := exp_local > 2,
            kernel_basis_vecs := kernel_basis_vecs,
            M_stack          := M_stack,
            row_torsion      := row_torsion,
            reduced_matrices := reduced_matrices);
    fi;
    # The propagated rows are mod-2 valued (since the GF(2) fast path
    # produces only order-2 quotient coordinates; row_torsion is all
    # 2s). So the kernel constraint M_stack . vec ≡ 0 mod 2 reduces
    # to F_2-nullspace computation. We've already computed the
    # column-wise zero pattern in `col_has_constraint`.
    #
    # NB: only the order-2 columns of vec are constrained by M_stack.
    # The order-exp generator's column in M_stack is zero (it's a
    # fail-column handled by fallback below).
    Print("Reading kernel from col_has_constraint bitvector...\n");
    snf := fail; snf_d := fail;  # not used in this branch
    kernel_torsion := [];        # not used
    kernel_rows := [];           # not used
    x_part := [];                # not used
    reduced_rows := [];          # not used
    normal_diag := [];           # not used
    big := [];                   # not used

    # ----- Cross-check style outputs (compatible with run_e_plus_m_kernel_hap.g) ---
    # Identify which unit generators e_i are in the kernel: e_i in ker iff
    # no propagated row has a nonzero entry in column i, i.e.
    # col_has_constraint[i] is false. For order-2 generators, this is
    # the exact condition. For fail-axis generators (and any generator
    # with h3_torsion[i] > 2), we fall back to a direct test below.
    in_kernel_gens := [];
    for i in [1..k] do
        if i in all_fail_columns then
            continue;   # decided by fallback path below
        fi;
        if h3_torsion[i] = 2 and not col_has_constraint[i] then
            Add(in_kernel_gens, i);
        fi;
    od;

    # ----- Fallback: per fail-column axis, test multiples k*e_fc directly. -----
    # For each fail column fc, we test for k = 1..h3_torsion[fc]-1 whether
    # k*e_fc is in ker(Tr) via the existing IsCoboundary2Split path per
    # orbit member. We find the smallest k_min > 0 in ker, then the
    # contribution to the kernel along axis fc is <k_min * e_fc> of order
    # h3_torsion[fc] / k_min.
    Print("\n--- Fallback per-axis test for fail columns: ", all_fail_columns,
          " ---\n");
    basis_orders := [];   # collected from in_kernel_gens (order 2 each)
    for i in in_kernel_gens do
        Add(basis_orders, 2);
    od;

    for fc in all_fail_columns do
        Print("  axis e_", fc, " (h3_torsion = ", h3_torsion[fc], "): ");
        # Sweep k in 1..h3_torsion[fc]-1, find smallest k_min with k_min*e_fc in ker.
        exp_axis_k := h3_torsion[fc];   # default: no k in ker, so axis kernel = 0
        for exp_axis_vec in [1..h3_torsion[fc] - 1] do
            # Test if `exp_axis_vec * e_fc` is in ker(Tr).
            exp_axis_in_ker_k := true;
            for j in [1..n_orbits] do
                orb_info := reduced_matrices[j].orb_info;
                cache_orbit := reduced_matrices[j].cache;
                if cache_orbit = fail then continue; fi;   # identity class
                # Issue #371: reuse cache_orbit.C captured at
                # BuildReducedTransgressionMatrix time. Saves a few
                # seconds of Centralizer(G, rep) over the sweep.
                C := cache_orbit.C;
                for fallback_target_idx in orb_info.orbit do
                    M_y_j_exp := H3MatrixForOrbitMember(
                        orb_info.start_idx, fallback_target_idx,
                        orb_info.parent, orb_info.gen_used,
                        h3_matrices, h3_torsion);
                    # Issue #371 + #387 audit-tier3 rank 1: unit_e_i =
                    # exp_axis_vec * e_fc has exactly one non-zero entry
                    # at index fc, so vec_target_exp[jj] is just
                    # M_y_j_exp[jj][fc] * exp_axis_vec mod h3_torsion[jj].
                    # Original `List([1..k], jj -> ...)` was k=165
                    # closures per iteration multiplied by axis_vec ×
                    # orbit × target depth. Pre-transpose once per
                    # target so column-fc becomes O(1) and the rest is
                    # compiled list-scalar mul + list-mod-list (#387).
                    M_y_j_exp_T := TransposedMat(M_y_j_exp);
                    vec_target_exp := (M_y_j_exp_T[fc] * exp_axis_vec)
                                          mod h3_torsion;
                    # Issue #370: cache_orbit.table is in IsMatrixRep
                    # after ConvertToMatrixRep at load time, so the `*`
                    # dispatches to compiled PROD_MAT_VEC_INT
                    # (~100-1000x faster than the interpreted
                    # `List(table, row -> Sum(jj, vec[jj]*row[jj]))`).
                    # Result is bit-identical at the integer level.
                    c_g_table_exp := cache_orbit.table * vec_target_exp;
                    if not IsCoboundary2SplitVec(C, c_g_table_exp,
                                                  vec_target_exp, setup) then
                        exp_axis_in_ker_k := false;
                        break;
                    fi;
                od;
                if not exp_axis_in_ker_k then break; fi;
            od;
            if exp_axis_in_ker_k then
                exp_axis_k := exp_axis_vec;
                break;   # smallest k_min found
            fi;
        od;
        if exp_axis_k = h3_torsion[fc] then
            Print("no k in ker (axis kernel = {0}, contributes 1)\n");
            # Axis contributes nothing to kernel.
        else
            Print("k_min = ", exp_axis_k, ", axis kernel = <",
                  exp_axis_k, "*e_", fc, "> of order ",
                  h3_torsion[fc] / exp_axis_k, "\n");
            Add(basis_orders, h3_torsion[fc] / exp_axis_k);
            # Bookkeeping: if k_min = 1, e_fc itself is in ker.
            if exp_axis_k = 1 then
                Add(in_kernel_gens, fc);
            fi;
        fi;
    od;

    # Sort in_kernel_gens for canonical output.
    Sort(in_kernel_gens);

    # Half-vec check for exp_index: per the existing driver convention,
    # we report "half_in_kernel" as whether 2*e_{exp_index} is in ker.
    # If exp_index is itself in in_kernel_gens, then trivially 2*e_{exp_index}
    # is too (it's a multiple). Otherwise, look up the axis kernel order
    # for exp_index from the fallback above.
    if exp_local = 2 or exp_index = fail then
        half_in_ker := fail;
    elif exp_index in in_kernel_gens then
        half_in_ker := true;
    elif exp_index in all_fail_columns then
        # exp_index was a fail column; its axis kernel was just computed.
        # 2*e_{exp_index} in ker iff axis kernel contains 2, i.e. iff
        # k_min divides 2.
        # Re-derive k_min for exp_index from basis_orders / position.
        # Simpler: directly test 2*e_{exp_index} via the same fallback.
        half_in_ker := true;
        for j in [1..n_orbits] do
            orb_info := reduced_matrices[j].orb_info;
            cache_orbit := reduced_matrices[j].cache;
            if cache_orbit = fail then continue; fi;
            # Issue #371: reuse captured cache_orbit.C (see axis_vec site).
            C := cache_orbit.C;
            for fallback_target_idx in orb_info.orbit do
                M_y_j_exp := H3MatrixForOrbitMember(
                    orb_info.start_idx, fallback_target_idx,
                    orb_info.parent, orb_info.gen_used,
                    h3_matrices, h3_torsion);
                # Issue #371 + #387 audit-tier3 rank 1 (half-vec branch):
                # same pre-transpose vectorisation as the main fail-column
                # path above. exp_axis_vec = 2 for the half-vec test.
                M_y_j_exp_T := TransposedMat(M_y_j_exp);
                vec_target_exp := (M_y_j_exp_T[exp_index] * 2) mod h3_torsion;
                # Issue #370: compiled PROD_MAT_VEC_INT (see note above
                # at the axis_vec site).
                c_g_table_exp := cache_orbit.table * vec_target_exp;
                if not IsCoboundary2SplitVec(C, c_g_table_exp,
                                              vec_target_exp, setup) then
                    half_in_ker := false;
                    break;
                fi;
            od;
            if not half_in_ker then break; fi;
        od;
    else
        # exp_index was a safe column; test via M_stack directly.
        # MEMORY FIX (#302): with the streaming Step 2 we no longer have
        # M_stack materialised. However, every propagated row is mod 2,
        # and half_vec is `2 * e_exp_index`. So
        #   Sum_i M_stack[l][i] * half_vec[i] = 2 * M_stack[l][exp_index]
        # and `(2 * x) mod 2 = 0` for any integer x. Hence the half-vec
        # check is trivially true on every row whenever row_torsion[l] = 2
        # (which is always the case in the F_2 path). Skip the loop.
        half_vec := List([1..k], j -> If_(j = exp_index, 2, 0));
        half_in_ker := true;
    fi;

    # Build kernel_basis_vecs in the run_e_plus_m_kernel_hap.g shape.
    kernel_basis_vecs := [];
    for i in in_kernel_gens do
        Add(kernel_basis_vecs, rec(
            generator_index := i,
            kind := Concatenation("e_", String(i)),
            order := h3_torsion[i],
            vec := List([1..k], j -> If_(j = i, 1, 0))));
    od;
    if exp_local > 2 and exp_index <> fail
       and (not (exp_index in in_kernel_gens))
       and half_in_ker = true then
        Add(kernel_basis_vecs, rec(
            generator_index := exp_index,
            kind := Concatenation("2 * e_", String(exp_index)),
            order := h3_torsion[exp_index] / GcdInt(h3_torsion[exp_index], 2),
            vec := List([1..k], j -> If_(j = exp_index, 2, 0))));
    fi;

    # The FINAL kernel size is the product of basis_orders. (Each entry
    # in basis_orders is the order of a unit-axis or sub-axis generator
    # in the kernel; their product = |ker(Tr)| under the Cartesian-
    # product assumption verified above.)
    kernel_size := Product(basis_orders);
    Print("\nbasis_orders: ", basis_orders, "\n");
    Print("kernel_size (product of basis_orders): ", kernel_size, "\n");

    return rec(
        kernel_size       := kernel_size,
        kernel_torsion    := kernel_torsion,
        in_kernel_gens    := in_kernel_gens,
        exp_index         := exp_index,
        half_in_kernel    := half_in_ker,
        kernel_basis_vecs := kernel_basis_vecs,
        basis_orders      := basis_orders,
        all_fail_columns  := all_fail_columns,
        M_stack           := M_stack,
        row_torsion       := row_torsion,
        snf               := snf,
        snf_d             := snf_d,
        reduced_matrices  := reduced_matrices);
end;;


# ---------------------------------------------------------------------
# Convenience entry point for simple G (not via the BRW driver):
# computes the conjugacy classes, treats each class as a singleton
# "orbit", and runs KernelOfTransgressionViaMBar without BRW propagation.
#
# Useful for smoke tests on small groups (e.g. E_+(2) when the BRW
# infrastructure is awkward to set up, or for parity-check with the
# baseline TransgressionKernel function in transgression_kernel.g).
# ---------------------------------------------------------------------

KernelOfTransgressionSimple := function(G)
    local setup, classes, n_classes, orbits_data, h3_matrices, k, i;
    setup := SetupCohomology3(G);
    classes := ConjugacyClasses(G);
    n_classes := Length(classes);
    k := setup.num_generators;

    # No BRW: each class is its own "orbit" with a trivial Schreier vec.
    orbits_data := List([1..n_classes], i -> rec(
        start_idx := i,
        orbit := [i],
        parent := List([1..n_classes], j -> If_(j = i, 0, -1)),
        gen_used := List([1..n_classes], j -> 0)));

    # h3_matrices = [] is fine because we never traverse Schreier paths
    # (each orbit is a singleton with target = start). H3MatrixForOrbitMember
    # returns the identity in this case.
    h3_matrices := [];

    return KernelOfTransgressionViaMBar(setup, orbits_data, classes, G,
                                         h3_matrices);
end;;
