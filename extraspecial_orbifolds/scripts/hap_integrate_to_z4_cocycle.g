# hap_integrate_to_z4_cocycle.g — integrate a Z/4 2n-cocycle on HAP's
# compact resolution down to a Z/4 (2n-1)-cocycle f with δ_4([f]) = [F]
# under the connecting hom from 0 → Z →·4 Z → Z/4 → 0.
#
# Issue #172 (Q-int B3-3). Builds on:
#   - #170 (B3-1): HAP_BarCoboundary, HAP_SteenrodCup1 on R.
#   - #171 (B3-2): HAP_PontryaginSquare, HAP_PontryaginGetResolution.
#   - #162 (B2-3a): the bar-resolution version `integrate_to_3cocycle.g`
#     — same math, different complex.
#
# # Mathematical setup.
#
# Given a free ZG-resolution R of Z (e.g. ResolutionFiniteGroup(G, 2n+1))
# and a Z/4-valued 2n-cocycle vector F on R (length R!.dimension(2n),
# entries in {0,1,2,3}), build a Z/4-valued (2n-1)-cocycle f on R with
# δ_4([f]) = [F] in H^{2n}(G; Z), where δ_4 is the Bockstein for the SES
# 0 → Z →·4 Z → Z/4 → 0.
#
# # Construction (two-stage linear solve over Z).
#
# Stage A — kill F mod 4. Lift F to integer cochain F_int (values in
# {0,1,2,3} ⊂ Z) on R. By the cocycle property of F over Z/4,
# δ(F_int) ∈ 4·Z componentwise. Solve over Z for a 2n-cochain h with
#   δh = δ(F_int) / 4.
# (Feasibility: the obstruction class [δ(F_int)/4] ∈ H^{2n+1}(G; Z) is
# zero because [F] lifts to H^{2n}(G; Z) — the Bockstein δ_4[F] is by
# definition that lift's class.) Set G_int := F_int - 4·h. Then G_int
# is a Z 2n-cocycle (δ(G_int) = δ(F_int) - 4·δh = 0) with G_int ≡ F mod 4
# at the chain level.
#
# Stage B — integrate. G_int is a Z 2n-cocycle. For 2-groups, H^{2n}(G; Z)
# is finite of 2-power order, so [4·G_int] = 0 in H^{2n}(G; Z) and there
# exists an integer (2n-1)-cochain f̃ with
#   δf̃ = 4·G_int.
# Solve over Z. Define f := f̃ mod 4 — a Z/4 (2n-1)-cocycle on R, since
# δf = δf̃ mod 4 = 4·G_int mod 4 = 0.
#
# # Why δ_4([f]) = [F]:
# By the connecting-hom definition, δ_4([f]) = [δf̃ / 4] = [G_int] in
# H^{2n}(G; Z). Reducing mod 4 gives the original [F] in H^{2n}(G; Z/4).
#
# # Tractability vs. bar resolution.
#
# At D_8 (m=1, |G|=8) on R = ResolutionFiniteGroup(G, 5), R!.dimension
# (d) for d=0..5 is small (∼ single digits), so the linear systems are
# tiny. The bar-resolution version (#162) at the same group already
# handled n=2 with 32^5 × 32^4 entries; the HAP version at 5×8 (Stage B)
# and 8×n (Stage A) is order-of-magnitude smaller.
#
# At m=3 (E_+(3), |G|=128), HAP keeps R!.dimension(d) growing
# polynomially while the bar resolution explodes exponentially — that's
# the whole point of moving to HAP's compact resolution for the
# extraspecial m=3/5/7 anchors (#164–#166).

if not IsBoundGlobal("HAP_BarCoboundary") then
    Read("hap_steenrod_cup1.g");
fi;
if not IsBoundGlobal("HAP_PontryaginSquare") then
    Read("hap_pontryagin_square.g");
fi;

# ------------------------------------------------------------------
# Boundary-matrix cache keyed by (R, p). Same R is used for both
# Stages, so we want to amortise the matrix construction across the
# two solves.
# ------------------------------------------------------------------

_HAP_Bdy_cache := [];;

# ------------------------------------------------------------------
# HAP_BoundaryMatrixZ(R, p)
#
# Integer matrix of shape R!.dimension(p+1) × R!.dimension(p) for the
# coboundary δ on R in degree p, where for a p-cochain α (a list of
# length R!.dimension(p)):
#
#   (δα)[k] = sum over (j, _) in R!.boundary(p+1, k) of SignInt(j) · α[|j|]
#
# (the group-coset index in each boundary entry doesn't enter cochain
# evaluation because cochains are Z-linear functionals on the free
# generators at the identity coset). The matrix element M[k][j] is the
# coefficient of α[j] in (δα)[k] — i.e. the signed count of pairs
# (signed_j, _) in R!.boundary(p+1, k) with AbsInt(signed_j) = j.
#
# So M[k][j] := sum over (s, _) in R!.boundary(p+1, k) of
#   { SignInt(s) if AbsInt(s) = j else 0 }.
#
# The matrix is cached per (R, p) (keyed by IsIdenticalObj of R) to
# avoid rebuilding when both Stages of HAP_IntegrateToZ4Cocycle ask
# for the same boundary matrix.
#
# Convention: with α as a column vector (a length-R!.dimension(p) list),
# δα := M · α  in GAP's standard row-times-column matrix-vector product.
# In GAP, `M * α` does exactly that on lists / matrices. We test this
# equality below against HAP_BarCoboundary, which is the same map by
# construction.
# ------------------------------------------------------------------

HAP_BoundaryMatrixZ := function(R, p)
    local entry, M, dim_p, dim_p1, k, b, e, j_signed, j_abs, sgn;
    for entry in _HAP_Bdy_cache do
        if IsIdenticalObj(entry.R, R) and entry.p = p then
            return entry.M;
        fi;
    od;

    dim_p  := R!.dimension(p);
    dim_p1 := R!.dimension(p + 1);
    M := List([1..dim_p1], _ -> ListWithIdenticalEntries(dim_p, 0));
    for k in [1..dim_p1] do
        b := R!.boundary(p + 1, k);
        for e in b do
            j_signed := e[1];
            j_abs := AbsInt(j_signed);
            sgn := SignInt(j_signed);
            M[k][j_abs] := M[k][j_abs] + sgn;
        od;
    od;

    Add(_HAP_Bdy_cache, rec(R := R, p := p, M := M));
    return M;
end;;

# ------------------------------------------------------------------
# HAP_IntegrateToZ4Cocycle(R, F_z4_vec, n)
#
# Inputs:
#   - R          : HAP free ZG-resolution (must have R!.dimension(d)
#                  defined for d ∈ [2n-1, 2n, 2n+1]). Typically
#                  R = HAP_PontryaginGetResolution(G, 2n + 1).
#   - F_z4_vec   : list of length R!.dimension(2n) with entries in
#                  {0, 1, 2, 3}, representing a Z/4-valued 2n-cocycle.
#   - n          : positive integer.
#
# Output: rec(
#   f       := <Z/4 (2n-1)-cocycle on R, length R!.dimension(2n-1)>,
#   h       := <integer 2n-cochain from Stage A>,
#   G_int   := <integer 2n-cocycle from Stage A>,
#   f_int   := <integer (2n-1)-cochain from Stage B (= f_tilde)>,
#   F_int   := <integer 2n-cochain lift of F (Stage A input)>,
# ).
#
# Error if either Stage's linear solve fails (e.g. obstruction class
# is non-zero — flagged as a math inconsistency or a bug in the input).
# ------------------------------------------------------------------

HAP_IntegrateToZ4Cocycle := function(R, F_z4_vec, n)
    local dim_2nm1, dim_2n, dim_2np1, F_int, M_2n, M_2nm1,
          dF_int, dF_div4, h, G_int, target_B, f_tilde, f_mod4,
          x_solA, x_solB;

    if not (IsInt(n) and n >= 1) then
        Error("HAP_IntegrateToZ4Cocycle: n must be a positive ",
              "integer, got ", n);
    fi;

    dim_2nm1 := R!.dimension(2 * n - 1);
    dim_2n   := R!.dimension(2 * n);
    dim_2np1 := R!.dimension(2 * n + 1);

    if Length(F_z4_vec) <> dim_2n then
        Error("HAP_IntegrateToZ4Cocycle: F_z4_vec has length ",
              Length(F_z4_vec), " but R!.dimension(", 2 * n, ") = ",
              dim_2n);
    fi;

    Print("  HAP_IntegrateToZ4Cocycle: dim(", 2*n - 1, ") = ", dim_2nm1,
          ", dim(", 2*n, ") = ", dim_2n,
          ", dim(", 2*n + 1, ") = ", dim_2np1, "\n");

    # Lift F to Z with values in {0,1,2,3}.
    if not ForAll(F_z4_vec, x -> x in [0, 1, 2, 3]) then
        Error("HAP_IntegrateToZ4Cocycle: F_z4_vec must have entries ",
              "in {0, 1, 2, 3} (Z-lift representatives of Z/4).");
    fi;
    F_int := List(F_z4_vec, x -> x);  # canonical Z-lift

    # Build boundary matrices for both Stages (cached per R, p).
    Print("  - Building HAP boundary matrix M_2n (",
          dim_2np1, " x ", dim_2n, ")\n");
    M_2n := HAP_BoundaryMatrixZ(R, 2 * n);
    Print("  - Building HAP boundary matrix M_2nm1 (",
          dim_2n, " x ", dim_2nm1, ")\n");
    M_2nm1 := HAP_BoundaryMatrixZ(R, 2 * n - 1);

    # ---- Stage A: solve δh = δ(F_int) / 4 ---------------------------
    # δF_int = M_2n · F_int (column-vector convention; in GAP just M * v).
    dF_int := M_2n * F_int;  # length dim_2np1 integer vector
    if not ForAll(dF_int, x -> x mod 4 = 0) then
        Error("HAP_IntegrateToZ4Cocycle: δ(F_int) is not in 4Z. ",
              "This contradicts F being a Z/4 cocycle on R. ",
              "(violations: ",
              Length(Filtered(dF_int, x -> x mod 4 <> 0)),
              " / ", Length(dF_int), ")");
    fi;
    dF_div4 := List(dF_int, x -> x / 4);

    Print("  - Stage A solve: M_2n · h = δ(F_int)/4  (",
          dim_2np1, " eqs in ", dim_2n, " unknowns)\n");
    # We want h with M_2n · h = dF_div4. In GAP row-vector form:
    # h * TransposedMat(M_2n) = dF_div4. Pass T(M_2n) to SolutionIntMat.
    x_solA := SolutionIntMat(TransposedMat(M_2n), dF_div4);
    if x_solA = fail then
        Error("HAP_IntegrateToZ4Cocycle: Stage A has no integer ",
              "solution. The obstruction class [δ(F_int)/4] in ",
              "H^{2n+1}(G; Z) is non-zero — F does not come from a ",
              "Z-lift, or there's a bug.");
    fi;
    h := x_solA;
    Print("  - Stage A solved: |h| = ", Length(h),
          ", max|h_i| = ", Maximum(List(h, AbsInt)), "\n");

    # G_int := F_int - 4·h. Verify it's a Z 2n-cocycle.
    G_int := List([1..Length(F_int)], i -> F_int[i] - 4 * h[i]);
    if not ForAll(M_2n * G_int, x -> x = 0) then
        Error("HAP_IntegrateToZ4Cocycle: G_int = F_int - 4h is not ",
              "a Z 2n-cocycle (bug in Stage A solve).");
    fi;
    Print("  - G_int constructed, δ(G_int) = 0 over Z\n");

    # ---- Stage B: solve δf̃ = 4·G_int -------------------------------
    target_B := List(G_int, x -> 4 * x);
    Print("  - Stage B solve: M_2nm1 · f̃ = 4·G_int  (",
          dim_2n, " eqs in ", dim_2nm1, " unknowns)\n");
    x_solB := SolutionIntMat(TransposedMat(M_2nm1), target_B);
    if x_solB = fail then
        Error("HAP_IntegrateToZ4Cocycle: Stage B has no integer ",
              "solution. [4·G_int] is non-zero in H^{2n}(G; Z), but ",
              "for a 2-group it should be 0 since H^{2n}(G; Z) is ",
              "2-power torsion.");
    fi;
    f_tilde := x_solB;
    Print("  - Stage B solved: |f_tilde| = ", Length(f_tilde),
          ", max|f_i| = ", Maximum(List(f_tilde, AbsInt)), "\n");

    # Sanity: δf̃ = 4·G_int over Z.
    if M_2nm1 * f_tilde <> target_B then
        Error("HAP_IntegrateToZ4Cocycle: Stage B solution does not ",
              "satisfy δf̃ = 4·G_int (bug in SolutionIntMat result).");
    fi;

    # f := f̃ mod 4 (Z/4 (2n-1)-cocycle on R).
    f_mod4 := List(f_tilde, x -> x mod 4);

    return rec(
        f       := f_mod4,
        h       := h,
        G_int   := G_int,
        f_int   := f_tilde,
        F_int   := F_int
    );
end;;

Print("Loaded hap_integrate_to_z4_cocycle.g ",
      "(HAP_IntegrateToZ4Cocycle, HAP_BoundaryMatrixZ).\n");
