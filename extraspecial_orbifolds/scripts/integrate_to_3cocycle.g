# integrate_to_3cocycle.g — Z/4 3-cocycle for the Z/4 generator of
# H^4(G; Z), via linear-solve integration of the Pontryagin square
# 4-cocycle P(Q).
#
# Issue #162 (Q-int B2-3a). Builds on #160 (Steenrod ∪₁) and #161
# (Pontryagin square). Spec:
# docs/superpowers/specs/2026-05-15-path3-pontryagin-square-design.md
#
# # Mathematical setup.
#
# Given:
#   - A finite group G.
#   - α: G^2 → F_2 an F_2 2-cocycle (e.g., the Quillen quadratic form
#     Q for E_+(m)).
#   - P(α): G^4 → Z/4 the Pontryagin square 4-cocycle (from #161).
#
# We want a Z/4 3-cocycle f: G^3 → Z/4 such that the connecting hom
#   δ_4 : H^3(G; Z/4) → H^4(G; Z)
# (from the SES 0 → Z →·4 Z → Z/4 → 0) sends [f] to the order-4
# generator of H^4(G; Z) (the cyclic A(4) summand at m ≥ 3 per
# Harada-Kono 1987 Thm 1.1; the Z/8 generator at m=2; etc.).
#
# # Construction (two-stage linear solve).
#
# Stage A: build an integer 4-cocycle G with G mod 4 ≡ P(Q) in
# H^4(G; Z/4). Let P(Q)_int be the integer lift of P(Q) (values in
# {0, 1, 2, 3}). Compute δ(P(Q)_int) — this lives in 4Z by the
# Brumfiel-Morgan cocycle proof in #161. Solve over Z for an integer
# 4-cochain h with
#   δh = δ(P(Q)_int) / 4
# (which is itself a Z 5-cocycle since δ²(...) = 0; the existence of
# h follows from the obstruction class being zero, which is true iff
# [P(Q)] is in the image of H^4(Z) → H^4(Z/4), guaranteed for our
# Harada-Kono setting). Then G := P(Q)_int - 4·h is a Z 4-cocycle
# with G ≡ P(Q) mod 4 (as cochains, hence as Z/4 classes).
#
# Stage B: build the 3-cochain f̃ with δf̃ = 4·G. Since [G] has
# order 4 in H^4(G; Z), [4·G] = 0, so 4·G is a Z-coboundary and f̃
# exists. Solve over Z. Set f := f̃ mod 4.
#
# # Why δ_4([f]) equals the Z/4 generator:
#   δ_4([f]) = [δf̃ / 4] = [4·G / 4] = [G] ∈ H^4(G; Z),
# and [G] mod 4 = [P(Q)] in H^4(G; Z/4) by construction. Since the
# Z/4 generator of H^4(Z) is the unique class that maps to [P(Q)]
# under the (injective at 4-torsion) mod-4 reduction, [G] is that
# generator.
#
# # Tractability.
# At m=1 (D_8, |G|=8): stage A is 32768 eqs × 4096 unknowns, stage B
# is 4096 × 512. Both feasible with GAP's SolutionIntMat in minutes.
# At m=3 (E_+(3), |G|=128): stage B is 2.7×10^8 × 2×10^6 — feasible
# with careful sparse-aware solver. m=5 onwards needs a smarter
# algorithm than naive Gaussian elimination (open algorithmic
# question — flagged in #137 / #166).

if not IsBoundGlobal("PontryaginSquare") then
    Read("pontryagin_square.g");
fi;

# ------------------------------------------------------------------
# Tuple indexing: bijection G^p ↔ [1..|G|^p] with a fixed element
# ordering AsList(G).
# ------------------------------------------------------------------

# Build the index/inverse pair for p-tuples of G.
_I3C_TupleIndexer := function(G, p)
    local elts, n, pos_of, idx, of_idx;
    elts := AsList(G);
    n := Length(elts);
    pos_of := function(g) return Position(elts, g); end;
    # p-tuple (g_1, ..., g_p) ↔ ((pos(g_1)-1)*n + pos(g_2)-1)*n + ... + 1
    idx := function(tuple)
        local r, i;
        r := 0;
        for i in [1..p] do r := r * n + pos_of(tuple[i]) - 1; od;
        return r + 1;
    end;
    of_idx := function(k)
        local r, i, result;
        result := [];
        r := k - 1;
        for i in [p, p-1..1] do
            result[i] := elts[(r mod n) + 1];
            r := QuoInt(r, n);
        od;
        return result;
    end;
    return rec(elts := elts, n := n, p := p,
               idx := idx, of_idx := of_idx,
               size := n ^ p);
end;;

# ------------------------------------------------------------------
# Bar coboundary matrix (over Z).
# Rows indexed by (p+1)-tuples; columns by p-tuples.
# (δ_p f)(g_1, ..., g_{p+1}) =
#   f(g_2, ..., g_{p+1})
#   + sum_{i=1}^p (-1)^i f(g_1, ..., g_i*g_{i+1}, ..., g_{p+1})
#   + (-1)^{p+1} f(g_1, ..., g_p).
# ------------------------------------------------------------------

BarCoboundaryMatrixZ := function(G, p)
    local idxp, idxp1, n_p, n_p1, M, row, args, sub_args, i, sign;
    idxp  := _I3C_TupleIndexer(G, p);
    idxp1 := _I3C_TupleIndexer(G, p + 1);
    n_p  := idxp.size;
    n_p1 := idxp1.size;

    # Plain dense integer matrix. Each row has p+2 non-zero entries.
    M := List([1..n_p1], _ -> ListWithIdenticalEntries(n_p, 0));
    for row in [1..n_p1] do
        args := idxp1.of_idx(row);
        # +1 at column for (g_2, ..., g_{p+1}).
        sub_args := args{[2..p+1]};
        M[row][idxp.idx(sub_args)] := M[row][idxp.idx(sub_args)] + 1;
        for i in [1..p] do
            if IsEvenInt(i) then sign := 1; else sign := -1; fi;
            sub_args := Concatenation(
                args{[1..i-1]},
                [args[i] * args[i+1]],
                args{[i+2..p+1]});
            M[row][idxp.idx(sub_args)] := M[row][idxp.idx(sub_args)] + sign;
        od;
        if IsEvenInt(p + 1) then sign := 1; else sign := -1; fi;
        sub_args := args{[1..p]};
        M[row][idxp.idx(sub_args)] := M[row][idxp.idx(sub_args)] + sign;
    od;
    return M;
end;;

# ------------------------------------------------------------------
# Tabulate a callable cochain over G^p into a length-|G|^p integer
# vector.
# ------------------------------------------------------------------

TabulateCochainZ := function(G, p, cochain)
    local idxp, vec, row;
    idxp := _I3C_TupleIndexer(G, p);
    vec := ListWithIdenticalEntries(idxp.size, 0);
    for row in [1..idxp.size] do
        vec[row] := CallFuncList(cochain, idxp.of_idx(row));
    od;
    return vec;
end;;

# ------------------------------------------------------------------
# Convert a length-|G|^p vector back into a callable cochain.
# ------------------------------------------------------------------

CallableFromVector := function(G, p, vec)
    local idxp;
    idxp := _I3C_TupleIndexer(G, p);
    return function(arg)
        local args;
        args := arg;
        if Length(args) <> p then
            Error("CallableFromVector: expected ", p,
                  " args, got ", Length(args));
        fi;
        return vec[idxp.idx(args)];
    end;
end;;

# ------------------------------------------------------------------
# Two-stage linear solve. Returns rec(f := callable G^3 -> Z/4,
#                                       G_int := integer 4-cocycle,
#                                       h := stage-A correction,
#                                       f_tilde := integer 3-cochain).
# ------------------------------------------------------------------

IntegrateToZ4ThreeCocycle := function(G, P_callable)
    local n, BC_3, BC_4, P_int, dP_int, target_A, h, G_int,
          target_B, f_tilde, f_mod4, x_solA, x_solB, dP_div4;
    n := Order(G);
    Print("  IntegrateToZ4ThreeCocycle: |G| = ", n,
          ", |G^3| = ", n^3, ", |G^4| = ", n^4,
          ", |G^5| = ", n^5, "\n");

    # ---- Tabulate P(Q) as an integer vector over G^4 -----------------
    Print("  - Tabulating P(Q) on G^4 (", n^4, " entries)\n");
    P_int := TabulateCochainZ(G, 4, P_callable);

    # ---- Build bar coboundary matrices -------------------------------
    Print("  - Building bar coboundary matrix BCM_3 (",
          n^4, " x ", n^3, ")\n");
    BC_3 := BarCoboundaryMatrixZ(G, 3);
    Print("  - Building bar coboundary matrix BCM_4 (",
          n^5, " x ", n^4, ")\n");
    BC_4 := BarCoboundaryMatrixZ(G, 4);

    # ---- Stage A: solve δh = δ(P(Q)_int) / 4 ------------------------
    # δ(P(Q)_int) = BCM_4 · P(Q)_int (column-vector convention).
    # In GAP row-vector convention: dP_int = P_int * TransposedMat(BCM_4).
    Print("  - Computing δ(P(Q)_int) = BCM_4 · P_int\n");
    dP_int := BC_4 * P_int;     # length n^5 integer vector
    # Verify δ(P(Q)_int) ∈ 4Z componentwise.
    if not ForAll(dP_int, x -> x mod 4 = 0) then
        Error("IntegrateToZ4ThreeCocycle: δ(P_int) is not in 4Z. ",
              "This contradicts Brumfiel-Morgan's cocycle property of ",
              "P(α). Bug or input not actually P(α).");
    fi;
    dP_div4 := List(dP_int, x -> x / 4);

    Print("  - Stage A solve: BCM_4 · h = δ(P_int)/4  (n^5 = ", n^5,
          " eqs in n^4 = ", n^4, " unknowns)\n");
    # We need h with BC_4 · h = dP_div4. In row-vector convention:
    # h * TransposedMat(BC_4) = dP_div4. So SolutionIntMat needs
    # TransposedMat(BC_4) as the matrix and dP_div4 as the target.
    x_solA := SolutionIntMat(TransposedMat(BC_4), dP_div4);
    if x_solA = fail then
        Error("IntegrateToZ4ThreeCocycle: stage A has no integer ",
              "solution. The Bockstein obstruction class ",
              "[δ(P_int)/4] ∈ H^5(G; Z) is non-zero. This contradicts ",
              "the Harada-Kono lifting argument.");
    fi;
    h := x_solA;
    Print("  - Stage A solved: |h| = ", Length(h),
          ", max|h_i| = ", Maximum(List(h, AbsInt)), "\n");

    # Build G_int = P_int - 4·h. Verify it's a Z 4-cocycle.
    G_int := List([1..Length(P_int)], i -> P_int[i] - 4 * h[i]);
    if not ForAll(BC_4 * G_int, x -> x = 0) then
        Error("IntegrateToZ4ThreeCocycle: G_int is not a Z 4-cocycle.");
    fi;
    Print("  - G_int constructed, δ(G_int) = 0 over Z\n");

    # ---- Stage B: solve δf̃ = 4·G_int -------------------------------
    target_B := List(G_int, x -> 4 * x);
    Print("  - Stage B solve: BCM_3 · f̃ = 4·G_int  (n^4 = ", n^4,
          " eqs in n^3 = ", n^3, " unknowns)\n");
    x_solB := SolutionIntMat(TransposedMat(BC_3), target_B);
    if x_solB = fail then
        Error("IntegrateToZ4ThreeCocycle: stage B has no integer ",
              "solution. [4·G_int] != 0 in H^4(G; Z), but should be ",
              "(since [G_int] has order ≤ 4).");
    fi;
    f_tilde := x_solB;
    Print("  - Stage B solved: |f_tilde| = ", Length(f_tilde),
          ", max|f_i| = ", Maximum(List(f_tilde, AbsInt)), "\n");

    # Verify δf̃ = 4·G_int.
    if BC_3 * f_tilde <> target_B then
        Error("IntegrateToZ4ThreeCocycle: stage B solution doesn't ",
              "satisfy δf̃ = 4·G_int.");
    fi;

    # ---- Return rec --------------------------------------------------
    f_mod4 := List(f_tilde, x -> x mod 4);
    return rec(
        f         := CallableFromVector(G, 3, f_mod4),
        f_tilde   := f_tilde,
        f_mod4    := f_mod4,
        G_int     := G_int,
        h         := h,
        P_int     := P_int
    );
end;;

Print("Loaded integrate_to_3cocycle.g ",
      "(IntegrateToZ4ThreeCocycle, BarCoboundaryMatrixZ, helpers).\n");
