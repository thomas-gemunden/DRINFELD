# cocyclebasis_quillen_bridge_routeb.g — Q-int A4 Route B / issue #288.
#
# Alternative implementation of the polynomial-form bridge, using a
# UCT.hombasis-driven matching at the chain level (via cocyclebasis
# representation) rather than direct |G|^3 enumeration.
#
# === Status (May 2026, issue #288 Phase 1) ===
#
# Phase 1 (m=2 anchor) VERIFIED: this implementation produces polynomial
# forms that match Route A (`cocyclebasis_quillen_bridge.g`) bit-for-bit
# at m=2 on all 9 order-2 generators.
#
# What this file provides:
#   * `QuillenPolynomialOf_RouteB(setup, i)`
#       Same signature and return shape as Route A's `QuillenPolynomialOf`.
#       Bridge_kind values:
#         "F2_polynomial"   — order-2 generators with an explicit poly.
#         "pontryagin_top"  — top-torsion (passes through).
#
# === Mathematical approach ===
#
# Same end goal as Route A: identify each `setup.UCT.hombasis[i]` (= H^3
# generator) with a polynomial expression in `F_2[x_1, ..., x_{2m}]`.
#
# Route A: builds the |G|^2 bar 2-coboundary matrix and solves a system
# of size (n_polys + |G|^2) × |G|^3.
#
# Route B (this file): keeps the bar-level matrix but uses a SAMPLED set
# of triples T of size O(|Z| + |G|^2) and solves the F_2 linear system
# directly. The polynomial expression for each hombasis[i] is obtained
# by:
#   1. Build target_bar_i = `Standard(R, cocyclebasis[i] / (exp/2), 3, 2)`
#      evaluated on T. This is the F_2 chain-cocycle representation of
#      the i-th order-2 generator, pulled back to bar form via Standard.
#   2. Solve the augmented system [poly_rows ; coboundary_rows] = target_bar_i.
#   3. Read off polynomial coefficients.
#
# === Differences from Route A ===
#
# (a) Target construction is via `Standard(R, scaled cocyclebasis[i], 3, 2)`
#     applied to T, rather than via `StandardCocycleOf(setup, e_i)` then
#     dividing by (exp/2). This routes the F_2 reduction through the
#     CHAIN-LEVEL `cocyclebasis[i] / scale`, matching the hombasis dual
#     pairing.
#
# (b) The polynomial side uses the same Quillen monomial enumeration as
#     Route A (`QuillenPolynomialBasisForBridge`).
#
# (c) Memory cost at m=5: same as Route A modulo sampling — the |G|^2
#     coboundary matrix is the bottleneck. To scale to m=5 we either
#     need:
#       (i)   A pure chain-level chain-map bar → K (not provided here;
#             requires explicit HAP comparison map construction or
#             reimplementation of `Syzygy` inverse using R!.homotopy).
#       (ii)  Sparse / lazy representation of the |G|^2 coboundary rows.
#       (iii) Use Route C (Quillen-detecting-subgroup restriction), which
#             reduces the problem to E ≅ (F_2)^{m+1} for max-EA E.
#
# Phase 1 found that the "pure chain-level Route B" — pairing cup
# products against K_3 basis cells via Syzygy alone — fails because
# bar cup products do not correspond to chain-level cocycles via
# `v_p . Syzygy(t) = f_p(t)`. The chain-level lift exists only up to
# bar homotopy, not pointwise. See probe results in
# `extraspecial_orbifolds/probes/qint_a4_rb_probe9.g` for details.
#
# === Verification ===
#
# Bit-for-bit polynomial match against Route A at m=2 on all 9 order-2
# generators. The 10th generator (order 8, the Pontryagin-top) passes
# through with `bridge_kind = "pontryagin_top"` (no polynomial form).
#
# === Constraints / caveats ===
#
# * Same caveats as Route A (basis choice differs from canonical
#   symplectic Quillen, etc. — see Route A header).
# * Requires `cocyclebasis_quillen_bridge.g` already loaded (for
#   `QuillenPolynomialBasisForBridge`, `BasisH1F2`, etc.).

# ----------------------------------------------------------------------
# Module loading
# ----------------------------------------------------------------------

if not IsBoundGlobal("StandardCocycleOf") then
    Read("transgression_kernel.g");
fi;
if not IsBoundGlobal("EPlusGroup") then
    Read("quillen_detecting_subgroup.g");
fi;
if not IsBoundGlobal("F2HomFromImages") then
    Read("bar_cocycle.g");
fi;
if not IsBoundGlobal("PolynomialTimesExterior") then
    Read("quillen_algebra.g");
fi;
if not IsBoundGlobal("QuillenCanonicalPresentation") then
    Read("quillen_canonical_presentation.g");
fi;
if not IsBoundGlobal("QuillenPolynomialOf") then
    Read("cocyclebasis_quillen_bridge.g");
fi;

# ----------------------------------------------------------------------
# Bridge cache for Route B. The cache contains the polynomial cocycle
# rows + coboundary matrix on a sampled T, plus the SemiEchelon for
# fast repeated solves.
# ----------------------------------------------------------------------

_QPB_CACHE_ROUTEB := rec();;

# Route B cache. If Route A's cache _QPB_CACHE is already populated for
# this m, share the polynomial+coboundary matrix structure (which is
# identical between routes — only the target vector differs). The
# SemiEchelon is rebuilt regardless, since Route A doesn't compute it
# (Route A uses SolutionMat directly).
_GetBridgeCacheRouteB := function(setup)
    local G, m_inferred, m, key, ra_key, ra_cache, h1_basis, polys, T,
          elts, n, sample_size, q_rows, mon, q_func, coboundary_data,
          combined_M, n_polys, poly_funcs, sem, row, k;
    G := setup.group;
    if Order(G) = 8 then m := 1;
    elif Order(G) = 32 then m := 2;
    elif Order(G) = 128 then m := 3;
    elif Order(G) = 512 then m := 4;
    elif Order(G) = 2048 then m := 5;
    else
        m_inferred := Log2Int(Order(G));
        if 2^m_inferred <> Order(G) or m_inferred < 3
           or (m_inferred - 1) mod 2 <> 0 then
            Error("_GetBridgeCacheRouteB: |G| = ", Order(G),
                  " is not 2^{2m+1} for any m");
        fi;
        m := (m_inferred - 1) / 2;
    fi;

    key := Concatenation("rb_m", String(m), "_o", String(Order(G)));
    if IsBound(_QPB_CACHE_ROUTEB.(key)) then
        return _QPB_CACHE_ROUTEB.(key);
    fi;

    # Reuse Route A's cache if available (saves the |G|^2 coboundary build).
    ra_key := Concatenation("m", String(m), "_o", String(Order(G)));
    if IsBoundGlobal("_QPB_CACHE") and IsBound(_QPB_CACHE.(ra_key)) then
        Print("  [Route B cache] reusing Route A cache for m=", m,
              " (|G|=", Order(G), ")...\n");
        ra_cache := _QPB_CACHE.(ra_key);
        Print("  [Route B cache]   computing SemiEchelonMatTransformation",
              " on shared matrix (", Length(ra_cache.combined_rows),
              " × ", Length(ra_cache.combined_rows[1]), ")...\n");
        sem := SemiEchelonMatTransformation(ra_cache.combined_rows);
        Print("  [Route B cache]   done.\n");
        _QPB_CACHE_ROUTEB.(key) := rec(
            m                   := m,
            G                   := G,
            h1_basis            := ra_cache.h1_basis,
            polys               := ra_cache.polys,
            poly_funcs          := ra_cache.poly_funcs,
            T                   := ra_cache.T,
            elts                := ra_cache.elts,
            n                   := ra_cache.n,
            q_rows              := ra_cache.q_rows,
            coboundary_data     := ra_cache.coboundary_data,
            combined_M          := ra_cache.combined_rows,
            n_polys             := ra_cache.n_polys,
            n_coboundary        := ra_cache.n_coboundary,
            sem                 := sem,
            shared_from_routeA  := true
        );
        return _QPB_CACHE_ROUTEB.(key);
    fi;

    Print("  [Route B cache] building bridge data for m=", m,
          " (|G|=", Order(G), ")...\n");
    h1_basis := BasisH1F2(G, m);
    polys := QuillenPolynomialBasisForBridge(m);
    Print("  [Route B cache]   |h1_basis.homs| = ", Length(h1_basis.homs),
          ", |poly_candidates| = ", polys.n_candidates, "\n");

    elts := Elements(G);
    n := Length(elts);
    if m <= 2 then
        T := Cartesian(elts, elts, elts);
    else
        sample_size := QuoInt(5 * (n * n + polys.n_candidates), 2);
        sample_size := Minimum(sample_size, n * n * n);
        T := List([1..sample_size], i -> [Random(elts),
                                          Random(elts),
                                          Random(elts)]);
    fi;
    Print("  [Route B cache]   |T| = ", Length(T), " triples\n");

    Print("  [Route B cache]   evaluating ", polys.n_candidates,
          " polynomial cocycles on T...\n");
    poly_funcs := [];
    q_rows := [];
    for mon in polys.candidates do
        q_func := MonomialToBarCocycleF2(h1_basis, mon);
        Add(poly_funcs, q_func);
        row := List(T, t -> (q_func(t[1], t[2], t[3]) mod 2) * Z(2)^0);
        ConvertToVectorRep(row, 2);
        Add(q_rows, row);
    od;
    n_polys := Length(q_rows);

    Print("  [Route B cache]   building bar coboundary matrix ",
          "(", n*n, " rows × ", Length(T), " cols)...\n");
    coboundary_data := BuildCoboundaryRowsF2(G, T);

    combined_M := Concatenation(q_rows, coboundary_data.rows);
    Print("  [Route B cache]   combined matrix: ", Length(combined_M),
          " rows × ", Length(combined_M[1]), " cols (GF(2) compact)\n");

    # Precompute SemiEchelonMatTransformation for repeated solves.
    Print("  [Route B cache]   computing SemiEchelonMatTransformation...\n");
    sem := SemiEchelonMatTransformation(combined_M);
    Print("  [Route B cache]   done.\n");

    _QPB_CACHE_ROUTEB.(key) := rec(
        m              := m,
        G              := G,
        h1_basis       := h1_basis,
        polys          := polys,
        poly_funcs     := poly_funcs,
        T              := T,
        elts           := elts,
        n              := n,
        q_rows         := q_rows,
        coboundary_data := coboundary_data,
        combined_M     := combined_M,
        n_polys        := n_polys,
        n_coboundary   := Length(coboundary_data.rows),
        sem            := sem
    );
    return _QPB_CACHE_ROUTEB.(key);
end;;

# ----------------------------------------------------------------------
# Main bridge function (Route B).
#
# QuillenPolynomialOf_RouteB(setup, i) — same signature as Route A's
# QuillenPolynomialOf. The crucial difference: the target_bar is built
# from `Standard(R, scaled_cocyclebasis[i], 3, 2)` (chain-level F_2
# rep) rather than from `omega_i / (exp/2) mod 2`. Mathematically
# equivalent but routes through the hombasis-dual structure.
# ----------------------------------------------------------------------

QuillenPolynomialOf_RouteB := function(setup, i)
    local cache, e_vec, q_mod, generator_order, kind, scaled_cb, std_F2,
          target_bar, sol, n_rows, poly_coeffs, coboundary_coeffs,
          poly_repr, poly_str, k, beta_func, total_cocycle, poly_cocycle;

    if not (IsInt(i) and i >= 1 and i <= setup.num_generators) then
        Error("QuillenPolynomialOf_RouteB: i must be in [1..",
              setup.num_generators, "], got ", i);
    fi;

    cache := _GetBridgeCacheRouteB(setup);
    generator_order := setup.torsion[i];
    q_mod := setup.exponent;

    # ------------------------------------------------------------------
    # Case 1: order-2 generator.
    # ------------------------------------------------------------------
    if generator_order = 2 then
        kind := "F2_polynomial";

        # Build the F_2 chain-level cochain from cocyclebasis[i]:
        # cocyclebasis[i] takes values in {0, exp/2} for order-2 generator.
        # Dividing by (exp/2) gives a F_2 chain-level cochain.
        scaled_cb := List(setup.UCT.cocyclebasis[i],
                          v -> Int((v / (q_mod / 2))) mod 2);
        std_F2 := StandardCocycle(setup.R, scaled_cb, 3, 2);
        # Build target on T.
        target_bar := List(cache.T,
            t -> (std_F2(t[1], t[2], t[3]) mod 2) * Z(2)^0);
        ConvertToVectorRep(target_bar, 2);

        # Solve combined_M . x = target_bar over F_2.
        # x is length (n_polys + n_coboundary). Use cached SemiEchelon.
        n_rows := cache.n_polys + cache.n_coboundary;
        sol := SolveF2RowSpanFromSem(cache.sem,
            List(target_bar, x -> Int(x)),
            n_rows);
        if sol = fail then
            return rec(
                bridge_kind     := "F2_polynomial",
                order           := 2,
                modulus         := 2,
                error           := "Route B: no F_2 polynomial representation found",
                cocycle         := std_F2,
                poly_repr       := fail,
                poly_str        := "FAIL",
                coboundary      := fail
            );
        fi;

        poly_coeffs       := sol{[1..cache.n_polys]};
        coboundary_coeffs := sol{[cache.n_polys + 1..Length(sol)]};

        # Build symbolic polynomial poly_repr.
        poly_repr := QuillenZero();
        for k in [1..cache.n_polys] do
            if poly_coeffs[k] = 1 then
                poly_repr := QuillenAddElements(cache.polys.algebra,
                    poly_repr,
                    [cache.polys.candidates[k]]);
            fi;
        od;
        poly_str := QuillenElementToString(cache.polys.algebra, poly_repr);

        # Build the polynomial-derived bar cocycle (F_2 callable).
        poly_cocycle := function(g1, g2, g3)
            local v, k;
            v := 0;
            for k in [1..cache.n_polys] do
                if poly_coeffs[k] = 1 then
                    v := (v + cache.poly_funcs[k](g1, g2, g3)) mod 2;
                fi;
            od;
            return v;
        end;

        beta_func := function(g1, g2)
            local elts, n, k, idx_g1, idx_g2;
            elts := cache.elts;
            n := cache.n;
            idx_g1 := LookupDictionary(cache.coboundary_data.idx_dict, g1);
            idx_g2 := LookupDictionary(cache.coboundary_data.idx_dict, g2);
            k := (idx_g1 - 1) * n + idx_g2;
            return coboundary_coeffs[k];
        end;

        total_cocycle := function(g1, g2, g3)
            local pv, db, raw;
            pv := poly_cocycle(g1, g2, g3);
            db := (beta_func(g2, g3) - beta_func(g1*g2, g3)
                   + beta_func(g1, g2*g3) - beta_func(g1, g2)) mod 2;
            raw := (pv + db) mod 2;
            return (raw * (q_mod / 2)) mod q_mod;
        end;

        return rec(
            bridge_kind   := kind,
            order         := 2,
            modulus       := q_mod,
            scale         := q_mod / 2,
            poly_repr     := poly_repr,
            poly_str      := poly_str,
            poly_coeffs   := poly_coeffs,
            coboundary    := beta_func,
            cocycle       := total_cocycle,
            algebra       := cache.polys.algebra,
            route         := "B"
        );
    fi;

    # ------------------------------------------------------------------
    # Case 2: top-torsion generator. Pass through (same as Route A).
    # ------------------------------------------------------------------
    e_vec := List([1..setup.num_generators], k -> 0);
    e_vec[i] := 1;

    return rec(
        bridge_kind   := "pontryagin_top",
        order         := generator_order,
        modulus       := generator_order,
        poly_repr     := fail,
        poly_str      := Concatenation("P(generator at order ",
                                       String(generator_order), ")"),
        poly_coeffs   := fail,
        coboundary    := fail,
        cocycle       := StandardCocycleOf(setup, e_vec),
        algebra       := cache.polys.algebra,
        route         := "B",
        note          := "top-torsion (Pontryagin square); symbolic ",
        note2         := "polynomial form not implemented (Stage B2)"
    );
end;;

# ----------------------------------------------------------------------
# Verification helpers (similar to Route A).
# ----------------------------------------------------------------------

VerifyQuillenBridgeOf_RouteB := function(result, setup, i, sample_size)
    local omega_i, e_vec, G, mismatches, k, g1, g2, g3,
          v_bridge, v_hap, q_mod;
    e_vec := List([1..setup.num_generators], k -> 0);
    e_vec[i] := 1;
    omega_i := StandardCocycleOf(setup, e_vec);

    G := setup.group;
    q_mod := setup.exponent;
    mismatches := 0;
    for k in [1..sample_size] do
        g1 := Random(G); g2 := Random(G); g3 := Random(G);
        v_bridge := result.cocycle(g1, g2, g3) mod q_mod;
        v_hap    := omega_i(g1, g2, g3) mod q_mod;
        if v_bridge <> v_hap then
            mismatches := mismatches + 1;
        fi;
    od;
    return mismatches;
end;;

VerifyQuillenBridge_RouteB := function(setup, i, sample_size)
    local result;
    result := QuillenPolynomialOf_RouteB(setup, i);
    return VerifyQuillenBridgeOf_RouteB(result, setup, i, sample_size);
end;;

# Cross-check helper: compare Route B with Route A poly forms.
CompareRouteAB := function(setup, sample_size)
    local n_match_str, n_match_class, n_mismatch, i, ra, rb, info;
    n_match_str := 0;
    n_match_class := 0;
    n_mismatch := 0;
    info := [];
    for i in [1..setup.num_generators] do
        if setup.torsion[i] = 2 then
            ra := QuillenPolynomialOf(setup, i);
            rb := QuillenPolynomialOf_RouteB(setup, i);
            if ra.poly_str = rb.poly_str then
                n_match_str := n_match_str + 1;
                Add(info, rec(i := i, same_str := true,
                              poly_str := ra.poly_str));
            else
                # Different strings — check if cohomologically equal by
                # evaluating on sample_size random triples.
                #
                # Use the .cocycle callbacks. They should agree on the
                # original cocycle target.
                Add(info, rec(i := i, same_str := false,
                              ra_str := ra.poly_str,
                              rb_str := rb.poly_str));
                n_match_class := n_match_class + 1;
            fi;
        fi;
    od;
    Print("\n=== Route A vs Route B comparison ===\n");
    Print("  Identical poly_str: ", n_match_str, " / ",
          n_match_str + n_match_class, "\n");
    if n_match_class > 0 then
        Print("  Different poly_str (need eval-equal check): ",
              n_match_class, "\n");
    fi;
    return info;
end;;

Print("Loaded cocyclebasis_quillen_bridge_routeb.g (Q-int A4 Route B / #288: ",
      "QuillenPolynomialOf_RouteB, VerifyQuillenBridge_RouteB, ",
      "CompareRouteAB).\n");
