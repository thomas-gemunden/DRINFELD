# cocyclebasis_quillen_bridge_routec.g — Q-int A4 Route C (issue #288).
#
# Polynomial-form bridge at m=5 via Quillen-detecting-subgroup restriction
# (Route C). Companion to `cocyclebasis_quillen_bridge.g` (Route A;
# exhaustive |G|^2 coboundary enumeration; infeasible at m=5).
#
# # Mathematical background
#
# By Quillen's faithfulness theorem (Quillen 1971, [AM04, V.6.5]),
# the restriction map
#
#     H^*(G; F_2) ---> ⊕_E H^*(E; F_2)
#
# is INJECTIVE, where E ranges over (a chosen set of representatives of)
# the conjugacy classes of maximal elementary-abelian subgroups of G.
#
# For G = E_+(m): the maximal-EA rank is m+1; |E| = 2^{m+1}; and the
# number of conjugacy classes of maximal EAs is:
#
#   m=2: 6
#   m=3: 30
#   m=5: variable (a few hundred — but only a *spanning* subset is needed
#                  for faithfulness; we use ALL of them returned by
#                  _DETF_AllMaxEAsIn).
#
# H^*(E; F_2) = F_2[t_1, ..., t_{m+1}] (polynomial ring on m+1 generators
# of degree 1, since E ≅ (Z/2)^{m+1}). The degree-3 part has dimension
# C(m+1+2, 3):
#
#   m=2: C(5, 3) = 10
#   m=3: C(6, 3) = 20
#   m=5: C(8, 3) = 56
#
# # Route C implementation strategy
#
# For each generator e_j of setup_G.UCT.cocyclebasis (j = 1..k_G):
#
#   1. Build the F_2 cocycle phi_j : G^3 -> F_2 from StandardCocycleOf
#      (= the i-th cocyclebasis cocycle, scaled to F_2).
#
#   2. For each maximal-EA E, restrict phi_j to E (= composition with
#      inclusion E -> G) and find its polynomial form on E:
#
#          phi_j|_E = sum_{(a,b,c)} c_{abc} (t_a t_b t_c) + delta(beta)
#                      in F_2[t_1, ..., t_{m+1}]_{deg 3} + coboundaries.
#
#      The polynomial coefficients (c_{abc}) are uniquely determined
#      since the cubic monomials are a F_2-basis of H^3(E; F_2). The
#      coboundary correction is one of many solutions but doesn't affect
#      (c_{abc}). The extraction is done via the cached poly_extractor
#      per E (one SemiEchelonMatTransformation per E, reused across all
#      generators).
#
#   3. For each candidate cubic monomial p ∈ F_2[x_1, ..., x_{2m}],
#      compute p|_E symbolically by substitution: each x_i restricts
#      to a linear form in t_1, ..., t_{m+1}, and a cubic monomial
#      becomes a sum of cubic monomials in t's. The restriction matrix
#      `M_E : F_2^{2m} → F_2^{m+1}` is computed via BasisH1F2 on G and E.
#
#   4. Solve the joint linear system over F_2: find polynomial
#      coefficients (c_p) such that
#
#          sum_p c_p * (p|_E) = poly_extractor.extract(phi_j|_E)  for all E.
#
#      By Quillen's faithfulness, this system has at most one solution
#      modulo G-side coboundaries (which contribute the trivial polynomial
#      on every E, so the polynomial form is determined uniquely modulo
#      the Quillen ideal Q + B(x, x²)).
#
# # Public API
#
#   QuillenPolynomialOf_RouteC(setup, i)
#       Returns the same shape as QuillenPolynomialOf (Route A) — a rec
#       with .poly_repr, .poly_str, .order, .modulus, .bridge_kind,
#       .cocycle, etc.
#
#   QuillenPolynomialBridgeReport_RouteC(setup, sample_size)
#       Same shape as QuillenPolynomialBridgeReport (Route A).
#
# # Caveats
#
#   * The Pontryagin-top generator (order 4 at m=3, order 8 at m=2,
#     order 4 at m=5) passes through as `bridge_kind = "pontryagin_top"`
#     — its symbolic polynomial form is a Stage B2 follow-up. Route C
#     doesn't change this.
#
#   * Multiple polynomials can represent the same H^3 class modulo
#     coboundaries + Quillen ideal relations. The returned polynomial
#     is one specific representative.
#
#   * The polynomial is expressed in the ELEMENTARY x_i basis (where
#     x_i is the projection homomorphism G → F_2 sending the i-th GAP
#     generator to 1 and the others to 0). This matches Route A's
#     convention.

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
# Note: we depend on cocyclebasis_quillen_bridge.g for SolveF2RowSpanFromSem,
# BuildCoboundaryRowsF2, QuillenPolynomialBasisForBridge, QuillenPolynomialOf
# (for the cross-check function), Cup1x1x1 (from bar_cocycle.g, transitively).
if not IsBoundGlobal("_GetBridgeCache") then
    Read("cocyclebasis_quillen_bridge.g");
fi;
# D-VAN m=5 enumerator: _DETF_AllMaxEAsIn (issue #287). At m >= 4 this
# returns 112 Lagrangian EAs directly without ConjugacyClassesSubgroups,
# which OOMs/timeouts on |G| = 2048.
if not IsBoundGlobal("_DETF_AllMaxEAsIn") then
    Read("detecting_family_restriction.g");
fi;

# ----------------------------------------------------------------------
# Generalised H^1 basis for arbitrary groups (variant of BasisH1F2).
#
# BasisH1F2(G, m) hardcodes target_rank = 2*m; here we accept the
# target rank directly. For elementary abelian E of rank r, pass r.
# For E_+(m), pass 2m.
# ----------------------------------------------------------------------

BasisH1F2_Rank := function(G, target_rank)
    local gens, n_gens, elementary, k, v, catch,
          homs_raw, homs, assignments, elts, idx_dict, n_elts,
          tab, j, hom_raw, _make_hom_lookup;
    gens := GeneratorsOfGroup(G);
    n_gens := Length(gens);
    elementary := [];
    for k in [1..n_gens] do
        v := List([1..n_gens], i -> 0);
        v[k] := 1;
        catch := CALL_WITH_CATCH(F2HomFromImages, [G, v]);
        if catch[1] then
            Add(elementary, v);
            if Length(elementary) = target_rank then break; fi;
        fi;
    od;
    if Length(elementary) < target_rank then
        Error("BasisH1F2_Rank: could not find ", target_rank,
              " independent F_2 generators (only ", Length(elementary),
              " found); G's GeneratorsOfGroup ordering may not be ",
              "compatible with elementary basis");
    fi;
    homs_raw := List(elementary, v -> F2HomFromImages(G, v));

    elts := Elements(G);
    n_elts := Length(elts);
    idx_dict := NewDictionary(elts[1], true, elts);
    for k in [1..n_elts] do AddDictionary(idx_dict, elts[k], k); od;

    homs := [];
    _make_hom_lookup := function(tab_local, idx_dict_local)
        return function(g)
            return tab_local[LookupDictionary(idx_dict_local, g)];
        end;
    end;
    for j in [1..Length(homs_raw)] do
        hom_raw := homs_raw[j];
        tab := List([1..n_elts], k -> hom_raw(elts[k]));
        Add(homs, _make_hom_lookup(tab, idx_dict));
    od;

    return rec(
        homs        := homs,
        assignments := elementary,
        n_gens      := n_gens,
        rank        := target_rank
    );
end;;

# ----------------------------------------------------------------------
# Helper: F_2 row reduce + null space
# ----------------------------------------------------------------------

# Solve x * M = b over F_2 with M given as a regular GAP list of int lists
# (entries 0/1) and b an int list. Returns x (int list) on success, fail
# otherwise. Wraps SolutionMat with GF(2) compact conversion.
_RC_SolveF2 := function(M, b)
    local A, b_vec, sol, row;
    if Length(M) = 0 then
        if ForAll(b, x -> x = 0) then return []; fi;
        return fail;
    fi;
    A := List(M, row -> List(row, x -> (x mod 2) * Z(2)^0));
    for row in A do ConvertToVectorRep(row, 2); od;
    b_vec := List(b, x -> (x mod 2) * Z(2)^0);
    ConvertToVectorRep(b_vec, 2);
    sol := SolutionMat(A, b_vec);
    if sol = fail then return fail; fi;
    return List(sol, x -> Int(x));
end;;

# ----------------------------------------------------------------------
# H^1 restriction matrix M_E.
#
# Given:
#   * h1_basis_G: BasisH1F2(G, m) — list of 2m homs G -> F_2 (the x_i's)
#   * h1_basis_E: BasisH1F2(E, m+1) — list of (m+1) homs E -> F_2 (the t_a's)
#   * embedding E -> G (since E is a SUBGROUP of G, the embedding is the
#     identity inclusion on elements).
#
# For each x_i (G -> F_2), restricting to E gives a hom E -> F_2.
# Express it as a F_2-linear combination of the t_a's (m+1 of them, basis
# of H^1(E; F_2)).
#
# Returns: a (m+1) x 2m matrix M_E over F_2 such that
#     x_i|_E = sum_a M_E[a][i] * t_a   (as a hom E -> F_2)
#
# Algorithm: for each x_i, evaluate it on each generator of E. The
# resulting (m+1)-length F_2 vector is the coordinate of x_i|_E in the
# t-basis (since the t_a's are dual to the generators of E).
#
# Note: BasisH1F2 chooses elementary indicator homs on GeneratorsOfGroup.
# For the t_a's to be a dual basis, BasisH1F2 must succeed in finding
# m+1 independent indicator homs on E's generators. For a properly
# constructed elementary abelian E, this should always succeed since
# every generator is non-central and they form a F_2-basis of E.
_RC_BuildRestrictionMatrixM_E := function(h1_basis_G, h1_basis_E, E)
    local elts_E, gens_E, n_t, n_x, M_E, t_evals, i, a, x_i, t_eval;

    # Generators of E -- a basis as F_2-vector space (since E is elementary
    # abelian).
    gens_E := GeneratorsOfGroup(E);
    n_t := Length(h1_basis_E.homs);
    n_x := Length(h1_basis_G.homs);

    # Evaluate each x_i (on G) at the F_2-basis of E.
    #
    # The t_a's, as constructed by BasisH1F2, are "indicator homs on
    # GeneratorsOfGroup(E)": t_a(generator_b) = delta_{ab}. So the
    # coordinate of x_i|_E in the t-basis is just:
    #     M_E[a][i] = x_i(generator_a of E).
    M_E := List([1..n_t], a -> List([1..n_x], i -> 0));
    for a in [1..n_t] do
        if a > Length(gens_E) then
            # Pad with zeros if E has fewer generators than rank
            # (shouldn't happen for a properly constructed EA).
            continue;
        fi;
        for i in [1..n_x] do
            M_E[a][i] := h1_basis_G.homs[i](gens_E[a]);
        od;
    od;
    return M_E;
end;;

# ----------------------------------------------------------------------
# Substitute x_i -> sum_a M_E[a][i] * t_a in a cubic monomial.
#
# Input:
#   * mon: a Quillen monomial record with mon.sym = [e_1, ..., e_{2m}, 0]
#          (degree-3 cubic, no w part).
#   * M_E: the (m+1) x 2m restriction matrix.
#
# Output: a F_2 vector of length C(m+1+2, 3) = number of cubic monomials
# in F_2[t_1, ..., t_{m+1}], in a canonical ordering (lex on multisets).
#
# The cubic monomial x_a * x_b * x_c (a, b, c possibly equal) expands as:
#   x_a * x_b * x_c
# = (sum_p M[p][a] t_p) * (sum_q M[q][b] t_q) * (sum_r M[r][c] t_r)
# = sum_{p,q,r} M[p][a] M[q][b] M[r][c] * t_p t_q t_r.
#
# We collect coefficients by the SORTED multiset (p, q, r) since t_p t_q
# = t_q t_p in F_2 (commutative polynomial ring); also t_p^2 != 0 — in
# the polynomial ring on (Z/2)^k, x^2 is a valid nonzero degree-2 element
# (corresponding to the Frobenius image). So we don't reduce t_p^2; we
# keep it.
#
# Returns: a F_2 vector indexed by the lex-sorted multiset (p1, p2, p3).
_RC_SubstituteCubicMon := function(mon_sym, M_E, n_t, cubic_index)
    # mon_sym is the integer vector [e_1, ..., e_{2m}].
    local indices, n_x, n_mons, vec, i, k, a, b, c, p, q, r,
          tmp, key;

    n_x := Length(mon_sym);
    # Build the multiset (a, b, c) from mon_sym.
    indices := [];
    for i in [1..n_x] do
        for k in [1..mon_sym[i]] do
            Add(indices, i);
        od;
    od;
    if Length(indices) <> 3 then
        Error("_RC_SubstituteCubicMon: monomial not of total degree 3 ",
              "(got ", Length(indices), " from sym = ", mon_sym, ")");
    fi;
    a := indices[1]; b := indices[2]; c := indices[3];

    n_mons := cubic_index.n;
    vec := List([1..n_mons], i -> 0);
    for p in [1..n_t] do
        if M_E[p][a] = 0 then continue; fi;
        for q in [1..n_t] do
            if M_E[q][b] = 0 then continue; fi;
            for r in [1..n_t] do
                if M_E[r][c] = 0 then continue; fi;
                # Coefficient: M[p][a] * M[q][b] * M[r][c] (mod 2).
                # In F_2 it's just AND, but be explicit:
                key := SortedList([p, q, r]);
                vec[cubic_index.index.(String(key))] :=
                    (vec[cubic_index.index.(String(key))] + 1) mod 2;
            od;
        od;
    od;
    return vec;
end;;

# Build the index of degree-3 monomials in F_2[t_1, ..., t_n].
# Each is identified by SortedList([p, q, r]) with 1 <= p, q, r <= n.
# Returns rec(monomials := [...], index := rec(key -> int)) where
# `index.(String(key))` is the position of key in monomials.
_RC_BuildCubicMonomialIndex := function(n_t)
    local monomials, p, q, r, lst, index;
    monomials := [];
    for p in [1..n_t] do
        for q in [p..n_t] do
            for r in [q..n_t] do
                Add(monomials, [p, q, r]);
            od;
        od;
    od;
    index := rec();
    for p in [1..Length(monomials)] do
        index.(String(monomials[p])) := p;
    od;
    return rec(monomials := monomials,
               index := index,
               n := Length(monomials));
end;;

# ----------------------------------------------------------------------
# Identify a F_2 cocycle on E (callable G^3 -> F_2 / E^3 -> F_2) as a
# polynomial in F_2[t_1, ..., t_{m+1}] of degree 3.
#
# Input:
#   * setup_E: SetupCohomology3(E) for E elementary abelian.
#   * cocycle_E: a F_2-valued bar 3-cocycle on E (callable).
#   * cubic_index: from _RC_BuildCubicMonomialIndex(m+1).
#   * h1_basis_E: from BasisH1F2(E, m+1).
#
# Returns: a F_2 vector of length cubic_index.n giving the polynomial
# coefficients, OR fail if no polynomial representation exists.
#
# Algorithm: this is essentially Route A on E (since |E| is small).
# Each cubic monomial t_p t_q t_r is a bar 3-cocycle on E (via Cup1x1x1).
# We solve `cocycle_E = sum c_{pqr} (t_p t_q t_r) + delta(beta)` over F_2.
_RC_CocycleToPolynomialOnE := function(setup_E, cocycle_E, cubic_index,
                                       h1_basis_E)
    local E, elts, n, T, mon_funcs, q_rows, k, mon_indices,
          fn, sol, n_polys, cob_rows, combined, target, coboundary_data,
          phi_vals, x, all_rows;
    E := setup_E.group;
    elts := AsList(E);
    n := Length(elts);
    # Use all of E^3 as the test triples (|E|^3 = 64^3 at m=5 - tractable).
    T := Cartesian(elts, elts, elts);

    # Build the monomial cocycle functions and their value rows.
    mon_funcs := [];
    q_rows := [];
    for k in [1..Length(cubic_index.monomials)] do
        mon_indices := cubic_index.monomials[k];
        fn := Cup1x1x1(h1_basis_E.homs[mon_indices[1]],
                       h1_basis_E.homs[mon_indices[2]],
                       h1_basis_E.homs[mon_indices[3]]);
        Add(mon_funcs, fn);
        Add(q_rows, List(T, t -> fn(t[1], t[2], t[3]) mod 2));
    od;
    n_polys := Length(q_rows);

    # Build coboundary matrix (|E|^2 rows).
    coboundary_data := BuildCoboundaryRowsF2(E, T);

    # Convert q_rows to integer rows (BuildCoboundaryRowsF2 already returns
    # GF(2) compact rows).
    # Combined matrix: poly rows (integer 0/1) and coboundary rows (GF(2)).
    # Build all rows as GF(2) compact.
    all_rows := [];
    for k in [1..n_polys] do
        x := List(q_rows[k], v -> (v mod 2) * Z(2)^0);
        ConvertToVectorRep(x, 2);
        Add(all_rows, x);
    od;
    for x in coboundary_data.rows do
        Add(all_rows, x);
    od;

    # Build target vector.
    phi_vals := List(T, t -> cocycle_E(t[1], t[2], t[3]) mod 2);

    sol := SolveF2RowSpan(all_rows, phi_vals);
    if sol = fail then return fail; fi;
    return rec(
        poly_coeffs := sol{[1..n_polys]},
        coboundary_coeffs := sol{[n_polys + 1..Length(sol)]},
        coboundary_data := coboundary_data,
        elts := elts
    );
end;;

# ----------------------------------------------------------------------
# Main cache builder.
#
# Builds:
#   * setup_G, h1_basis_G (G-side)
#   * For each maximal-EA E_i:
#       - E_i (subgroup), h1_basis_E_i
#       - M_E_i: the (m+1) x 2m restriction matrix on H^1
#       - cand_subst[k]: substitution of candidate k into F_2[t_1..t_{m+1}]
#   * cubic_index: index of cubic monomials in F_2[t_1,...,t_{m+1}].
#   * candidates: list of cubic monomials in F_2[x_1,...,x_{2m}].
#
# The cache deliberately does NOT use UCT.hombasis on E (cocyclebasis vs
# hombasis indexing is delicate); instead the per-generator query
# QuillenPolynomialOf_RouteC computes omega_j on G and restricts it
# to E directly, then finds the polynomial form on E.
# ----------------------------------------------------------------------

_QPB_ROUTEC_CACHE := rec();;

# ----------------------------------------------------------------------
# Build a "polynomial extractor" for E that takes any F_2 cocycle on E
# and returns its polynomial form. Cached/reused across all generators
# to amortise the expensive coboundary-matrix construction.
#
# The extractor stores:
#   * T: the triple set (= E^3, since |E| <= 64 is small).
#   * combined_rows_sem: SemiEchelonMatTransformation of the matrix
#     whose rows are (poly_monomials | coboundary_rows), in GF(2).
#   * n_polys: number of polynomial monomial rows.
#
# Querying (in poly_extractor.extract(f)):
#   * Evaluate f on T to get a F_2 vector.
#   * Use SolveF2RowSpanFromSem with combined_rows_sem to find solution
#     coefficients. First n_polys coefficients are the polynomial form.
# ----------------------------------------------------------------------

_RC_BuildPolyExtractor_E := function(E, cubic_index, h1_basis_E)
    local elts, n, T, mon_funcs, q_rows, k, mon_indices, fn,
          coboundary_data, all_rows, n_polys, sem, x, sample_size,
          i, n_target;

    elts := AsList(E);
    n := Length(elts);
    # For small |E| (m <= 2, |E| <= 8) use full E^3. For larger |E|
    # (m >= 3, |E| >= 16) use a random sample large enough to discriminate
    # Z^3(E; F_2) (= |E|^2 - dim Z^2 + dim H^3 <= |E|^2 + 100). We use
    # |T| = 4 * (|E|^2 + cubic_index.n), capped at |E|^3.
    if n <= 8 then
        T := Cartesian(elts, elts, elts);
    else
        # |E| = 16 (m=3), 32 (m=4) or 64 (m=5). Sample 4 * (|E|^2 + n_polys).
        n_target := 4 * (n * n + cubic_index.n);
        n_target := Minimum(n_target, n * n * n);
        T := List([1..n_target], i -> [Random(elts),
                                       Random(elts),
                                       Random(elts)]);
    fi;

    # Build the monomial cocycle functions and their value rows.
    mon_funcs := [];
    q_rows := [];
    for k in [1..Length(cubic_index.monomials)] do
        mon_indices := cubic_index.monomials[k];
        fn := Cup1x1x1(h1_basis_E.homs[mon_indices[1]],
                       h1_basis_E.homs[mon_indices[2]],
                       h1_basis_E.homs[mon_indices[3]]);
        Add(mon_funcs, fn);
        Add(q_rows, List(T, t -> fn(t[1], t[2], t[3]) mod 2));
    od;
    n_polys := Length(q_rows);

    # Build coboundary matrix.
    coboundary_data := BuildCoboundaryRowsF2(E, T);

    # Convert poly rows to GF(2) compact form and concatenate with
    # coboundary rows (already in GF(2) form).
    all_rows := [];
    for k in [1..n_polys] do
        x := List(q_rows[k], v -> (v mod 2) * Z(2)^0);
        ConvertToVectorRep(x, 2);
        Add(all_rows, x);
    od;
    for x in coboundary_data.rows do
        Add(all_rows, x);
    od;

    sem := SemiEchelonMatTransformation(all_rows);

    return rec(
        E := E,
        T := T,
        n_polys := n_polys,
        n_rows := Length(all_rows),
        sem := sem,
        mon_funcs := mon_funcs,
        cubic_index := cubic_index,
        extract := function(f_E)
            local phi_vals, sol;
            phi_vals := List(T, t -> f_E(t[1], t[2], t[3]) mod 2);
            sol := SolveF2RowSpanFromSem(sem, phi_vals, Length(all_rows));
            if sol = fail then return fail; fi;
            return sol{[1..n_polys]};
        end,
        # Variant for when phi_vals are already precomputed (e.g., from
        # batch Syzygy precomputation). Saves per-call cocycle evaluation.
        extract_from_vals := function(phi_vals)
            local sol;
            sol := SolveF2RowSpanFromSem(sem, phi_vals, Length(all_rows));
            if sol = fail then return fail; fi;
            return sol{[1..n_polys]};
        end
    );
end;;

# ----------------------------------------------------------------------
# Precompute the G-resolution Syzygy values for all (E, T_E) triples.
#
# `Syzygy(R_G, [g1, g2, g3])` is the chain-level representation of the
# bar triple (g1, g2, g3). For each generator e_i, the F_2 cocycle value
# is computed as the dot product with `cocyclebasis[i]` (mod q_G, then
# scaled to F_2). The Syzygy itself is independent of i — so we can
# precompute it once per (E, triple) and amortise across generators.
#
# Returns: a list parallel to T (one entry per triple) giving the
# `R_G.dimension(3)`-length integer vector representing the chain-level
# signed-multiplicity counts. The vector v is constructed so that
# v[k] := signed count of |sign| = k in Syzygy(R_G, [g1, g2, g3]).
#
# For any generator e_i, the cocycle value is v · cocyclebasis[i] (mod q_G).
# ----------------------------------------------------------------------

_RC_PrecomputeSyzygiesOnT := function(R_G, T)
    local n_dim, syz_table, i, t, S, v, x;
    n_dim := R_G!.dimension(3);
    syz_table := [];
    for i in [1..Length(T)] do
        t := T[i];
        S := Syzygy(R_G, [t[1], t[2], t[3]]);
        Apply(S, x -> x[1]);
        v := List([1..n_dim], k -> 0);
        for x in S do
            v[AbsoluteValue(x)] := v[AbsoluteValue(x)] + SignInt(x);
        od;
        Add(syz_table, v);
    od;
    return syz_table;
end;;

# Find all max-EA conj class reps in a pinned G.
#
# Delegates to `_DETF_AllMaxEAsIn` from detecting_family_restriction.g
# (D-VAN m=5 OOM fix, issue #287):
#
#   * m <= 3: full ConjugacyClassesSubgroups enumeration (6 reps at m=2,
#     30 at m=3). This preserves bit-for-bit m=2/m=3 anchor compatibility
#     with the prior _RC_AllMaxEAsInG implementation.
#   * m >= 4: direct Lagrangian-style enumeration. At m=5 ConjugacyClassesSubgroups
#     on E_+(5) (|G|=2048) OOMs at 32 GB / >10 min wall. _DETF_AllMaxEAsIn
#     returns 32 axis-aligned + 80 diagonal pair-swap Lagrangians = 112
#     max EAs at m=5, empirically sufficient for Quillen restriction-
#     injectivity (per #287's audit at #289).
#
# Return shape matches the original: a list of subgroups of G (each a
# rank-(m+1) elementary abelian), suitable for further H^* restriction
# work. _RC_GetCache iterates over this list and computes h1_basis_E,
# M_E, cand_subst, poly_extractor, syz_table per EA — those are all
# group-theoretic operations on the subgroup and so insensitive to
# whether the list came from ConjugacyClassesSubgroups (m <= 3) or
# direct Lagrangian construction (m >= 4).
_RC_AllMaxEAsInG := function(G, m)
    local candidates;
    candidates := _DETF_AllMaxEAsIn(G, m);
    if Length(candidates) = 0 then
        Error("_RC_AllMaxEAsInG: no rank-", m + 1,
              " elementary abelian in G");
    fi;
    return candidates;
end;;

# Module-level config: max number of EAs to use. Set to a positive
# integer to cap. With _DETF_AllMaxEAsIn (issue #287) the EA count is
# already bounded: 6 (m=2), 30 (m=3), 112 (m=5), so the cap is no longer
# needed for OOM/timeout protection — it's kept as a safety guard.
# Defaults to 0 (use all).
_RC_MAX_EAS := 0;;

_RC_GetCache := function(setup_G)
    local G, m, key, h1_basis_G, ea_list, n_ea, ea_data,
          i, E, h1_basis_E, M_E, candidates, cand_subst, n_polys, k,
          cubic_index, big_S_int, big_S_gf2, big_S_sem,
          sub_row, x, ea_idx, poly_extractor, syz_table;

    G := setup_G.group;
    # Infer m from |G|: |E_+(m)| = 2^{2m+1}.
    if Order(G) = 8 then m := 1;
    elif Order(G) = 32 then m := 2;
    elif Order(G) = 128 then m := 3;
    elif Order(G) = 512 then m := 4;
    elif Order(G) = 2048 then m := 5;
    else
        Error("_RC_GetCache: |G| = ", Order(G), " not in {8,32,128,512,2048}");
    fi;
    key := Concatenation("rc_m", String(m), "_o", String(Order(G)));
    if IsBound(_QPB_ROUTEC_CACHE.(key)) then
        return _QPB_ROUTEC_CACHE.(key);
    fi;

    Print("  [rc cache] building Route-C cache for m=", m,
          " (|G|=", Order(G), ")\n");

    # H^1 basis on G.
    h1_basis_G := BasisH1F2(G, m);
    Print("  [rc cache] |h1_basis_G.homs| = ", Length(h1_basis_G.homs), "\n");

    # Find all max-EA conj class reps inside THIS G (using setup_G.group).
    Print("  [rc cache] enumerating maximal EA conj classes in G...\n");
    ea_list := _RC_AllMaxEAsInG(G, m);
    n_ea := Length(ea_list);
    Print("  [rc cache]   got ", n_ea, " max-EA classes\n");
    if _RC_MAX_EAS > 0 and n_ea > _RC_MAX_EAS then
        Print("  [rc cache]   capping to first ", _RC_MAX_EAS, " (_RC_MAX_EAS)\n");
        ea_list := ea_list{[1.._RC_MAX_EAS]};
        n_ea := _RC_MAX_EAS;
    fi;

    cubic_index := _RC_BuildCubicMonomialIndex(m + 1);
    Print("  [rc cache] cubic monomials in F_2[t_1..t_{m+1}]: ",
          cubic_index.n, " (expected C(m+3,3) = ",
          Binomial(m + 3, 3), ")\n");

    # Build cubic monomial candidates in F_2[x_1, ..., x_{2m}].
    candidates := [];
    for k in QuillenPolynomialBasisForBridge(m).candidates do
        Add(candidates, k);
    od;
    Print("  [rc cache] candidate polys in F_2[x_1..x_{2m}]: ",
          Length(candidates), " (expected C(2m+2,3) = ",
          Binomial(2*m + 2, 3), ")\n");

    # Per-EA data.
    ea_data := [];
    for i in [1..n_ea] do
        E := ea_list[i];
        Print("  [rc cache] processing EA #", i, "/", n_ea, " (|E|=",
              Order(E), ")...\n");
        # h1_basis on E (rank m+1).
        h1_basis_E := BasisH1F2_Rank(E, m + 1);
        # Restriction matrix on H^1.
        M_E := _RC_BuildRestrictionMatrixM_E(h1_basis_G, h1_basis_E, E);

        # Substitution matrix: for each candidate p, p|_E as cubic-in-t.
        cand_subst := List(candidates, c ->
            _RC_SubstituteCubicMon(c.sym{[1..2*m]}, M_E, m + 1, cubic_index));

        # Build the F_2 cocycle-to-polynomial extractor for E.
        # Reusing the same matrix across all 165 generators saves O(n_gen)x.
        Print("    [rc cache] building poly_extractor + syzygy table...\n");
        poly_extractor := _RC_BuildPolyExtractor_E(E, cubic_index,
                                                    h1_basis_E);
        # Precompute Syzygy values on the extractor's T using the
        # G-side resolution. This amortises Syzygy across all generators.
        syz_table := _RC_PrecomputeSyzygiesOnT(setup_G.R, poly_extractor.T);

        Add(ea_data, rec(
            i := i,
            E := E,
            h1_basis_E := h1_basis_E,
            M_E := M_E,
            cand_subst := cand_subst,
            poly_extractor := poly_extractor,
            syz_table := syz_table
        ));
    od;

    # Precompute big_S over GF(2) for fast per-generator solves.
    Print("  [rc cache] building big_S matrix (",
          Length(candidates), " rows × ", n_ea * cubic_index.n,
          " cols)...\n");
    big_S_int := [];
    for k in [1..Length(candidates)] do
        sub_row := [];
        for ea_idx in [1..n_ea] do
            Append(sub_row, ea_data[ea_idx].cand_subst[k]);
        od;
        Add(big_S_int, sub_row);
    od;
    big_S_gf2 := List(big_S_int, row -> List(row, x -> (x mod 2) * Z(2)^0));
    for x in big_S_gf2 do ConvertToVectorRep(x, 2); od;
    big_S_sem := SemiEchelonMatTransformation(big_S_gf2);

    _QPB_ROUTEC_CACHE.(key) := rec(
        m := m,
        G := G,
        setup_G := setup_G,
        h1_basis_G := h1_basis_G,
        ea_data := ea_data,
        candidates := candidates,
        cubic_index := cubic_index,
        big_S_int := big_S_int,
        big_S_gf2 := big_S_gf2,
        big_S_sem := big_S_sem
    );
    Print("  [rc cache] done.\n");
    return _QPB_ROUTEC_CACHE.(key);
end;;

# ----------------------------------------------------------------------
# Convert a restriction vector (in setup_E.UCT.hombasis coords) to a
# cubic polynomial in F_2[t_1, ..., t_{m+1}].
#
# Input: res_E_vec, a length-k_E integer vector (entries in Z/exp_E).
#        ea_record, the rec from cache.ea_data[i].
#
# Output: F_2 vector of length cubic_index.n, OR fail if any
# basis_to_poly_E[j] is fail.
_RC_RestrictionVecToPolyOnE := function(res_E_vec, ea_record, cubic_index)
    local n_mons, poly_vec, j, contrib, c_val, k;
    n_mons := cubic_index.n;
    poly_vec := List([1..n_mons], i -> 0);
    for j in [1..Length(res_E_vec)] do
        c_val := res_E_vec[j] mod 2;
        if c_val = 0 then continue; fi;
        contrib := ea_record.basis_to_poly_E[j];
        if contrib = fail then
            return fail;   # can't represent
        fi;
        for k in [1..n_mons] do
            poly_vec[k] := (poly_vec[k] + contrib[k]) mod 2;
        od;
    od;
    return poly_vec;
end;;

# ----------------------------------------------------------------------
# Main API: QuillenPolynomialOf_RouteC(setup, i)
#
# Returns the same shape as Route A's QuillenPolynomialOf, but uses
# Route C (Quillen-detecting-subgroup restriction).
# ----------------------------------------------------------------------

QuillenPolynomialOf_RouteC := function(setup, i)
    local cache, generator_order, q_mod, kind, ea_record, target_E,
          target_concat, big_S, n_polys, sol, poly_coeffs, poly_repr, k,
          poly_str, omega_i, e_vec, scale, n_ea,
          ea_idx, sub_row, omega_i_F2_G, omega_i_F2_E, half_q,
          dir_result;

    if not (IsInt(i) and i >= 1 and i <= setup.num_generators) then
        Error("QuillenPolynomialOf_RouteC: i must be in [1..",
              setup.num_generators, "], got ", i);
    fi;

    cache := _RC_GetCache(setup);
    generator_order := setup.torsion[i];

    # Build omega_i for output (the cocycle on G via HAP).
    e_vec := List([1..setup.num_generators], k -> 0);
    e_vec[i] := 1;
    omega_i := StandardCocycleOf(setup, e_vec);
    q_mod := setup.exponent;

    # Case 1: order-2 generator -> F_2 polynomial.
    if generator_order = 2 then
        kind := "F2_polynomial";
        n_ea := Length(cache.ea_data);
        n_polys := Length(cache.candidates);
        half_q := q_mod / 2;

        # The chain-level cocycle vector for e_i.
        # `cocyclebasis[i]` is a length-R.dimension(3) integer vector.
        # The cocycle value at a triple t is dot(syz_table[t], cocyclebasis[i])
        # (mod q_G, then scaled / half_q mod 2 for F_2 reduction).

        # For each E, directly restrict omega_i to E and find its
        # polynomial form in F_2[t_1,...,t_{m+1}].
        # Uses cached syz_table for fast cocycle evaluation.
        target_concat := [];
        for ea_idx in [1..n_ea] do
            ea_record := cache.ea_data[ea_idx];
            # Compute phi_vals from syz_table.
            dir_result := ea_record.poly_extractor.extract_from_vals(
                List(ea_record.syz_table, v ->
                    (((v * setup.UCT.cocyclebasis[i]) mod q_mod)
                     / half_q) mod 2));
            if dir_result = fail then
                Print("[Route C] could not represent omega_", i,
                      "|_E #", ea_idx, " as polynomial; this E fails ",
                      "F_2-injectivity (shouldn't happen for elementary ",
                      "abelian)\n");
                Append(target_concat,
                       ListWithIdenticalEntries(cache.cubic_index.n, 0));
            else
                Append(target_concat, dir_result);
            fi;
        od;

        # Use the cached big_S_sem from the cache for fast solving.
        sol := SolveF2RowSpanFromSem(cache.big_S_sem, target_concat, n_polys);
        if sol = fail then
            return rec(
                bridge_kind := "F2_polynomial",
                order := 2,
                modulus := 2,
                error := "no F_2 polynomial found via Route C",
                cocycle := omega_i,
                poly_repr := fail,
                poly_str := "FAIL",
                coboundary := fail
            );
        fi;
        poly_coeffs := sol;
        poly_repr := QuillenZero();
        for k in [1..n_polys] do
            if poly_coeffs[k] = 1 then
                poly_repr := QuillenAddElements(
                    QuillenCanonicalPresentation(cache.m),
                    poly_repr,
                    [cache.candidates[k]]);
            fi;
        od;
        poly_str := QuillenElementToString(
            QuillenCanonicalPresentation(cache.m),
            poly_repr);
        scale := q_mod / 2;

        return rec(
            bridge_kind := kind,
            order := 2,
            modulus := q_mod,
            scale := scale,
            poly_repr := poly_repr,
            poly_str := poly_str,
            poly_coeffs := poly_coeffs,
            cocycle := omega_i,
            algebra := QuillenCanonicalPresentation(cache.m),
            route := "C"
        );
    fi;

    # Case 2: top-torsion. Pass through as Route A does.
    return rec(
        bridge_kind := "pontryagin_top",
        order := generator_order,
        modulus := generator_order,
        poly_repr := fail,
        poly_str := Concatenation("P(generator at order ",
                                   String(generator_order), ")"),
        poly_coeffs := fail,
        coboundary := fail,
        cocycle := omega_i,
        algebra := QuillenCanonicalPresentation(cache.m),
        note := "top-torsion (Pontryagin square); symbolic ",
        note2 := "polynomial form not implemented (Stage B2)",
        route := "C"
    );
end;;

# ----------------------------------------------------------------------
# Diagnostic: comprehensive report (parallel to Route A's).
# ----------------------------------------------------------------------

QuillenPolynomialBridgeReport_RouteC := function(setup, sample_size)
    local results, i, r, line, ok_count, n_gen;
    Print("\n=== Quillen polynomial bridge report (Route C) ===\n");
    Print("  G = ", StructureDescription(setup.group),
          ", |G| = ", Order(setup.group), "\n");
    Print("  torsion = ", setup.torsion, "\n");
    Print("  exponent = ", setup.exponent, "\n");
    Print("  num_generators = ", setup.num_generators, "\n\n");

    n_gen := setup.num_generators;
    results := [];
    ok_count := 0;
    for i in [1..n_gen] do
        r := QuillenPolynomialOf_RouteC(setup, i);
        if r.bridge_kind = "F2_polynomial" and IsBound(r.poly_str)
           and r.poly_str <> "FAIL" then
            ok_count := ok_count + 1;
            line := Concatenation("  e_", String(i),
                                  "  order=", String(r.order),
                                  "  poly = ", r.poly_str);
        else
            line := Concatenation("  e_", String(i),
                                  "  order=", String(r.order),
                                  "  kind=", r.bridge_kind);
        fi;
        Print(line, "\n");
        Add(results, rec(i := i, order := r.order, kind := r.bridge_kind,
                         poly_str := If_(IsBound(r.poly_str),
                                         r.poly_str, ""),
                         ok := (r.bridge_kind = "F2_polynomial" and
                                IsBound(r.poly_str) and r.poly_str <> "FAIL")));
    od;

    Print("\n=== Summary ===\n");
    Print("  Total generators: ", Length(results), "\n");
    Print("  Route C F_2 matches: ", ok_count, " / ", Length(results), "\n");
    return rec(results := results, ok_count := ok_count, n := n_gen);
end;;

# ----------------------------------------------------------------------
# Cross-check Route C against Route A at small m (m=2, m=3).
#
# For each generator e_i:
#   - run Route A (poly_A) and Route C (poly_C).
#   - check that poly_A and poly_C represent the same H^3(G; F_2) class.
#     Concretely: substitute both polynomials into each E and check
#     they give the same polynomial in F_2[t_1,...,t_{m+1}].
#
# Returns rec(n_match, n_mismatch, details := list).
# ----------------------------------------------------------------------

QuillenRouteACvsRouteCCheck := function(setup)
    local results_A, results_C, cache, i, r_a, r_c, n_gen, sub_a, sub_c,
          n_match, n_mismatch, details, ea_idx, n_polys, ea_record, k, p,
          sub_row_a, sub_row_c, n_ea;

    Print("\n=== Route A vs Route C cross-check ===\n");
    cache := _RC_GetCache(setup);
    n_gen := setup.num_generators;
    n_polys := Length(cache.candidates);
    n_ea := Length(cache.ea_data);

    n_match := 0;
    n_mismatch := 0;
    details := [];

    for i in [1..n_gen] do
        r_a := QuillenPolynomialOf(setup, i);
        r_c := QuillenPolynomialOf_RouteC(setup, i);

        if r_a.bridge_kind <> r_c.bridge_kind then
            n_mismatch := n_mismatch + 1;
            Add(details, rec(i := i, status := "kind_mismatch",
                             kind_a := r_a.bridge_kind,
                             kind_c := r_c.bridge_kind));
            Print("  e_", i, ": KIND MISMATCH (A=", r_a.bridge_kind,
                  ", C=", r_c.bridge_kind, ")\n");
            continue;
        fi;

        if r_a.bridge_kind <> "F2_polynomial" then
            # Pontryagin-top — both should pass through. Count as match.
            n_match := n_match + 1;
            continue;
        fi;

        # Substitute poly_A and poly_C into each E and compare.
        sub_a := ListWithIdenticalEntries(n_ea * cache.cubic_index.n, 0);
        sub_c := ListWithIdenticalEntries(n_ea * cache.cubic_index.n, 0);
        for k in [1..n_polys] do
            if r_a.poly_coeffs[k] = 1 then
                for ea_idx in [1..n_ea] do
                    ea_record := cache.ea_data[ea_idx];
                    for p in [1..cache.cubic_index.n] do
                        sub_a[(ea_idx - 1) * cache.cubic_index.n + p] :=
                            (sub_a[(ea_idx - 1) * cache.cubic_index.n + p]
                             + ea_record.cand_subst[k][p]) mod 2;
                    od;
                od;
            fi;
            if r_c.poly_coeffs[k] = 1 then
                for ea_idx in [1..n_ea] do
                    ea_record := cache.ea_data[ea_idx];
                    for p in [1..cache.cubic_index.n] do
                        sub_c[(ea_idx - 1) * cache.cubic_index.n + p] :=
                            (sub_c[(ea_idx - 1) * cache.cubic_index.n + p]
                             + ea_record.cand_subst[k][p]) mod 2;
                    od;
                od;
            fi;
        od;
        if sub_a = sub_c then
            n_match := n_match + 1;
            Print("  e_", i, ": MATCH (same H^3(G; F_2) class)\n");
        else
            n_mismatch := n_mismatch + 1;
            Add(details, rec(i := i, status := "poly_differs",
                             poly_a := r_a.poly_str,
                             poly_c := r_c.poly_str));
            Print("  e_", i, ": POLY DIFFER (different H^3 classes!)\n");
            Print("    A: ", r_a.poly_str, "\n");
            Print("    C: ", r_c.poly_str, "\n");
        fi;
    od;

    Print("\n=== Summary ===\n");
    Print("  Total: ", n_gen, "\n");
    Print("  Match: ", n_match, "\n");
    Print("  Mismatch: ", n_mismatch, "\n");
    return rec(n_match := n_match, n_mismatch := n_mismatch,
               details := details);
end;;

Print("Loaded cocyclebasis_quillen_bridge_routec.g ",
      "(Q-int A4 Route C: QuillenPolynomialOf_RouteC).\n");
