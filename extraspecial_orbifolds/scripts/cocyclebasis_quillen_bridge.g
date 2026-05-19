# cocyclebasis_quillen_bridge.g — Q-int A4 / issue #285.
#
# Bridge HAP's UCT.cocyclebasis (chain-level integer vectors) to the
# Quillen polynomial presentation of H^*(E_+(m); F_2).
#
# Public API
# ----------
#   QuillenPolynomialOf(setup, i)
#       For setup := SetupCohomology3(EPlusGroup(m)) and i in
#       [1..Length(setup.UCT.cocyclebasis)], identify the i-th H^3
#       generator as a symbolic polynomial in the Quillen
#       presentation. Returns a record with fields:
#         .poly_repr        : symbolic polynomial (a Q-1 element in the
#                             canonical Quillen presentation A_m =
#                             QuillenCanonicalPresentation(m)).
#         .poly_str         : human-readable string form.
#         .order            : the torsion order of the generator
#                             (setup.torsion[i]).
#         .modulus          : the modulus the polynomial lives in
#                             (2 for Z/2 generators, otherwise the
#                             top-torsion modulus).
#         .bridge_kind      : "F2_polynomial" for the order-2 generators;
#                             "pontryagin_top" for the top-torsion
#                             (Z/4 or Z/8) generator.
#         .coboundary       : a function (g1, g2) -> Z/q realising the
#                             coboundary delta(beta) that makes the
#                             polynomial bar cocycle equal omega_i
#                             pointwise (mod q). May be the zero
#                             function when no correction is needed.
#         .cocycle          : a callable (g1, g2, g3) -> Z/q that equals
#                             StandardCocycleOf(setup, e_i) pointwise
#                             (mod q). Built as poly_cocycle + delta beta.
#
#   QuillenPolynomialBasisForBridge(m)
#       Returns the F_2 basis of degree-3 elements of the canonical
#       Quillen presentation A_m, along with the corresponding bar
#       cocycle constructors.
#
# Mathematical context (see issue #285 + Quillen [Q4]):
#
# The bridge maps a chain-level cocycle vector v = UCT.cocyclebasis[i]
# (an integer vector of length R_3.dim representing a class in
# H^3(G; Z/exp)) to a polynomial p in the canonical Quillen
# presentation S(V*)/J  with V = E_+(m)/Z and J = (Q, B(x, x^2), ...).
#
# At F_2 level. Most generators have order 2 in H^3(G; U(1)) (= H^4(G; Z))
# and lift to the F_2 cohomology basis of degree 3 in A_m. The matching
# is done by:
#   1. Reducing omega_i = StandardCocycleOf(setup, e_i) mod 2 to obtain
#      a Z/2-valued bar 3-cocycle phi_i : G^3 -> F_2.
#   2. Building bar cocycles q_1, ..., q_d for the F_2 basis of degree
#      3 in A_m (d = 15 at m=2, 49 at m=3) via cup products
#      Cup1x1x1(x_a, x_b, x_c) over the canonical x_i : G -> F_2 basis.
#   3. Solving a linear system over F_2 for which combination of q_k's
#      (modulo coboundaries delta(beta), beta : G^2 -> F_2) equals phi_i.
#   4. The polynomial part of the solution is the symbolic identifier;
#      the coboundary part is the correction making the values match
#      pointwise.
#
# At top torsion (Z/4 or Z/8). The single top-torsion generator
# represents the Pontryagin square of the unique even-degree polynomial
# generator. For the present implementation we name it symbolically
# (bridge_kind = "pontryagin_top") and provide the HAP cocycle as the
# cocycle field, with no symbolic polynomial form. A full Pontryagin
# square treatment is a follow-up (see Stage B2 of Quillen integration).
#
# Constraints / caveats
# ---------------------
# * Requires |G|^2 to fit in memory (we materialise the coboundary
#   matrix delta : C^2(G; F_2) -> C^3(G; F_2) row by row). At m=2 this
#   is 32^2 = 1024 rows, very cheap; at m=3 it's 128^2 = 16384 rows;
#   at m=5 it would be 2048^2 = 4M rows -- infeasible by this route.
# * The discriminating triple set T defaults to a random sample of size
#   2.5 * (|G|^2 + n_polys) for m=3 (large enough that the row-rank on T
#   matches the full-G^3 row-rank, which equals dim Z^3(G; F_2) =
#   |G|^2 - dim Z^2 + dim H^3). At m=2 we use all of G^3 (32768) for
#   exhaustive coverage.
# * The polynomial expression is given in the ELEMENTARY x_i basis,
#   where x_i is the projection homomorphism G -> F_2 sending the i-th
#   GAP generator of G to 1 and the others to 0. This basis is NOT the
#   canonical Quillen symplectic basis (where Q = sum x_i x_{m+i} =0).
#   In our basis, x_{2k-1} and x_{2k} form a symplectic pair (each pair
#   comes from one D_8 factor in the central product E_+(m) = D_8 *...).
#   The relation Q in our basis reads (for m=2):
#     Q_elementary = x_1*x_2 + x_3*x_4   (paired (a, b) generators)
#   which differs from canonical Quillen by the basis change.
# * Multiple polynomials can represent the same cohomology class
#   modulo the coboundary subspace and the Quillen ideal relations.
#   The polynomial returned is one specific representative chosen by
#   the F_2-linear-algebra solver. Different runs may give different
#   representatives if the linear system has multiple solutions
#   (which happens whenever the coboundary correction is not unique).

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

# ----------------------------------------------------------------------
# Step 1: Find the F_2-cohomology degree-1 generator homomorphisms.
#
# For G = E_+(m), we have G^ab = (F_2)^{2m}. Find 2m linearly independent
# basis homomorphisms x_1, ..., x_{2m} : G -> F_2.
# ----------------------------------------------------------------------

# Build a 2m-element basis of H^1(G; F_2). Uses elementary-vector
# enumeration over generators of G; assumes that the first 2m generators
# (in GeneratorsOfGroup order) are mod-2 linearly independent in G^ab.
# Returns a record with .homs (list of functions G -> {0,1}) and
# .assignments (the F_2 image vectors of GeneratorsOfGroup -- length-n
# vectors where n = Length(GeneratorsOfGroup(G))).
#
# Performance: the homs are wrapped in value-table lookups (build a table
# of size |G| once, then lookups are O(1)). This avoids repeated
# Image(hom, g) calls in inner loops.
BasisH1F2 := function(G, m)
    local gens, n_gens, target_rank, elementary, k, v, catch,
          homs_raw, homs, hom, assignments, elts, idx_dict, n_elts,
          tab, g, j, hom_raw, _make_hom_lookup;
    gens := GeneratorsOfGroup(G);
    n_gens := Length(gens);
    target_rank := 2 * m;
    # Find the first 2m generators where setting that generator to 1
    # (and others to 0) yields a valid hom. These will be linearly
    # independent if they form a basis of the abelian quotient.
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
        Error("BasisH1F2: could not find ", target_rank,
              " independent F_2 generators (only ", Length(elementary),
              " found); G's GeneratorsOfGroup ordering may not be ",
              "compatible with elementary basis");
    fi;
    homs_raw := List(elementary, v -> F2HomFromImages(G, v));

    # Tabulate each hom for O(1) lookup. Use a dictionary keyed by group
    # element.
    elts := Elements(G);
    n_elts := Length(elts);
    idx_dict := NewDictionary(elts[1], true, elts);
    for k in [1..n_elts] do AddDictionary(idx_dict, elts[k], k); od;

    homs := [];
    # Helper to build a closure with proper per-iteration variable capture
    # (avoids GAP's shared-loop-var pitfall).
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
        m           := m
    );
end;;

# ----------------------------------------------------------------------
# Step 2: Convert a degree-3 Quillen monomial to a bar cocycle.
#
# A degree-3 monomial mon.sym = [e_1, ..., e_{2m}, 0] with sum = 3 and
# mon.ext = [] corresponds to the polynomial x_1^{e_1} * ... * x_{2m}^{e_{2m}}.
# Its bar cocycle is the iterated cup product: Cup1x1x1(x_a, x_b, x_c)
# where (a, b, c) is the multiset of indices according to e_i.
# (The ordering choice doesn't affect the cohomology class, only the
# pointwise representative.)
#
# Returns a function G^3 -> F_2.
# ----------------------------------------------------------------------

MonomialToBarCocycleF2 := function(h1_basis, mon)
    local n_sym, indices, i, k, a, b, c;
    n_sym := Length(mon.sym);
    # Skip the w generator (last index) — at deg 3, w doesn't appear
    # for m >= 2 (deg(w) = 2^m >= 4) and at m=1 we don't deal with w
    # at the deg-3 level via this function.
    #
    # Build the multiset (a, b, c) from mon.sym[1..2m].
    indices := [];
    for i in [1..n_sym] do
        for k in [1..mon.sym[i]] do
            Add(indices, i);
        od;
    od;
    if Length(indices) <> 3 then
        Error("MonomialToBarCocycleF2: monomial is not of total degree 3 ",
              "(got total deg = ", Length(indices), " from sym = ", mon.sym, ")");
    fi;
    if ForAny(indices, i -> i > Length(h1_basis.homs)) then
        Error("MonomialToBarCocycleF2: monomial references the w-generator ",
              "(index ", Length(h1_basis.homs) + 1, " = w with deg = 2^m) ",
              "or beyond. Cannot reduce w to cup products of degree-1 homs.");
    fi;
    a := indices[1]; b := indices[2]; c := indices[3];
    return Cup1x1x1(h1_basis.homs[a], h1_basis.homs[b], h1_basis.homs[c]);
end;;

# Convenience: pretty-print a degree-3 Quillen polynomial monomial.
MonomialToString := function(A, mon)
    return QuillenMonomialToString(A, mon);
end;;

# ----------------------------------------------------------------------
# Step 3: Build the F_2 basis of degree-3 polynomial cocycles for m.
# ----------------------------------------------------------------------

QuillenPolynomialBasisForBridge := function(m)
    local A, basis_d3, candidates, mon, basis_record, n_x, e, all_d3_mons,
          mon_rec;
    if m < 1 then
        Error("QuillenPolynomialBasisForBridge: m must be >= 1, got ", m);
    fi;
    A := QuillenCanonicalPresentation(m);
    # Enumerate ALL degree-3 monomials in F_2[x_1, ..., x_{2m}] (excluding w).
    # That is, all non-negative integer vectors e = (e_1, ..., e_{2m}) with
    # sum(e) = 3.
    #
    # Reason: our F_2-basis homs may not coincide with the canonical
    # Quillen x_i (which require a symplectic basis decomposition). By
    # enumerating ALL monomials we leave the linear-algebra solver to
    # find the correct combination modulo coboundaries.
    n_x := 2 * m;
    candidates := [];
    # Enumerate compositions of 3 into 2m parts.
    # Use a simple recursive enumeration; for small m this is cheap.
    all_d3_mons := [];
    # Manual enumeration: monomials are records (sym, ext) of length
    # A.n_sym = 2m+1 with sym[1..2m] >= 0 summing to 3 and sym[2m+1] = 0.
    for e in Cartesian(List([1..n_x], i -> [0..3])) do
        if Sum(e) = 3 then
            mon_rec := rec(
                sym := Concatenation(e, [0]),
                ext := []
            );
            Add(candidates, mon_rec);
        fi;
    od;
    Sort(candidates, QuillenLTMonomial(A));

    basis_d3 := BasisInDegree(A, 3);
    return rec(
        m              := m,
        algebra        := A,
        basis_d3       := basis_d3,
        candidates     := candidates,
        n_candidates   := Length(candidates),
        # Also keep the canonical-basis monomials (those not in the
        # ideal under canonical Quillen relations). These are used as
        # the "preferred" representatives in the symbolic output.
        canonical_basis := List(basis_d3, b -> b[1])
    );
end;;

# ----------------------------------------------------------------------
# Step 4: Evaluate a bar 3-cocycle on a fixed list of triples.
#
# Given a function f : G^3 -> Z/q and a list of triples T = [(g1, g2, g3), ...],
# returns the vector [f(g1, g2, g3) for each triple] mod 2.
# ----------------------------------------------------------------------

EvaluateBar3CocycleOnTriples := function(f, T)
    return List(T, t -> f(t[1], t[2], t[3]) mod 2);
end;;

# Build the coboundary matrix: rows are delta(beta) for beta = each
# F_2-basis 2-cochain on G. There are |G|^2 such cochains; the matrix
# has |G|^2 rows and |T| columns.
#
# A 2-cochain beta : G x G -> F_2 has |G|^2 free parameters. The k-th
# basis cochain is the indicator of the k-th (g1, g2) pair (in the
# enumeration Elements(G)). Its coboundary is
#   delta(beta_{ij})(a, b, c) = beta(b, c) - beta(a*b, c) + beta(a, b*c)
#                              - beta(a, b)
# At F_2 the signs disappear: it's a sum of four terms.
#
# Implementation: build each row as a transient list of length T_size,
# then convert to GF(2) compact form. This avoids allocating |G|^2
# unconverted full-precision rows simultaneously.
BuildCoboundaryRowsF2 := function(G, T)
    local elts, n, idx_dict, i, j, T_size, t, a, b, c, ij_ab, ij_bc,
          rows, beta_idx, row, indicator, contributions, contrib_t,
          row_idx, k, row_int, contributions_per_row;
    elts := Elements(G);
    n := Length(elts);
    idx_dict := NewDictionary(elts[1], true, elts);
    for i in [1..n] do AddDictionary(idx_dict, elts[i], i); od;

    T_size := Length(T);

    # First pass: for each triple t, compute the four (beta_idx)'s
    # contributing. Store as a list `contributions` of length T_size,
    # each entry a list of 4 beta indices that toggle for that triple.
    Print("    [coboundary] computing per-triple contributions...\n");
    contributions := [];
    for t in [1..T_size] do
        a := T[t][1]; b := T[t][2]; c := T[t][3];
        Add(contributions, [
            (LookupDictionary(idx_dict, b) - 1) * n
                + LookupDictionary(idx_dict, c),
            (LookupDictionary(idx_dict, a*b) - 1) * n
                + LookupDictionary(idx_dict, c),
            (LookupDictionary(idx_dict, a) - 1) * n
                + LookupDictionary(idx_dict, b*c),
            (LookupDictionary(idx_dict, a) - 1) * n
                + LookupDictionary(idx_dict, b)
        ]);
    od;

    # Second pass: invert the index. For each beta_idx (= row idx), find
    # the list of triple t's where this row contributes (with parity).
    # contribs_per_row[row_idx] is a list of integers t_1, t_2, ... where
    # multiplicity matters (we'll mod 2 when building the row).
    Print("    [coboundary] inverting index (row -> list of columns)...\n");
    contributions_per_row := List([1..n*n], i -> []);
    for t in [1..T_size] do
        for k in [1..4] do
            Add(contributions_per_row[contributions[t][k]], t);
        od;
    od;

    # Third pass: build each row as a sparse F_2 vector, convert to GF(2).
    Print("    [coboundary] materialising ", n*n, " rows in GF(2)...\n");
    rows := [];
    for row_idx in [1..n*n] do
        row_int := List([1..T_size], i -> 0);
        for t in contributions_per_row[row_idx] do
            row_int[t] := (row_int[t] + 1) mod 2;
        od;
        # Convert to GF(2) compact form.
        row := List(row_int, x -> x * Z(2)^0);
        ConvertToVectorRep(row, 2);
        Add(rows, row);
        if row_idx mod 1000 = 0 then
            Print("      [coboundary] row ", row_idx, " / ", n*n, "\n");
        fi;
    od;
    Print("    [coboundary] done.\n");
    return rec(
        rows    := rows,
        elts    := elts,
        idx_dict := idx_dict,
        n       := n
    );
end;;

# ----------------------------------------------------------------------
# Step 5: Solve x * M = b over F_2.
#
# Given matrix M (m × c) and vector b (length c), find x (length m)
# with x * M = b (mod 2). Returns x on success, fail otherwise.
#
# Uses GAP's compressed GF(2) matrices (ConvertToMatrixRep / GF(2)
# elements) for memory efficiency. Without compression, an n × c
# F_2 matrix takes 8 * n * c bytes; with compression it's roughly
# n * c / 8 bytes (a 64x reduction).
# ----------------------------------------------------------------------

# SolveF2RowSpanRaw expects M, b to be integer-valued (entries 0/1).
SolveF2RowSpanRaw := function(M, b)
    local m, c, sol, A, b_vec, row;
    if Length(M) = 0 then
        if ForAll(b, x -> x = 0) then return []; fi;
        return fail;
    fi;
    m := Length(M);
    c := Length(M[1]);
    # Convert M and b to GF(2) compact form.
    A := List(M, row -> List(row, x -> x * Z(2)^0));
    for row in A do ConvertToVectorRep(row, 2); od;
    b_vec := List(b, x -> x * Z(2)^0);
    ConvertToVectorRep(b_vec, 2);
    sol := SolutionMat(A, b_vec);
    if sol = fail then return fail; fi;
    return List(sol, x -> Int(x));
end;;

# SolveF2RowSpan expects M already in GF(2) compact form and b as
# integer-valued (entries 0/1). Returns x with x * M = b (mod 2) on
# success, fail otherwise.
SolveF2RowSpan := function(M_gf2, b)
    local sol, b_vec;
    if Length(M_gf2) = 0 then
        if ForAll(b, x -> x = 0) then return []; fi;
        return fail;
    fi;
    b_vec := List(b, x -> x * Z(2)^0);
    ConvertToVectorRep(b_vec, 2);
    sol := SolutionMat(M_gf2, b_vec);
    if sol = fail then return fail; fi;
    return List(sol, x -> Int(x));
end;;

# Fast solve using precomputed SemiEchelonMatTransformation.
# Given the SemiEchelon `sem` of matrix M and a target b, solve x · M = b.
# This is the inner loop of SolutionMat extracted, but reused across many
# b vectors with the same M.
#
# `b` is given as an integer 0/1 list. The function converts to GF(2)
# compact form internally.
SolveF2RowSpanFromSem := function(sem, b, n_rows)
    local ncols, z, sol, i, vno, x, vec, one;
    ncols := Length(b);
    z := Z(2) * 0;
    one := Z(2)^0;
    # Build sol as a mutable GF(2) compact zero vector.
    sol := ListWithIdenticalEntries(n_rows, z);
    ConvertToVectorRep(sol, 2);
    # Build vec from b. Using a single ConvertToVectorRep at the end is
    # the bottleneck-free path.
    vec := List(b, x -> x * one);
    ConvertToVectorRep(vec, 2);
    # Make sure vec is mutable.
    if not IsMutable(vec) then vec := ShallowCopy(vec); fi;
    for i in [1..ncols] do
        vno := sem.heads[i];
        if vno <> 0 then
            x := vec[i];
            if x <> z then
                AddRowVector(vec, sem.vectors[vno], -x);
                AddRowVector(sol, sem.coeffs[vno], x);
            fi;
        fi;
    od;
    if IsZero(vec) then
        return List(sol, y -> Int(y));
    else
        return fail;
    fi;
end;;

# ----------------------------------------------------------------------
# Step 6: Main bridge function.
#
# QuillenPolynomialOf(setup, i) — for setup = SetupCohomology3(EPlusGroup(m))
# and i in [1..Length(setup.UCT.cocyclebasis)].
#
# Returns a record (see file header).
#
# Implementation: builds the necessary data on first call (per setup);
# subsequent calls reuse cached F_2 basis homs + coboundary matrix.
# ----------------------------------------------------------------------

_QPB_CACHE := rec();;

# Helper to get/build the cached bridge data for a given setup.
_GetBridgeCache := function(setup)
    local G, m_inferred, m, key, h1_basis, polys, T, elts, n, sample_size,
          q_rows, q_eval, mon, q_func, coboundary_data, combined_M,
          combined_rows, n_polys, sol, poly_funcs;
    G := setup.group;
    # Infer m from |G|: |E_+(m)| = 2^{2m+1}.
    if Order(G) = 8 then m := 1;
    elif Order(G) = 32 then m := 2;
    elif Order(G) = 128 then m := 3;
    elif Order(G) = 512 then m := 4;
    elif Order(G) = 2048 then m := 5;
    else
        # Generic fallback: 2^{2m+1}.
        m_inferred := Log2Int(Order(G));
        if 2^m_inferred <> Order(G) or m_inferred < 3 or (m_inferred - 1) mod 2 <> 0 then
            Error("_GetBridgeCache: |G| = ", Order(G), " is not 2^{2m+1} for any m");
        fi;
        m := (m_inferred - 1) / 2;
    fi;
    key := Concatenation("m", String(m), "_o", String(Order(G)));
    if IsBound(_QPB_CACHE.(key)) then
        return _QPB_CACHE.(key);
    fi;

    # First call for this m: build everything.
    Print("  [bridge cache] building bridge data for m=", m,
          " (|G|=", Order(G), ")...\n");
    h1_basis := BasisH1F2(G, m);
    polys := QuillenPolynomialBasisForBridge(m);
    Print("  [bridge cache]   |h1_basis.homs| = ", Length(h1_basis.homs),
          ", |poly_candidates| = ", polys.n_candidates, "\n");

    # Build the triple set T. For m <= 2 use all of G^3; for m >= 3 use
    # a random sample large enough to discriminate cocycles on G^3.
    #
    # The discriminating power needs T_size >> dim Z^3. For E_+(3),
    # dim Z^3 = 16291 (= dim B^3 + dim H^3 = 16242 + 49); we use
    # T_size = 2 * (n^2 + n_polys) ≈ 32880 for safety margin.
    elts := Elements(G);
    n := Length(elts);
    if m <= 2 then
        T := Cartesian(elts, elts, elts);
    else
        # Use sample_size = round-up to nearest 5000 of 2.5 * (n^2 + n_polys).
        sample_size := QuoInt(5 * (n * n + polys.n_candidates), 2);
        sample_size := Minimum(sample_size, n * n * n);
        T := List([1..sample_size], i -> [Random(elts),
                                          Random(elts),
                                          Random(elts)]);
    fi;
    Print("  [bridge cache]   |T| = ", Length(T), " triples\n");

    # Evaluate polynomial cocycles on T, building rows directly in GF(2).
    # Precompute and cache the monomial cocycle functions (one per
    # candidate monomial). These are used both here and later when
    # evaluating the bridge's total cocycle on arbitrary triples.
    Print("  [bridge cache]   evaluating ", polys.n_candidates,
          " polynomial cocycles on T (GF(2) compact form)...\n");
    poly_funcs := [];
    q_rows := [];
    for mon in polys.candidates do
        q_func := MonomialToBarCocycleF2(h1_basis, mon);
        Add(poly_funcs, q_func);
        sol := List(T, t -> q_func(t[1], t[2], t[3]) mod 2);
        sol := List(sol, x -> x * Z(2)^0);
        ConvertToVectorRep(sol, 2);
        Add(q_rows, sol);
    od;
    n_polys := Length(q_rows);

    # Build the coboundary matrix (rows already in GF(2) form).
    Print("  [bridge cache]   building coboundary matrix ",
          "(", n*n, " rows × ", Length(T), " cols)...\n");
    coboundary_data := BuildCoboundaryRowsF2(G, T);

    # Combined matrix: polynomial rows first, then coboundary rows.
    combined_rows := Concatenation(q_rows, coboundary_data.rows);
    Print("  [bridge cache]   combined matrix: ", Length(combined_rows),
          " rows × ", Length(T), " cols (GF(2) compact)\n");

    _QPB_CACHE.(key) := rec(
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
        combined_rows  := combined_rows,
        n_polys        := n_polys,
        n_coboundary   := Length(coboundary_data.rows)
    );
    return _QPB_CACHE.(key);
end;;

# Bridge function: identify the i-th UCT.cocyclebasis entry as a
# polynomial in the canonical Quillen presentation.
QuillenPolynomialOf := function(setup, i)
    local cache, e_vec, omega_i, phi_i_vals, sol, poly_coeffs,
          coboundary_coeffs, beta_func, poly_repr, poly_str, k, mon,
          poly_cocycle, total_cocycle, q_mod, generator_order, kind,
          combined_solution, contributions;

    if not (IsInt(i) and i >= 1 and i <= setup.num_generators) then
        Error("QuillenPolynomialOf: i must be in [1..",
              setup.num_generators, "], got ", i);
    fi;

    cache := _GetBridgeCache(setup);
    generator_order := setup.torsion[i];

    # Build omega_i = StandardCocycleOf(setup, e_i) and reduce mod the
    # appropriate modulus.
    e_vec := List([1..setup.num_generators], k -> 0);
    e_vec[i] := 1;
    omega_i := StandardCocycleOf(setup, e_vec);
    q_mod := setup.exponent;

    # ------------------------------------------------------------------
    # Case 1: order-2 generator (Z/2 class). Match in F_2 cohomology.
    # ------------------------------------------------------------------
    if generator_order = 2 then
        kind := "F2_polynomial";

        # IMPORTANT: HAP's StandardCocycle returns values in Z/exponent
        # (= 8 at m=2, = 4 at m=3). For an order-2 generator, the values
        # live in (exponent / 2) * {0, 1} ⊂ Z/exponent. To get the
        # underlying F_2 cocycle, we divide by (exponent / 2) and reduce
        # mod 2.
        #
        # Concretely: omega_i takes values in {0, 4} (mod 8) at m=2.
        # We define phi_i := omega_i / (exponent / 2) mod 2.
        phi_i_vals := List(cache.T, t ->
            (omega_i(t[1], t[2], t[3]) / (q_mod / 2)) mod 2);

        # Solve combined_rows * x = phi_i over F_2.
        # We want x of length n_polys + n_coboundary.
        sol := SolveF2RowSpan(cache.combined_rows, phi_i_vals);
        if sol = fail then
            return rec(
                bridge_kind     := "F2_polynomial",
                order           := 2,
                modulus         := 2,
                error           := "no F_2 polynomial representation found",
                cocycle         := omega_i,
                poly_repr       := fail,
                poly_str        := "FAIL",
                coboundary      := fail
            );
        fi;

        poly_coeffs       := sol{[1..cache.n_polys]};
        coboundary_coeffs := sol{[cache.n_polys + 1..Length(sol)]};

        # Build the symbolic polynomial poly_repr as a Quillen element.
        # Note: poly_repr is expressed in our elementary basis x_1,..,x_{2m}
        # (the indicator homs on GeneratorsOfGroup(G) listed below the
        # commutator subgroup). It is NOT generally in canonical Quillen
        # form -- to reach that form one would have to perform a
        # symplectic-basis change for the quadratic form Q on V = G/Z.
        # For symbolic output we keep the raw form. See the file header
        # for the basis convention.
        poly_repr := QuillenZero();
        for k in [1..cache.n_polys] do
            if poly_coeffs[k] = 1 then
                poly_repr := QuillenAddElements(cache.polys.algebra,
                    poly_repr,
                    [cache.polys.candidates[k]]);
            fi;
        od;
        poly_str := QuillenElementToString(cache.polys.algebra, poly_repr);

        # Build the polynomial-derived bar cocycle (as F_2 callable).
        # Uses the cached precomputed monomial-cocycle functions.
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

        # Build the coboundary correction beta : G x G -> F_2.
        beta_func := function(g1, g2)
            local elts, n, k, idx_g1, idx_g2;
            elts := cache.elts;
            n := cache.n;
            idx_g1 := LookupDictionary(cache.coboundary_data.idx_dict, g1);
            idx_g2 := LookupDictionary(cache.coboundary_data.idx_dict, g2);
            k := (idx_g1 - 1) * n + idx_g2;
            return coboundary_coeffs[k];
        end;

        # Total cocycle: (poly + delta(beta)) mod 2, then scaled back
        # to Z/exponent to match the original HAP encoding. For an
        # order-2 generator with exponent=q, the encoded value is
        #   omega_i(g1,g2,g3) ∈ {0, q/2} ⊂ Z/q.
        # So total_cocycle returns (poly + delta(beta)) * (q/2) mod q.
        total_cocycle := function(g1, g2, g3)
            local pv, db, raw;
            pv := poly_cocycle(g1, g2, g3);
            # delta(beta)(g1, g2, g3) =
            #   beta(g2, g3) - beta(g1*g2, g3) + beta(g1, g2*g3) - beta(g1, g2).
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
            algebra       := cache.polys.algebra
        );
    fi;

    # ------------------------------------------------------------------
    # Case 2: top-torsion generator (Z/4 at m=3, Z/8 at m=2).
    #
    # This is the Pontryagin square of the Quillen polynomial generator w
    # at m=1 (deg(w) = 2) — but at m >= 2, deg(w) = 2^m >= 4 so w
    # doesn't appear at deg 3 directly. The Z/8 (m=2) or Z/4 (m=3)
    # generator instead arises from the integral Bockstein of a deg-2
    # F_2 class (or from a Pontryagin-square construction on F_2-degree-2
    # generators), which lives in H^4(G; Z) and corresponds (via
    # 0 -> Z -> R -> U(1) -> 0) to a class in H^3(G; U(1)).
    #
    # We do NOT yet have a symbolic polynomial form for this case (it
    # requires Stage B2 Pontryagin square construction). For now we
    # return the HAP cocycle as-is, flagged as bridge_kind = "pontryagin_top".
    # ------------------------------------------------------------------

    return rec(
        bridge_kind   := "pontryagin_top",
        order         := generator_order,
        modulus       := generator_order,
        poly_repr     := fail,
        poly_str      := Concatenation("P(generator at order ",
                                       String(generator_order), ")"),
        poly_coeffs   := fail,
        coboundary    := fail,
        cocycle       := omega_i,
        algebra       := cache.polys.algebra,
        note          := "top-torsion (Pontryagin square); symbolic ",
        note2         := "polynomial form not implemented (Stage B2)"
    );
end;;

# ----------------------------------------------------------------------
# Verification helper: check that the bridge result's cocycle agrees
# with StandardCocycleOf(setup, e_i) on a sample of triples. Returns
# the number of mismatches (0 = perfect).
#
# Two-argument form: VerifyQuillenBridge(setup, i, sample_size) builds
# the bridge result internally (re-solves the linear system).
# Three-argument form: VerifyQuillenBridgeOf(result, setup, i, sample_size)
# accepts a precomputed bridge result, for amortising the solve cost.
# ----------------------------------------------------------------------

VerifyQuillenBridgeOf := function(result, setup, i, sample_size)
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

VerifyQuillenBridge := function(setup, i, sample_size)
    local result;
    result := QuillenPolynomialOf(setup, i);
    return VerifyQuillenBridgeOf(result, setup, i, sample_size);
end;;

# ----------------------------------------------------------------------
# Diagnostic: build a comprehensive report for all generators in `setup`.
#
# Returns a record .results (list of QuillenPolynomialOf records, one
# per generator) and .summary (a string-rendered table). The summary
# is also printed to stdout.
# ----------------------------------------------------------------------

QuillenPolynomialBridgeReport := function(setup, sample_size)
    local results, i, r, n_mismatch, status, summary_lines, line;
    Print("\n=== Quillen polynomial bridge report ===\n");
    Print("  G = ", StructureDescription(setup.group),
          ", |G| = ", Order(setup.group), "\n");
    Print("  torsion = ", setup.torsion, "\n");
    Print("  exponent = ", setup.exponent, "\n");
    Print("  num_generators = ", setup.num_generators, "\n\n");

    results := [];
    summary_lines := [];
    for i in [1..setup.num_generators] do
        r := QuillenPolynomialOf(setup, i);
        n_mismatch := VerifyQuillenBridgeOf(r, setup, i, sample_size);
        status := If_(n_mismatch = 0, "OK", "MISMATCH");
        line := Concatenation(
            "  e_", String(i),
            "  order=", String(r.order),
            "  kind=", r.bridge_kind,
            "  mismatches=", String(n_mismatch), "/", String(sample_size),
            "  poly = ", r.poly_str);
        Print(line, "  [", status, "]\n");
        Add(summary_lines, line);
        Add(results, rec(
            i := i,
            order := r.order,
            kind := r.bridge_kind,
            poly_str := r.poly_str,
            n_mismatch := n_mismatch,
            ok := (n_mismatch = 0)
        ));
    od;

    Print("\n=== Summary ===\n");
    Print("  Total generators: ", Length(results), "\n");
    Print("  All-zero-mismatch: ",
          Number(results, r -> r.ok), " / ", Length(results), "\n");

    return rec(
        results := results,
        summary_lines := summary_lines
    );
end;;

Print("Loaded cocyclebasis_quillen_bridge.g (Q-int A4: QuillenPolynomialOf, ",
      "VerifyQuillenBridge, QuillenPolynomialBridgeReport).\n");
