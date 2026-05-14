# quillen_algebra.g — Polynomial-times-exterior graded algebra over F_2.
#
# Issue Q-1 / GitHub #8 / Task #34. See
# `extraspecial_orbifolds/parallel_workstreams_design.md` § Q-1 (line 150).
#
# Background. The mod-2 cohomology of an extraspecial 2-group has the form
#
#     F_2[c, x_1, ..., x_{2m}] ⊗ Λ(y_1, ..., y_{2m})
#
# modulo Quillen relations [Qui71, Thm 5.4]. This module provides the
# data structure (graded F_2-algebra with polynomial part * exterior part
# / ideal of relations) needed by the rest of workstream Q. The actual
# Quillen relations specific to E_+(m) are deferred to Q-2; this file
# provides only the generic engine.
#
# Representation.
#   * A "monomial" is a record  rec(sym := [e_1, ..., e_{n_sym}],
#                                   ext := <sorted list of indices>)
#     with sym a list of non-negative integer exponents and ext a
#     sorted list of distinct indices in [1..n_ext]. Over F_2 the
#     exterior square is zero (y_i ∧ y_i = 0), so ext is naturally a
#     subset of {1, ..., n_ext}; the sign is always +1 in F_2.
#   * An "element" is a SORTED list of such monomials (no duplicates).
#     The empty list represents 0. Over F_2 coefficients are implicit:
#     a monomial appearing in the list contributes +1 (mod 2).
#   * An "algebra" is a record with fields .sym_gens, .ext_gens (each a
#     list of rec(name, deg)), .relations (list of elements forming the
#     ideal), .is_quillen_algebra := true.
#
# Monomial ordering.  Graded lex on (total_degree, sym, ext). Inside a
# fixed homogeneous component this collapses to lex on (sym, ext); we
# rely on this for canonical form and for leading-monomial reduction.
#
# Reduction modulo the ideal.  Iteratively: while some monomial of f is
# divisible by the leading monomial of some relation r, subtract the
# appropriate multiple of r from f. This terminates because every
# subtraction strictly decreases the largest monomial (in the graded
# order) of f, and within bounded degree the monomial set is finite.
# `QuillenReduce` gives a normal form modulo the leading-term reduction
# rule, NOT a canonical form modulo the whole ideal; the two coincide
# only when the relations form a Gröbner basis.
#
# `BasisInDegree`, however, IS correct for arbitrary (non-Gröbner)
# relations. It uses the ideal-span method: directly enumerate
# {r · μ : r ∈ relations, deg(r · μ) = d}, row-reduce them, and read
# off the basis of the quotient as the non-pivot monomials of S_d.
# This works regardless of whether the relations are Gröbner-reduced;
# the Q-2a canonical Quillen presentation and the Q-2a Jena
# transcription both rely on this property (their relations are
# regular sequences in S(V*) per [Q4] Cor 2.6 but NOT Gröbner bases —
# e.g. for E_+(2) the S-polynomial S(Q, B(x,x²)) generates a new
# ideal element).

# ---- F_2 linear algebra (local copy; we do NOT pull in qforms_f2.g
# to keep this module self-contained) ---------------------------------

QuillenF2Mod := function(M)
    return List(M, row -> List(row, x -> x mod 2));
end;;

QuillenF2RowAdd := function(r1, r2)
    return List([1..Length(r1)], i -> (r1[i] + r2[i]) mod 2);
end;;

QuillenF2RREF := function(M)
    local A, m, n, pivots, r, c, i, k;
    A := QuillenF2Mod(M);
    m := Length(A);
    if m = 0 then return rec(rref := [], pivots := [], rank := 0); fi;
    n := Length(A[1]);
    pivots := [];
    r := 1;
    for c in [1..n] do
        if r > m then break; fi;
        i := r;
        while i <= m and A[i][c] = 0 do i := i + 1; od;
        if i > m then continue; fi;
        if i <> r then
            A{[r, i]} := A{[i, r]};
        fi;
        for k in [1..m] do
            if k <> r and A[k][c] = 1 then
                A[k] := QuillenF2RowAdd(A[k], A[r]);
            fi;
        od;
        Add(pivots, c);
        r := r + 1;
    od;
    return rec(rref := A, pivots := pivots, rank := Length(pivots));
end;;

# ---- Monomial-level utilities ----------------------------------------

# Create the multiplicative identity monomial 1.
QuillenOneMonomial := function(n_sym)
    return rec(sym := List([1..n_sym], i -> 0), ext := []);
end;;

# Total degree of a monomial in the algebra A.
QuillenMonomialDegree := function(A, mon)
    local d, i;
    d := 0;
    for i in [1..A.n_sym] do
        d := d + mon.sym[i] * A.sym_gens[i].deg;
    od;
    for i in mon.ext do
        d := d + A.ext_gens[i].deg;
    od;
    return d;
end;;

# Compare two monomials by graded lex with the EXTERIOR part more
# significant than the symmetric part. Returns -1, 0, +1 for
# a < b, a = b, a > b.
#
# The choice (ext before sym) makes monomials with more exterior
# letters "larger". Combined with leading-monomial reduction, a
# relation of the form y_1 y_2 - c = 0 (degree 2) thus rewrites the
# leading monomial y_1 y_2 down to c, which is the natural Quillen
# identification: exterior squares of degree-1 classes equal the
# Bockstein-like polynomial generator. Concretely, this means our
# canonical forms preserve the "polynomial part" wherever possible.
QuillenCompareMonomials := function(A, a, b)
    local da, db;
    da := QuillenMonomialDegree(A, a);
    db := QuillenMonomialDegree(A, b);
    if da < db then return -1; fi;
    if da > db then return  1; fi;
    if a.ext < b.ext then return -1; fi;
    if a.ext > b.ext then return  1; fi;
    if a.sym < b.sym then return -1; fi;
    if a.sym > b.sym then return  1; fi;
    return 0;
end;;

# `lt`-style comparator for use with Sort/SortedList.
QuillenLTMonomial := function(A)
    return function(a, b) return QuillenCompareMonomials(A, a, b) < 0; end;
end;;

# Equality check: structurally identical sym and ext.
QuillenMonomialsEqual := function(a, b)
    return a.sym = b.sym and a.ext = b.ext;
end;;

# Multiply two monomials. Returns either a record (the canonical
# product monomial) or `fail` if the product is zero (because some
# exterior index would be repeated).
QuillenMultiplyMonomials := function(a, b)
    local sym, ext, i, n_sym;
    n_sym := Length(a.sym);
    sym := List([1..n_sym], i -> a.sym[i] + b.sym[i]);
    # exterior part: union of disjoint sets, else 0
    for i in b.ext do
        if i in a.ext then return fail; fi;
    od;
    ext := Set(Concatenation(a.ext, b.ext));   # already disjoint, gives sorted
    return rec(sym := sym, ext := ext);
end;;

# Test divisibility: does monomial `divisor` divide `dividend` ?
# Sym part: every divisor exponent ≤ dividend exponent. Ext part:
# divisor.ext is a subset of dividend.ext.
QuillenMonomialDivides := function(divisor, dividend)
    local i;
    for i in [1..Length(divisor.sym)] do
        if divisor.sym[i] > dividend.sym[i] then return false; fi;
    od;
    return IsSubset(dividend.ext, divisor.ext);
end;;

# Quotient monomial dividend / divisor (assumes divisibility was checked).
# For the exterior part the quotient is dividend.ext \ divisor.ext, and
# the F_2 sign is +1 (no signs to track in characteristic 2).
QuillenDivideMonomials := function(dividend, divisor)
    local sym, ext, i;
    sym := List([1..Length(dividend.sym)],
                i -> dividend.sym[i] - divisor.sym[i]);
    ext := Filtered(dividend.ext, i -> not (i in divisor.ext));
    return rec(sym := sym, ext := ext);
end;;

# ---- Element-level utilities -----------------------------------------
#
# An element is a sorted list of monomials with implicit coefficient 1.
# All combination is over F_2: cancellation = symmetric difference.

# Helper: given a sorted list of monomials (possibly with duplicates),
# return the F_2 canonical form by cancelling adjacent equal pairs.
QuillenCanonicaliseSorted := function(sorted_list)
    local out, i, n;
    out := [];
    i := 1;
    n := Length(sorted_list);
    while i <= n do
        if i < n and QuillenMonomialsEqual(sorted_list[i], sorted_list[i+1]) then
            i := i + 2;   # cancel
        else
            Add(out, sorted_list[i]);
            i := i + 1;
        fi;
    od;
    return out;
end;;

# Zero element.
QuillenZero := function() return []; end;;

# One element of the algebra.
QuillenOne := function(A)
    return [QuillenOneMonomial(A.n_sym)];
end;;

# Add two elements over F_2 (symmetric difference of monomial sets).
# Both inputs must be sorted by QuillenCompareMonomials. The output
# is sorted as well.
QuillenAddElements := function(A, e1, e2)
    local out, i, j, c;
    out := [];
    i := 1;
    j := 1;
    while i <= Length(e1) and j <= Length(e2) do
        c := QuillenCompareMonomials(A, e1[i], e2[j]);
        if   c < 0 then Add(out, e1[i]); i := i + 1;
        elif c > 0 then Add(out, e2[j]); j := j + 1;
        else                              i := i + 1; j := j + 1;   # cancel mod 2
        fi;
    od;
    while i <= Length(e1) do Add(out, e1[i]); i := i + 1; od;
    while j <= Length(e2) do Add(out, e2[j]); j := j + 1; od;
    return out;
end;;

# Multiply an element by a single monomial (no reduction).
QuillenScaleByMonomial := function(A, e, m)
    local out, p, mon, lt;
    out := [];
    for mon in e do
        p := QuillenMultiplyMonomials(mon, m);
        if p <> fail then Add(out, p); fi;
    od;
    lt := QuillenLTMonomial(A);
    Sort(out, lt);
    # over F_2 the multiset can collapse: take symmetric difference
    return QuillenCanonicaliseSorted(out);
end;;

# Multiply two elements (no reduction). The naive distributive product:
# every pair of monomials, multiplied, then sorted and F_2-cancelled.
QuillenMultiplyElementsRaw := function(A, e1, e2)
    local prods, m1, m2, p, lt;
    prods := [];
    for m1 in e1 do
        for m2 in e2 do
            p := QuillenMultiplyMonomials(m1, m2);
            if p <> fail then Add(prods, p); fi;
        od;
    od;
    lt := QuillenLTMonomial(A);
    Sort(prods, lt);
    return QuillenCanonicaliseSorted(prods);
end;;

# Leading (largest) monomial of an element, or fail if zero.
QuillenLeadingMonomial := function(e)
    if Length(e) = 0 then return fail; fi;
    return e[Length(e)];
end;;

# Reduce element `e` modulo the ideal generated by `relations` (a list
# of elements). Iteratively rewrite: if some monomial of e is divisible
# by the leading monomial of some relation r, subtract the appropriate
# multiple of r. Terminates because each rewrite strictly reduces the
# largest monomial of e in the graded order, and within fixed total
# degree the monomial set is finite.
QuillenReduce := function(A, e, relations)
    local progress, e_curr, k, mon, r, lm, q, scaled, did_step;
    e_curr := e;
    progress := true;
    while progress do
        progress := false;
        # Walk monomials from the LARGEST downwards.
        k := Length(e_curr);
        while k >= 1 do
            mon := e_curr[k];
            did_step := false;
            for r in relations do
                lm := QuillenLeadingMonomial(r);
                if lm <> fail and QuillenMonomialDivides(lm, mon) then
                    q := QuillenDivideMonomials(mon, lm);
                    scaled := QuillenScaleByMonomial(A, r, q);
                    e_curr := QuillenAddElements(A, e_curr, scaled);
                    progress := true;
                    did_step := true;
                    break;
                fi;
            od;
            if did_step then break; fi;   # restart outer while
            k := k - 1;
        od;
    od;
    return e_curr;
end;;

# ---- Sym-multidegree enumeration helper ------------------------------

# Recursive enumerator for QuillenSymCompositions. Mutates `out`.
QuillenSymCompositionsRec := function(weights, n, idx, remaining, partial, out)
    local k, max_k, partial_new;
    if idx > n then
        if remaining = 0 then Add(out, ShallowCopy(partial)); fi;
        return;
    fi;
    if idx = n then
        # last slot: must absorb all remaining degree exactly
        if remaining mod weights[idx] = 0 then
            partial_new := ShallowCopy(partial);
            Add(partial_new, remaining / weights[idx]);
            Add(out, partial_new);
        fi;
        return;
    fi;
    max_k := QuoInt(remaining, weights[idx]);
    for k in [0..max_k] do
        partial_new := ShallowCopy(partial);
        Add(partial_new, k);
        QuillenSymCompositionsRec(weights, n, idx + 1,
            remaining - k * weights[idx], partial_new, out);
    od;
end;;

# Enumerate all non-negative integer vectors v of length A.n_sym with
# sum_i v[i] * A.sym_gens[i].deg = target. If A.n_sym = 0 the only
# vector is the empty one, valid iff target = 0.
QuillenSymCompositions := function(A, target)
    local out, n, weights;
    n := A.n_sym;
    weights := List(A.sym_gens, g -> g.deg);
    out := [];
    if n = 0 then
        if target = 0 then Add(out, []); fi;
        return out;
    fi;
    QuillenSymCompositionsRec(weights, n, 1, target, [], out);
    return out;
end;;

# Enumerate every monomial of total degree exactly d.
QuillenAllMonomialsOfDegree := function(A, d)
    local results, ext_subsets, esub, ext_deg, sym_part, sym_combos, i, lt;

    ext_subsets := Combinations([1..A.n_ext]);

    results := [];
    for esub in ext_subsets do
        ext_deg := 0;
        for i in esub do ext_deg := ext_deg + A.ext_gens[i].deg; od;
        if ext_deg > d then continue; fi;
        sym_combos := QuillenSymCompositions(A, d - ext_deg);
        for sym_part in sym_combos do
            Add(results, rec(sym := sym_part, ext := esub));
        od;
    od;
    lt := QuillenLTMonomial(A);
    Sort(results, lt);
    return results;
end;;

# ---- Public API ------------------------------------------------------

# Constructor.
#
# sym_gens : list of records rec(name := <string>, deg := <pos int>)
#            for the polynomial generators.
# ext_gens : list of records rec(name := <string>, deg := <pos int>)
#            for the exterior generators.
# relations: list of elements, each a homogeneous polynomial in the
#            free quillen-algebra. The ideal they generate is quotiented
#            out. May be the empty list.
PolynomialTimesExterior := function(sym_gens, ext_gens, relations)
    local A, normalised, lt, r, sorted;
    A := rec(
        sym_gens          := sym_gens,
        ext_gens          := ext_gens,
        n_sym             := Length(sym_gens),
        n_ext             := Length(ext_gens),
        relations         := [],
        is_quillen_algebra := true
    );
    lt := QuillenLTMonomial(A);
    normalised := [];
    for r in relations do
        sorted := ShallowCopy(r);
        Sort(sorted, lt);
        sorted := QuillenCanonicaliseSorted(sorted);
        if Length(sorted) > 0 then Add(normalised, sorted); fi;
    od;
    A.relations := normalised;
    return A;
end;;

# Build the element corresponding to a single sym generator (returns x_i).
QuillenSymGenerator := function(A, i)
    local mon;
    mon := QuillenOneMonomial(A.n_sym);
    mon.sym[i] := 1;
    return [mon];
end;;

# Build the element corresponding to a single ext generator (returns y_j).
QuillenExtGenerator := function(A, j)
    return [rec(sym := List([1..A.n_sym], i -> 0), ext := [j])];
end;;

# Multiply two elements and reduce mod the ideal. This is the public
# multiplication operation. The acceptance criterion in the issue calls
# this "Multiply(a, b)" but we expose the algebra-aware form
# "QuillenMultiply(A, a, b)" to avoid global-name collisions.
QuillenMultiply := function(A, e1, e2)
    return QuillenReduce(A, QuillenMultiplyElementsRaw(A, e1, e2), A.relations);
end;;

# Return an F_2-basis of the degree-d component of A. Each basis
# element is the singleton [m_i] where m_i is a representative monomial.
#
# Strategy (ideal-span method): the degree-d component of S/J is
# S_d / (J ∩ S_d), so we compute J ∩ S_d directly by enumerating
# {r · μ : r ∈ relations, deg(r · μ) = d}, expressing each as a row
# vector indexed by S_d's monomial basis, and RREF'ing to find the
# pivot positions. Non-pivot monomials of S_d form a basis of the
# quotient.
#
# Why not the per-monomial-reduce-then-row-reduce approach: that gives
# correct dims only when the relations are Gröbner-reduced. The Q-2a
# canonical Quillen presentation and the Jena transcription both
# supply minimal relation sets that are regular sequences but NOT
# Gröbner bases (the S-polynomial S(Q, B(x,x²)) generates a new
# normal-form monomial not detected by per-monomial reduction). The
# ideal-span method handles this correctly because it never relies
# on reductions being unique.
#
# Assumes relations are HOMOGENEOUS (which the constructor expects),
# so each r·μ has total degree d.
BasisInDegree := function(A, d)
    local mons, idx_of, lt, row_matrix, r, deg_r, mu_deg, mu, scaled,
          row, mon, rref, pivot_cols, basis_elts, i;

    mons := QuillenAllMonomialsOfDegree(A, d);
    if Length(mons) = 0 then return []; fi;

    lt := QuillenLTMonomial(A);
    idx_of := function(target)
        local lo, hi, mid, c;
        lo := 1; hi := Length(mons);
        while lo <= hi do
            mid := QuoInt(lo + hi, 2);
            c := QuillenCompareMonomials(A, mons[mid], target);
            if   c = 0 then return mid;
            elif c < 0 then lo := mid + 1;
            else            hi := mid - 1;
            fi;
        od;
        return fail;
    end;

    # Build the matrix W whose rows span J ∩ S_d: for each relation r
    # and each monomial μ with deg(r · μ) = d, the product r · μ
    # becomes one row.
    row_matrix := [];
    for r in A.relations do
        # Relations are homogeneous; degree = degree of any monomial.
        deg_r := QuillenMonomialDegree(A, r[1]);
        mu_deg := d - deg_r;
        if mu_deg < 0 then continue; fi;
        for mu in QuillenAllMonomialsOfDegree(A, mu_deg) do
            scaled := QuillenScaleByMonomial(A, r, mu);
            if Length(scaled) = 0 then continue; fi;
            row := List([1..Length(mons)], k -> 0);
            for mon in scaled do row[idx_of(mon)] := 1; od;
            Add(row_matrix, row);
        od;
    od;

    if Length(row_matrix) = 0 then
        return List(mons, m -> [m]);
    fi;

    rref := QuillenF2RREF(row_matrix);
    pivot_cols := [];
    for i in [1..rref.rank] do
        row := rref.rref[i];
        Add(pivot_cols, First([1..Length(row)], j -> row[j] = 1));
    od;

    basis_elts := [];
    for i in [1..Length(mons)] do
        if not (i in pivot_cols) then
            Add(basis_elts, [mons[i]]);
        fi;
    od;
    return basis_elts;
end;;

# Dimension of the degree-d component (convenience).
DimensionInDegree := function(A, d)
    return Length(BasisInDegree(A, d));
end;;

# ---- Pretty-printing (debug aid) -------------------------------------

QuillenMonomialToString := function(A, mon)
    local s, i, parts;
    parts := [];
    for i in [1..A.n_sym] do
        if mon.sym[i] > 0 then
            if mon.sym[i] = 1 then
                Add(parts, A.sym_gens[i].name);
            else
                Add(parts, Concatenation(A.sym_gens[i].name, "^",
                                         String(mon.sym[i])));
            fi;
        fi;
    od;
    for i in mon.ext do
        Add(parts, A.ext_gens[i].name);
    od;
    if Length(parts) = 0 then return "1"; fi;
    s := parts[1];
    for i in [2..Length(parts)] do s := Concatenation(s, "*", parts[i]); od;
    return s;
end;;

QuillenElementToString := function(A, e)
    local s, i;
    if Length(e) = 0 then return "0"; fi;
    s := QuillenMonomialToString(A, e[1]);
    for i in [2..Length(e)] do
        s := Concatenation(s, " + ", QuillenMonomialToString(A, e[i]));
    od;
    return s;
end;;

Print("Loaded quillen_algebra.g (Q-1: polynomial-times-exterior over F_2).\n");
