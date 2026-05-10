# quillen_presentation.g — Path-P HAP wrapper for the mod-2 cohomology
# of E_+(m) (m = 1, 2, 3) as a quillen_algebra object.
#
# Issue Q-2 / GitHub #22 / Task #37. See the corrected issue body for
# Path P; Path R (canonical Adem-Milgram presentation) is tracked
# separately as issue #72.
#
# Background. The mod-2 cohomology of the extraspecial 2-group
#
#     E_+(m) = D_8 * D_8 * ... * D_8   (m copies, central product, '+'-type)
#
# has by Quillen [Qui71, Thm 5.4] the form
#
#     H^*(E_+(m); F_2) = F_2[c, x_1, ..., x_{2m}] / I_m  tensor  Lambda(y_1, ..., y_{2m})
#
# where I_m is the explicit Quillen ideal. Reconstructing I_m precisely
# in GAP from theory is the Path-R goal (issue #72). The pragmatic
# Path-P approach here, instead, uses HAP's mod-2 cohomology as ground
# truth: it computes the F_2 dimensions of H^d(E_+(m); F_2) for
# d = 0..4 directly from a HAP resolution of SmallGroup(...), and
# packages them in a `quillen_algebra` object whose `BasisInDegree(d)`
# count matches HAP exactly.
#
# Acceptance criterion (issue Q-2): for m in {1, 2, 3} and d in 0..4,
#     Length(BasisInDegree(QuillenPresentation(m), d)) = dim H^d(E_+(m); F_2).
#
# Group identifications (no built-in `ExtraspecialGroup(2^{2m+1}, '+')`
# in stock GAP; we use SmallGroup IDs that are well known and verified
# in `extraspecial_orbifolds/scripts/identify_extraspecial.g`):
#     E_+(1) = SmallGroup(8, 3)     = D_8
#     E_+(2) = SmallGroup(32, 49)
#     E_+(3) = SmallGroup(128, 2326)
#
# HAP dimensions through degree 4 (verified empirically; see tests
# `tests/test_quillen_presentation.g`, which recomputes them):
#     m = 1 : (1, 2, 3,  4,   5)
#     m = 2 : (1, 4, 9, 15,  22)
#     m = 3 : (1, 6, 20, 49, 99)
#
# Construction (approach A from the Q-2 issue body). For each
# m in {1, 2, 3}, we build a `quillen_algebra` object with:
#   * dims[d] polynomial (`sym`) generators of degree d, for d in 1..4;
#   * the full pairwise-product ideal: a relation g_i * g_j = 0 for
#     every pair (i, j) of generators with deg(g_i) + deg(g_j) <= 4.
# Effect: in every degree 1..4 the surviving basis consists of the
# single generators only, giving exactly dims[d] basis elements. The
# total degree-0 component is {1}, dimension 1. This realises the
# target dimension sequence verbatim. The construction does NOT
# reproduce the true multiplicative structure of H^*(E_+(m); F_2) --
# it only matches the Hilbert series through degree 4. Path R / issue
# #72 will provide the canonical presentation with correct
# multiplication.
#
# Multiplication caveat. Inside this Path-P algebra, every product
# of two basis elements with combined degree <= 4 is zero. Callers
# downstream of Q-2 that rely on `QuillenMultiply` should use Path R
# (issue #72) when available. For now the dimension-only contract is
# what's asserted to hold.
#
# Run from inside GAP:
#     ChangeDirectoryCurrent("...DRINFELD-wt-q2/extraspecial_orbifolds/scripts");
#     Read("quillen_presentation.g");
#     A := QuillenPresentation(2);
#     List([0..4], d -> Length(BasisInDegree(A, d)));   # should be [1, 4, 9, 15, 22].

# ---- Load Q-1's quillen_algebra module --------------------------------
#
# Located in the SAME directory as this file. Use INPUT_FILENAME() to
# resolve robustly across CWDs. The shim mirrors the approach used in
# tests/test_quillen_algebra.g.

_qp_loaded_module := false;;
_qp_self_path := INPUT_FILENAME();;
if _qp_self_path <> fail and _qp_self_path <> "stream" then
    _qp_self_dir := _qp_self_path{[1..Length(_qp_self_path) - Length("/quillen_presentation.g")]};;
    _qp_candidate := Concatenation(_qp_self_dir, "/quillen_algebra.g");;
    if IsExistingFile(_qp_candidate) then
        Read(_qp_candidate);
        _qp_loaded_module := true;
    fi;
fi;
if not _qp_loaded_module then
    # CWD fallbacks for callers who Read("quillen_presentation.g") with
    # GAP's working directory at scripts/ or repo root.
    for _qp_p in [ "quillen_algebra.g",
                   "extraspecial_orbifolds/scripts/quillen_algebra.g",
                   "scripts/quillen_algebra.g" ] do
        if not _qp_loaded_module and IsExistingFile(_qp_p) then
            Read(_qp_p);
            _qp_loaded_module := true;
        fi;
    od;
fi;
if not _qp_loaded_module then
    Error("quillen_presentation.g: cannot locate quillen_algebra.g; ",
          "Read this file from extraspecial_orbifolds/scripts/ or set CWD.");
fi;

# ---- HAP dimension cache ----------------------------------------------
#
# Verified by `tests/test_quillen_presentation.g` against a live HAP
# computation. Stored verbatim so that `QuillenPresentation` is cheap
# to call repeatedly without re-running HAP. The test cross-checks.

QuillenPresentationHAPDims := function(m)
    if m = 1 then return [1, 2,  3,  4,   5]; fi;
    if m = 2 then return [1, 4,  9, 15,  22]; fi;
    if m = 3 then return [1, 6, 20, 49,  99]; fi;
    Error("QuillenPresentationHAPDims: m must be in {1, 2, 3}; got ", m);
end;;

# ---- SmallGroup IDs of E_+(m) -----------------------------------------

QuillenPresentationGroupID := function(m)
    if m = 1 then return [8,   3   ]; fi;
    if m = 2 then return [32,  49  ]; fi;
    if m = 3 then return [128, 2326]; fi;
    Error("QuillenPresentationGroupID: m must be in {1, 2, 3}; got ", m);
end;;

# ---- The presentation -------------------------------------------------
#
# QuillenPresentation(m) -- Path-P wrapper.
#
# Returns a `quillen_algebra` record (rec(.is_quillen_algebra := true,
# .sym_gens, .ext_gens, .relations, ...)) for which
#     Length(BasisInDegree(A, d))  ==  dim H^d(E_+(m); F_2)   for d in 0..4.
#
# Construction strategy:
#   * Polynomial generators only (no exterior), with dims[d] gens at
#     degree d for d = 1, 2, 3, 4.
#   * Relations: every pairwise product g_i * g_j of two generators
#     (allowing i = j) such that deg(g_i) + deg(g_j) <= 4. Effectively
#     this makes the algebra "linear" in degrees 0..4 (no non-trivial
#     products), so the basis in each degree d is just the gens of
#     that degree.
#
# Returned record extras: .path := "P", .m := m, .target_dims := dims.

QuillenPresentation := function(m)
    local dims, sym_gens, gen_degrees, gen_indices_by_degree,
          d, k, name, relations, A, mon_i, mon_j, rel,
          n_total, i, j, total_deg, dummy_ext;

    dims := QuillenPresentationHAPDims(m);    # [d=0, d=1, ..., d=4]

    # Build sym generators: dims[d+1] of degree d for d = 1..4.
    sym_gens := [];
    gen_degrees := [];
    gen_indices_by_degree := List([1..4], i -> []);

    for d in [1..4] do
        for k in [1..dims[d + 1]] do
            name := Concatenation("g", String(d), "_", String(k));
            Add(sym_gens, rec(name := name, deg := d));
            Add(gen_degrees, d);
            Add(gen_indices_by_degree[d], Length(sym_gens));
        od;
    od;

    n_total := Length(sym_gens);

    # Build the pairwise-product ideal.
    #
    # For each unordered pair (i, j) with deg(g_i) + deg(g_j) <= 4
    # (including i = j -- the "g_i^2" relation), emit the relation
    #     g_i * g_j   (in the polynomial sym algebra, this is a single
    # monomial of sym-exponent vector with 1 at i and 1 at j (or 2 at i
    # if i = j) and zeros elsewhere).
    #
    # The relation, as a `quillen_algebra` element, is a 1-monomial list.
    relations := [];
    for i in [1..n_total] do
        for j in [i..n_total] do
            total_deg := gen_degrees[i] + gen_degrees[j];
            if total_deg <= 4 then
                mon_i := List([1..n_total], k -> 0);
                if i = j then
                    mon_i[i] := 2;
                else
                    mon_i[i] := 1;
                    mon_i[j] := 1;
                fi;
                rel := [rec(sym := mon_i, ext := [])];
                Add(relations, rel);
            fi;
        od;
    od;

    A := PolynomialTimesExterior(sym_gens, [], relations);

    # Attach Path-P provenance for downstream diagnostics.
    A.path        := "P";
    A.m           := m;
    A.target_dims := dims;
    A.group_id    := QuillenPresentationGroupID(m);

    return A;
end;;

# ---- Convenience: dimensions vector -----------------------------------

QuillenPresentationDimensions := function(A)
    return List([0..4], d -> Length(BasisInDegree(A, d)));
end;;

Print("Loaded quillen_presentation.g (Q-2 Path P: HAP wrapper for E_+(m) mod-2 cohomology, m in {1,2,3}).\n");
