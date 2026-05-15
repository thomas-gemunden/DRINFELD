# quillen_bockstein.g — Stage A1 of the Quillen integration roadmap.
#
# Source: docs/superpowers/plans/2026-05-15-quillen-integration.md
# Task A1: "Document Bockstein action on Quillen generators".
#
# Provides the mod-2 Bockstein β: H^*(E_+(m); F_2) → H^*(E_+(m); F_2)
# as a derivation on the canonical Quillen presentation produced by
# `quillen_canonical_presentation.g` (Q-2a, issue #133).
#
# Conventions.
#   * The Quillen presentation has n_sym = 2m + 1 symmetric generators:
#     indices [1..2m] are x_1, ..., x_{2m} (each of degree 1), and
#     index 2m+1 is w (of degree 2^m).
#   * β satisfies the Leibniz rule β(uv) = β(u)v + uβ(v); over F_2
#     (where there are no signs) this is the usual derivation rule.
#   * β(x_i) = x_i² for all degree-1 classes (standard mod-2 result;
#     follows from H*(BZ/2; F_2) = F_2[x] with β(x) = x²).
#   * β(w) is m-dependent. For m = 1 (D_8) the Cohen-Quillen formula
#     gives β(w) = (x_1 + x_2) w (this is Sq¹(w) computed via Wu's
#     formula); for m ≥ 2 the explicit polynomial is not yet entered
#     in our table and BocksteinOnGenerator returns `fail` (Stage A2
#     work fills these in by cross-checking against HAP at m = 2, 3).
#
# The point of this file is to provide the algebraic machinery so that
# Stage A2 (integer torsion of H^4 via the Bockstein spectral sequence)
# reduces to a finite linear-algebra computation on the F_2 cohomology
# basis already given by `BasisInDegree(R, d)`.

if not IsBoundGlobal("PolynomialTimesExterior") then
    _qb_self := INPUT_FILENAME();;
    if _qb_self <> fail and _qb_self <> "stream" then
        _qb_dir := _qb_self{[1..Length(_qb_self) -
                          Length("/quillen_bockstein.g")]};;
        _qb_cand := Concatenation(_qb_dir, "/quillen_algebra.g");;
        if IsExistingFile(_qb_cand) then Read(_qb_cand); fi;
    fi;
    if not IsBoundGlobal("PolynomialTimesExterior")
       and IsExistingFile("quillen_algebra.g") then
        Read("quillen_algebra.g");
    fi;
fi;

# ---- m-inference from the Quillen algebra ---------------------------

# A Quillen canonical presentation R has n_sym = 2m + 1. Recover m.
_QB_InferM := function(R)
    local k;
    k := R.n_sym - 1;
    if k mod 2 <> 0 or k < 2 then
        Error("quillen_bockstein: algebra n_sym = ", R.n_sym,
              " is not of canonical Quillen E_+(m) shape (2m+1)");
    fi;
    return k / 2;
end;;

# ---- β on a single sym generator ------------------------------------

# β(x_i) = x_i^2 for i in [1..2m]. Returns a Quillen element (sorted,
# F_2-canonicalised list of monomials).
_QB_BocksteinOnX := function(R, i)
    local mon;
    mon := QuillenOneMonomial(R.n_sym);
    mon.sym[i] := 2;
    return [mon];
end;;

# β(w) for E_+(m). Hardcoded table; m = 1 is the Cohen-Quillen result,
# m >= 2 returns fail until Stage A2 derives the explicit polynomial
# (via HAP cross-check on m = 2, 3 followed by extrapolation to
# m = 5, 7 using the recursive structure of E_+).
#
# For m = 1: β(w) = (x_1 + x_2) w. As a sym-only element this is two
# monomials: x_1^1 x_2^0 w^1 = sym = [1, 0, 1] and x_1^0 x_2^1 w^1 =
# sym = [0, 1, 1] (n_sym = 3 = 2*1 + 1, w is index 3).
_QB_BocksteinOnW := function(R, m)
    local n_sym, w_idx, mon1, mon2;
    n_sym := R.n_sym;
    w_idx := n_sym;                              # w is always the last gen
    if m = 1 then
        # x_1 * w
        mon1 := QuillenOneMonomial(n_sym);
        mon1.sym[1]     := 1;
        mon1.sym[w_idx] := 1;
        # x_2 * w
        mon2 := QuillenOneMonomial(n_sym);
        mon2.sym[2]     := 1;
        mon2.sym[w_idx] := 1;
        return QuillenAddElements(R, [mon1], [mon2]);
    fi;
    # No formula yet for m >= 2 — flag at the call site so the caller
    # can decide between "compute the torsion via β-on-the-rest-only"
    # and "stop and ask".
    return fail;
end;;

# β on the i-th sym generator of the canonical Quillen presentation R.
# i in [1..2m]   -> x_i, β = x_i^2.
# i = 2m+1       -> w,   β looked up via _QB_BocksteinOnW (may be fail).
BocksteinOnGenerator := function(R, i)
    local m, w_idx;
    if not (IsRecord(R) and IsBound(R.is_quillen_algebra)
            and R.is_quillen_algebra = true) then
        Error("BocksteinOnGenerator: R must be a quillen algebra record");
    fi;
    if not (IsInt(i) and i >= 1 and i <= R.n_sym) then
        Error("BocksteinOnGenerator: i must be an integer in [1..", R.n_sym, "]");
    fi;
    m := _QB_InferM(R);
    w_idx := R.n_sym;
    if i < w_idx then
        return _QB_BocksteinOnX(R, i);
    fi;
    return _QB_BocksteinOnW(R, m);
end;;

# ---- β on a single monomial via the Leibniz rule --------------------

# Leibniz over F_2: β(x_1^{e_1} ... x_n^{e_n}) =
#   sum_{i : e_i is odd} (x_1^{e_1} ... x_i^{e_i - 1} ... x_n^{e_n}) * β(x_i).
# Even-exponent terms drop because e_i = 0 mod 2 in F_2 kills the
# binomial coefficient e_i in the Leibniz expansion. (Equivalently:
# β(x^2) = 2x β(x) = 0 in char 2.)
#
# The output is a Quillen element (canonical F_2 form). Returns `fail`
# if β on some required generator is fail and that generator's odd-
# exponent contribution is non-zero.
BocksteinOnMonomial := function(R, mon)
    local out, n_sym, i, exps_i, mon_minus, beta_gen, contribution;
    if not IsRecord(R) or not IsBound(R.is_quillen_algebra) then
        Error("BocksteinOnMonomial: R must be a quillen algebra record");
    fi;
    if not (IsRecord(mon) and IsBound(mon.sym) and IsBound(mon.ext)) then
        Error("BocksteinOnMonomial: mon must be a monomial record");
    fi;
    if Length(mon.ext) > 0 then
        # The canonical Quillen E_+(m) presentation has no exterior
        # generators; if a caller hands us one we don't know β on it.
        Error("BocksteinOnMonomial: monomial has ext generators; ",
              "β on exterior part is not defined in the Quillen ",
              "E_+(m) canonical presentation");
    fi;

    n_sym := R.n_sym;
    out := QuillenZero();
    for i in [1..n_sym] do
        exps_i := mon.sym[i];
        if exps_i mod 2 = 0 then continue; fi;
        beta_gen := BocksteinOnGenerator(R, i);
        if beta_gen = fail then
            # We don't know β on this generator, and this term contributes
            # (since e_i is odd). The whole β(mon) is therefore unknown.
            return fail;
        fi;
        # Build the "mon with e_i decremented" monomial.
        mon_minus := rec(
            sym := ShallowCopy(mon.sym),
            ext := ShallowCopy(mon.ext));
        mon_minus.sym[i] := exps_i - 1;
        contribution := QuillenMultiplyElementsRaw(R, [mon_minus], beta_gen);
        out := QuillenAddElements(R, out, contribution);
    od;
    return out;
end;;

# ---- β on an element (sum over its monomials) -----------------------

# Linear extension. Returns a Quillen element, reduced mod the ideal.
# Returns fail if any monomial's β returns fail.
BocksteinOnElement := function(R, e)
    local out, mon, beta_mon;
    out := QuillenZero();
    for mon in e do
        beta_mon := BocksteinOnMonomial(R, mon);
        if beta_mon = fail then return fail; fi;
        out := QuillenAddElements(R, out, beta_mon);
    od;
    # Reduce mod the ideal so the result is the unique normal form in the
    # quotient algebra (so far as the relations are Gröbner; for the
    # Q-2a presentation the relations are a regular sequence but not a
    # Gröbner basis, so the reduction gives a representative, not a
    # canonical form — downstream BasisInDegree-based linear algebra
    # handles equivalence robustly).
    return QuillenReduce(R, out, R.relations);
end;;

# ---- Predicate: is β fully known for E_+(m)? ------------------------

BocksteinAvailableOnW := function(m)
    return m = 1;
end;;

Print("Loaded quillen_bockstein.g ",
      "(BocksteinOnGenerator/Monomial/Element; β(w) only m=1).\n");
