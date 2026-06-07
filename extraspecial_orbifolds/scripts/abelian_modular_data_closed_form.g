# abelian_modular_data_closed_form.g
#
# Issue #487: closed-form (q_omega, b_omega) -> (S, T) for abelian H.
#
# Replaces the O(|H|^4) generic ComputeModularData(H, omega_fn, val, expon)
# call when H is abelian, dropping the construction cost to O(|H|^2) for
# the S-matrix and O(|H|) for the T-vector.
#
# Used by:
#   - ComputeUntwistedModularData (when H is abelian): replaces the
#     generic O(|H|^4) Bantay build with the analytical formula. This
#     is the headline use case (untwisted ω = 0).
#   - The e2e sweep at m=5 / m=7 (PR #488 / PR #489) — synthesises
#     modular data for each cohomology class on each EA in the
#     detecting family. EAs are elementary abelian 2-groups
#     (Z/2)^{m+1}; the formula matches legacy ComputeModularData on
#     V_4 = (Z/2)^2 across all 8 cohomology classes.
#
# Math (DGNO 2010, Naidu-Nikshych 2008):
#
# For abelian H and 3-cocycle omega : H^3 -> Z/N (i.e. actual phase is
# E(N)^{omega(a, b, c)}), define the quadratic form
#     q_omega(a)    := omega(a, a, a)               (integer in [0, N))
#     b_omega(a, b) := q_omega(a*b) - q_omega(a) - q_omega(b)   (integer)
#
# Both lift to Z/(2N) (NOT just Z/N) — the natural quadratic form
# associated to a 3-cocycle on an abelian group lives at modulus 2N,
# not N. This is a standard cohomological doubling: H^3(G; U(1)) for
# G abelian is in bijection with quadratic forms q : G -> Q/Z (whose
# associated bicharacter takes values in 1/N · Z/Z, but q itself takes
# values in 1/(2N) · Z/Z).
#
# The modular data of Z(Vec^omega_H) is then:
#     T_{(a, chi)}        = chi(a) * E(2N)^{q_omega(a)}
#     S_{(a,chi),(b,psi)} = (1/|H|) * psi(a)^{-1} * chi(b)^{-1}
#                           * E(2N)^{-b_omega(a, b)}
# where chi, psi range over the linear characters Hat(H) and a, b range
# over H. The simple-index lex order is outer over a, inner over chi.
#
# The sign of -b_omega(a, b) in the S-exponent (and the use of 2N rather
# than N in both the T- and S-exponents) is fixed by matching against
# the legacy ComputeModularData(H, omega, val, expon) on V_4 across all
# 8 cohomology classes — see tests/test_abelian_modular_data_closed_form.g.
#
# DOMAIN OF VALIDITY
# ------------------
# The closed-form formula assumes the 2-cocycle beta_a (a in H) derived
# from omega induces an ABELIAN central extension of H by Z/N — i.e.
# beta_a is symmetric for all a. Equivalently, all projective characters
# of (H, beta_a) are 1-dimensional, so the Drinfeld center has the
# canonical |H|^2 simples labelled (a, chi) with chi in Hat(H).
#
# This always holds:
#   * For untwisted omega = 0 (any abelian H). All |H|^2 simples are
#     1-dim. Matches legacy ComputeUntwistedModularData(H) on the
#     anchor tests for k = 1..5 in (Z/2)^k and Z/3, Z/4, Z/2 x Z/4.
#   * For H = (Z/2)^k with the "decomposable" cohomology classes
#     (products of degree-1 generators). On V_4 this covers ALL 8
#     classes; on (Z/2)^k with k >= 3 some classes give non-abelian
#     extensions and the rank of the legacy MTC drops below |H|^2.
#
# This may FAIL silently:
#   * For H = Z/n (n >= 3) with non-trivial omega: the projective
#     characters live at modulus n*N rather than 2N. The closed-form
#     T-multiset differs from legacy and JointPermutationMatcher
#     reports no match. Caller should use the generic builder.
#   * For H = (Z/2)^k with k >= 3 and the Bockstein/Steenrod-type
#     classes (where beta_a is alternating, inducing a non-abelian
#     extension like Q_8 x (Z/2)^{k-2}): the legacy MTC has fewer
#     than |H|^2 simples (due to higher-dim projective characters),
#     so the closed-form (which always produces |H|^2 1-dim simples)
#     represents a different MTC.
#
# Practical implication: this file is SAFE to wire into
# ComputeUntwistedModularData for abelian H (the omega = 0 case is
# always valid) but should NOT be used as a drop-in replacement for
# ComputeModularData with non-trivial omega outside (Z/2)^k k <= 2.
# Downstream consumers wanting twisted modular data on EAs should
# anchor against ComputeModularData on V_4 (or a representative EA
# subgroup of V_4 x ... x V_4) before trusting the result.
#
# SCALING (full S vs factored S)
# ------------------------------
# `ComputeAbelianModularDataFromQB` / `ComputeAbelianModularDataClosedForm`
# materialise the FULL |H|^2 x |H|^2 S-matrix. This is fine for k <= 6
# in (Z/2)^k (|H|^4 = 2^24 = 16M cyclotomic entries, ~few GB at most),
# but infeasible at k = 7 (|H|^4 = 2.7e8) and definitely k = 8
# (|H|^4 = 4.3e9). At k = 8 the storage would be ~100 GB+.
#
# For k = 7, 8 use the factored variant:
#   `ComputeAbelianModularDataFactored(H, omega_cocycle, modulus)`
# which returns a record with O(|H|^2) precomputed tables (the
# character-value table, q and b cocycle tables, T-vector) plus an
# `S_at(global_i, global_j)` accessor closure that computes any single
# S-entry in O(1). Total memory O(|H|^2), per-query time O(1).
#
# Conventions: matches the gauge used by ComputeModularData up to a
# permutation of simples; the equivalence is witnessed by
# JointPermutationMatcher.
#
# Refs: DGNO 2010 (Drinfeld center of fusion category); Naidu-Nikshych
# 2008 (twisted Drinfeld doubles of finite abelian groups); PR #487
# (this file).

if not IsBound(_LogStamped) then
    # standalone load fallback
    _LogStamped := function(args...) Print(args, "\n"); end;
fi;

DeclareGlobalFunction("ComputeAbelianModularDataClosedForm");
DeclareGlobalFunction("ComputeAbelianModularDataFromQB");
DeclareGlobalFunction("ComputeAbelianModularDataFactored");
DeclareGlobalFunction("AbelianModularDataSEntry");
DeclareGlobalFunction("AbelianModularDataTEntry");

# ---------------------------------------------------------------------
# Helper: enumerate the linear characters of an abelian group H.
# For abelian H every irrep is 1-dim, so Irr(CharacterTable(H)) gives
# the linear characters of H as class functions. The class-of-element
# dictionary maps each element of H to its class index (since each
# class is a singleton for abelian H, this is a labelling of elements).
#
# Returns rec(
#   H            : the abelian group H,
#   elems        : AsList(H) — fixed enumeration of elements,
#   n            : |H|,
#   chi          : Irr(CharacterTable(H)) — length-n list of class
#                  functions; chi[k][ci] is the value of the k-th
#                  linear character at the class with index ci.
#   class_of_elt : Dictionary mapping each element of H to its class
#                  index in [1..n]. For abelian H each class is a
#                  singleton, so this is effectively an element index.
# )
# ---------------------------------------------------------------------
_AbelianCharacterTable := function(H)
    local elems, n, tbl, cc, irr, k, class_of_elt, e, ci;
    if not IsAbelian(H) then
        Error("_AbelianCharacterTable: H must be abelian");
    fi;
    elems := AsList(H);
    n := Size(H);
    tbl := CharacterTable(H);
    cc := ConjugacyClasses(tbl);
    irr := Irr(tbl);
    if Length(irr) <> n then
        Error("_AbelianCharacterTable: |Irr(H)| = ", Length(irr),
              " != |H| = ", n, " — H is not actually abelian?");
    fi;
    # Build the elt -> class index lookup. For abelian H each class is
    # a singleton {a}; we map each element to its class index.
    class_of_elt := NewDictionary(elems[1], true);
    for ci in [1..Length(cc)] do
        for e in AsList(cc[ci]) do
            AddDictionary(class_of_elt, e, ci);
        od;
    od;
    return rec(
        H := H,
        elems := elems,
        n := n,
        chi := irr,
        class_of_elt := class_of_elt
    );
end;;

# ---------------------------------------------------------------------
# ComputeAbelianModularDataFromQB(H, q_omega, b_omega, modulus)
#
# Inputs:
#   H         : abelian group
#   q_omega   : list of length |H| indexed parallel to AsList(H);
#               q_omega[i] = omega(a_i, a_i, a_i)
#               (integer in any range; reduced mod 2*modulus internally).
#   b_omega   : |H| x |H| integer matrix indexed parallel to AsList(H);
#               b_omega[i][j] = q_omega(a_i * a_j) - q_omega(a_i)
#                              - q_omega(a_j)
#               (integer; reduced mod 2*modulus internally).
#   modulus   : positive integer N. The cocycle phase convention is
#               E(N)^{omega(a, b, c)}; the natural quadratic form
#               lives in Z/(2N) so the closed-form S/T uses E(2N)
#               internally.
#
# Output:
#   rec(
#     S       : (|H|^2 x |H|^2) cyclotomic matrix,
#     T       : length-|H|^2 cyclotomic vector (NOT a DiagonalMat),
#     simples : list of [a_index, chi_index] pairs in matching order
#               (i_a-1) * |H| + i_chi.
#     modulus, H : metadata for downstream consumers.
#   )
# Lex ordering of simples: outer over i_a in [1..|H|], inner over
# i_chi in [1..|H|].
# ---------------------------------------------------------------------
InstallGlobalFunction(ComputeAbelianModularDataFromQB,
function(H, q_omega, b_omega, modulus)
    local ct_rec, elems, n, m, T, S, normaliser,
          i_a, i_chi, i_b, i_psi, val_T, val_S,
          row_idx, col_idx, simples, i, j,
          two_N, zeta_q, ci_table, chi_at, chi_at_inv,
          zeta_b_row, factor_ai, S_row;

    if not IsAbelian(H) then
        Error("ComputeAbelianModularDataFromQB: H must be abelian");
    fi;
    ct_rec := _AbelianCharacterTable(H);
    elems := ct_rec.elems;
    n := Size(H);
    m := n;  # = |Hat(H)| for abelian H
    two_N := 2 * modulus;

    if Length(q_omega) <> n then
        Error("ComputeAbelianModularDataFromQB: length of q_omega (",
              Length(q_omega), ") does not match |H| = ", n);
    fi;
    if Length(b_omega) <> n then
        Error("ComputeAbelianModularDataFromQB: rows of b_omega (",
              Length(b_omega), ") does not match |H| = ", n);
    fi;

    # Cache the elements-to-class-index mapping as a flat plist for
    # speed in the inner loops.
    ci_table := List(elems, e ->
        LookupDictionary(ct_rec.class_of_elt, e));

    # Precompute the |H| x |H| character-value table:
    #   chi_at[k][i] = chi_k(elems[i])
    # And its entry-wise inverse for the S-formula's chi(b)^{-1} factor.
    chi_at := List([1..m], k ->
        List([1..n], i -> ct_rec.chi[k][ci_table[i]]));
    chi_at_inv := List(chi_at, row -> List(row, x -> 1 / x));

    # Precompute zeta^{q(a)} for each a, and the |H| x |H| zeta-b matrix
    # zeta_b_row[i_a][i_b] = E(2N)^{-b_omega[i_a][i_b]}.
    zeta_q := List(q_omega, k -> E(two_N)^k);

    # ---- T-vector ----
    # T_{(a, chi)} = chi(a) * E(2N)^{q_omega(a)}.
    T := EmptyPlist(n * m);
    for i_a in [1..n] do
        for i_chi in [1..m] do
            val_T := chi_at[i_chi][i_a] * zeta_q[i_a];
            Add(T, val_T);
        od;
    od;

    # ---- S-matrix ----
    # S_{(a,chi),(b,psi)} = (1/|H|) * psi(a)^{-1} * chi(b)^{-1}
    #                       * E(2N)^{-b_omega(a, b)}.
    #
    # Factor: per i_a we compute
    #   factor_ai := (1/|H|) * (psi(a))^{-1}    [length-m vector over i_psi]
    # and zeta_b_row[i_b] = E(2N)^{-b_omega[i_a, i_b]} for each i_b.
    # Then for each i_chi, the row (i_a, i_chi) is built by
    # multiplying chi_at_inv[i_chi] (length-n over i_b) elementwise by
    # zeta_b_row to get a length-n "scalar per i_b", then outer with
    # factor_ai to fill the (i_b, i_psi) block.
    S := NullMat(n * m, n * m, Cyclotomics);
    normaliser := 1 / n;
    for i_a in [1..n] do
        # factor_ai[i_psi] = normaliser * psi(a)^{-1}
        factor_ai := List([1..m], i_psi ->
            normaliser * chi_at_inv[i_psi][i_a]);
        # zeta_b_row[i_b] = E(2N)^{-b_omega[i_a][i_b]}
        zeta_b_row := List([1..n], i_b -> E(two_N)^(-b_omega[i_a][i_b]));
        for i_chi in [1..m] do
            row_idx := (i_a - 1) * m + i_chi;
            S_row := S[row_idx];
            for i_b in [1..n] do
                # scalar = zeta_b_row[i_b] * chi(b)^{-1}
                val_S := zeta_b_row[i_b] * chi_at_inv[i_chi][i_b];
                col_idx := (i_b - 1) * m;
                for i_psi in [1..m] do
                    S_row[col_idx + i_psi] := val_S * factor_ai[i_psi];
                od;
            od;
        od;
    od;

    simples := EmptyPlist(n * m);
    for i in [1..n] do
        for j in [1..m] do
            Add(simples, [i, j]);
        od;
    od;

    return rec(
        S := S,
        T := T,
        simples := simples,
        modulus := modulus,
        H := H
    );
end);

# ---------------------------------------------------------------------
# ComputeAbelianModularDataClosedForm(H, omega_cocycle, modulus)
#
# Higher-level helper: take a 3-cocycle omega : H^3 -> Z/N as a callable
# (actual phase = E(N)^{omega(a, b, c)}) and produce (S, T) via the
# closed form.
#
# Inputs:
#   H            : abelian group
#   omega_cocycle: callable (a, b, c) -> integer; will be used as-is
#                  (the doubling of modulus is handled internally).
#   modulus      : positive integer N (the cocycle's coefficient
#                  modulus; phase = E(N)^omega).
#
# Output: same shape as ComputeAbelianModularDataFromQB.
# ---------------------------------------------------------------------
InstallGlobalFunction(ComputeAbelianModularDataClosedForm,
function(H, omega_cocycle, modulus)
    local elems, n, q, b, i, j, ab, row, pos_dict, e, k, two_N;
    if not IsAbelian(H) then
        Error("ComputeAbelianModularDataClosedForm: H must be abelian");
    fi;
    elems := AsList(H);
    n := Size(H);
    two_N := 2 * modulus;

    # Build a Position dictionary once (cheaper than O(n) Position calls
    # per ab lookup).
    pos_dict := NewDictionary(elems[1], true);
    for k in [1..n] do
        AddDictionary(pos_dict, elems[k], k);
    od;

    # Compute q with values reduced mod 2N (preserves the doubled lift).
    q := List(elems, a -> omega_cocycle(a, a, a) mod two_N);
    b := EmptyPlist(n);
    for i in [1..n] do
        row := EmptyPlist(n);
        for j in [1..n] do
            ab := elems[i] * elems[j];
            row[j] := (q[LookupDictionary(pos_dict, ab)]
                       - q[i] - q[j]) mod two_N;
        od;
        b[i] := row;
    od;

    return ComputeAbelianModularDataFromQB(H, q, b, modulus);
end);

# ---------------------------------------------------------------------
# ComputeAbelianModularDataFactored(H, omega_cocycle, modulus)
#
# Factored / lazy variant of ComputeAbelianModularDataClosedForm. Builds
# only the |H|-sized "factor" tables (chi_at, chi_at_inv, zeta_q,
# b_omega, T_vec) and returns a record containing those, plus accessor
# closures S_at(global_i, global_j) and T_at(global_i) that compute
# any single (S, T) entry in O(1).
#
# Use this at H = (Z/2)^k for k >= 7 (|H| >= 128) where materialising
# the full (|H|^2 x |H|^2) S matrix is infeasible: |H|^4 = 2.7e8
# entries at k=7 (about 5 GB if each cyclotomic averages ~20 bytes),
# and |H|^4 = 4.3e9 at k=8 (terabytes). For k <= 6 the full-materialise
# `ComputeAbelianModularDataFromQB` is fine and ~50% faster per query.
#
# Returns:
#   rec(
#     H            : abelian group
#     n            : |H|
#     modulus      : N
#     simples      : list of [i_a, i_chi] in lex order
#     T_vec        : length-|H|^2 cyclotomic vector (full T diag)
#     S_at         : function(global_i, global_j) -> cyclotomic
#     T_at         : function(global_i) -> cyclotomic
#     normaliser   : 1/|H|
#     chi_at       : |H| x |H| character-value table
#     chi_at_inv   : entry-wise inverse of chi_at
#     zeta_q       : list of E(2N)^{q_omega[a]} per a
#     b_omega      : |H| x |H| matrix of b_omega entries (Z/2N)
#     two_N        : 2 * modulus
#   )
# ---------------------------------------------------------------------
InstallGlobalFunction(ComputeAbelianModularDataFactored,
function(H, omega_cocycle, modulus)
    local elems, n, m, ct_rec, ci_table, chi_at, chi_at_inv,
          two_N, q, b, pos_dict, i, j, k, ab, row, zeta_q,
          T_vec, i_a, i_chi, simples, normaliser, rec_out;

    if not IsAbelian(H) then
        Error("ComputeAbelianModularDataFactored: H must be abelian");
    fi;
    elems := AsList(H);
    n := Size(H);
    m := n;
    two_N := 2 * modulus;
    normaliser := 1 / n;

    ct_rec := _AbelianCharacterTable(H);
    ci_table := List(elems, e ->
        LookupDictionary(ct_rec.class_of_elt, e));
    chi_at := List([1..m], k_ ->
        List([1..n], i_ -> ct_rec.chi[k_][ci_table[i_]]));
    chi_at_inv := List(chi_at, r -> List(r, x -> 1 / x));

    # q_omega, b_omega from omega_cocycle.
    pos_dict := NewDictionary(elems[1], true);
    for k in [1..n] do
        AddDictionary(pos_dict, elems[k], k);
    od;
    q := List(elems, a -> omega_cocycle(a, a, a) mod two_N);
    b := EmptyPlist(n);
    for i in [1..n] do
        row := EmptyPlist(n);
        for j in [1..n] do
            ab := elems[i] * elems[j];
            row[j] := (q[LookupDictionary(pos_dict, ab)]
                       - q[i] - q[j]) mod two_N;
        od;
        b[i] := row;
    od;
    zeta_q := List(q, k_ -> E(two_N)^k_);

    # T vector (always materialised — |H|^2 entries, manageable).
    T_vec := EmptyPlist(n * m);
    for i_a in [1..n] do
        for i_chi in [1..m] do
            Add(T_vec, chi_at[i_chi][i_a] * zeta_q[i_a]);
        od;
    od;

    simples := EmptyPlist(n * m);
    for i in [1..n] do
        for j in [1..m] do
            Add(simples, [i, j]);
        od;
    od;

    rec_out := rec(
        H := H,
        n := n,
        modulus := modulus,
        two_N := two_N,
        normaliser := normaliser,
        simples := simples,
        T_vec := T_vec,
        chi_at := chi_at,
        chi_at_inv := chi_at_inv,
        zeta_q := zeta_q,
        b_omega := b,
        is_factored := true
    );

    # S_at: accessor for a single S-entry.
    rec_out.S_at := function(global_i, global_j)
        local i_a_, i_chi_, i_b_, i_psi_;
        # global_i = (i_a_ - 1) * m + i_chi_  in 1-based GAP indexing
        i_a_   := QuoInt(global_i - 1, m) + 1;
        i_chi_ := ((global_i - 1) mod m) + 1;
        i_b_   := QuoInt(global_j - 1, m) + 1;
        i_psi_ := ((global_j - 1) mod m) + 1;
        return normaliser
               * chi_at_inv[i_psi_][i_a_]
               * chi_at_inv[i_chi_][i_b_]
               * E(two_N)^(-b[i_a_][i_b_]);
    end;

    # T_at: accessor for a single T-entry.
    rec_out.T_at := function(global_i)
        return T_vec[global_i];
    end;

    return rec_out;
end);

# Convenience accessors at the top level (forward to the rec's
# closures); the rec field versions are faster (avoid the indirection)
# but these are nicer for one-shot queries.
InstallGlobalFunction(AbelianModularDataSEntry,
function(factored, i, j)
    return factored.S_at(i, j);
end);

InstallGlobalFunction(AbelianModularDataTEntry,
function(factored, i)
    return factored.T_at(i);
end);


if IsBoundGlobal("_LogStamped") then
    _LogStamped("Loaded abelian_modular_data_closed_form.g (#487).");
else
    Print("Loaded abelian_modular_data_closed_form.g (#487).\n");
fi;
