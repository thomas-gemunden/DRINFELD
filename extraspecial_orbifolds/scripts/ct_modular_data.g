# ct_modular_data.g
#
# K-4a-T5b (issue #199): modular data (S^α, T^α) of Z(Vec_H^α) in the
# CT (cohomologically trivial) case via CGR §5.2.
#
# Status: downscoped per T4a (#196 / PR #206) under ε ≡ 1 ⟹ σ ≡ 1.
# In this gauge:
#   * S^α reduces to the standard (untwisted-form) Bantay/CGR S
#     (CGR eq 5.20 with σ ≡ 1), exactly what `ProjectorFormula` in
#     `krr_projector.g` computes for an intertwiner_data with
#     `epsilon(g_1, g_2, a, b) ≡ 1` (i.e. the output of
#     `BuildIntertwinerDataUntwisted`).
#   * T^α_{(a, χ), (a, χ)} = (χ(a) / χ(e)) · ε_a(a) = χ(a) / χ(e)
#     since ε_a ≡ 1 (CGR eq 5.21).
#
# PUBLIC API
# ----------
#   ComputeCTModularData(intertwiner_data, H)
#
# `intertwiner_data` is a K-1-compatible record (the output of
# `BuildIntertwinerDataUntwisted(H)` from `krr_projector.g`, or the
# future T4c `BuildKRRSpectralCharacters(...)`). It must expose
#   .group       : H
#   .idx         : BuildSimpleIndex(H)
#   .transport   : BuildTransports(idx)
#   .trace_on_W  : function(class_idx, irrep_idx, h) -> cyclotomic
#                  (under ε ≡ 1 this is just `EvalIrr(idx, ...)`)
#   .epsilon     : function(g_1, g_2, a, b) -> cyclotomic
#                  (always 1 under T4a's downscope; the signature is
#                  preserved for forward-compat with twisted ε.)
# `H` is the underlying finite group (typically intertwiner_data.group,
# accepted as a separate argument for clarity).
#
# Returns
#   rec(
#     S       : square cyclotomic matrix |simples| x |simples|,
#     T       : DiagonalMat of cyclotomic values, same size,
#     simples : list of records (class_idx, irrep_idx) in matching order,
#     group   : H
#   )
#
# The `simples` list orders the rows/cols of S, T by `(class_idx,
# irrep_idx)` in the canonical lex order — identical to the global
# indexing used by `BuildSimpleIndex(H).global_to_local`. This is the
# same convention used by `untwisted_modular_data.g` (`ComputeUntwistedS`).
#
# PERFORMANCE NOTE
# ----------------
# A naive implementation calling `ProjectorFormula` once per (i, j)
# simple-pair revisits the (a, b) enumeration |Irr(C_i)| × |Irr(C_j)|
# times per class-pair. We instead compute each class-pair block in a
# single sweep of commuting (a, b) pairs (mirroring `ComputeSBlock`'s
# block strategy), evaluating the `intertwiner_data.epsilon` /
# `trace_on_W` callables for every (k, l) irrep choice in the inner
# loop. This matches ProjectorFormula entry-by-entry by construction:
# the math is the same sum, just reordered.
#
# DEPENDENCIES
# ------------
# Reads `untwisted_modular_data.g` and `krr_projector.g` (sibling files
# in this directory) on load. Per CLAUDE.md, neither file pulls in
# `src/modular_data.g` or `src/universal_coefficients.g`, so there is no
# global-name clobber risk from loading them here.
#
# If the caller already has these in scope (common for downstream
# orchestrators like T6 `K4aClassify`), the duplicate Reads are no-ops
# in practice — GAP reloads the function definitions but does not break
# the existing bindings.

# ---- Load sibling files ------------------------------------------------

_ct_modular_data_self := INPUT_FILENAME();;
if _ct_modular_data_self <> fail and _ct_modular_data_self <> "stream" then
    _ct_modular_data_dir := _ct_modular_data_self{
        [1..Length(_ct_modular_data_self) - Length("/ct_modular_data.g")]};;
    if not IsBound(BuildSimpleIndex) then
        Read(Concatenation(_ct_modular_data_dir,
                           "/untwisted_modular_data.g"));
    fi;
    if not IsBound(ProjectorFormula) then
        Read(Concatenation(_ct_modular_data_dir, "/krr_projector.g"));
    fi;
fi;

if not IsBound(BuildSimpleIndex) then
    Error("ct_modular_data.g: BuildSimpleIndex not bound; ",
          "Read \"untwisted_modular_data.g\" before this file.");
fi;
if not IsBound(ProjectorFormula) then
    Error("ct_modular_data.g: ProjectorFormula not bound; ",
          "Read \"krr_projector.g\" before this file.");
fi;

# PR #492: abelian-H closed-form dispatch reuses _AbelianCharacterTable
# from abelian_modular_data_closed_form.g (which is auto-loaded by
# untwisted_modular_data.g via its header guard — see the file header
# of that sibling).
if not IsBound(_AbelianCharacterTable) then
    Error("ct_modular_data.g: _AbelianCharacterTable not bound; ",
          "Read \"abelian_modular_data_closed_form.g\" before this ",
          "file (or load \"untwisted_modular_data.g\" which auto-loads ",
          "it).");
fi;


# ============================================================
# Internal helper: batched per-(class, element) trace_on_W lookup.
# ============================================================
#
# Issue #449 / Audit B4 (was 2026-06-02 A-K4-4):
# The naive `_CTComputeSBlock` calls `intertwiner_data.trace_on_W(i, k, h)`
# at the innermost (k, l) loop. For fixed (i, h) the value
# `trace_on_W(i, k, h)` is INDEPENDENT of the (a, b, k', l') outer iteration
# state, so we can batch the per-k calls into a single length-Ni vector
# lookup per (i, h).
#
# Quantitative impact:
#   Before — per (a, b) commuting pair: Ni + Ni × Nj `trace_on_W` calls
#            (Ni at the eps_chi_b precompute, Ni × Nj inside the l loop).
#   After  — per (a, b) commuting pair: Ni + Nj `trace_on_W` calls
#            (one length-Ni chi_vec_b lookup + one length-Nj chi_vec_a
#            lookup; the inner (k, l) loop becomes scalar arithmetic on
#            pre-evaluated values).
# At m=5 K-4b with the |EA|=64 / |D_8|=8 branch, Ni ≈ Nj ≈ 8 and the
# saving on `trace_on_W` calls per (a, b) is Ni × Nj − Nj = 56 calls
# per (a, b). At m=7 with |EA|=256, Ni ≈ Nj ≈ 258 so the saving is
# 258 × 258 − 258 = ~66 250 calls per (a, b).
#
# The helper supports three paths in order of preference:
#  (1) Caller-supplied `trace_on_W_vec(i, h) -> length-Ni vector`.
#      Hook for future spectral builders that can compute the vector
#      cheaply in bulk; currently no builder publishes this field but
#      the protocol is in place.
#  (2) `EvalIrr` fast-lookup bypass when `intertwiner_data.trace_on_W`
#      reduces to `EvalIrr(idx, i, *, h)`. Detected via the
#      `intertwiner_data.trace_on_W_kind` flag set to "evalirr". Single
#      `ClassIndexInCentraliser(idx, i, h)` call + Ni table reads.
#  (3) Fallback: invoke `intertwiner_data.trace_on_W(i, k, h)` per
#      k ∈ [1..Ni]. Same call count Ni as path (2) but goes through
#      the scalar callable interface — universal correctness regardless
#      of which builder produced the intertwiner_data.
#
# Path (2) detection: we inspect `intertwiner_data.trace_on_W_kind` if
# set by the caller. Recognised tags:
#   "evalirr"     -> path (2) bypass for ALL classes (e.g. the output
#                    of `BuildIntertwinerDataUntwisted`,
#                    `RestrictTraceOnWToSubgroup`, and
#                    `RestrictTraceOnWToSubgroupHonourParent`, which
#                    all return `EvalIrr(idx, i, k, h)` directly per
#                    `restrict_to_subgroup.g:770-772`).
# Absent or any other value: fall back to path (3). No correctness
# difference, just no batching savings on the table-lookup step.

_CTBatchedTraceOnW := function(intertwiner_data, i, h, Ni)
    local idx, vec, cc_idx, k, kind;
    # Path (1): caller-supplied batched callable.
    if IsBound(intertwiner_data.trace_on_W_vec) then
        return intertwiner_data.trace_on_W_vec(i, h);
    fi;
    idx := intertwiner_data.idx;
    kind := fail;
    if IsBound(intertwiner_data.trace_on_W_kind) then
        kind := intertwiner_data.trace_on_W_kind;
    fi;
    # Path (2): EvalIrr fast bypass.
    # `EvalIrr(idx, i, k, h)` decomposes as:
    #     cc_idx := ClassIndexInCentraliser(idx, i, h);
    #     return idx.irreps[i][k][cc_idx];
    # The `cc_idx` is INDEPENDENT of k; the closed-form bypass for
    # central E_+(m) classes (also triggered inside `EvalIrr`) materialises
    # `idx.irreps[i]` as a real list-of-rows via `_EnsureClassData`, so the
    # `[cc_idx]` indexing path is uniform across closed-form and generic
    # paths once class data is materialised.
    if kind = "evalirr" then
        # Force class data to materialise (no-op on subsequent calls
        # for the same i, including the lazy and closed-form paths).
        cc_idx := ClassIndexInCentraliser(idx, i, h);
        vec := EmptyPlist(Ni);
        for k in [1..Ni] do
            Add(vec, idx.irreps[i][k][cc_idx]);
        od;
        return vec;
    fi;
    # Path (3): fallback via the scalar callable.
    vec := EmptyPlist(Ni);
    for k in [1..Ni] do
        Add(vec, intertwiner_data.trace_on_W(i, k, h));
    od;
    return vec;
end;;


# ============================================================
# Internal helper: compute the (i, j) class-pair S-block via the
# intertwiner_data callables.
# ============================================================
#
# Block layout: M[k][l] = S^α_{(g_i, chi_{i,k}), (g_j, chi_{j,l})}.
#
# The math is exactly CGR (5.20) under ε ≡ 1 / σ ≡ 1:
#   M[k][l] = (1/|H|) Σ_{(a, b) ∈ class_i × class_j, ab = ba}
#               eps(g_i, g_j, a, b)
#             * conj( chi_{i, k}( t_a^{-1} b t_a ) )
#             * conj( chi_{j, l}( s_b^{-1} a s_b ) )
#
# Implementation mirrors `ComputeSBlock`'s two-path dispatch
# (`untwisted_modular_data.g` :: `ComputeSBlock`) but routes the
# character evaluation through `intertwiner_data.trace_on_W` and
# multiplies in `intertwiner_data.epsilon`. The eps factor is computed
# **once per (a, b) pair** (not per (k, l)) since it does not depend on
# the irreps, only on the group elements.
#
# Issue #449 / Audit B4: per-(a, b) batched trace_on_W lookup.
# For each (i, b_tilde) and (j, a_tilde) we precompute the length-Ni
# (resp. length-Nj) vector of trace_on_W values ONCE via
# `_CTBatchedTraceOnW`, then the inner (k, l) loop reads pre-evaluated
# scalars. This eliminates Ni × Nj − Nj `trace_on_W` calls per (a, b)
# pair, replacing them with simple list indexing.

_CTComputeSBlock := function(intertwiner_data, i, j)
    local idx, transport, M, Ni, Nj, elts_i, elts_j, ts_i, ts_j,
          ai, bi, a, b, t_a, s_b, b_tilde, a_tilde, k, l, ord,
          cen_i_elts, c, elt_to_idx_j, eps, eps_chi_b,
          g_i, g_j, t_i, t_j, chi_vec_b, chi_vec_a,
          chi_vec_b_conj, chi_vec_a_conj, M_k;

    idx := intertwiner_data.idx;
    transport := intertwiner_data.transport;
    g_i := idx.reps[i];
    g_j := idx.reps[j];
    Ni := idx.num_irreps[i];
    Nj := idx.num_irreps[j];
    M := List([1..Ni], k -> List([1..Nj], l -> 0));
    # K-2c (#129): route per-class reads through GetTransport so this
    # block worker handles both eager and lazy transport lists.
    t_i := GetTransport(transport, idx, i);
    t_j := GetTransport(transport, idx, j);
    elts_i := t_i.elements;
    elts_j := t_j.elements;
    ts_i := t_i.t_of;
    ts_j := t_j.t_of;
    # Issue #449 A1': lazy centraliser materialisation for closed-form
    # E_+(m) idxs. No-op for eager idxs.
    if IsBoundGlobal("_EPlusCentraliserOf") then
        cen_i_elts := AsList(_EPlusCentraliserOf(idx, i));
    else
        cen_i_elts := AsList(idx.centralisers[i]);
    fi;
    elt_to_idx_j := t_j.elt_to_idx;
    ord := idx.order;

    if Length(elts_j) <= Length(cen_i_elts) then
        # Path (A): iterate class_j directly (smaller of the two).
        for ai in [1..Length(elts_i)] do
            a := elts_i[ai];
            t_a := ts_i[ai];
            for bi in [1..Length(elts_j)] do
                b := elts_j[bi];
                if a * b <> b * a then continue; fi;
                s_b := ts_j[bi];
                b_tilde := t_a^-1 * b * t_a;     # in C_H(g_i)
                a_tilde := s_b^-1 * a * s_b;     # in C_H(g_j)
                eps := intertwiner_data.epsilon(g_i, g_j, a, b);
                # B4: batched per-(class, element) trace_on_W vectors.
                chi_vec_b := _CTBatchedTraceOnW(intertwiner_data, i,
                                                 b_tilde, Ni);
                chi_vec_a := _CTBatchedTraceOnW(intertwiner_data, j,
                                                 a_tilde, Nj);
                chi_vec_b_conj := List(chi_vec_b, ComplexConjugate);
                chi_vec_a_conj := List(chi_vec_a, ComplexConjugate);
                for k in [1..Ni] do
                    eps_chi_b := eps * chi_vec_b_conj[k];
                    M_k := M[k];
                    for l in [1..Nj] do
                        M_k[l] := M_k[l] + eps_chi_b * chi_vec_a_conj[l];
                    od;
                od;
            od;
        od;
    else
        # Path (B): iterate C_H(g_i) and conjugate by t_a.
        for ai in [1..Length(elts_i)] do
            a := elts_i[ai];
            t_a := ts_i[ai];
            for c in cen_i_elts do
                b := t_a * c * t_a^(-1);
                bi := LookupDictionary(elt_to_idx_j, b);
                if bi = fail then continue; fi;
                s_b := ts_j[bi];
                b_tilde := c;                    # = t_a^{-1} * b * t_a
                a_tilde := s_b^-1 * a * s_b;     # in C_H(g_j)
                eps := intertwiner_data.epsilon(g_i, g_j, a, b);
                # B4: batched per-(class, element) trace_on_W vectors.
                chi_vec_b := _CTBatchedTraceOnW(intertwiner_data, i,
                                                 b_tilde, Ni);
                chi_vec_a := _CTBatchedTraceOnW(intertwiner_data, j,
                                                 a_tilde, Nj);
                chi_vec_b_conj := List(chi_vec_b, ComplexConjugate);
                chi_vec_a_conj := List(chi_vec_a, ComplexConjugate);
                for k in [1..Ni] do
                    eps_chi_b := eps * chi_vec_b_conj[k];
                    M_k := M[k];
                    for l in [1..Nj] do
                        M_k[l] := M_k[l] + eps_chi_b * chi_vec_a_conj[l];
                    od;
                od;
            od;
        od;
    fi;
    return M / ord;
end;;


# ============================================================
# Internal helper: build the simples list from the underlying idx.
# ============================================================
#
# Each simple is a record (class_idx, irrep_idx). The ordering follows
# `idx.global_to_local`: outer loop over classes, inner loop over irreps
# of the centraliser. This is the canonical lex order matching
# `BuildSimpleIndex(H).global_to_local`.

_CTBuildSimplesList := function(idx)
    local simples, i, k;
    simples := [];
    for i in [1..Length(idx.classes)] do
        for k in [1..idx.num_irreps[i]] do
            Add(simples, rec(class_idx := i, irrep_idx := k));
        od;
    od;
    return simples;
end;;


# ============================================================
# Abelian-H closed-form specialisation (PR #492)
# ============================================================
#
# When H is abelian, the (S, T) computed by the generic loop above
# admits a closed-form representation in terms of a quadratic form
# q_α : H → Z/(2N) and its polarisation b_α : H × H → Z/(2N):
#
#   T_{(a, χ)}        = χ(a) · E(2N)^{q_α(a)}
#   S_{(a,χ),(b,ψ)}   = (1/|H|) · ψ(a)^{-1} · χ(b)^{-1} · E(2N)^{-b_α(a, b)}
#
# (See `abelian_modular_data_closed_form.g` for the math; the factored
# variant produces a record with O(|H|^2) memory + O(1) per-entry S.)
#
# Under the K-4b CT pipeline gauge ε ≡ 1 with `trace_on_W` = ordinary
# H-characters (the `EvalIrr` baseline produced by
# `BuildIntertwinerDataUntwisted` / `RestrictTraceOnWToSubgroupHonourParent`),
# the diagonal T-entry at the trivial character of H reduces to
#
#   T_{(a, χ_triv)} = trace_on_W(class_of(a), trivial_irrep_idx, a)
#                     / trace_on_W(class_of(a), trivial_irrep_idx, e)
#
# from which q_α(a) is the discrete log to base E(2N). This single
# closed-form `_CTModularDataAbelianClosedForm` handles both the ε ≡ 1
# baseline (untwisted, q = b = 0) and any forward-compatible α-twisted
# extension that uses the same gauge convention.
#
# Returns a factored modular-data record (PR #487 shape) when |H| is
# large; the same record is consumed by `ClassifyEAFromModularData`
# (PR #486 + #490) via its `qb_extraction` path. At small |H| (k ≤ 4
# in (Z/2)^k) the record is still factored — the downstream consumer
# handles both shapes uniformly.

# Helper: find the index of the trivial irrep (all-1 character) in
# idx.irreps[class_idx]. For abelian H, every centraliser is H, and
# the trivial irrep is the row of `Irr(CharacterTable(H))` that is
# identically 1. In GAP's standard ordering this is row 1 for
# elementary-abelian groups; we scan robustly.
_CTFindTrivialIrrepIdx := function(idx, class_idx)
    local irreps, num_cc, k, k_idx, all_one;
    _EnsureClassData(idx, class_idx);
    irreps := idx.irreps[class_idx];
    num_cc := Length(idx.cc_centraliser[class_idx]);
    for k in [1..Length(irreps)] do
        all_one := true;
        for k_idx in [1..num_cc] do
            if irreps[k][k_idx] <> 1 then
                all_one := false;
                break;
            fi;
        od;
        if all_one then
            return k;
        fi;
    od;
    Error("_CTFindTrivialIrrepIdx: no all-1 row in idx.irreps[", class_idx,
          "]; centraliser is not abelian as expected");
end;;

# Helper: determine the modulus N such that all T-values are powers
# of E(2N). T-values are roots of unity; we take 2N = LCM of their
# orders. If all T-values equal 1, return N = 1 (so 2N = 2; E(2)^0 = 1
# is a valid representation).
_CTDetermineModulusFromTValues := function(T_values)
    local order_lcm, v, ord;
    order_lcm := 1;
    for v in T_values do
        if v = 1 then
            ord := 1;
        elif v = -1 then
            ord := 2;
        else
            ord := Order(v);
        fi;
        order_lcm := LcmInt(order_lcm, ord);
    od;
    # 2N must be a multiple of order_lcm. Use the smallest N >= 1 such
    # that 2N is divisible by order_lcm. If order_lcm is odd, N = order_lcm
    # gives 2N = 2*order_lcm, which works. If order_lcm is even, N = order_lcm/2
    # gives 2N = order_lcm. We pick N = max(1, order_lcm / 2) when order_lcm
    # is even, else N = order_lcm.
    if order_lcm mod 2 = 0 then
        return order_lcm / 2;
    fi;
    # Odd order_lcm: 2N = 2*order_lcm.
    return order_lcm;
end;;

# Helper: compute the discrete log of x to base E(2N), returning k ∈
# [0, 2N) such that x = E(2N)^k. Fails (returns `fail`) if no such k
# exists.
_CTDiscreteLogBaseE2N := function(x, two_N)
    local k, z, pow;
    z := E(two_N);
    pow := 1;
    for k in [0..two_N - 1] do
        if pow = x then
            return k;
        fi;
        pow := pow * z;
    od;
    return fail;
end;;

# Helper: build the (q, b) representation of the modular data from
# the intertwiner_data record. Returns rec(q, b, modulus, elems) where:
#   - elems = idx.reps  (the class-representative list of the cached
#                        idx; for abelian H every class is a singleton
#                        so this is the full element list of the idx's
#                        group instance).
#   - q[i_a] = q_α(elems[i_a]) mod 2*modulus
#   - b[i_a][i_b] = q_α(elems[i_a]*elems[i_b]) - q_α(elems[i_a])
#                   - q_α(elems[i_b]) mod 2*modulus
#   - modulus = N (chosen minimally; 2N is the actual exponent for E(.))
#
# CRITICAL CONVENTION (PR #492):
# We use `idx.reps` (the cached group instance's class reps) rather
# than `AsList(H)`. In the K-4b spectral pipeline, `_RTS_GetBIDUCached(H)`
# may return an intertwiner_data whose `idx.classes` lives in a CACHED
# group instance that is isomorphic-but-not-equal to H (when two H_EA
# subgroups share the same `IdGroup` key). Using `idx.reps` keeps the
# q/b indexing consistent with the idx ordering and avoids cross-instance
# element-equality bugs in dictionary lookup.
#
# For abelian H every class is a singleton, so `idx.reps[i]` is the i-th
# element of the cached group instance, and the class index of
# `idx.reps[i]` is exactly i.
_CTExtractQBFromIntertwinerData := function(intertwiner_data, H)
    local idx, elems, n, T_values, i_a, a, cls_idx,
          triv_idx_cache, triv_idx, chi_e, chi_a, T_a, modulus, two_N,
          q, b, i_b, ab, q_ab_idx, row, e_idx, one_idx_group;
    idx := intertwiner_data.idx;
    elems := idx.reps;
    n := Length(elems);

    # Sanity: |idx.reps| must match |H|. For abelian H every class is a
    # singleton so this is automatic — but we guard against a caller
    # accidentally passing the wrong intertwiner_data.
    if n <> Size(H) then
        Error("_CTExtractQBFromIntertwinerData: |idx.reps| = ", n,
              " but |H| = ", Size(H),
              " — intertwiner_data built for a different-order group?");
    fi;

    # Identity of the cached group instance (NOT One(H), which may live
    # in a different instance). idx.reps[i] is a class representative
    # in the cached idx.group instance; One(idx.reps[1]) gives the
    # identity element in that instance. We pick reps[1] arbitrarily
    # since `One` only depends on the parent group, not the element.
    one_idx_group := One(idx.reps[1]);

    # Cache the trivial irrep index per class (it can vary per class
    # since each class has a different centraliser; for abelian H all
    # centralisers are the same group, but we don't assume that.)
    triv_idx_cache := [];

    # Evaluate T_{(a, χ_triv)} = trace_on_W(cls, triv, a) /
    #                            trace_on_W(cls, triv, e).
    # For abelian H the class index of elems[i_a] is exactly i_a.
    T_values := EmptyPlist(n);
    for i_a in [1..n] do
        a := elems[i_a];
        cls_idx := i_a;
        if not IsBound(triv_idx_cache[cls_idx]) then
            triv_idx_cache[cls_idx] := _CTFindTrivialIrrepIdx(idx, cls_idx);
        fi;
        triv_idx := triv_idx_cache[cls_idx];
        chi_e := intertwiner_data.trace_on_W(cls_idx, triv_idx,
                                              one_idx_group);
        chi_a := intertwiner_data.trace_on_W(cls_idx, triv_idx, a);
        T_a := chi_a / chi_e;
        Add(T_values, T_a);
    od;

    modulus := _CTDetermineModulusFromTValues(T_values);
    two_N := 2 * modulus;

    # Discrete-log each T_value to read off q.
    q := EmptyPlist(n);
    for i_a in [1..n] do
        e_idx := _CTDiscreteLogBaseE2N(T_values[i_a], two_N);
        if e_idx = fail then
            Error("_CTExtractQBFromIntertwinerData: T_value at i_a = ",
                  i_a, " (= ", T_values[i_a],
                  ") is not a power of E(", two_N, ")");
        fi;
        Add(q, e_idx);
    od;

    # b via polarisation. For abelian H, elems[i_a] * elems[i_b] is also
    # in the cached group; use Position on idx.reps for the index lookup.
    b := EmptyPlist(n);
    for i_a in [1..n] do
        row := EmptyPlist(n);
        for i_b in [1..n] do
            ab := elems[i_a] * elems[i_b];
            q_ab_idx := Position(elems, ab);
            if q_ab_idx = fail then
                Error("_CTExtractQBFromIntertwinerData: product ", ab,
                      " not in idx.reps; H non-abelian or caching bug?");
            fi;
            row[i_b] := (q[q_ab_idx] - q[i_a] - q[i_b]) mod two_N;
        od;
        b[i_a] := row;
    od;

    return rec(
        q := q,
        b := b,
        modulus := modulus,
        two_N := two_N,
        elems := elems
    );
end;;

# Helper: build a factored modular-data record from pre-computed (q, b).
# Indexes chi_at via `idx.reps` (the cached idx's class-representative
# ordering), aligning with `_CTExtractQBFromIntertwinerData`'s output.
#
# For abelian H every class is a singleton, so `idx.irreps[k][j][i]` =
# j-th irrep of `C_H(idx.reps[k])` = H evaluated at the i-th class
# representative = chi_at[j][i] when the i-th class rep is idx.reps[i].
#
# We use `idx.irreps[1]` (the irreps of C_H(idx.reps[1]) = H) since for
# abelian H all centralisers are H and idx.irreps[k] = Irr(H) for every k.
#
# Output shape matches `ComputeAbelianModularDataFactored`:
#   rec(is_factored := true, n, modulus, two_N, normaliser, simples,
#        T_vec, chi_at, chi_at_inv, zeta_q, b_omega, S_at, T_at)
_CTBuildFactoredFromQB := function(idx, H, q, b, modulus)
    local n, m, two_N, normaliser, irreps_H, chi_at, chi_at_inv,
          zeta_q, T_vec, i_a, i_chi, simples, i, j, rec_out;
    n := Length(idx.reps);
    m := n;
    two_N := 2 * modulus;
    normaliser := 1 / n;

    # Materialise the class data for the first class (so idx.irreps[1]
    # is populated under the lazy idx). For abelian H idx.irreps[k]
    # equals Irr(H) for every k; we only need k = 1.
    _EnsureClassData(idx, 1);
    irreps_H := idx.irreps[1];
    if Length(irreps_H) <> n then
        Error("_CTBuildFactoredFromQB: |idx.irreps[1]| = ",
              Length(irreps_H), " != |H| = ", n,
              "; H is not actually abelian?");
    fi;
    # chi_at[k][i] = k-th irrep evaluated at the i-th class
    # (= idx.reps[i] under abelian H).
    chi_at := List([1..m], k_idx ->
        List([1..n], i_idx -> irreps_H[k_idx][i_idx]));
    chi_at_inv := List(chi_at, r -> List(r, x -> 1 / x));

    zeta_q := List(q, k_ -> E(two_N)^k_);

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
        is_factored := true,
        # Preserve `group` for API symmetry with the generic path's
        # return (the generic path sets `.group := H`).
        group := H,
        # PR #492 marker: this record came from the abelian closed-form
        # specialisation of ComputeCTModularData (not from the generic
        # loop). Surface for diagnostic / test introspection.
        source := "ct-abelian-closed-form"
    );

    rec_out.S_at := function(global_i, global_j)
        local i_a_, i_chi_, i_b_, i_psi_;
        i_a_   := QuoInt(global_i - 1, m) + 1;
        i_chi_ := ((global_i - 1) mod m) + 1;
        i_b_   := QuoInt(global_j - 1, m) + 1;
        i_psi_ := ((global_j - 1) mod m) + 1;
        return normaliser
               * chi_at_inv[i_psi_][i_a_]
               * chi_at_inv[i_chi_][i_b_]
               * E(two_N)^(-b[i_a_][i_b_]);
    end;
    rec_out.T_at := function(global_i)
        return T_vec[global_i];
    end;

    # API compatibility: the generic path also returns a `T` field
    # (a DiagonalMat). We surface the same shape via a T DiagonalMat
    # synthesised from T_vec — but at large |H| this would materialise
    # |H|^2 x |H|^2 zeros, which we do NOT want. Skip the DiagonalMat
    # synthesis; the downstream consumer (`ClassifyEAFromModularData`)
    # detects `is_factored` and reads `T_vec` directly. Callers wanting
    # the legacy DiagonalMat T can synthesise it themselves.

    return rec_out;
end;;

# Public-facing closed-form: builds the factored modular-data record
# from `intertwiner_data` for abelian H. Returns a record matching the
# `ComputeAbelianModularDataFactored` shape (with `is_factored := true`).
_CTModularDataAbelianClosedForm := function(intertwiner_data, H)
    local qb;
    qb := _CTExtractQBFromIntertwinerData(intertwiner_data, H);
    return _CTBuildFactoredFromQB(intertwiner_data.idx, H,
                                   qb.q, qb.b, qb.modulus);
end;;


# ============================================================
# Public: ComputeCTModularData(intertwiner_data, H)
# ============================================================
#
# See the file header for the contract. The math is CGR (5.20)+(5.21)
# specialised to the CT case under T4a's gauge choice ε ≡ 1.
#
# Dispatch (PR #492):
#   * H abelian → `_CTModularDataAbelianClosedForm(intertwiner_data, H)`.
#     Returns a FACTORED modular-data record (see PR #487 + #490). The
#     downstream consumer `ClassifyEAFromModularData` reads `is_factored`
#     and routes through the `qb_extraction` path (O(|H|^2) memory +
#     O(1) per-entry S accessor). At H = (Z/2)^8 (m=7 max EA) the
#     generic O(|H|^4) loop is infeasible (~10 h / EA); the closed-form
#     completes in minutes.
#   * H non-abelian → generic O(|H|^4) block-sweep loop (unchanged).

ComputeCTModularData := function(intertwiner_data, H)
    local idx, simples, n, S, T_diag, i, j, off_i, off_j, k, l, block,
          a_i, chi_e, chi_a;

    # Validate the intertwiner_data shape minimally — guard against the
    # common "called with idx instead of intertwiner_data" mistake.
    if not (IsRecord(intertwiner_data)
            and IsBound(intertwiner_data.idx)
            and IsBound(intertwiner_data.transport)
            and IsBound(intertwiner_data.trace_on_W)
            and IsBound(intertwiner_data.epsilon)) then
        Error("ComputeCTModularData: intertwiner_data must be a record ",
              "with fields .idx, .transport, .trace_on_W, .epsilon ",
              "(see BuildIntertwinerDataUntwisted in krr_projector.g).");
    fi;

    idx := intertwiner_data.idx;
    if not IsBound(idx.classes) then
        Error("ComputeCTModularData: intertwiner_data.idx is missing ",
              ".classes; was it built via BuildSimpleIndex?");
    fi;

    # PR #492: abelian-H closed-form dispatch.
    if IsAbelian(H) then
        return _CTModularDataAbelianClosedForm(intertwiner_data, H);
    fi;

    simples := _CTBuildSimplesList(idx);
    n := Length(simples);

    # ----- S^α via the block sweep ----------------------------------
    S := List([1..n], i -> List([1..n], j -> 0));
    for i in [1..Length(idx.classes)] do
        for j in [1..Length(idx.classes)] do
            block := _CTComputeSBlock(intertwiner_data, i, j);
            off_i := idx.global_offset[i];
            off_j := idx.global_offset[j];
            for k in [1..idx.num_irreps[i]] do
                for l in [1..idx.num_irreps[j]] do
                    S[off_i + k][off_j + l] := block[k][l];
                od;
            od;
        od;
    od;

    # ----- T^α via CGR (5.21) under ε ≡ 1 ----------------------------
    #   T^α_{(a, χ)} = (χ(a) / χ(e)) · ε_a(a) = χ(a) / χ(e).
    # We compute χ(a) / χ(e) via the simple-index's stored
    # irrep_dims[i][k] (which is χ_{i,k}(e)) and `EvalIrr` for χ_{i,k}(a).
    #
    # NOTE on intertwiner_data.trace_on_W vs EvalIrr: under ε ≡ 1 the
    # T-matrix is determined by the **character** χ at (a, e), not by a
    # generic trace functional. For the CT case the centraliser-character
    # functional (= EvalIrr) and the spectral-character functional from
    # T4c (= projection of Ω_0 onto χ-isotypic) must agree on χ values,
    # so using trace_on_W here is equivalent. We use trace_on_W for
    # consistency with the S formula above — that way any future
    # twisted ε implementation gets a uniform path.
    T_diag := [];
    for i in [1..Length(idx.classes)] do
        a_i := idx.reps[i];
        for k in [1..idx.num_irreps[i]] do
            chi_e := intertwiner_data.trace_on_W(i, k, One(H));
            chi_a := intertwiner_data.trace_on_W(i, k, a_i);
            Add(T_diag, chi_a / chi_e);
        od;
    od;

    return rec(
        S       := S,
        T       := DiagonalMat(T_diag),
        simples := simples,
        group   := H
    );
end;;
