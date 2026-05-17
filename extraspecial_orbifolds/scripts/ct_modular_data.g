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

_CTComputeSBlock := function(intertwiner_data, i, j)
    local idx, transport, M, Ni, Nj, elts_i, elts_j, ts_i, ts_j,
          ai, bi, a, b, t_a, s_b, b_tilde, a_tilde, k, l, ord,
          cen_i_elts, c, elt_to_idx_j, eps, eps_chi_b, chi2_val,
          g_i, g_j;

    idx := intertwiner_data.idx;
    transport := intertwiner_data.transport;
    g_i := idx.reps[i];
    g_j := idx.reps[j];
    Ni := idx.num_irreps[i];
    Nj := idx.num_irreps[j];
    M := List([1..Ni], k -> List([1..Nj], l -> 0));
    elts_i := transport[i].elements;
    elts_j := transport[j].elements;
    ts_i := transport[i].t_of;
    ts_j := transport[j].t_of;
    cen_i_elts := AsList(idx.centralisers[i]);
    elt_to_idx_j := transport[j].elt_to_idx;
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
                for k in [1..Ni] do
                    eps_chi_b := eps * ComplexConjugate(
                        intertwiner_data.trace_on_W(i, k, b_tilde));
                    for l in [1..Nj] do
                        chi2_val := ComplexConjugate(
                            intertwiner_data.trace_on_W(j, l, a_tilde));
                        M[k][l] := M[k][l] + eps_chi_b * chi2_val;
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
                for k in [1..Ni] do
                    eps_chi_b := eps * ComplexConjugate(
                        intertwiner_data.trace_on_W(i, k, b_tilde));
                    for l in [1..Nj] do
                        chi2_val := ComplexConjugate(
                            intertwiner_data.trace_on_W(j, l, a_tilde));
                        M[k][l] := M[k][l] + eps_chi_b * chi2_val;
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
# Public: ComputeCTModularData(intertwiner_data, H)
# ============================================================
#
# See the file header for the contract. The math is CGR (5.20)+(5.21)
# specialised to the CT case under T4a's gauge choice ε ≡ 1.

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
