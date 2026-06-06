# K-1: Projector formula KRR24 eq (2.1.2) — single-entry adapter.
#
# Implements `ProjectorFormula(W_g1, W_g2, intertwiner_data)` returning
# one S-matrix entry of S^Keller for the index pair
#       ((g_1, chi_1), (g_2, chi_2))
# from the underlying intertwiner-trace machinery.
#
# CONVENTIONS / PAPER ASSUMPTIONS
# ===============================
# The KRR paper [Keller-Roberts-Roberts, arXiv:2411.13646] is NOT in
# this repository. We use the equivalent formulation from
# [DPR91; Coste-Gannon-Ruelle 2000, eq. (2.7)] which the writeup
# (extraspecial_orbifolds/writeup.md §6.2) and design doc § K-1 cite as
# the convention KRR24 uses for assembling intertwiner outputs into
# S-matrix entries:
#
#   S^Keller_{((g_1, chi_1), (g_2, chi_2))}
#       = (1/|G|) * sum_{a in [g_1], b in [g_2], ab = ba}
#                    epsilon_omega(g_1, g_2, a, b)
#                  * conj( chi_1( t_a^{-1} b t_a ) )
#                  * conj( chi_2( s_b^{-1} a s_b ) )
#
# where t_a, s_b are conjugating elements with t_a g_1 t_a^{-1} = a and
# s_b g_2 s_b^{-1} = b, and chi_i is the projective character of
# C_G(g_i) carried by the i-th simple object — implemented here as a
# trace functional on the corresponding twisted-module piece.
#
# For omega = 0 the phase epsilon vanishes (epsilon == 1) and the
# projective characters reduce to ordinary characters; the formula
# collapses to the standard Bantay/CGR untwisted S-matrix.
#
# This is the K-1 ACCEPTANCE ANCHOR: at omega = 0, m = 3, central-row
# entries must reproduce the dense untwisted S computed by
# `untwisted_modular_data.g` exactly (in cyclotomic arithmetic, no
# numerical tolerance needed).
#
# DELIBERATELY OUT OF SCOPE
# =========================
# - Decoding global simple indices i -> (g, chi) (K-2 wraps that).
# - Computing epsilon_omega for non-trivial omega (V-1 supplies that).
# - Hooking up KRR's actual W_g/Omega_0 traces to project_data
#   (downstream task; for now the trace functional defaults to the
#    centraliser-character functional, which is the omega = 0 ground
#    truth).
#
# DEPENDENCIES
# ============
# Consumer is expected to have read `untwisted_modular_data.g` so that
# `BuildSimpleIndex`, `BuildTransports`, `ClassIndexInCentraliser`, and
# `EvalIrr` are in scope. (We do not Read it here to avoid double-Read
# clobbering when a driver script chains multiple files.)


# ============================================================
# Building the intertwiner_data record
# ============================================================

# Build an `intertwiner_data` record suitable for `ProjectorFormula` from
# a finite group G, using the centraliser-character functional as the
# trace evaluator. This is the omega = 0 baseline; for non-trivial omega
# the caller would override `.trace_on_W` with a projective-character
# evaluator and `.epsilon` with a non-trivial phase callable.
#
# Returned record fields:
#   .group              : G
#   .idx                : BuildSimpleIndex(G)
#   .transport          : BuildTransports(idx)
#   .trace_on_W(i, k, h): trace of h ∈ C_G(g_i) on the (i, k)-th simple's
#                          twisted-module piece. For omega = 0 this is
#                          chi_{i,k}(h) where chi_{i,k} is the k-th irrep
#                          of C_G(g_i).
#   .epsilon(g1, g2, a, b)
#                       : the CGR phase. omega = 0 gives 1.
BuildIntertwinerDataUntwisted := function(G)
    local idx, transport;
    idx := BuildSimpleIndex(G);
    transport := BuildTransports(idx);
    return rec(
        group := G,
        idx := idx,
        transport := transport,
        trace_on_W := function(class_idx, irrep_idx, h)
            return EvalIrr(idx, class_idx, irrep_idx, h);
        end,
        epsilon := function(g1, g2, a, b) return 1; end
    );
end;;

# K-2c (#129): lazy variant for the single-query SKeller path.
# Same shape as the eager version above but BOTH the inner index AND the
# transports defer per-class work until first access.
#
# Use this when only a small number of (class_i, class_j) pairs will be
# queried (e.g. SKeller(7, i, j) for a single (i, j)). For full S-matrix
# work the eager version is still preferred since every class would be
# touched anyway.
#
# K-2c FOLLOW-UP (this PR): BuildTransportsLazy + GetTransport mean that
# at m=7 only the queried classes pay the BFS cost (each per-class BFS is
# O(|G|) = ~30K ops vs ~16M ops for the eager full sweep across ~16K
# classes). The consumers (`ComputeSBlock`, `ProjectorFormula`,
# `_CTComputeSBlock`) route reads through `GetTransport` so the lazy
# transport list is transparent to them.
BuildIntertwinerDataUntwistedLazy := function(G)
    local idx, transport;
    idx := BuildSimpleIndexLazy(G);
    transport := BuildTransportsLazy(idx);
    return rec(
        group := G,
        idx := idx,
        transport := transport,
        trace_on_W := function(class_idx, irrep_idx, h)
            return EvalIrr(idx, class_idx, irrep_idx, h);
        end,
        epsilon := function(g1, g2, a, b) return 1; end
    );
end;;


# ============================================================
# Simple-object descriptors W_g
# ============================================================

# Build a W_g descriptor record (a "simple object handle") from a class
# index and an irrep index, given an existing intertwiner_data record.
#
# Returned record fields:
#   .class_idx : index of the conjugacy class in intertwiner_data.idx.classes
#   .irrep_idx : index of the irrep in centraliser irreps for that class
#   .g         : the class representative element of G
MakeWg := function(intertwiner_data, class_idx, irrep_idx)
    return rec(
        class_idx := class_idx,
        irrep_idx := irrep_idx,
        g := intertwiner_data.idx.reps[class_idx]
    );
end;;


# ============================================================
# The projector formula itself
# ============================================================

# ProjectorFormula(W_g1, W_g2, intertwiner_data)
#   -> single complex (cyclotomic) entry of S^Keller.
#
# Implements
#   S^Keller_{((g_1, chi_1), (g_2, chi_2))}
#     = (1/|G|) * sum_{a in [g_1], b in [g_2], ab = ba}
#                  eps(g_1, g_2, a, b) *
#                  conj( chi_1(t_a^{-1} b t_a) ) *
#                  conj( chi_2(s_b^{-1} a s_b) )
#
# with t_a, s_b drawn from intertwiner_data.transport (which fixes one
# choice per class element — the formula is independent of the choice
# because chi_i is a class function on C_G(g_i)).
ProjectorFormula := function(W_g1, W_g2, intertwiner_data)
    local idx, transport, i, j, total, ord, elts_i, elts_j,
          ts_i, ts_j, ai, bi, a, b, t_a, s_b, b_in_C1, a_in_C2,
          eps, chi1_val, chi2_val, cen_i_elts, c, elt_to_idx_j,
          t_i, t_j;
    # P-9 (#126): we have two ways to enumerate commuting (a, b)
    # pairs in class_i × class_j:
    #   (A) iterate a ∈ class_i, b ∈ class_j, commutation test.
    #       Cost: |class_i| × |class_j| pair iterations, each one
    #       pc-group commutation test.
    #   (B) iterate a ∈ class_i, c ∈ C_G(g_i); set b = t_a c t_a^{-1};
    #       dictionary-test b ∈ class_j.
    #       Cost: |class_i| × |C_G(g_i)| = |G| pair iterations.
    # (A) is faster when |class_j| < |C_G(g_i)| (smaller j-class than
    # i-centraliser); (B) is faster otherwise. Dispatch.
    idx := intertwiner_data.idx;
    transport := intertwiner_data.transport;
    i := W_g1.class_idx;
    j := W_g2.class_idx;
    # K-2c (#129): GetTransport materialises per-class transports on
    # demand when `transport` came from BuildTransportsLazy, and is a
    # no-op when it came from eager BuildTransports.
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
    total := 0;
    if Length(elts_j) <= Length(cen_i_elts) then
        # Path (A): iterate class_j directly.
        for ai in [1..Length(elts_i)] do
            a := elts_i[ai];
            t_a := ts_i[ai];
            for bi in [1..Length(elts_j)] do
                b := elts_j[bi];
                if a * b <> b * a then continue; fi;
                s_b := ts_j[bi];
                b_in_C1 := t_a^-1 * b * t_a;     # ∈ C_G(g_1)
                a_in_C2 := s_b^-1 * a * s_b;     # ∈ C_G(g_2)
                eps := intertwiner_data.epsilon(W_g1.g, W_g2.g, a, b);
                chi1_val := intertwiner_data.trace_on_W(i, W_g1.irrep_idx, b_in_C1);
                chi2_val := intertwiner_data.trace_on_W(j, W_g2.irrep_idx, a_in_C2);
                total := total
                         + eps
                         * ComplexConjugate(chi1_val)
                         * ComplexConjugate(chi2_val);
            od;
        od;
    else
        # Path (B): iterate C_G(g_i) and conjugate by t_a.
        for ai in [1..Length(elts_i)] do
            a := elts_i[ai];
            t_a := ts_i[ai];
            for c in cen_i_elts do
                b := t_a * c * t_a^(-1);
                bi := LookupDictionary(elt_to_idx_j, b);
                if bi = fail then continue; fi;
                s_b := ts_j[bi];
                b_in_C1 := c;                    # = t_a^{-1} * b * t_a
                a_in_C2 := s_b^-1 * a * s_b;     # ∈ C_G(g_2)
                eps := intertwiner_data.epsilon(W_g1.g, W_g2.g, a, b);
                chi1_val := intertwiner_data.trace_on_W(i, W_g1.irrep_idx, b_in_C1);
                chi2_val := intertwiner_data.trace_on_W(j, W_g2.irrep_idx, a_in_C2);
                total := total
                         + eps
                         * ComplexConjugate(chi1_val)
                         * ComplexConjugate(chi2_val);
            od;
        od;
    fi;
    return total / ord;
end;;


# ============================================================
# Convenience: query S^Keller_{((g_1, k_1), (g_2, k_2))} given
# class/irrep coordinates, without manually building W_g records.
# ============================================================

ProjectorFormulaByIndex := function(class_idx_1, irrep_idx_1,
                                     class_idx_2, irrep_idx_2,
                                     intertwiner_data)
    local W1, W2;
    W1 := MakeWg(intertwiner_data, class_idx_1, irrep_idx_1);
    W2 := MakeWg(intertwiner_data, class_idx_2, irrep_idx_2);
    return ProjectorFormula(W1, W2, intertwiner_data);
end;;
