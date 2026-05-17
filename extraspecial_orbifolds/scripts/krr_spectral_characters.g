# K-4a-T4c (issue #208): Spectral trace_on_W from KRR lattice
# intertwiners.
#
# Implements `BuildKRRSpectralCharacters(m)` which returns a record
# providing a `trace_on_W(class_idx, irrep_idx, h)` callable derived
# from KRR's lattice intertwiners T_h on Omega_0.
#
# IMPORTANT — SEMANTICS:
#   trace_on_W(class_idx, irrep_idx, h) returns
#     Tr(T_h | W_a^chi_k) = mult_k * chi_k(h)
#   where mult_k is the dimension of the irrep_idx-th joint eigenspace
#   of {T_h : h in generators of C_G(a)} on W_a, and chi_k is the
#   linear character carried by that eigenspace.  This is the
#   "spectral trace" — NOT the standard untwisted character functional
#   used by `BuildIntertwinerDataUntwisted` in krr_projector.g (which
#   returns chi_k(h) directly with no multiplicity weighting).
#
# To use this in a `ProjectorFormula`-compatible record, a downstream
# normalisation (divide by mult_k, or equivalently treat each joint
# eigenspace as one "simple" with dim = mult_k) is required.  That
# normalisation is the K-4a / K-4 integration step and is OUT OF
# SCOPE for this PR — see issue #208 acceptance tests, which only
# verify the joint-eigendecomposition + character_match pipeline.
#
# Also note: `idx.num_irreps[i]` (from `BuildSimpleIndex`) gives the
# total irrep count |Irr(C_G(g_i))| (e.g. 65 at m=3 for the central
# class -I in E_+(3)), while the central class's `character_match[i]`
# from this file has *only* `Length(eigenspaces)` entries (e.g. 12 at
# m=3) — one per joint eigenspace, NOT one per standard irrep.  The
# central class's `irrep_idx` here is therefore in [1..K] for K <
# `idx.num_irreps[i]`.  Downstream code that iterates over all
# `idx.num_irreps[i]` (e.g. `ProjectorFormula`) will receive
# out-of-range errors unless K-4 reconciles the two indexings.
#
# Math summary (see DRINFELD-wt-k4a-t4a/docs/superpowers/research/
# 2026-05-17-epsilon-extraction-from-krr.md for the full derivation):
#
# Per KRR (arXiv:2411.13646) and verified in `test_defect_rep_optim.g`
# Tests 3 and 4 for m = 5, 7, the intertwiners T_h on the defect rep
# Omega_0 (for the central twist g = -I) satisfy
#   T_h^2 = scalar * I,    T_{h_1} T_{h_2} = T_{h_2} T_{h_1}        (*)
# for h running over the natural generators {Sigma_{a, r}} of E_+(m).
# After normalisation \hat{T}_h := T_h / 2^k these are commuting
# involutions, faithfully representing E_+(m)/<z> = F_2^{2m}.
#
# Omega_0 then decomposes as a direct sum of joint eigenspaces under
# {\hat{T}_h : h in generators}.  Each joint eigenspace W_a^chi carries
# a linear character chi of C_G(a) (the eigenvalue of \hat{T}_h is
# chi(h)).
#
# For non-central twists a != -I, the centraliser C_G(a) acts
# trivially on N (KRR p.13, end of section 4.4 — empirically verified
# in `test_defect_rep_other.g`), so T_h on Omega_theta is itself
# trivial and there is no non-trivial spectral information to extract.
# In that case we fall back to the standard centraliser-character
# functional (EvalIrr) which is the omega = 0 ground truth — same as
# `BuildIntertwinerDataUntwisted` (krr_projector.g).
#
# This file is a pure library (no QUIT).
#
# DEPENDENCIES (already loaded by the test driver):
#   em_construction.g        -> Sigma_ar, ZGen, EmGroup
#   twisted_group_algebra.g  -> UnimodSigma, UnimodZ
#   bw_lattice.g, qforms_f2.g
#   defect_rep_minus_id.g    -> BuildIntertwiner, InterTwineref,
#                               BasisForN, TwoCocycleForN, F2_ZeroVec,
#                               DecodeBitVec, EncodeBitVec
#   defect_rep_minus_id_optim.g
#                            -> HardCodeShortComputeInterTwineref,
#                               _efPerHData, _efShAndTarget
#   untwisted_modular_data.g -> BuildSimpleIndex, EvalIrr,
#                               ClassIndexInCentraliser
#
# IMPORTANT: defect_rep_minus_id_optim.g overrides several functions
# defined in defect_rep_minus_id.g (F2_Mul, F2_VMul, F2_Trans, F2_Add,
# MatOfBilForm) with faster versions. Always Read the optim file LAST
# among those two.

# ============================================================
# EmUnimodGroup: matrix group built from UnimodSigma generators.
# This is the lattice-basis representation of E_+(m); same abstract
# group as EmGroup(m) but the generators are the unimodular lattice
# matrices that the optim pipeline consumes directly.
#
# PERFORMANCE NOTE: at m >= 5 the matrix group has degree 2^m >= 32
# and GAP's `ConjugacyClasses(EmUnimodGroup(m))` / `CharacterTable` calls
# are slow (and can run out of memory).  For m = 5 in production, the
# convention used elsewhere in this repo is
#   `Image(IsomorphismPcGroup(EmGroup(m)))`
# which gives a pc-group of order 2^{2m+1} that GAP handles
# efficiently.  Migrating BuildKRRSpectralCharacters to use a pc-group
# would require:
#   1. Build the isomorphism phi : pc-group -> EmUnimodGroup.
#   2. For every centraliser element h in pc-group form, apply phi to
#      get the integer matrix that the optim pipeline expects.
# This is mechanical but adds complexity; deferred until m = 5 is
# actually required by downstream code.
# ============================================================

EmUnimodGroup := function(m)
    local n, gens, a, r;
    n := 2^m;
    gens := [-IdentityMat(n)];
    for a in [1..m] do
        for r in [1, 2] do
            Add(gens, UnimodSigma(m, a, r));
        od;
    od;
    return Group(gens);
end;;


# ============================================================
# Build the full (2^k x 2^k) intertwiner T_h matrix on Omega_0,
# using the optim closed-form entries.
# ============================================================
#
# Returns M such that M[di][ci] = (T_h)_{c, d} where c, d are the F_2
# vectors corresponding to ci, di (via DecodeBitVec), matching the
# convention of `BuildIntertwiner` in defect_rep_minus_id.g.
#
# Cost: O(2^{2k}) entries, each evaluated via
# HardCodeShortComputeInterTwineref.
#   m = 3 (k = 4):  dim W_a = 16, matrix has 256 entries — ~10 ms.
#   m = 5 (k = 16): dim W_a = 65536, matrix has 2^32 ≈ 4.3e9 entries
#                   × ~27 ms/entry (measured) = ~3.7 YEARS for ONE
#                   matrix.  NOT FEASIBLE with the present full-matrix
#                   approach.
#   m = 7 (k = 64): dim W_a = 2^64 ≈ 1.8e19, completely infeasible.
#
# For m >= 5 a sparse / structural method is required.  Possible
# approaches: (a) compute traces Tr(T_h^j) for the centraliser
# generators directly via the closed-form Schur sums (each trace is a
# sum of only 2^k = 65536 diagonal entries, doable in ~30 minutes per
# trace), and use character-theoretic inversion to read off
# multiplicities; (b) Lanczos-style power iteration to find one
# eigenvalue at a time; (c) restrict to a small invariant subspace
# using known structure.  Tracked as a follow-up to this PR.
BuildIntertwinerOptim := function(h, m)
    local k, dim, M, ci, di, c, d, val, zero_k, zero_n, mhh, A, B, R;
    k := 2^(m - 1);
    dim := 2^k;
    zero_k := F2_ZeroVec(k);
    zero_n := F2_ZeroVec(2 * k);
    mhh := MhHalfefMat(h, m);
    A := Kernef(h, m);
    B := BasisForN(m);
    R := TwoCocycleForN(m);
    # Trigger per-h cache for h.
    _efPerHData(h, m);
    _efShAndTarget(h, m);
    M := List([1..dim], i -> List([1..dim], j -> 0));
    for ci in [1..dim] do
        c := DecodeBitVec(ci, k);
        for di in [1..dim] do
            d := DecodeBitVec(di, k);
            val := HardCodeShortComputeInterTwineref(
                       h, zero_k, zero_k, c, d, zero_n,
                       mhh, A, B, R, m);
            M[di][ci] := val;
        od;
    od;
    return M;
end;;


# ============================================================
# Normalisation helper: (T_h^2)_{0,0} is 2^{2k} per the
# Appendix A-bis observation in the T4a research note. Scale so that
# T_h^2 = I.
# ============================================================

NormaliseIntertwiner := function(M, m)
    local k, scale, dim;
    k := 2^(m - 1);
    # (M^2)_{0, 0}: M is 2^k x 2^k.  After normalisation by 2^k,
    # M^2 should be I.
    scale := 2^k;
    dim := 2^k;
    return List([1..dim], i -> List([1..dim], j -> M[i][j] / scale));
end;;


# ============================================================
# Joint eigendecomposition of a commuting family {M_1, ..., M_t}.
# Returns a list of records, each with .basis (a list of vectors
# spanning the joint eigenspace) and .eigenvalues (the eigenvalue
# tuple).  The eigenspaces are returned in some deterministic order
# (sorted by their eigenvalue tuples).
# ============================================================

# Internal: refine a list of vector-space records under one new matrix.
# Each input record has .basis (list of row vectors) and .eigenvalues
# (a list of eigenvalues so far). Returns a new list of records
# refining each input by the eigenspaces of M acting on its basis.
_RefineByMatrix := function(eigenspaces, M, field)
    local newlist, rec_es, basis, restricted, i, evs,
          ev, vects, kerBasis, restRow, newRec, c, dim_in, M_T;
    newlist := [];
    # Audit (#258 follow-up): hoist TransposedMat(M) out of the per-record
    # loops below. M is loop-invariant across all eigenspaces and basis
    # vectors; one transpose suffices.
    M_T := TransposedMat(M);
    for rec_es in eigenspaces do
        basis := rec_es.basis;
        dim_in := Length(basis);
        if dim_in = 0 then
            continue;
        fi;
        # Express the action of M on the span(basis) as a dim_in x dim_in
        # matrix `restricted`.  M acts by column-vector multiplication
        # on R^n: y = M * x.  But our basis vectors are row vectors.
        # We need to write the matrix of M restricted to span(basis),
        # i.e. find scalars c_{i,j} such that M * basis[i] = sum_j c_{i,j} basis[j].
        # If basis is a Length(basis) x n matrix B (rows), then
        #   M B^T = B^T * C^T   <=>   B M^T = C B    <=>   C = (B M^T) * B^(-1)
        # But B is rectangular; we instead solve   M * basis[i]^T = (sum_j c_{i,j} basis[j])^T.
        # Equivalently: for each row basis[i] of B, compute v_i := M * basis[i]^T
        # (a column vector), then express v_i in the basis B (as a row).
        # Concretely: solve C such that C * B = (M * B^T)^T, i.e. C * B = B * M^T.
        # So C is the change-of-basis matrix.
        # GAP: use SolutionMat repeatedly.
        restricted := [];
        for i in [1..dim_in] do
            # restRow such that  restRow * basis  =  M * basis[i]  (as row vec)
            # i.e. basis[i] is a row vector; compute  basis[i] * M^T (row times matrix)
            # which equals (M * basis[i]^T)^T  =  row vector.
            restRow := basis[i] * M_T;
            # Express restRow as a linear combination of basis vectors:
            # solve  c * basis = restRow.
            c := SolutionMat(basis, restRow);
            if c = fail then
                Error("Matrix does not preserve eigenspace: ",
                      "M * basis[", i, "] is not in span(basis).");
            fi;
            Add(restricted, c);
        od;
        # Now compute eigenvalues / eigenspaces of `restricted` (dim_in x dim_in).
        evs := Eigenvalues(field, restricted);
        for ev in evs do
            # Eigenspace of `restricted` for ev: solve (restricted - ev*I)^T * y = 0
            # i.e. left nullspace of (restricted - ev*I).
            # Convert the eigenspace back to vectors in the original space.
            kerBasis := NullspaceMat(TransposedMat(
                  restricted - ev * IdentityMat(dim_in)));
            # Each row of kerBasis is a coefficient vector; the corresponding
            # actual vector in original space is row * basis.
            vects := List(kerBasis, r -> r * basis);
            newRec := rec(
                basis := vects,
                eigenvalues := Concatenation(rec_es.eigenvalues, [ev])
            );
            Add(newlist, newRec);
        od;
    od;
    return newlist;
end;;

# Joint eigendecomposition of a list of commuting matrices M_list,
# acting on the standard R^n column-vector space, over `field`
# (typically Rationals; eigenvalues fall in {1, -1} for our case).
# Returns a list of records with fields .basis (list of row vectors
# spanning the joint eigenspace) and .eigenvalues (tuple of eigenvalues
# for each M_i in order).
JointEigendecomposition := function(M_list, field)
    local dim, eigenspaces, M;
    if Length(M_list) = 0 then
        Error("JointEigendecomposition: empty matrix list.");
    fi;
    dim := Length(M_list[1]);
    # Start with the whole space: a single record with .basis = full
    # standard basis and .eigenvalues = empty tuple.
    eigenspaces := [
        rec(basis := IdentityMat(dim), eigenvalues := [])
    ];
    for M in M_list do
        eigenspaces := _RefineByMatrix(eigenspaces, M, field);
    od;
    return eigenspaces;
end;;


# ============================================================
# Per-class W_a setup.
# ============================================================

# For a given class representative a (a matrix in EmUnimodGroup), and
# given generators of C_G(a), build the list of normalised T_h matrices
# on W_a.  For the central class a = -I, the optim pipeline applies
# directly: W_a = Omega_0 = R^{2^k} (k = 2^{m-1}), and T_h is computed
# via BuildIntertwinerOptim.
#
# For non-central a, KRR show that the centraliser action is trivial,
# so T_h = I for every h ∈ C_G(a).  We then return an empty list
# (signalling "use the standard character functional"); the caller is
# responsible for handling that case.
#
# Returns a record:
#   .is_central     : true iff a = +/- I (centre of E_+(m))
#   .W_dim          : dimension of W_a as a complex vector space
#   .T_gens         : list of T_h matrices on W_a (one per centraliser generator)
#   .gen_elements   : the centraliser generators h (parallel to T_gens)
BuildTgens := function(a, G, m)
    local n, k, dim, is_minus_id, C, gens, T_gens, h, T_h, T_h_norm,
          z, idMat;
    n := 2^m;
    k := n / 2;
    dim := 2^k;
    z := -IdentityMat(n);
    idMat := IdentityMat(n);
    # The KRR defect-rep machinery (defect_rep_minus_id_optim.g) is
    # specific to the central twist a = -I.  For all other classes
    # (including the trivial class a = identity), the joint
    # eigendecomposition reduces to the standard centraliser-character
    # fallback (per the T4a research note: ε ≡ 1 and trace_on_W reduces
    # to EvalIrr for these classes).
    is_minus_id := (a = z);
    C := Centralizer(G, a);
    gens := GeneratorsOfGroup(C);
    if is_minus_id then
        T_gens := [];
        for h in gens do
            if h = idMat then
                # T_e is the identity matrix on Omega_0.
                Add(T_gens, IdentityMat(dim));
            else
                T_h := BuildIntertwinerOptim(h, m);
                T_h_norm := NormaliseIntertwiner(T_h, m);
                Add(T_gens, T_h_norm);
            fi;
        od;
        return rec(is_minus_id := true,
                   W_dim := dim,
                   T_gens := T_gens,
                   gen_elements := gens);
    fi;
    # Non-(-I) class: identity, non-central, or order-4 representative.
    # For non-central a ≠ -I, KRR §4.4 establishes that the centraliser
    # acts trivially on N_theta, so T_h on Omega_theta is itself
    # trivial.  For the identity class, the KRR defect-rep machinery
    # does not directly apply; the standard untwisted character
    # functional is correct (ω = 0 baseline).  In both cases we fall
    # back to EvalIrr.
    return rec(is_minus_id := false,
               W_dim := fail,
               T_gens := fail,
               gen_elements := gens);
end;;


# ============================================================
# Character matching: given a joint-eigenspace eigenvalue tuple
# (eigenvalues on generators h_1, ..., h_t of C_G(a)), find the
# index k in Irr(C_G(a)) such that chi_k(h_i) = eigenvalue_i for all
# i. Returns the index in Irr(C_G(a)), or `fail`.
# ============================================================

MatchCharacter := function(idx, class_idx, generators, eigenvalues)
    local irreps, num_irreps, k, chi, match, i, val,
          gen_class_indices;
    irreps := idx.irreps[class_idx];
    num_irreps := idx.num_irreps[class_idx];
    # Precompute the class index of each generator in C_G(a).
    gen_class_indices := List(generators,
                               h -> ClassIndexInCentraliser(idx, class_idx, h));
    for k in [1..num_irreps] do
        chi := irreps[k];
        match := true;
        for i in [1..Length(generators)] do
            val := chi[gen_class_indices[i]];
            if val <> eigenvalues[i] then
                match := false;
                break;
            fi;
        od;
        if match then
            return k;
        fi;
    od;
    return fail;
end;;


# ============================================================
# BuildKRRSpectralCharacters(m) -- the main entry point.
# ============================================================

BuildKRRSpectralCharacters := function(m)
    local n, k, dim, G, idx, num_classes, character_match,
          eigenspace_cache, trace_on_W, i, a, setup, eigenspaces,
          em, es, std_idx, z, idMat;
    n := 2^m;
    k := n / 2;
    dim := 2^k;
    G := EmUnimodGroup(m);
    idx := BuildSimpleIndex(G);
    num_classes := Length(idx.classes);
    z := -IdentityMat(n);
    idMat := IdentityMat(n);

    # Per-class precomputation: eigenspaces (for central) and matching.
    # eigenspace_cache[i] is either:
    #   - a list of records (one per joint eigenspace), each with
    #     .basis, .eigenvalues, .standard_irrep_idx, .multiplicity
    #     (the dim of the joint eigenspace, which equals the multiplicity
    #     of the matched chi in W_a).
    #   - `false` for non-central classes (handled by fallback).
    eigenspace_cache := [];
    # character_match[i] is a list of records, one per irrep_idx.
    character_match := [];

    for i in [1..num_classes] do
        a := idx.reps[i];
        setup := BuildTgens(a, G, m);
        if not setup.is_minus_id then
            # Class is not the central -I twist.  Use the standard
            # centraliser-character fallback (ε ≡ 1, trace_on_W = EvalIrr).
            # irrep_idx maps to standard_irrep_idx by the identity
            # permutation; eigenvalue_pattern is "all 1's" (since T_h
            # is trivial / not used).
            eigenspace_cache[i] := false;
            character_match[i] := List([1..idx.num_irreps[i]], irrep_idx ->
                rec(standard_irrep_idx := irrep_idx,
                    eigenvalue_pattern :=
                        List(setup.gen_elements, h -> 1)));
            continue;
        fi;
        # Central class: joint eigendecomposition.
        eigenspaces := JointEigendecomposition(setup.T_gens, Rationals);
        # Match each joint eigenspace to a standard irrep.
        em := [];
        for es in eigenspaces do
            std_idx := MatchCharacter(idx, i, setup.gen_elements,
                                       es.eigenvalues);
            Add(em, rec(basis := es.basis,
                        eigenvalues := es.eigenvalues,
                        standard_irrep_idx := std_idx,
                        multiplicity := Length(es.basis)));
        od;
        eigenspace_cache[i] := em;
        # character_match[i]: irrep_idx -> rec(standard_irrep_idx,
        # eigenvalue_pattern).  We use the joint-eigenspace ordering for
        # irrep_idx (NOT the standard Irr() ordering).  This is the
        # "K-4a-T4c-native" labelling.
        character_match[i] := List(em, x ->
            rec(standard_irrep_idx := x.standard_irrep_idx,
                eigenvalue_pattern := x.eigenvalues));
    od;

    # ====================================================================
    # trace_on_W(class_idx, irrep_idx, h) =
    #   trace of T_h restricted to the (class_idx, irrep_idx)-th
    #   joint eigenspace of {T_h : h in generators of C_G(a)}.
    # ====================================================================
    #
    # For central classes: trace is multiplicity * chi(h), where chi is
    #   the linear character carried by the irrep_idx-th joint eigenspace.
    #   chi(h) is obtained from the standard_irrep_idx match (if any) or
    #   from a direct entry-by-entry T_h computation on the eigenspace.
    # For non-central classes: fall back to the standard centraliser
    #   character via EvalIrr.
    trace_on_W := function(class_idx, irrep_idx, h)
        local em, e_rec, std_idx, idMat_loc, T_h_full, T_h_full_T,
              v, b, total, j, c, mult;
        idMat_loc := IdentityMat(2^m);
        if eigenspace_cache[class_idx] = false then
            # Non-central fallback.
            return EvalIrr(idx, class_idx, irrep_idx, h);
        fi;
        em := eigenspace_cache[class_idx];
        if irrep_idx < 1 or irrep_idx > Length(em) then
            Error("trace_on_W: irrep_idx ", irrep_idx,
                  " out of range for class ", class_idx,
                  " (have ", Length(em), " eigenspaces).");
        fi;
        e_rec := em[irrep_idx];
        std_idx := e_rec.standard_irrep_idx;
        mult := e_rec.multiplicity;
        # If h is the identity, T_h is the identity, so trace is dim(W_a^chi).
        if h = idMat_loc then
            return mult;
        fi;
        # If we successfully matched a standard irrep, use its character
        # value (avoids computing T_h for arbitrary h).
        if std_idx <> fail then
            return mult * EvalIrr(idx, class_idx, std_idx, h);
        fi;
        # Fallback (shouldn't happen for m=3, 5, 7 per T4a's analysis):
        # build T_h fully and compute its trace on the eigenspace basis.
        T_h_full := NormaliseIntertwiner(BuildIntertwinerOptim(h, m), m);
        # Audit (#258 follow-up): hoist TransposedMat(T_h_full) out of the
        # for-j loop. T_h_full is loop-invariant; transposing it once instead
        # of per-iteration trims wall in the rare fallback path.
        T_h_full_T := TransposedMat(T_h_full);
        # Trace of T_h restricted to the eigenspace = sum_i b_i^T * T_h * b_i
        # / (b_i^T * b_i)  if orthonormal; for generic basis use
        # b_i^T * T_h * dual_basis_i.  Simpler: compute the projector
        # P = sum_i basis_i (basis_i^T projected); but for diagonal action
        # the trace = mult * (eigenvalue of T_h on the eigenspace).
        # Since we have the basis as row vectors and T_h acts (column-vec
        # convention) as v |-> T_h * v, the restriction-trace equals
        # the trace of the basis-change of T_h on the eigenspace basis.
        # Compute via: for each basis vec b, find c such that c * basis = b * T_h^T;
        # the trace is sum of c[i]_i (diagonal of restriction).
        total := 0;
        for j in [1..Length(e_rec.basis)] do
            b := e_rec.basis[j];
            v := b * T_h_full_T;
            c := SolutionMat(e_rec.basis, v);
            if c = fail then
                # Should not happen — T_h preserves joint eigenspaces.
                Error("trace_on_W: T_h does not preserve eigenspace ",
                      irrep_idx, " of class ", class_idx);
            fi;
            total := total + c[j];
        od;
        return total;
    end;

    return rec(
        group := G,
        idx := idx,
        m := m,
        trace_on_W := trace_on_W,
        character_match := character_match,
        # Diagnostic / introspection:
        eigenspace_cache := eigenspace_cache
    );
end;;
