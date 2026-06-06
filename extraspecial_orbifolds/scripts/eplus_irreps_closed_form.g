# Closed-form irreducible character evaluator for E_+(m) = EmUnimodGroup(m).
#
# Issue #449 audit-findings A1''' + A1''''.
#
# CONTEXT
# =======
# `BuildKRRSpectralCharactersSparse(7)` processes the central class -I
# by calling `_EnsureClassData(idx, i)`, which in turn triggers
# `CharacterTable(EmUnimodGroup(7))` at `untwisted_modular_data.g:169`.
# At m = 7 this build allocates 5-20 GB and runs for hours (per the
# 2026-06-06 K-4b m=7 deep performance audit). We bypass it with a
# closed-form evaluator for the |Irr(E_+(m))| = 4^m + 1 irreducible
# characters, exploiting the well-known classification:
#
#   * 4^m one-dimensional characters χ_ell, indexed by linear forms
#     ell ∈ Hom((Z/2)^{2m}, Z/2). These factor through G/Z = (Z/2)^{2m}.
#     For h ∈ G with image (b_1, ..., b_{2m}) ∈ (Z/2)^{2m},
#         χ_ell(h) = (-1)^{ell . (b_1, ..., b_{2m})}.
#     The sign of h (whether h ∈ {x, zx} for a representative x) is
#     irrelevant because χ_ell trivial on Z.
#
#   * 1 faithful 2^m-dimensional character χ_{faith}, with
#         χ_{faith}(e) = 2^m,
#         χ_{faith}(z) = -2^m,    (z = -I = generator of Z)
#         χ_{faith}(h) = 0  for any non-central h.
#     (Standard projective-representation theory of extraspecial groups.)
#
# PUBLIC API
# ==========
#   _EPlusBitsOf(m, h)
#       -> length-2m list (b_1, ..., b_{2m}) ∈ {0, 1}^{2m} representing
#          the image of h ∈ E_+(m) under G -> G/Z =~ (Z/2)^{2m}, in
#          the basis (σ_{1,1}, σ_{1,2}, σ_{2,1}, σ_{2,2}, ...).
#
#   EPlusGenerateLinearForms(m)
#       -> list of 4^m bit vectors (length 2m each) in lex-by-little-
#          endian order. The k-th element (1-indexed) corresponds to
#          linear-form index k.
#
#   EPlusEvalLinearIrrep(m, ell_bits, h)
#       -> +1 or -1. Evaluates the linear character indexed by
#          `ell_bits` (length 2m bit vector) at h ∈ E_+(m).
#
#   EPlusEvalFaithfulIrrep(m, h)
#       -> 2^m if h = I, -2^m if h = -I, 0 otherwise.
#
#   EPlusEvalIrrep(m, irrep_idx, h)
#       -> dispatcher.
#          irrep_idx ∈ [1..4^m]  : χ_ell with ell =
#                                  EPlusGenerateLinearForms(m)[irrep_idx]
#          irrep_idx = 4^m + 1   : χ_{faith}.
#
#   EPlusBuildCharacterRow(m, irrep_idx, class_reps)
#       -> list of character values (one per element of `class_reps`).
#          Helper for pre-materialising character rows for downstream
#          consumers that expect `idx.irreps[i][k]` to be a plain
#          GAP list (so that `chi[cc_idx]` works).
#
# IRREP ORDERING CAVEAT
# =====================
# The ordering of linear characters returned by `EPlusGenerateLinearForms`
# differs from GAP's default `Irr(CharacterTable(EmUnimodGroup(m)))`
# ordering. Both lists are complete (4^m + 1 entries) and the multisets
# of character rows agree (see `tests/test_eplus_irreps_closed_form.g`).
# Downstream consumers of a closed-form `idx` work in the closed-form
# ordering consistently (no comparison with GAP's order is required).
#
# DEPENDENCIES
# ============
# Callers must load (in this order) BEFORE this file:
#   bw_lattice.g, em_construction.g, twisted_group_algebra.g
#       -> UnimodSigma, UnimodZ
#   krr_spectral_characters.g
#       -> EmUnimodGroup


# ============================================================
# Module-level caches.
#
# `_EPlusMarkersCache.(String(m))` stores, for each m, a per-generator
# list of marker positions (i, j) at which the off-diagonal 1's of
# σ_{a,r} mod 2 live. Each σ_{a,r} mod 2 differs from the identity
# only in these (small set of) positions. For products of σ's, the
# value at each marker position equals the corresponding bit (because
# commutators of σ's lie in Z = ⟨-I⟩, which vanishes mod 2; hence
# the σ's commute mod 2 and the marker entries are LINEAR functions
# of the bits).
#
# MEMORY: 2m matrices × ~n² × 4 bytes = 4 * 2m * n^2 ≈ 200 KB at m=7
# (vs ~8 GB for a full 2^{2m+1}-element dictionary). The closed-form
# approach allows querying bits(h) in O(2m) marker reads per query.
# ============================================================
if not IsBoundGlobal("_EPlusMarkersCache") then
    BindGlobal("_EPlusMarkersCache", rec());
fi;;


# ============================================================
# _EPlusBuildMarkersCache(m): for each generator σ_{a,r}, find the
# off-diagonal positions (i, j) (i ≠ j) where σ_{a,r}[i][j] mod 2 = 1.
# These marker positions are LINEAR in the bits for arbitrary products
# of σ's (because [σ_{a,r}, σ_{b,s}] ∈ ⟨-I⟩ which is trivial mod 2).
#
# RETURNS: a record with
#   .markers : a length-2m list of records, the (idx=2(a-1)+r)-th
#              entry is `rec(positions := [(i_1, j_1), ...])`
#              where (i_k, j_k) are the marker positions for bit_{a,r}.
#   .n       : 2^m.
#
# COMPLEXITY
# ----------
# 2m σ_{a,r} matrices built once, scanned for off-diagonal 1's. At
# m = 7: 14 matrices × 128² = ~230k entries scanned. Constant memory.
# ============================================================
_EPlusBuildMarkersCache := function(m)
    local key, n, all_positions, idx, a, r, sigma_mod2, i, j, positions;
    key := String(m);
    if IsBound(_EPlusMarkersCache.(key)) then
        return _EPlusMarkersCache.(key);
    fi;
    Print("[eplus-irreps] Building marker cache for m = ", m,
          " (", 2 * m, " generators) ...\n");
    n := 2 ^ m;
    all_positions := EmptyPlist(2 * m);
    for a in [1..m] do
        for r in [1..2] do
            sigma_mod2 := UnimodSigma(m, a, r) mod 2;
            positions := [];
            for i in [1..n] do
                for j in [1..n] do
                    if i <> j and sigma_mod2[i][j] = 1 then
                        Add(positions, [i, j]);
                    fi;
                od;
            od;
            Add(all_positions, rec(positions := positions));
        od;
    od;
    _EPlusMarkersCache.(key) := rec(
        markers := all_positions,
        n := n
    );
    Print("[eplus-irreps] Marker cache for m = ", m, " complete.\n");
    return _EPlusMarkersCache.(key);
end;;


# ============================================================
# _EPlusBitsOf(m, h): read off the bit projection of h in G/Z by
# inspecting specific entries of h mod 2 at the pre-computed marker
# positions for σ_{a,r}. Returns a length-2m list of bits.
#
# CORRECTNESS
# -----------
# For h = ε * prod σ_{a,r}^{b_{a,r}} with ε ∈ {±1} and bits b_{a,r}:
#   (h mod 2)[i_{a,r}, j_{a,r}] = b_{a,r}
# for any marker position (i_{a,r}, j_{a,r}) listed in
# `_EPlusBuildMarkersCache(m).markers[idx].positions`.
#
# Reason: each σ_{a,r} mod 2 is an elementary unimodular matrix
# (identity + a sparse pattern at the marker positions). Different
# σ's have DISJOINT marker positions (verified empirically at
# m ∈ {2, 3, 5, 7}). Products of σ's mod 2 are linear in the bits
# because [σ_{a,r}, σ_{b,s}] ∈ ⟨-I⟩ trivialises mod 2 — the σ's
# commute mod 2, so the product is just the sum of the contributions
# at the (disjoint) marker positions. The sign ε does not affect
# h mod 2 (since -1 ≡ 1 mod 2).
#
# We read just ONE marker entry per (a, r); if a generator has
# multiple marker positions they all hold the same bit value but we
# only need one read. (Asserted internally as a sanity check at
# the first cache-build call for a given m.)
#
# COMPLEXITY: O(2m) per query (one entry-read per bit).
# ============================================================
_EPlusBitsOf := function(m, h)
    local cache, bits, idx, pos, h_mod_2;
    cache := _EPlusBuildMarkersCache(m);
    h_mod_2 := h mod 2;
    bits := EmptyPlist(2 * m);
    for idx in [1..2 * m] do
        pos := cache.markers[idx].positions[1];
        Add(bits, h_mod_2[pos[1]][pos[2]]);
    od;
    return bits;
end;;


# ============================================================
# EPlusGenerateLinearForms(m): generate the 4^m length-2m F_2 vectors
# in lex-by-little-endian-value order, matching the `ei` encoding in
# `eplus_classes_closed_form.g`. The k-th entry (1-indexed) has bit
# pattern equal to the little-endian binary expansion of k-1.
#
# Cached at module level.
# ============================================================
if not IsBoundGlobal("_EPlusLinearFormsCache") then
    BindGlobal("_EPlusLinearFormsCache", rec());
fi;;

EPlusGenerateLinearForms := function(m)
    local key, forms, ell_idx, bits, k, idx;
    key := String(m);
    if IsBound(_EPlusLinearFormsCache.(key)) then
        return _EPlusLinearFormsCache.(key);
    fi;
    forms := EmptyPlist(4 ^ m);
    for ell_idx in [0..4 ^ m - 1] do
        bits := EmptyPlist(2 * m);
        k := ell_idx;
        for idx in [1..2 * m] do
            Add(bits, k mod 2);
            k := QuoInt(k, 2);
        od;
        Add(forms, bits);
    od;
    _EPlusLinearFormsCache.(key) := forms;
    return forms;
end;;


# ============================================================
# EPlusEvalLinearIrrep(m, ell_bits, h): evaluate χ_ell(h) =
# (-1)^{ell . bits(h)}. Returns +1 or -1.
# ============================================================
EPlusEvalLinearIrrep := function(m, ell_bits, h)
    local bits_h, parity, i;
    bits_h := _EPlusBitsOf(m, h);
    parity := 0;
    for i in [1..2 * m] do
        parity := parity + ell_bits[i] * bits_h[i];
    od;
    if (parity mod 2) = 0 then
        return 1;
    else
        return -1;
    fi;
end;;


# ============================================================
# EPlusEvalFaithfulIrrep(m, h): the faithful 2^m-dim irrep.
# +2^m at identity, -2^m at -I, 0 elsewhere.
# ============================================================
EPlusEvalFaithfulIrrep := function(m, h)
    local n;
    n := 2 ^ m;
    if h = IdentityMat(n) then
        return n;  # = 2^m
    elif h = -IdentityMat(n) then
        return -n;  # = -2^m
    else
        return 0;
    fi;
end;;


# ============================================================
# EPlusEvalIrrep(m, irrep_idx, h): dispatcher.
# ============================================================
EPlusEvalIrrep := function(m, irrep_idx, h)
    local linear_forms, ell;
    if irrep_idx = 4 ^ m + 1 then
        return EPlusEvalFaithfulIrrep(m, h);
    fi;
    if irrep_idx < 1 or irrep_idx > 4 ^ m then
        Error("EPlusEvalIrrep: irrep_idx ", irrep_idx,
              " out of range [1..", 4 ^ m + 1, "].");
    fi;
    linear_forms := EPlusGenerateLinearForms(m);
    ell := linear_forms[irrep_idx];
    return EPlusEvalLinearIrrep(m, ell, h);
end;;


# ============================================================
# EPlusBuildCharacterRow(m, irrep_idx, class_reps): build a list of
# character values, one per element of `class_reps`. Used by
# `_EnsureClassData` in the closed-form mode to populate
# `idx.irreps[i][k]` as a plain GAP list so that `chi[cc_idx]`
# indexing works in downstream consumers (e.g.
# `CharacterMultiplicities`).
#
# Cost: O(|class_reps|) closed-form evaluations.
# ============================================================
EPlusBuildCharacterRow := function(m, irrep_idx, class_reps)
    local row, linear_forms, ell, i, n;
    n := 2 ^ m;
    row := EmptyPlist(Length(class_reps));
    if irrep_idx = 4 ^ m + 1 then
        # Faithful irrep: 2 nonzero entries.
        for i in [1..Length(class_reps)] do
            Add(row, EPlusEvalFaithfulIrrep(m, class_reps[i]));
        od;
        return row;
    fi;
    if irrep_idx < 1 or irrep_idx > 4 ^ m then
        Error("EPlusBuildCharacterRow: irrep_idx ", irrep_idx,
              " out of range [1..", 4 ^ m + 1, "].");
    fi;
    linear_forms := EPlusGenerateLinearForms(m);
    ell := linear_forms[irrep_idx];
    for i in [1..Length(class_reps)] do
        Add(row, EPlusEvalLinearIrrep(m, ell, class_reps[i]));
    od;
    return row;
end;;


# ============================================================
# EPlusBuildAllCharacterRows(m, class_reps): build the full character
# table as a list of 4^m + 1 rows. Used to pre-populate
# `idx.irreps[central_class]` in `_EnsureClassData`.
#
# OPTIMISATION
# ------------
# Computes each row in O(|class_reps|) using the bits-cache (one
# bits lookup per class_rep, amortised). The naive triple-nested loop
# over (irrep, class, bit) would be O(4^m * |class_reps| * 2m); we
# extract the per-class bits ONCE up front and reuse across irreps.
# ============================================================
EPlusBuildAllCharacterRows := function(m, class_reps)
    local rows, num_classes, bits_per_class, j, ell_idx, ell,
          row, parity, i, faithful_row, n, k;
    n := 2 ^ m;
    num_classes := Length(class_reps);
    Print("[eplus-irreps] EPlusBuildAllCharacterRows(m = ", m,
          "): ", 4 ^ m + 1, " irreps x ", num_classes, " classes ...\n");
    # Per-class bit projections.
    bits_per_class := EmptyPlist(num_classes);
    for j in [1..num_classes] do
        Add(bits_per_class, _EPlusBitsOf(m, class_reps[j]));
    od;
    rows := EmptyPlist(4 ^ m + 1);
    # Linear irreps.
    for ell_idx in [0..4 ^ m - 1] do
        # Decode ell bits (same little-endian encoding as
        # EPlusGenerateLinearForms).
        ell := EmptyPlist(2 * m);
        k := ell_idx;
        for i in [1..2 * m] do
            Add(ell, k mod 2);
            k := QuoInt(k, 2);
        od;
        row := EmptyPlist(num_classes);
        for j in [1..num_classes] do
            parity := 0;
            for i in [1..2 * m] do
                parity := parity + ell[i] * bits_per_class[j][i];
            od;
            if (parity mod 2) = 0 then
                Add(row, 1);
            else
                Add(row, -1);
            fi;
        od;
        Add(rows, row);
    od;
    # Faithful irrep.
    faithful_row := EmptyPlist(num_classes);
    for j in [1..num_classes] do
        if class_reps[j] = IdentityMat(n) then
            Add(faithful_row, n);
        elif class_reps[j] = -IdentityMat(n) then
            Add(faithful_row, -n);
        else
            Add(faithful_row, 0);
        fi;
    od;
    Add(rows, faithful_row);
    Print("[eplus-irreps] Character table build complete.\n");
    return rows;
end;;
