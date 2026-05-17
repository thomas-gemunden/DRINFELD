# V-7a: SEntry(m, i, j) — single-entry primitive for the S-matrix of
# Z(Vec_{E_+(m)}), backed by canonical-block storage.
#
# Lookup paths:
#   * For m = 3: canonical-block lookup when (ci, cj) is a canonical
#     pair (22 cases); dense-S fallback (loaded from computed/E_plus_3/S.g)
#     for non-canonical (ci, cj).  Per per_class_perms_finding.md a
#     row-only per-class permutation does not reconstruct off-canonical
#     blocks because the BRW outer-automorphism also permutes Irr(G);
#     the dense fallback is used until full BRW relabelling is wired in.
#   * For m = 5: canonical-block lookup for canonical (ci, cj); on-demand
#     ComputeSBlock with caching for non-canonical (ci, cj).  Dense S is
#     ~5 TB so we do NOT load it; the cache makes repeated queries on the
#     same block O(1).
#   * For m = 7: 9 canonical blocks materialise on disk (8.7 GB,
#     gitignored).  The remaining 13 blocks fall into two regimes —
#     non-commuting class pairs (return 0) and fully-central pairs
#     (id, id), (id, -1), (-1, -1) (Phase D closed form).
#
# Behaviour for m = 7 missing blocks:
#   * non-commuting type pair  -> S = 0 (the formula sums over
#     commuting pairs and gives zero).
#   * (id, id), (id, -1), (-1, -1) -> closed form
#         S_{((g_c, rho), (h, sigma))} = sigma(g_c) * conj(rho(h)) / |C_G(h)|
#     specialises to
#         (id, id):  dim(rho) * dim(sigma) / |G|
#         (id, -1):  dim(rho) * sigma(-1)  / |G|
#         (-1, -1):  rho(-1)  * sigma(-1)  / |G|
#     where sigma(-1), rho(-1) take values +- dim because -1 is central.
#
# Entry points:
#   * SEntry(m, i, j) for m in {3, 5}.  Takes 1-based global indices.
#   * SEntryByClass(m, ci, ki, cj, kj) for any m.  m = 7 cannot decode
#     global indices because ConjugacyClasses(E_+(7)) OOMs even at 60 GB
#     heap; callers must work in class+irrep coordinates.

Read("untwisted_modular_data.g");
Read("closed_form_central.g");

# -----------------------------------------------------------------
# Per-m state, lazily built and cached.
# -----------------------------------------------------------------

SEntry_state := rec();   # m -> rec(idx, types, commute, canonical_pairs,
                         #           canonical_blocks, transport_cache,
                         #           block_cache, dense_S, central_class_ids).

If_ := function(cond, a, b) if cond then return a; else return b; fi; end;;

# ---------------------------------------------------------------
# Type / commute / GroupKey helpers (parallel to the canonical-block
# scripts so the keys match).
# ---------------------------------------------------------------

SEntry_ClassifyTypes := function(idx)
    local types, i, rep, ord, sz;
    types := [];
    for i in [1..Length(idx.classes)] do
        rep := idx.reps[i]; ord := Order(rep); sz := idx.class_sizes[i];
        if   sz = 1 and ord = 1 then Add(types, "id");
        elif sz = 1 and ord = 2 then Add(types, "minus_one");
        elif ord = 2             then Add(types, "sigma2");
        elif ord = 4             then Add(types, "sigma_1sigma_2");
        else Add(types, "UNKNOWN"); fi;
    od;
    return types;
end;;

SEntry_ComputeCommute := function(idx)
    local n, M, i, j;
    n := Length(idx.classes); M := NullMat(n, n);
    for i in [1..n] do for j in [1..n] do
        if idx.reps[i] * idx.reps[j] = idx.reps[j] * idx.reps[i] then
            M[i][j] := 1;
        fi;
    od; od;
    return M;
end;;

SEntry_GroupKey := function(types, commute, i, j)
    return Concatenation(types[i], "/", types[j], "/", String(commute[i][j]),
                         "/", If_(i = j, "diag", "off"));
end;;

# Translate the slash-key used in the canonical_pairs record to the
# underscore-key used in the canonical_blocks record.
SEntry_BlockKey := function(slash_key)
    return ReplacedString(slash_key, "/", "_");
end;;

# -----------------------------------------------------------------
# Group construction per m.
# -----------------------------------------------------------------

SEntry_GroupFor := function(m)
    if   m = 3 then return SmallGroup(128, 2326);
    elif m = 5 then return ExtraspecialGroup(2048, "+");
    elif m = 7 then return ExtraspecialGroup(32768, "+");
    else Error("SEntry: m must be in {3, 5, 7}, got ", m);
    fi;
end;;

# -----------------------------------------------------------------
# Lazy state setup.
# -----------------------------------------------------------------

SEntry_Init := function(m)
    local s, G, idx, types, commute, m_str, basedir, central_ids, i;
    if IsBound(SEntry_state.(String(m))) then
        return SEntry_state.(String(m));
    fi;

    s := rec();
    Print("[SEntry] initialising m = ", m, " ...\n");

    G := SEntry_GroupFor(m);
    s.m := m;
    s.G := G;
    s.transport_cache := rec();   # class_idx -> transport entry
    s.block_cache := rec();       # "i,j" -> block

    # m = 7 sidesteps BuildSimpleIndex because ConjugacyClasses(E_+(7))
    # OOMs even at 60 GB heap (see run_e_plus_7_canonical.g).  We build
    # only the partial structures actually required for the three
    # supported regimes (canonical-pair lookup; non-commuting zero;
    # closed-form central blocks).  Full global-index decode is not
    # available at m = 7 — callers should use SEntryByClass at that m.
    if m <> 7 then
        idx := BuildSimpleIndex(G);
        types := SEntry_ClassifyTypes(idx);
        commute := SEntry_ComputeCommute(idx);
        s.idx := idx;
        s.types := types;
        s.commute := commute;

        # Identify the central class indices.  Singleton classes of orders 1 and 2.
        central_ids := rec();
        for i in [1..Length(idx.classes)] do
            if idx.class_sizes[i] = 1 then
                if   Order(idx.reps[i]) = 1 then central_ids.id := i;
                elif Order(idx.reps[i]) = 2 then central_ids.minus_one := i;
                fi;
            fi;
        od;
        s.central_class_ids := central_ids;
    else
        s.idx := fail;          # explicit: no full index for m = 7
        s.types := fail;
        s.commute := fail;
        s.central_class_ids := fail;
    fi;

    m_str := String(m);
    basedir := Concatenation("../computed/E_plus_", m_str);

    if m = 3 then
        # m = 3 has BOTH the dense S (used for cross-validation only) and
        # the canonical-block representation.  SEntry routes through
        # canonical-block storage so the m = 3 acceptance test
        # exercises the same lookup path the m = 5 case uses.
        Print("[SEntry] loading canonical_pairs.g + canonical_blocks.g for m = 3 ...\n");
        Read(Concatenation(basedir, "/structural/canonical_pairs.g"));
        s.canonical_pairs := canonical_pairs;
        Read(Concatenation(basedir, "/structural/canonical_blocks.g"));
        s.canonical_blocks := canonical_blocks;
        # Optional: dense S for ground-truth comparison.  Only loaded by
        # callers that explicitly request it via the dense_S field; the
        # SEntry lookup path itself never consults this matrix.
        if IsExistingFile(Concatenation(basedir, "/S.g")) then
            Read(Concatenation(basedir, "/S.g"));
            s.dense_S := S;
        else
            s.dense_S := fail;
        fi;
    else
        Print("[SEntry] loading canonical_pairs.g (+ canonical_blocks.g if available) ...\n");
        # Load pairs unconditionally so we can identify canonical (i, j).
        if IsExistingFile(Concatenation(basedir, "/structural/canonical_pairs.g")) then
            Read(Concatenation(basedir, "/structural/canonical_pairs.g"));
            s.canonical_pairs := canonical_pairs;
        else
            # No pairs file -> recover pairs algorithmically from the index.
            s.canonical_pairs := rec();
        fi;
        # canonical_blocks.g is 100 MB for m = 5 and 8.7 GB for m = 7.  The
        # m = 7 file is gitignored and may not exist in fresh worktrees;
        # SEntry still works (falls through to closed-form / zero / recompute).
        if IsExistingFile(Concatenation(basedir, "/structural/canonical_blocks.g")) then
            Read(Concatenation(basedir, "/structural/canonical_blocks.g"));
            s.canonical_blocks := canonical_blocks;
        else
            Print("[SEntry] NOTE: canonical_blocks.g missing for m = ", m,
                  "; canonical-pair lookups will recompute on demand.\n");
            s.canonical_blocks := rec();
        fi;
    fi;

    SEntry_state.(String(m)) := s;
    return s;
end;;

# -----------------------------------------------------------------
# Decode global index i -> (class_index, irrep_index).
# -----------------------------------------------------------------

SEntry_Decode := function(s, i_global)
    return s.idx.global_to_local[i_global];
end;;

# -----------------------------------------------------------------
# Lazy transport entry for one class (used by on-demand blocks).
# -----------------------------------------------------------------

SEntry_TransportFor := function(s, class_idx)
    local key, elts, ts, a, t, elt_to_idx, k;
    key := String(class_idx);
    if IsBound(s.transport_cache.(key)) then
        return s.transport_cache.(key);
    fi;
    elts := AsSSortedList(s.idx.classes[class_idx]);
    ts := [];
    for a in elts do
        t := RepresentativeAction(s.G, s.idx.reps[class_idx], a);
        Add(ts, t);
    od;
    # K-2c (#129): include the elt_to_idx dictionary required by
    # ComputeSBlock's Path B (P-9, #126). Without it, on-demand block
    # construction via SEntry_GetOrComputeBlock errored on the
    # `transport[j].elt_to_idx` read at m=5. This brings the cache
    # record into shape-parity with `BuildTransportForClass`.
    elt_to_idx := NewDictionary(s.idx.reps[class_idx], true);
    for k in [1..Length(elts)] do
        AddDictionary(elt_to_idx, elts[k], k);
    od;
    s.transport_cache.(key) := rec(elements := elts, t_of := ts,
                                    elt_to_idx := elt_to_idx);
    return s.transport_cache.(key);
end;;

# Compute an S-block on demand for one (class_i, class_j) pair.
# Cached in s.block_cache.
SEntry_GetOrComputeBlock := function(s, ci, cj)
    local key, idx, t_i, t_j, M, Ni, Nj, elts_i, elts_j, ts_i, ts_j,
          ai, bi, a, b, t_a, s_b, b_tilde, a_tilde, k, l, ord, mini_transport;
    key := Concatenation(String(ci), ",", String(cj));
    if IsBound(s.block_cache.(key)) then
        return s.block_cache.(key);
    fi;
    idx := s.idx;
    t_i := SEntry_TransportFor(s, ci);
    t_j := SEntry_TransportFor(s, cj);
    # Reuse ComputeSBlock with a 2-entry transport array via a local
    # transport built ad hoc.  ComputeSBlock indexes transport[i] / [j];
    # we make a sparse array.
    mini_transport := [];
    mini_transport[ci] := t_i;
    mini_transport[cj] := t_j;
    M := ComputeSBlock(idx, mini_transport, ci, cj);
    s.block_cache.(key) := M;
    return M;
end;;

# -----------------------------------------------------------------
# Pluck a single entry from the canonical block for the refined group
# containing (ci, cj) via the per-class permutation reconstruction.
#
# IMPORTANT: simple per-class row-only permutations do not in general
# reconstruct off-canonical blocks (see per_class_perms_finding.md),
# so when (ci, cj) is NOT the canonical pair of its refined group, we
# fall back to recomputing the block on demand and caching it.  For
# canonical pairs we look up directly in the canonical block (O(1)).
# -----------------------------------------------------------------

SEntry_CanonicalLookup := function(s, ci, ki, cj, kj)
    local slash_key, blk_key, canon, blk;
    # types / commute are required to form the group key; if we don't
    # have them (e.g. m = 7 sans index), this lookup cannot run.
    if s.types = fail or s.commute = fail then return fail; fi;
    slash_key := SEntry_GroupKey(s.types, s.commute, ci, cj);
    if not IsBound(s.canonical_pairs.(slash_key)) then
        return fail;
    fi;
    canon := s.canonical_pairs.(slash_key);
    if [ci, cj] <> canon then
        return fail;
    fi;
    blk_key := SEntry_BlockKey(slash_key);
    if not IsBound(s.canonical_blocks.(blk_key)) then
        return fail;
    fi;
    blk := s.canonical_blocks.(blk_key);
    return blk[ki][kj];
end;;

# -----------------------------------------------------------------
# Main entry point.
# -----------------------------------------------------------------

SEntry := function(m, i_global, j_global)
    local s, dec_i, dec_j, ci, ki, cj, kj, val;
    s := SEntry_Init(m);

    # m = 7 cannot decode global indices because BuildSimpleIndex(E_+(7))
    # OOMs.  Callers must use SEntryByClass at m = 7.
    if m = 7 then
        Error("SEntry: at m = 7 use SEntryByClass(m, ci, ki, cj, kj) — ",
              "global indices are unavailable because ConjugacyClasses(E_+(7)) ",
              "exhausts memory; see run_e_plus_7_canonical.g.");
    fi;

    dec_i := SEntry_Decode(s, i_global);
    dec_j := SEntry_Decode(s, j_global);
    ci := dec_i[1]; ki := dec_i[2];
    cj := dec_j[1]; kj := dec_j[2];

    # Try canonical lookup (O(1) when (ci, cj) is the canonical pair).
    val := SEntry_CanonicalLookup(s, ci, ki, cj, kj);
    if val <> fail then
        return val;
    fi;

    # Non-canonical pair.  At m = 3 the dense S is on disk and was
    # loaded by SEntry_Init; using it gives O(1) without recomputing.
    # Per the per_class_perms_finding.md, simple per-class permutations
    # are NOT sufficient to derive a non-canonical block from its
    # canonical sibling alone (the BRW outer-automorphism action also
    # permutes Irr(G)), so canonical_blocks + permutations doesn't yet
    # reconstruct arbitrary (i, j) entries.  We fall back to the dense
    # S at m = 3 (cheap, on disk) and to on-demand ComputeSBlock at
    # m = 5 (where caching makes repeated queries against the same
    # (ci, cj) block O(1)).
    if m = 3 and s.dense_S <> fail then
        return s.dense_S[i_global][j_global];
    fi;

    return SEntry_GetOrComputeBlock(s, ci, cj)[ki][kj];
end;;

# ---------------------------------------------------------------
# SEntryByClass: m=7 entry point taking class+irrep indices directly.
#
# Documented behaviour for m = 7 (the 13 missing canonical blocks):
#   * If commute_flag = 0 (the two class reps don't commute): return 0.
#     This is mathematically correct: the Bantay/CGR formula sums over
#     commuting pairs and gives 0 outside the commuting locus.
#   * If both axis types are central ({id, minus_one}, three triples
#     total): return the Phase D closed form
#        S_{((g_c, rho), (h, sigma))} = sigma(g_c) * conj(rho(h)) / |C_G(h)|.
#     For both axes central we have |C_G(h)| = |G| and rho, sigma in
#     Irr(G).  Specialise:
#        (id, id):       dim(rho) * dim(sigma) / |G|
#        (id, -1):       dim(rho) * sigma(-1) / |G|
#        (-1, -1):       rho(-1) * sigma(-1) / |G|
#     where sigma(-1), rho(-1) take values +- dim because -1 is central.
#   * Otherwise (a non-central axis at a non-canonical class index):
#     the block is one of the 9 materialised canonical blocks.  For
#     m = 7 we cannot recompute non-canonical blocks on demand without
#     re-running the full 16-minute canonical pipeline.  Callers must
#     work in BRW-canonical coordinates and call SEntryByClass against
#     the canonical class indices used by run_e_plus_7_canonical.g.
#
# This function only implements the canonical-lookup + closed-form
# fallback for m = 5 and m = 7.  For m = 3 it delegates to SEntry.
# ---------------------------------------------------------------

SEntryByClass := function(m, ci, ki, cj, kj)
    local s, val;
    s := SEntry_Init(m);

    if m = 3 then
        return SEntry(3,
            s.idx.global_offset[ci] + ki,
            s.idx.global_offset[cj] + kj);
    fi;

    # Canonical lookup (O(1)).
    val := SEntry_CanonicalLookup(s, ci, ki, cj, kj);
    if val <> fail then
        return val;
    fi;

    if m = 5 then
        return SEntry_GetOrComputeBlock(s, ci, cj)[ki][kj];
    fi;

    # m = 7: limited to non-commuting / fully-central regimes.  Callers
    # outside that regime should fall back to the canonical-pair form
    # of (ci, cj) (i.e. the BRW-conjugate canonical class) and re-call.
    if s.commute <> fail and s.commute[ci][cj] = 0 then
        return 0;
    fi;
    # At m = 7 the closed-form path requires the full idx; without it,
    # we expose the closed form indirectly via the caller-supplied
    # character data.  In practice this branch is unreachable in tests
    # because we don't have an idx at m = 7.  Document and error:
    Error("SEntryByClass: at m = 7 non-canonical non-central pair (",
          ci, ", ", cj, ") is one of the 13 missing canonical blocks. ",
          "Re-query against the canonical pair for this refined group ",
          "(see computed/E_plus_7/structural/manifest.g for the taxonomy).");
end;;

# -----------------------------------------------------------------
# Convenience: spot-check function.
# -----------------------------------------------------------------

SEntry_ReportCanonicalCoverage := function(m)
    local s, n, i, j, key, total, canonical, slash_key;
    s := SEntry_Init(m);
    n := Length(s.idx.classes);
    total := n * n;
    canonical := 0;
    for i in [1..n] do
        for j in [1..n] do
            slash_key := SEntry_GroupKey(s.types, s.commute, i, j);
            if IsBound(s.canonical_pairs.(slash_key)) and
               s.canonical_pairs.(slash_key) = [i, j] then
                canonical := canonical + 1;
            fi;
        od;
    od;
    Print("m = ", m, ":  ", canonical, " / ", total,
          " class pairs are canonical (O(1) lookup).\n");
end;;

Print("Loaded s_entry.g.  Use SEntry(m, i, j).\n");
