# K-2: Single-entry S^Keller adapter.
#
# Wraps K-1's `ProjectorFormula` with the index-decoding logic that maps a
# global simple index i in [1..rank] to a class/irrep coordinate pair
# (class_idx, irrep_idx) within the Drinfeld center Z(Vec_{E_+(m)}).
#
# The public entry point is
#     SKeller(m, i, j)
# which returns the single complex (cyclotomic) entry
#     S^Keller_{ij}
# of the modular S-matrix of Z(Vec_{E_+(m)}) at omega = 0.
#
# At omega = 0 this reduces to the standard Bantay/CGR S-matrix entry; the
# acceptance criterion (issue #39) is that on central-row entries at m = 3
# the value agrees with the dense untwisted S computed by
# `untwisted_modular_data.g`.
#
# CONVENTIONS
# ===========
# * Global indices are 1-based and follow the same ordering as
#   `BuildSimpleIndex`: classes in the order returned by
#   `ConjugacyClasses(G)`, irreps in the order returned by Irr on the
#   centraliser of the class representative. The cumulative offsets are
#   `idx.global_offset[i]` so that the simple index for the k-th irrep on
#   class i is `idx.global_offset[i] + k`.
# * The total number of simples is `idx.rank`.
# * `idx.global_to_local[i]` directly decodes a global index to
#   `[class_idx, irrep_idx]`.
#
# V-2 DEPENDENCY NOTE
# ===================
# The issue body says the m = 3 acceptance is "agrees with V-2's S^omega
# for omega = 0". V-2 is not yet implemented in this branch. At omega = 0
# the V-2 closed form for central rows reduces to the standard untwisted
# S-matrix entry, so we use the dense untwisted S (computed by
# `ComputeSBlock` from `untwisted_modular_data.g`) as the V-2 stand-in.
# This is the same ground truth K-1's tests already validated.
#
# CACHING
# =======
# Building the intertwiner data for E_+(m) (in particular the transports)
# is expensive: it walks every class and calls `RepresentativeAction` for
# every element. We cache the data per m in a global `SKellerCache`,
# keyed by m, so a query session pays the build cost once.
#
# DEPENDENCIES
# ============
# Consumer must have read `em_construction.g`, `untwisted_modular_data.g`,
# and `krr_projector.g` (in that order) before this file. To avoid double-
# Read clobbering we do not Read them here.


# ============================================================
# Build E_+(m) as a finite group GAP can compute centralisers of.
# ============================================================
#
# `EmGroup(m)` from em_construction.g returns a matrix group; for
# m >= 3 the small-group library still recognises it (size 128 for m=3,
# 512 for m=4, etc.), but for fast centraliser/conjugacy operations we
# prefer the pc-group representation. We use IsomorphismPcGroup when
# available; otherwise we fall back to the matrix group.
#
# Returns a record:
#   .group   : a permutation/pc group isomorphic to E_+(m)
#   .matrix  : the original matrix group (for reference)
SKellerBuildEmAsPcOrPerm := function(m)
    local Gmat, iso, Gp;
    Gmat := EmGroup(m);
    # Try a pc-group representation (faster for centralisers / classes).
    iso := IsomorphismPcGroup(Gmat);
    if iso = fail then
        # Fallback: try a permutation representation.
        iso := IsomorphismPermGroup(Gmat);
        if iso = fail then
            return rec(group := Gmat, matrix := Gmat);
        fi;
    fi;
    Gp := Image(iso);
    return rec(group := Gp, matrix := Gmat);
end;;


# ============================================================
# Per-m intertwiner-data cache.
# ============================================================
#
# SKellerCache.[m] = record with fields
#       .group     : the finite group used (pc or perm)
#       .data      : intertwiner_data for that group
#       .rank      : total simples
#       .built_at  : Runtime() in ms when first built (for diagnostics)

if not IsBoundGlobal("SKellerCache") then
    BindGlobal("SKellerCache", rec());
fi;


# Force-rebuild (or build for the first time) the cache for E_+(m).
# Returns the cached intertwiner_data.
SKellerRebuildCache := function(m)
    local t0, Gbuilt, idata, entry, key;
    t0 := Runtime();
    Gbuilt := SKellerBuildEmAsPcOrPerm(m);
    # K-2c (#129): use the lazy intertwiner data so that CharacterTable
    # builds happen on-demand per class (only c1 and c2 for a single
    # SKeller(m, i, j) call) rather than eagerly for every class. At
    # m=7 this should turn the CT portion of cache build from minutes
    # into O(1) per query. Note: BuildTransports is still eager.
    idata := BuildIntertwinerDataUntwistedLazy(Gbuilt.group);
    entry := rec(
        group := Gbuilt.group,
        matrix := Gbuilt.matrix,
        data := idata,
        rank := idata.idx.rank,
        built_at := Runtime() - t0
    );
    key := Concatenation("m", String(m));
    SKellerCache.(key) := entry;
    return entry;
end;;


# Lazily fetch (and build if absent) the cache entry for E_+(m).
SKellerGetCache := function(m)
    local key;
    key := Concatenation("m", String(m));
    if not IsBound(SKellerCache.(key)) then
        return SKellerRebuildCache(m);
    fi;
    return SKellerCache.(key);
end;;


# ============================================================
# Public introspection: how many simples does E_+(m) have?
# ============================================================
SKellerRank := function(m)
    return SKellerGetCache(m).rank;
end;;


# ============================================================
# Decode a global simple index i in [1..rank] to (class_idx, irrep_idx).
# ============================================================
#
# Throws an error if i is out of range. Returns a 2-element list
# [class_idx, irrep_idx].
SKellerDecodeIndex := function(m, i)
    local entry, idx, pair;
    entry := SKellerGetCache(m);
    idx := entry.data.idx;
    if i < 1 or i > idx.rank then
        Error("global simple index out of range: i = ", i,
              " not in [1..", idx.rank, "] for E_+(", m, ")");
    fi;
    pair := idx.global_to_local[i];
    return [pair[1], pair[2]];
end;;


# Inverse: encode (class_idx, irrep_idx) -> global simple index.
SKellerEncodeIndex := function(m, class_idx, irrep_idx)
    local entry, idx;
    entry := SKellerGetCache(m);
    idx := entry.data.idx;
    if class_idx < 1 or class_idx > Length(idx.classes) then
        Error("class index out of range: class_idx = ", class_idx,
              " not in [1..", Length(idx.classes), "] for E_+(", m, ")");
    fi;
    if irrep_idx < 1 or irrep_idx > idx.num_irreps[class_idx] then
        Error("irrep index out of range: irrep_idx = ", irrep_idx,
              " not in [1..", idx.num_irreps[class_idx],
              "] for class ", class_idx, " of E_+(", m, ")");
    fi;
    return idx.global_offset[class_idx] + irrep_idx;
end;;


# ============================================================
# THE PUBLIC ADAPTER: SKeller(m, i, j).
# ============================================================
#
# Returns the single S^Keller entry at global indices (i, j) for
# Z(Vec_{E_+(m)}) at omega = 0.
SKeller := function(m, i, j)
    local entry, di, dj, c1, k1, c2, k2;
    entry := SKellerGetCache(m);
    di := SKellerDecodeIndex(m, i);
    dj := SKellerDecodeIndex(m, j);
    c1 := di[1]; k1 := di[2];
    c2 := dj[1]; k2 := dj[2];
    return ProjectorFormulaByIndex(c1, k1, c2, k2, entry.data);
end;;


# ============================================================
# Convenience: list the central-row global indices for E_+(m).
# Central rows correspond to class indices with |class| = 1 and
# representative central in G. For E_+(m) these are the two singleton
# central classes containing 1 and z = -I. Each carries 2^{2m} linear
# irreps.
# ============================================================
SKellerCentralRowIndices := function(m)
    local entry, idx, central, out, i, g, gens, ok, h, k;
    entry := SKellerGetCache(m);
    idx := entry.data.idx;
    central := [];
    gens := GeneratorsOfGroup(idx.group);
    for i in [1..Length(idx.classes)] do
        if idx.class_sizes[i] <> 1 then continue; fi;
        g := idx.reps[i];
        ok := true;
        for h in gens do
            if g * h <> h * g then ok := false; break; fi;
        od;
        if ok then Add(central, i); fi;
    od;
    out := [];
    for i in central do
        for k in [1..idx.num_irreps[i]] do
            Add(out, idx.global_offset[i] + k);
        od;
    od;
    return out;
end;;
