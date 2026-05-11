# aut_nt.g — Aut(N, T) by backtracking with refinement-based pruning.
#
# Task V-5c (issue #36). Builds on:
#   * aut_nt_partition.g (V-5a) — InitialPartition(N, T, QD) by joint
#     (T, QD) value.
#   * aut_nt_refine.g    (V-5b) — RefineByFusion(p, N) iterating
#     colour-refinement (1-WL) on fusion-row signatures.
#
# Goal. Given a modular tensor category C with fusion ring N (3D list
# of non-negative integers, the Verlinde coefficients N_{ij}^k),
# T-vector T (list of cyclotomics, length r = #simples) and QD list,
# compute
#
#     Aut(N, T) := { σ ∈ Sym([1..r]) : T_{σ(i)} = T_i for all i,
#                                      N_{σ(i),σ(j)}^{σ(k)} = N_{ij}^k
#                                      for all i, j, k }.
#
# AutNT(N, T, QD) returns rec(order, generators) where `generators` is
# a list of permutations encoded as length-r lists (σ[i] = image of i).
#
# Algorithm. Classical McKay-style backtracking over partial maps:
#
#   State: sigma_partial[1..r]  - partial assignment, 0 = unassigned.
#          image_used[1..r]     - boolean, true if some i has σ(i) = t.
#          p_src                - partition of [1..r] as source-side
#                                 orbits under the current partial-σ-
#                                 induced refinement (i.e. blocks of
#                                 unassigned sources sharing the same
#                                 colour-refinement signature).
#          p_img                - same for image-side. Always parallel
#                                 to p_src: source-block B has image-
#                                 block σ(B) of the same size.
#
# Each branching step: pick first non-singleton source-block B, with
# representative b0 := B[1]. For each candidate image t ∈ (image-block
# of B), set σ(b0) := t, refine both partitions (each must split
# {b0} and {t} into singletons), recurse.
#
# At a leaf (every block in p_src is a singleton), σ is determined:
# for each source-singleton {s}, σ(s) is the SOLE element of the
# matching image-block. (Refinement-induced singletons {x} in p_src
# correspond to refinement-induced singletons {y} = {x_image} in
# p_img with x = y when no branching has happened yet; matching is
# tracked via the colour vector — both partitions have the same colours
# in the same order.)
#
# Orbit-stabiliser counting. At the top, the orbit O(b0) of b0 is the
# set of t ∈ image-block(b0) admitting at least one extension. The
# stabiliser is |Aut_{σ(b0)=b0}(N, T)|, recursively. The order is the
# product. We collect generators by tagging each non-identity leaf σ
# during the orbit-enumeration.
#
# Complexity. Each refinement is O(r^3). The orbit-stabiliser tree
# depth is the number of non-singleton blocks we encounter, bounded
# by r. So |Aut(N,T)| × r^4 total work. For r = 22 this is ~10^5;
# for r = 184 it is ~10^9 in the worst case — slow but OK in GAP.
#
# Globals installed by this file:
#   AutNT(N, T, QD[, opts])     — main entry point.
#   IsAutomorphismCandidate(σ, N) — verify σ preserves N.

# ---- Verification ----------------------------------------------------

IsAutomorphismCandidate := function(sigma, N)
    local r, i, j, k;
    r := Length(sigma);
    if Length(N) <> r then
        return false;
    fi;
    for i in [1 .. r] do
        for j in [1 .. r] do
            for k in [1 .. r] do
                if N[sigma[i]][sigma[j]][sigma[k]] <> N[i][j][k] then
                    return false;
                fi;
            od;
        od;
    od;
    return true;
end;

# ---- Partition handling --------------------------------------------
# A partition is a list of disjoint non-empty blocks (lists), each
# block sorted ascending, blocks themselves in some deterministic
# order. We also use:
#   colours : length-r list, colours[i] = block index of i.

_aut_nt_partition_to_colour := function(r, partition)
    local c, b, i;
    c := ListWithIdenticalEntries(r, 0);
    for b in [1 .. Length(partition)] do
        for i in partition[b] do
            c[i] := b;
        od;
    od;
    return c;
end;

# Split a single block of a partition: replace block at index
# `block_idx` with [[singleton_elt], rest], where rest = block \
# {singleton_elt}. If the block has only one element, no-op.
# Block order remains: the singleton replaces the original block in
# place, and `rest` is appended.

_aut_nt_singletonize := function(partition, block_idx, singleton_elt)
    local new_p, i, blk, rest;
    new_p := [];
    for i in [1 .. Length(partition)] do
        if i = block_idx then
            blk := partition[i];
            rest := Filtered(blk, x -> x <> singleton_elt);
            Add(new_p, [singleton_elt]);
            if Length(rest) > 0 then
                Add(new_p, rest);
            fi;
        else
            Add(new_p, ShallowCopy(partition[i]));
        fi;
    od;
    return new_p;
end;

# Locate the block of `partition` containing index `elt`. Returns
# the block's index in the partition list (1-based), or fail.

_aut_nt_find_block_index := function(partition, elt)
    local i;
    for i in [1 .. Length(partition)] do
        if elt in partition[i] then
            return i;
        fi;
    od;
    return fail;
end;

# ---- Refinement of source-image pair --------------------------------
# Given (p_src, p_img) with the invariant that they have the same
# block structure (size sequence) — refine BOTH by the colour-
# refinement using N. We use V-5b's RefineByFusion on each, but
# crucially: after refining p_src to (block sizes s1, s2, ..., sk)
# and p_img to (sizes s1', s2', ..., sk'), the corresponding blocks
# must have the same size — else the constraint is infeasible.
#
# Returns: rec(p_src, p_img, feasible).

_aut_nt_refine_pair := function(p_src, p_img, N)
    local q_src, q_img, sizes_src, sizes_img;
    q_src := RefineByFusion(p_src, N);
    q_img := RefineByFusion(p_img, N);
    sizes_src := List(q_src, Length);
    sizes_img := List(q_img, Length);
    # If the size sequences don't match, we have infeasibility.
    # (Since RefineByFusion sorts deterministically by signature, two
    # partitions of the same underlying multiset converging to the
    # same stable colouring have the same block structure. If we get
    # different sizes, the σ we are trying to construct can't exist.)
    if sizes_src <> sizes_img then
        return rec(p_src := q_src, p_img := q_img, feasible := false);
    fi;
    return rec(p_src := q_src, p_img := q_img, feasible := true);
end;

# ---- Backtracking core ----------------------------------------------
# State held in `_aut_nt_state` so deeply-nested closures can read it.

_aut_nt_state := rec();

# Recurse: count number of σ extensions of `sigma_partial` consistent
# with (p_src, p_img). If `early_stop_on_leaf` is true, we abort as
# soon as we hit one leaf (used for orbit-detection). Otherwise we
# enumerate every leaf, calling `leaf_cb(σ)` per leaf.
#
# Returns the count of leaves discovered.

_aut_nt_search := function(p_src, p_img, sigma_partial, image_used,
                            N, r, leaf_cb, early_stop_on_leaf)
    local idx, B, B_img, b0, count, t, q_src, q_img, ref,
          sigma, i, success, leaf_sigma, src_singletons, img_singletons,
          s, image_t;
    # If the search has been signalled to stop, do nothing.
    if _aut_nt_state.stop_now then
        return 0;
    fi;
    # Find first non-singleton block in p_src.
    idx := fail;
    for i in [1 .. Length(p_src)] do
        if Length(p_src[i]) > 1 then
            idx := i;
            break;
        fi;
    od;
    if idx = fail then
        # Leaf: every block is singleton. Assemble σ by matching
        # source-singletons {s} to their parallel image-singletons
        # {t} = p_img[b] where b is the (common) index in both
        # partitions. By construction p_src and p_img have parallel
        # block sizes; both have only singletons here, so blocks
        # 1..r are each a singleton.
        if Length(p_src) <> r then
            # Should not happen if we are consistent.
            return 0;
        fi;
        sigma := ListWithIdenticalEntries(r, 0);
        for i in [1 .. r] do
            s := p_src[i][1];
            image_t := p_img[i][1];
            sigma[s] := image_t;
        od;
        # Cross-check with sigma_partial (which has the explicit
        # branch-time assignments). They must agree.
        for i in [1 .. r] do
            if sigma_partial[i] <> 0 and sigma_partial[i] <> sigma[i] then
                # Inconsistent — this branch is dead.
                return 0;
            fi;
        od;
        # Verify σ is a permutation. By construction (each block
        # was non-empty and we singletonised to all-singleton with
        # parallel sizes) it should be.
        if Set(sigma) <> [1 .. r] then
            return 0;
        fi;
        # Verify N is preserved. T is preserved by V-5a.
        if not IsAutomorphismCandidate(sigma, N) then
            return 0;
        fi;
        if leaf_cb(sigma) then
            _aut_nt_state.stop_now := true;
        fi;
        return 1;
    fi;
    B := p_src[idx];
    B_img := p_img[idx];
    if Length(B) <> Length(B_img) then
        # Should be caught by _aut_nt_refine_pair feasibility.
        return 0;
    fi;
    b0 := B[1];
    count := 0;
    for t in B_img do
        # Try σ(b0) := t.
        if image_used[t] then
            continue;
        fi;
        sigma_partial[b0] := t;
        image_used[t] := true;
        # Split p_src to singletonise b0; split p_img to singletonise t.
        q_src := _aut_nt_singletonize(p_src, idx, b0);
        q_img := _aut_nt_singletonize(p_img, idx, t);
        # Refine the pair.
        ref := _aut_nt_refine_pair(q_src, q_img, N);
        if ref.feasible then
            count := count + _aut_nt_search(ref.p_src, ref.p_img,
                                             sigma_partial, image_used,
                                             N, r, leaf_cb,
                                             early_stop_on_leaf);
        fi;
        # Undo.
        sigma_partial[b0] := 0;
        image_used[t] := false;
        if _aut_nt_state.stop_now then
            return count;
        fi;
        if early_stop_on_leaf and count > 0 then
            return count;
        fi;
    od;
    return count;
end;

# ---- Orbit-stabiliser order computation -----------------------------
# `p_src` and `p_img` here are EQUAL — at the start of order
# computation we haven't made any assignment, so both partitions
# match. We pick the first non-singleton block B (same for both,
# since p_src = p_img). For each t ∈ B, we test whether ∃ σ in the
# subgroup with σ(b0) = t (set sigma_partial[b0]=t, refine pair,
# recurse to first leaf). Orbit size = #{t : feasible}. Then we fix
# σ(b0) = b0 and recurse for stabiliser order. Total = orbit * stab.

_aut_nt_order := function(p_src, p_img, sigma_partial, image_used,
                           N, r)
    local idx, i, B, B_img, b0, orbit_size, t, q_src, q_img, ref,
          found, leaf_cb_stop, stab_order;
    # Find the first non-singleton block.
    idx := fail;
    for i in [1 .. Length(p_src)] do
        if Length(p_src[i]) > 1 then
            idx := i;
            break;
        fi;
    od;
    if idx = fail then
        # Trivial stabiliser: every block is a singleton. The single
        # σ consistent with the partition is the one induced by
        # parallel singletons (and it's an automorphism by hypothesis
        # because we got here through refinement). Order = 1.
        return 1;
    fi;
    B := p_src[idx];
    B_img := p_img[idx];
    b0 := B[1];
    # Compute orbit size of b0 under the subgroup.
    orbit_size := 0;
    for t in B_img do
        if image_used[t] then
            continue;
        fi;
        # Try σ(b0) = t.
        sigma_partial[b0] := t;
        image_used[t] := true;
        q_src := _aut_nt_singletonize(p_src, idx, b0);
        q_img := _aut_nt_singletonize(p_img, idx, t);
        ref := _aut_nt_refine_pair(q_src, q_img, N);
        if ref.feasible then
            _aut_nt_state.stop_now := false;
            leaf_cb_stop := function(sigma) return true; end;
            found := _aut_nt_search(ref.p_src, ref.p_img,
                                     sigma_partial, image_used,
                                     N, r, leaf_cb_stop, true);
            if found > 0 then
                orbit_size := orbit_size + 1;
            fi;
        fi;
        # Undo.
        sigma_partial[b0] := 0;
        image_used[t] := false;
    od;
    if orbit_size = 0 then
        # Should not happen — at the very least t = b0 yields the
        # identity which is always feasible.
        Error("_aut_nt_order: orbit of b0 has size 0.");
    fi;
    # Compute stabiliser order: fix σ(b0) := b0.
    sigma_partial[b0] := b0;
    image_used[b0] := true;
    q_src := _aut_nt_singletonize(p_src, idx, b0);
    q_img := _aut_nt_singletonize(p_img, idx, b0);
    ref := _aut_nt_refine_pair(q_src, q_img, N);
    if not ref.feasible then
        # Identity must be feasible.
        Error("_aut_nt_order: identity-stabilising branch infeasible.");
    fi;
    stab_order := _aut_nt_order(ref.p_src, ref.p_img,
                                 sigma_partial, image_used, N, r);
    # Undo.
    sigma_partial[b0] := 0;
    image_used[b0] := false;
    return orbit_size * stab_order;
end;

# ---- Generator collection -------------------------------------------
# Enumerate all leaves; tag each non-identity σ. Bounded by
# `max_generators` for safety.

_aut_nt_collect_generators := function(p_src, p_img, N, r,
                                        max_generators)
    local sigma_partial, image_used, leaf_cb;
    _aut_nt_state.generators := [];
    _aut_nt_state.stop_now := false;
    sigma_partial := ListWithIdenticalEntries(r, 0);
    image_used := ListWithIdenticalEntries(r, false);
    leaf_cb := function(sigma)
        if sigma <> [1 .. r] then
            Add(_aut_nt_state.generators, ShallowCopy(sigma));
            if Length(_aut_nt_state.generators) >= max_generators then
                return true;
            fi;
        fi;
        return false;
    end;
    _aut_nt_search(p_src, p_img, sigma_partial, image_used, N, r,
                    leaf_cb, false);
    return _aut_nt_state.generators;
end;

# ---- Main entry point ------------------------------------------------
# AutNT(N, T, QD[, opts])
#   N      : fusion ring as 3D list.
#   T      : T-vector (list of cyclotomics).
#   QD     : quantum-dimension vector.
#   opts   : optional record. Fields:
#              max_generators : int, default 32. Cap on # generators
#                               collected.
#              skip_generators : bool, default false. If true, skip
#                                generator collection (much faster
#                                for large |Aut|; only `order` is
#                                returned).
# Returns: rec(order := |Aut(N, T)|,
#              generators := list of σ as length-r lists).

AutNT := function(arg)
    local N, T, QD, opts, r, p0, p, sigma_partial, image_used,
          order, generators;
    if Length(arg) < 3 or Length(arg) > 4 then
        Error("AutNT: expected 3 or 4 arguments (N, T, QD[, opts]).");
    fi;
    N := arg[1];
    T := arg[2];
    QD := arg[3];
    if Length(arg) = 4 then
        opts := arg[4];
    else
        opts := rec();
    fi;
    if not IsBound(opts.max_generators) then
        opts.max_generators := 32;
    fi;
    if not IsBound(opts.skip_generators) then
        opts.skip_generators := false;
    fi;
    r := Length(T);
    if Length(QD) <> r then
        Error("AutNT: |T| = ", r, " but |QD| = ", Length(QD), ".");
    fi;
    if Length(N) <> r then
        Error("AutNT: |T| = ", r, " but |N| = ", Length(N), ".");
    fi;
    # Initial Aut(N, T)-invariant partition + stable refinement.
    p0 := InitialPartition(N, T, QD);
    p := RefineByFusion(p0, N);
    # Source and image partitions both start equal.
    sigma_partial := ListWithIdenticalEntries(r, 0);
    image_used := ListWithIdenticalEntries(r, false);
    order := _aut_nt_order(p, ShallowCopy(p), sigma_partial,
                            image_used, N, r);
    if opts.skip_generators then
        return rec(order := order, generators := []);
    fi;
    generators := _aut_nt_collect_generators(p, ShallowCopy(p),
                                              N, r,
                                              opts.max_generators);
    return rec(order := order,
               generators := generators);
end;

Print("Loaded aut_nt.g (AutNT, IsAutomorphismCandidate).\n");
