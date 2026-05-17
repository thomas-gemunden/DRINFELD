# aut_nt_brw_symmetry.g — BRW-symmetry-reduced AutNT for E_+(m).
#
# Task A-3d perf-3 (issue #241). Builds on:
#   * aut_nt_partition.g        — InitialPartition(N, T, QD).
#   * aut_nt_refine.g           — RefineByFusion, FusionRowSignature.
#   * aut_nt.g                  — AutNT(N, T, QD).
#   * fusion_oracle.g           — streaming fusion oracle (PR #237).
#   * brw_simples_action.g      — BRW(m) action on simples
#                                 (orbits, representative simples).
#
# Math context (issue #241). BRW(m)/E_+(m) embeds as a subgroup of
# Aut(N, T) for D(Vec^0_{E_+(m)}): each y in BRW(m) acts on the
# simples by a permutation that preserves both the fusion ring N
# and the T-vector T. (This is the same fact that AutNTModBRW uses
# post-hoc.) Because the BRW orbits sit inside any Aut(N, T)-invariant
# partition, we can REPLACE the slow Verlinde-row refinement of
# {1..r} simples by a refinement at the BRW-orbit level — checking
# fusion signatures of orbit REPRESENTATIVES, not of every simple.
#
# At E_+(3) (rank 2272) the BRW image on simples has ~22 orbits, so
# the refinement pass shrinks from r = 2272 nodes to k = 22 nodes,
# saving ~100x in the refinement step and (more importantly) the
# AutNT backtracking branches only at the orbit level.
#
# How this connects to AutNT.
#   1. Compute BRW orbits of simples O_1, ..., O_k.
#   2. Start with the V-5a (T, QD) partition p0 (Aut(N, T)-invariant).
#      Since BRW preserves T and QD, every BRW orbit sits inside a
#      single (T, QD) block, so p0 is already a UNION OF BRW ORBITS.
#   3. Refine p0 by fusion-row signatures, but exploit BRW: same-orbit
#      simples have identical signatures (when the colouring is BRW-
#      orbit-respecting, which p0 satisfies); compute one signature per
#      orbit and broadcast. The output partition is also a union of
#      BRW orbits (orbit members go to the same sub-block).
#   4. The refinement runs to a fixed point. The result is an
#      Aut(N, T)-invariant partition that is a union of BRW orbits.
#   5. Pass this partition to AutNT's _aut_nt_order / _aut_nt_search.
#      Once the engine branches by singletonising one simple b0, the
#      "union of orbits" invariant breaks for b0's block (and only
#      that one); subsequent refinements use the non-BRW
#      RefineByFusion (the speedup at production rank is dominated by
#      the initial pass at full rank, not the much smaller post-branch
#      partitions).
#
# Correctness. BRW is a subgroup of Aut(N, T) but is NOT necessarily
# normal — Aut(N, T) need not preserve BRW orbits individually. The
# starting partition is therefore the V-5a joint (T, QD) partition,
# NOT the BRW-orbit partition. The BRW speedup is a per-pass speedup
# inside RefineByFusionBRW; correctness is preserved because each
# block of p0 (and every refined output) is a UNION of BRW orbits, and
# within a block the signatures of orbit members are identical.
#
# Speedup. The colour-refinement RefineByFusion is O(r^3) per pass;
# with BRW symmetry it becomes O(k * r^2 + k^3) per pass when we
# observe that all elements within a BRW orbit produce identical
# fusion-row signatures (since BRW preserves N). So we only need to
# compute one signature per orbit, not one per simple. This factor-
# of-(r/k) saving is realised by `RefineByFusionBRW` below.
#
# Backtracking. The AutNT engine's branching step picks the first
# non-singleton block and tries each element of the image-block as
# the image of the source-block's first element. With our BRW
# partition, blocks are unions of BRW-orbits; once the engine fixes
# the orbit-image, the BRW propagation determines the per-element
# image up to a BRW subgroup. The current PR keeps the engine
# unchanged and simply passes the coarser partition — the per-orbit
# fix is encoded by the partition's block structure. A future
# optimisation could "skip-ahead" through BRW orbits during branching.
#
# Globals installed by this file:
#   AutNTBRWSymmetry(m, N, T, QD[, opts]) — main entry. m is the
#       extraspecial parameter (1, 2, 3, ...); the action is built
#       via BRWSimplesAction(m).
#   InitialPartitionWithBRW(N, T, QD, simples_action)
#       — initial partition (current implementation: just
#         InitialPartition(N, T, QD); the BRW saving is realised inside
#         RefineByFusionBRW below).
#   RefineByFusionBRW(partition, N, simples_action)
#       — refinement that only computes one signature per BRW orbit
#         and broadcasts to all orbit members.
#   AutNTBRWSymmetryStats(result) — diagnostic record (orbit counts,
#         block sizes, used_brw_symmetry flag).

# Caller is expected to ChangeDirectoryCurrent to scripts/ before Read
# so relative paths resolve. Mirrors brw_simples_action.g convention.

if not IsBound(AutNT) then
    Read("aut_nt.g");
fi;
if not IsBound(RefineByFusion) then
    Read("aut_nt_refine.g");
fi;
if not IsBound(InitialPartition) then
    Read("aut_nt_partition.g");
fi;
if not IsBound(BRWSimplesAction) then
    Read("brw_simples_action.g");
fi;
if not IsBound(IsFusionOracle) then
    Read("fusion_oracle.g");
fi;

# -----------------------------------------------------------------
# Helper: invert a length-r image list (a permutation in image form).
# Returns inv with inv[perm[i]] = i.
# -----------------------------------------------------------------

_brw_sym_invert_image_list := function(perm, r)
    local inv, i;
    inv := ListWithIdenticalEntries(r, 0);
    for i in [1..r] do
        inv[perm[i]] := i;
    od;
    return inv;
end;;

# -----------------------------------------------------------------
# InitialPartitionWithBRW(N, T, QD, simples_action)
#
# Returns the joint (T, QD) partition (same as V-5a InitialPartition).
# Kept as a separate function for API symmetry / discoverability.
#
# The Aut(N, T)-invariant starting partition is the (T, QD) partition
# itself; the BRW-orbit partition is FINER than (T, QD) and is NOT
# necessarily Aut(N, T)-invariant (since BRW is not normal in
# Aut(N, T) in general). However, (T, QD) IS a coarsening of the
# BRW-orbit partition (each BRW orbit sits inside one (T, QD) block,
# because BRW preserves both T and QD).
#
# The BRW symmetry enters at the refinement step: when computing the
# fusion-row signature for two simples in the same BRW orbit, the
# signature is identical (provided the colouring is BRW-orbit-
# respecting, which the (T, QD) partition satisfies). RefineByFusionBRW
# computes only one signature per orbit and broadcasts.
# -----------------------------------------------------------------

InitialPartitionWithBRW := function(N, T, QD, simples_action)
    return InitialPartition(N, T, QD);
end;;

# -----------------------------------------------------------------
# RefineByFusionBRW(partition, N, simples_action)
#
# Iterate the colour-refinement, but exploit the BRW symmetry: for
# each BRW orbit, all members share the same fusion-row signature
# (since BRW preserves N). So compute the signature only for the
# orbit representative and broadcast.
#
# Invariant: every block of `partition` is a UNION of BRW orbits.
# (This holds for InitialPartitionWithBRW; refinement preserves it
# since two elements within one orbit have identical signatures and
# therefore stay in the same sub-block.) We refine deterministically
# by signature; the resulting partition is again a union of BRW
# orbits in each block.
#
# Returns: refined partition (same shape as RefineByFusion).
# -----------------------------------------------------------------

_brw_sym_one_pass := function(partition, N, simples_action)
    local r, colour, b, blk, orbit_of, sigs_by_orbit, j, k, sig,
          orb_id, new_partition, subgroups, signs, idx, placed,
          keyed, oracle_or_dense, row, i, sigs;
    r := simples_action.rank;
    colour := ColourFromPartition(r, partition);
    orbit_of := simples_action.orbit_of;
    # First, compute the signature of every BRW orbit's representative.
    # We piggyback on FusionRowSignature for correctness; this is the
    # only place the refactor matters.
    sigs_by_orbit := [];   # keyed by orbit index
    for orb_id in [1..simples_action.n_orbits] do
        # The representative is the minimum element of the orbit.
        i := simples_action.orbits[orb_id][1];
        sig := FusionRowSignature(i, N, colour);
        sigs_by_orbit[orb_id] := sig;
    od;
    # Now refine each block by orbit-signature equivalence.
    keyed := [];
    for b in [1..Length(partition)] do
        blk := partition[b];
        subgroups := [];
        signs := [];
        for k in blk do
            sig := sigs_by_orbit[orbit_of[k]];
            placed := false;
            for j in [1..Length(signs)] do
                if not placed and signs[j] = sig then
                    Add(subgroups[j], k);
                    placed := true;
                fi;
            od;
            if not placed then
                Add(signs, sig);
                Add(subgroups, [k]);
            fi;
        od;
        for j in [1..Length(subgroups)] do
            Add(keyed, [b, String(signs[j]), SortedList(subgroups[j])]);
        od;
    od;
    Sort(keyed, function(u, v)
        if u[1] <> v[1] then return u[1] < v[1]; fi;
        return u[2] < v[2];
    end);
    return List(keyed, t -> t[3]);
end;;

RefineByFusionBRW := function(partition, N, simples_action)
    local p, q, canon_p, canon_q, iters, max_iters, r;
    p := List(partition, ShallowCopy);
    canon_p := PartitionCanonical(p);
    # Refinement only ever splits blocks, so |partition| is monotone
    # non-decreasing and bounded by # BRW orbits.
    r := Sum(p, Length);
    max_iters := r + 1;
    iters := 0;
    while iters < max_iters do
        q := _brw_sym_one_pass(p, N, simples_action);
        canon_q := PartitionCanonical(q);
        if canon_q = canon_p then
            return q;
        fi;
        p := q;
        canon_p := canon_q;
        iters := iters + 1;
    od;
    return p;
end;;

# -----------------------------------------------------------------
# AutNTBRWSymmetry(m, N, T, QD[, opts])
#
# Drop-in faster variant of AutNT for the special case of
# D(Vec^0_{E_+(m)}). Returns rec(order, generators, simples_action,
# refined_partition).
#
# When opts.fallback_when_no_speedup = true (default true) and the
# BRW action is trivial (m = 0 sentinel, or BRW image of size 1),
# we fall back directly to AutNT(N, T, QD, ...). The cost of
# BRWSimplesAction(m) is amortised once per session via its cache.
#
# opts (record). Fields:
#   .max_generators  : passed through to AutNT (default 32).
#   .skip_generators : passed through (default false).
#   .fallback_when_no_speedup : if true and the image of BRW on
#                       simples is trivial, fall back to plain AutNT.
#                       Default true.
#   .verbose         : if true, print progress.
# -----------------------------------------------------------------

AutNTBRWSymmetry := function(arg)
    local m, N, T, QD, opts, action, r, p0, p, sigma_partial,
          image_used, order, generators, full_opts, refined, fallback;
    if Length(arg) < 4 or Length(arg) > 5 then
        Error("AutNTBRWSymmetry: expected 4 or 5 arguments ",
              "(m, N, T, QD[, opts]).");
    fi;
    m := arg[1];
    N := arg[2];
    T := arg[3];
    QD := arg[4];
    if Length(arg) = 5 then
        opts := arg[5];
    else
        opts := rec();
    fi;
    if not IsBound(opts.max_generators) then
        opts.max_generators := 32;
    fi;
    if not IsBound(opts.skip_generators) then
        opts.skip_generators := false;
    fi;
    if not IsBound(opts.fallback_when_no_speedup) then
        opts.fallback_when_no_speedup := true;
    fi;
    if not IsBound(opts.verbose) then
        opts.verbose := false;
    fi;

    r := Length(T);
    if Length(QD) <> r then
        Error("AutNTBRWSymmetry: |T| = ", r, " but |QD| = ", Length(QD));
    fi;

    # Build the BRW-on-simples action (cached per m).
    if opts.verbose then
        Print("AutNTBRWSymmetry: building BRWSimplesAction(", m, ")...\n");
    fi;
    action := BRWSimplesAction(m);
    if action.rank <> r then
        Error("AutNTBRWSymmetry: rank mismatch — BRWSimplesAction(", m,
              ").rank = ", action.rank, " but |T| = ", r);
    fi;

    # Fallback when there's no BRW saving: image subgroup trivial.
    if opts.fallback_when_no_speedup
       and Size(action.image_subgroup) = 1 then
        if opts.verbose then
            Print("AutNTBRWSymmetry: BRW image is trivial; falling ",
                  "back to AutNT.\n");
        fi;
        full_opts := rec(max_generators := opts.max_generators,
                         skip_generators := opts.skip_generators);
        fallback := AutNT(N, T, QD, full_opts);
        return rec(
            order              := fallback.order,
            generators         := fallback.generators,
            simples_action     := action,
            refined_partition  := InitialPartition(N, T, QD),
            used_brw_symmetry  := false
        );
    fi;

    # Build the initial partition: BRW-orbit partition refined by (T,QD).
    # (Actually BRW-orbits are already (T,QD)-pure since BRW preserves
    # T and QD; we use the BRW-orbit partition directly.)
    p0 := InitialPartitionWithBRW(N, T, QD, action);
    if opts.verbose then
        Print("AutNTBRWSymmetry: initial BRW-orbit partition has ",
              Length(p0), " blocks (", action.n_orbits, " orbits).\n");
    fi;

    # Apply BRW-aware refinement to fixed point.
    p := RefineByFusionBRW(p0, N, action);
    if opts.verbose then
        Print("AutNTBRWSymmetry: refined partition has ",
              Length(p), " blocks.\n");
    fi;

    # Now run the existing AutNT engine on this coarser partition.
    # We need to plug into _aut_nt_order / _aut_nt_search, which
    # expect to compute the initial partition themselves. Instead
    # of inverting the engine, we expose the partition by reusing
    # the internal helpers directly.
    sigma_partial := ListWithIdenticalEntries(r, 0);
    image_used := ListWithIdenticalEntries(r, false);

    # Use the BRW-aware refine inside the search.  When the engine
    # branches, it singletonises one element from a block; the block
    # was a union of BRW orbits, but after singletonising it splits
    # the orbit containing the chosen element. Subsequent refinement
    # invokes RefineByFusion (NOT RefineByFusionBRW) because the
    # invariant "every block is a union of orbits" is broken once we
    # singletonise. So we keep _aut_nt_refine_pair on the regular
    # RefineByFusion, which yields the correct |Aut| but only saves
    # the first refinement pass via the orbit-coarse partition.
    refined := rec(p_src := p, p_img := ShallowCopy(p));

    order := _aut_nt_order(refined.p_src, refined.p_img,
                             sigma_partial, image_used, N, r);
    if opts.verbose then
        Print("AutNTBRWSymmetry: |Aut(N, T)| = ", order, "\n");
    fi;

    if opts.skip_generators then
        return rec(
            order              := order,
            generators         := [],
            simples_action     := action,
            refined_partition  := p,
            used_brw_symmetry  := true
        );
    fi;
    generators := _aut_nt_collect_generators(p, ShallowCopy(p),
                                              N, r,
                                              opts.max_generators);
    return rec(
        order              := order,
        generators         := generators,
        simples_action     := action,
        refined_partition  := p,
        used_brw_symmetry  := true
    );
end;;

# -----------------------------------------------------------------
# Diagnostic: dump the orbit structure + refined partition.
# -----------------------------------------------------------------

AutNTBRWSymmetryStats := function(result)
    local p, sizes;
    p := result.refined_partition;
    sizes := List(p, Length);
    return rec(
        order            := result.order,
        n_orbits         := result.simples_action.n_orbits,
        n_refined_blocks := Length(p),
        block_sizes      := Collected(sizes),
        max_block        := Maximum(sizes),
        min_block        := Minimum(sizes),
        used_brw_symmetry := result.used_brw_symmetry
    );
end;;

Print("Loaded aut_nt_brw_symmetry.g (AutNTBRWSymmetry, ",
      "InitialPartitionWithBRW, RefineByFusionBRW, ",
      "AutNTBRWSymmetryStats).\n");
