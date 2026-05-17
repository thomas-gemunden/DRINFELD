# aut_nt_v5c_brw.g — BRW-aware V-5c backtracking for Aut(N, T).
#
# Task V-5c perf (issue #257). Builds on:
#   * aut_nt.g            — _aut_nt_order, _aut_nt_search (the engine).
#   * aut_nt_refine.g     — RefineByFusion, FusionRowSignature.
#   * aut_nt_brw_symmetry.g — RefineByFusionBRW.
#   * brw_simples_action.g  — BRW orbits / perms on simples.
#
# Math context (issue #257). At E_+(m) the BRW(m) group embeds as a
# subgroup of Aut(N, T) for D(Vec^0_{E_+(m)}). The plain V-5c engine
# refines and branches without exploiting this symmetry, leading to
# O(r^3) refinement work per branch (r = rank). At m=2 (r=184) a single
# refinement pass after singletonisation takes ~3 s; the engine does not
# terminate in observed wall time.
#
# This file installs a BRW-aware V-5c engine:
#   * The orbit-stabiliser loop in _aut_nt_order_brw enumerates one
#     representative per H-orbit instead of every element of the block,
#     where H is the pointwise stabiliser in BRW of the simples
#     already pinned by branching.
#   * The refinement uses orbit-broadcast for blocks that are H-orbit-
#     pure: one signature per H-orbit broadcast to all members.
#   * Since H shrinks with each branch, the broadcast becomes weaker
#     deeper in the tree, but the top-level branches (which dominate
#     wall) get the full speedup.
#
# Mathematical justification.
#   (i) BRW ⊆ Aut(N, T), so feasibility of one orbit member implies
#       feasibility of every orbit member. The orbit-counting loop only
#       needs one feasibility test per H-orbit ∩ B_img.
#   (ii) Two simples i, i' in the same H-orbit have equal fusion-row
#       signatures under the current colouring c, provided every block
#       of c is H-invariant. After we singletonise b0, the new partition
#       remains H'-invariant where H' = Stab_H(b0); so the broadcast
#       works at every level if we descend H along the branching.
#
# Globals installed:
#   AutNTV5cBRW(m, N, T, QD[, opts])  — main entry point.
#   _v5c_brw_orbits(H, r)             — H-orbits on [1..r] as a
#                                       length-r list orbit_of[i] = orbit-id.
#   _v5c_brw_stab(H, pts)             — pointwise stabiliser of pts in H.
#   _v5c_brw_refine_pair(p_src, p_img, N, orbit_of_src, orbit_of_img)
#                                     — refinement-pair via orbit broadcast.

# Resolve dependencies (caller is expected to ChangeDirectoryCurrent
# to scripts/ before Read, matching aut_nt_brw_symmetry.g).
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
if not IsBound(RefineByFusionBRW) then
    Read("aut_nt_brw_symmetry.g");
fi;

# -----------------------------------------------------------------
# H is now a LIST of permutations (Elements(brw_group)), not a Group.
# At small m (|H| <= O(50K)) this is cheap to materialise and lets us
# replace GAP's group-theoretic Stabilizer/Orbits with O(|H|) and O(|H|·r)
# list operations — eliminating the CollectBags/Image/Sym overhead that
# dominated the live profile of the group-based path.
#
# Scaling:
#   m=1: |H|=2,     trivial
#   m=2: |H|=72,    ~150 KB perm list
#   m=3: |H|=40320, ~900 MB perm list (borderline)
#   m>=4: prohibitive; group-theoretic path required (not optimised here).
#
# AutNTV5cBRW will Error out if |H| exceeds the safety bound.
# -----------------------------------------------------------------

# _v5c_brw_stab(perm_list, pts) — sublist of perm_list whose elements
# pointwise-fix every point in pts. Pure list filter, O(|H|·|pts|).

_v5c_brw_stab := function(perm_list, pts)
    local result, perm, all_fix, p;
    result := [];
    for perm in perm_list do
        all_fix := true;
        for p in pts do
            if p^perm <> p then
                all_fix := false;
                break;
            fi;
        od;
        if all_fix then
            Add(result, perm);
        fi;
    od;
    return result;
end;;

# _v5c_brw_orbits(perm_list, r) — orbits of <perm_list> on [1..r]
# via union-find. Returns rec(orbits, orbit_of, orbit_reps, n_orbits).
# O(|H|·r) build + O(r·alpha(r)) finalisation.

_v5c_brw_orbits := function(perm_list, r)
    local parent, find_root, perm, p, q, orbit_of, orbits, orbit_reps,
          k, root, x, y;
    if Length(perm_list) <= 1 then
        # Identity-only (or empty): every point is its own orbit.
        return rec(
            orbits := List([1..r], i -> [i]),
            orbit_of := List([1..r], i -> i),
            orbit_reps := List([1..r], i -> i),
            n_orbits := r);
    fi;
    # Union-find with path compression.
    parent := List([1..r], i -> i);
    find_root := function(x)
        local root, y;
        root := x;
        while parent[root] <> root do
            root := parent[root];
        od;
        while parent[x] <> root do
            y := parent[x];
            parent[x] := root;
            x := y;
        od;
        return root;
    end;
    for perm in perm_list do
        for p in [1..r] do
            q := p^perm;
            if q <> p then
                root := find_root(p);
                y := find_root(q);
                if root <> y then
                    parent[root] := y;
                fi;
            fi;
        od;
    od;
    # Finalise: assign orbit-ids in increasing-min-element order.
    orbit_of := List([1..r], i -> find_root(i));
    orbits := List([1..r], i -> []);
    for p in [1..r] do
        Add(orbits[orbit_of[p]], p);
    od;
    orbits := Filtered(orbits, o -> Length(o) > 0);
    orbits := List(orbits, SortedList);
    Sort(orbits, function(a, b) return a[1] < b[1]; end);
    orbit_of := ListWithIdenticalEntries(r, 0);
    for k in [1..Length(orbits)] do
        for p in orbits[k] do
            orbit_of[p] := k;
        od;
    od;
    orbit_reps := List(orbits, o -> o[1]);
    return rec(orbits := orbits, orbit_of := orbit_of,
               orbit_reps := orbit_reps, n_orbits := Length(orbits));
end;;

# -----------------------------------------------------------------
# _v5c_brw_refine_one_pass(partition, N, orbit_of, n_orbits, r)
#
# One refinement pass on `partition` using H-orbit broadcast. Each
# H-orbit-pure block is split by signature; one signature is computed
# per orbit representative and broadcast.
#
# Precondition: every block of `partition` is a union of H-orbits.
# (Maintained by initial state + this function's output.)
#
# Returns: refined partition.
# -----------------------------------------------------------------

_v5c_brw_refine_one_pass := function(partition, N, orbit_of, orbit_reps,
                                      n_orbits, r)
    local colour, sigs_by_orbit, b, blk, subgroups, signs, k, sig,
          j, placed, keyed, i;
    colour := ColourFromPartition(r, partition);
    # Compute one signature per H-orbit representative.
    sigs_by_orbit := [];
    for k in [1..n_orbits] do
        sigs_by_orbit[k] := FusionRowSignature(orbit_reps[k], N, colour);
    od;
    # Refine each block.
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

# -----------------------------------------------------------------
# _v5c_brw_refine_to_fixed_point(partition, N, orbit_of, orbit_reps,
#                                 n_orbits, r)
# -----------------------------------------------------------------

_v5c_brw_refine_to_fixed_point := function(partition, N, orbit_of,
                                            orbit_reps, n_orbits, r)
    local p, q, canon_p, canon_q, iters, max_iters;
    p := List(partition, ShallowCopy);
    canon_p := PartitionCanonical(p);
    max_iters := r + 1;
    iters := 0;
    while iters < max_iters do
        q := _v5c_brw_refine_one_pass(p, N, orbit_of, orbit_reps,
                                       n_orbits, r);
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
# _v5c_brw_refine_pair(p_src, p_img, N, orbit_of, orbit_reps, n_orbits, r)
#
# Drop-in for `_aut_nt_refine_pair` but using H-orbit broadcast on
# BOTH sides. Both sides share the same H-orbit structure (since H
# acts on the simple-set, not on a copy).
#
# Returns rec(p_src, p_img, feasible).
# -----------------------------------------------------------------

_v5c_brw_refine_pair := function(p_src, p_img, N, orbit_of, orbit_reps,
                                  n_orbits, r)
    local q_src, q_img, sizes_src, sizes_img;
    q_src := _v5c_brw_refine_to_fixed_point(p_src, N, orbit_of,
                                              orbit_reps, n_orbits, r);
    q_img := _v5c_brw_refine_to_fixed_point(p_img, N, orbit_of,
                                              orbit_reps, n_orbits, r);
    sizes_src := List(q_src, Length);
    sizes_img := List(q_img, Length);
    if sizes_src <> sizes_img then
        return rec(p_src := q_src, p_img := q_img, feasible := false);
    fi;
    return rec(p_src := q_src, p_img := q_img, feasible := true);
end;;

# -----------------------------------------------------------------
# State for the BRW engine. Parallel to _aut_nt_state.
# -----------------------------------------------------------------

_v5c_brw_state := rec();

# -----------------------------------------------------------------
# _v5c_brw_search — feasibility search at a refined position.
#
# Identical to _aut_nt_search but uses _v5c_brw_refine_pair after
# singletonisation. The H-group is passed down (so deeper levels use
# Stab_H(b0)).
#
# Arguments: p_src, p_img, sigma_partial, image_used, N, r,
#            leaf_cb, early_stop_on_leaf, H, orbit_info
# where orbit_info is rec(orbit_of, orbit_reps, n_orbits) for the
# current H.
# -----------------------------------------------------------------

_v5c_brw_search := function(p_src, p_img, sigma_partial, image_used,
                              N, r, leaf_cb, early_stop_on_leaf,
                              H, orbit_info)
    local idx, i, B, B_img, b0, count, t, q_src, q_img, ref,
          sigma, s, image_t, H_new, oi_new;
    if _v5c_brw_state.stop_now then
        return 0;
    fi;
    # Find first non-singleton block.
    idx := fail;
    for i in [1..Length(p_src)] do
        if Length(p_src[i]) > 1 then
            idx := i;
            break;
        fi;
    od;
    if idx = fail then
        # Leaf: assemble σ.
        if Length(p_src) <> r then
            return 0;
        fi;
        sigma := ListWithIdenticalEntries(r, 0);
        for i in [1..r] do
            s := p_src[i][1];
            image_t := p_img[i][1];
            sigma[s] := image_t;
        od;
        for i in [1..r] do
            if sigma_partial[i] <> 0 and sigma_partial[i] <> sigma[i] then
                return 0;
            fi;
        od;
        if Set(sigma) <> [1..r] then
            return 0;
        fi;
        if not IsAutomorphismCandidate(sigma, N) then
            return 0;
        fi;
        if leaf_cb(sigma) then
            _v5c_brw_state.stop_now := true;
        fi;
        return 1;
    fi;
    B := p_src[idx];
    B_img := p_img[idx];
    if Length(B) <> Length(B_img) then
        return 0;
    fi;
    b0 := B[1];
    count := 0;
    # Update H by stabilising b0 (we will require σ(b0) = t below).
    H_new := _v5c_brw_stab(H, [b0]);
    oi_new := _v5c_brw_orbits(H_new, r);
    for t in B_img do
        if image_used[t] then
            continue;
        fi;
        sigma_partial[b0] := t;
        image_used[t] := true;
        q_src := _aut_nt_singletonize(p_src, idx, b0);
        q_img := _aut_nt_singletonize(p_img, idx, t);
        ref := _v5c_brw_refine_pair(q_src, q_img, N,
                                     oi_new.orbit_of, oi_new.orbit_reps,
                                     oi_new.n_orbits, r);
        if ref.feasible then
            count := count + _v5c_brw_search(ref.p_src, ref.p_img,
                                              sigma_partial, image_used,
                                              N, r, leaf_cb,
                                              early_stop_on_leaf,
                                              H_new, oi_new);
        fi;
        sigma_partial[b0] := 0;
        image_used[t] := false;
        if _v5c_brw_state.stop_now then
            return count;
        fi;
        if early_stop_on_leaf and count > 0 then
            return count;
        fi;
    od;
    return count;
end;;

# -----------------------------------------------------------------
# _v5c_brw_order — orbit-stabiliser order computation.
#
# Speedup vs _aut_nt_order: enumerate one rep per H-orbit ∩ B_img.
# Mathematical fact: feasibility is constant on H-orbits intersected
# with B_img (because BRW ⊆ Aut(N, T), so any BRW element witnessing
# a transport can be composed with the witness σ).
#
# Returns: |Aut_{≤ current pin}(N, T)| (a positive integer).
# -----------------------------------------------------------------

_v5c_brw_order := function(p_src, p_img, sigma_partial, image_used,
                            N, r, H, orbit_info)
    local idx, i, B, B_img, b0, b0_orbit, orbit_size, t,
          q_src, q_img, ref, found, leaf_cb_stop, stab_order,
          H_new, oi_new, tested_orbits, t_orbit, in_B_img,
          orbit_size_in_B, t_count;
    # Find the first non-singleton block.
    idx := fail;
    for i in [1..Length(p_src)] do
        if Length(p_src[i]) > 1 then
            idx := i;
            break;
        fi;
    od;
    if idx = fail then
        return 1;
    fi;
    B := p_src[idx];
    B_img := p_img[idx];
    b0 := B[1];
    # Group B_img elements by current H-orbit. We test one per orbit.
    # H must be the group for the CURRENT colouring (matching p_src/p_img).
    in_B_img := ListWithIdenticalEntries(r, false);
    for t in B_img do
        in_B_img[t] := true;
    od;
    tested_orbits := rec();   # set of orbit-ids already handled
    orbit_size := 0;
    H_new := _v5c_brw_stab(H, [b0]);
    oi_new := _v5c_brw_orbits(H_new, r);
    for t in B_img do
        if image_used[t] then
            continue;
        fi;
        t_orbit := orbit_info.orbit_of[t];
        if IsBound(tested_orbits.(String(t_orbit))) then
            continue;     # already tested via earlier rep
        fi;
        tested_orbits.(String(t_orbit)) := true;
        # Count members of this H-orbit that lie in B_img and are not
        # already image-used.
        orbit_size_in_B := 0;
        for t_count in orbit_info.orbits[t_orbit] do
            if in_B_img[t_count] and not image_used[t_count] then
                orbit_size_in_B := orbit_size_in_B + 1;
            fi;
        od;
        # Test feasibility of this single representative t.
        sigma_partial[b0] := t;
        image_used[t] := true;
        q_src := _aut_nt_singletonize(p_src, idx, b0);
        q_img := _aut_nt_singletonize(p_img, idx, t);
        ref := _v5c_brw_refine_pair(q_src, q_img, N,
                                     oi_new.orbit_of, oi_new.orbit_reps,
                                     oi_new.n_orbits, r);
        if ref.feasible then
            _v5c_brw_state.stop_now := false;
            leaf_cb_stop := function(sigma) return true; end;
            found := _v5c_brw_search(ref.p_src, ref.p_img,
                                      sigma_partial, image_used,
                                      N, r, leaf_cb_stop, true,
                                      H_new, oi_new);
            if found > 0 then
                orbit_size := orbit_size + orbit_size_in_B;
            fi;
        fi;
        sigma_partial[b0] := 0;
        image_used[t] := false;
    od;
    if orbit_size = 0 then
        # At minimum the identity branch σ(b0)=b0 should succeed.
        Error("_v5c_brw_order: orbit of b0=", b0, " has size 0.");
    fi;
    # Stabiliser branch: fix σ(b0) := b0.
    sigma_partial[b0] := b0;
    image_used[b0] := true;
    q_src := _aut_nt_singletonize(p_src, idx, b0);
    q_img := _aut_nt_singletonize(p_img, idx, b0);
    ref := _v5c_brw_refine_pair(q_src, q_img, N,
                                 oi_new.orbit_of, oi_new.orbit_reps,
                                 oi_new.n_orbits, r);
    if not ref.feasible then
        Error("_v5c_brw_order: identity-stabilising branch infeasible.");
    fi;
    stab_order := _v5c_brw_order(ref.p_src, ref.p_img,
                                  sigma_partial, image_used, N, r,
                                  H_new, oi_new);
    sigma_partial[b0] := 0;
    image_used[b0] := false;
    return orbit_size * stab_order;
end;;

# -----------------------------------------------------------------
# AutNTV5cBRW(m, N, T, QD[, opts])
#
# Main entry point. Returns rec(order, generators, simples_action,
# refined_partition, used_brw_symmetry).
#
# opts:
#   .max_generators  : default 32.
#   .skip_generators : default false.
#   .verbose         : default false.
# -----------------------------------------------------------------

_v5c_brw_collect_generators := function(p_src, p_img, N, r, max_gens,
                                         H, orbit_info)
    local sigma_partial, image_used, leaf_cb;
    _v5c_brw_state.generators := [];
    _v5c_brw_state.stop_now := false;
    sigma_partial := ListWithIdenticalEntries(r, 0);
    image_used := ListWithIdenticalEntries(r, false);
    leaf_cb := function(sigma)
        if sigma <> [1..r] then
            Add(_v5c_brw_state.generators, ShallowCopy(sigma));
            if Length(_v5c_brw_state.generators) >= max_gens then
                return true;
            fi;
        fi;
        return false;
    end;;
    _v5c_brw_search(p_src, p_img, sigma_partial, image_used, N, r,
                     leaf_cb, false, H, orbit_info);
    return _v5c_brw_state.generators;
end;;

AutNTV5cBRW := function(arg)
    local m, N, T, QD, opts, action, r, p0, p, sigma_partial,
          image_used, order, generators, brw_group, H, oi;
    if Length(arg) < 4 or Length(arg) > 5 then
        Error("AutNTV5cBRW: expected 4 or 5 arguments (m, N, T, QD[, opts]).");
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
    if not IsBound(opts.verbose) then
        opts.verbose := false;
    fi;

    r := Length(T);
    if Length(QD) <> r then
        Error("AutNTV5cBRW: |T| = ", r, " but |QD| = ", Length(QD));
    fi;

    if opts.verbose then
        Print("AutNTV5cBRW: building BRWSimplesAction(", m, ")...\n");
    fi;
    action := BRWSimplesAction(m);
    if action.rank <> r then
        Error("AutNTV5cBRW: rank mismatch — BRWSimplesAction(", m,
              ").rank = ", action.rank, " but |T| = ", r);
    fi;

    brw_group := action.image_subgroup;
    # Materialise H as an explicit list of permutations. The list-based
    # Stab/Orbits below avoid GAP's group-theoretic overhead (Stabilizer,
    # Image, Sym) that dominated the live profile.
    #
    # Safety: at m >= 4 |H| explodes (m=4 ~ 174M, m=5 ~ 24e12), so refuse.
    if Size(brw_group) > 100000 then
        Error("AutNTV5cBRW: |BRW image| = ", Size(brw_group),
              " too large to materialise as a perm list. ",
              "This engine is for small m (m <= 3); use the BRW lower bound (PR #249) at m >= 4.");
    fi;
    if opts.verbose then
        Print("AutNTV5cBRW: materialising H as list (|H| = ",
              Size(brw_group), ") ... ");
    fi;
    H := Elements(brw_group);
    if opts.verbose then
        Print("done.\n");
    fi;
    oi := rec(orbit_of := action.orbit_of,
               orbits := action.orbits,
               orbit_reps := action.orbit_reps,
               n_orbits := action.n_orbits);

    # Initial partition = (T, QD)-joint.
    p0 := InitialPartition(N, T, QD);
    if opts.verbose then
        Print("AutNTV5cBRW: initial (T,QD) partition has ",
              Length(p0), " blocks (", action.n_orbits, " BRW orbits, |H|=",
              Size(H), ").\n");
    fi;

    # BRW-aware refinement to fixed point.
    p := _v5c_brw_refine_to_fixed_point(p0, N, oi.orbit_of,
                                          oi.orbit_reps, oi.n_orbits, r);
    if opts.verbose then
        Print("AutNTV5cBRW: refined partition has ",
              Length(p), " blocks, sizes ", List(p, Length), "\n");
    fi;

    sigma_partial := ListWithIdenticalEntries(r, 0);
    image_used := ListWithIdenticalEntries(r, false);

    if opts.verbose then
        Print("AutNTV5cBRW: starting _v5c_brw_order...\n");
    fi;
    order := _v5c_brw_order(p, ShallowCopy(p), sigma_partial,
                             image_used, N, r, H, oi);
    if opts.verbose then
        Print("AutNTV5cBRW: |Aut(N, T)| = ", order, "\n");
    fi;

    if opts.skip_generators then
        return rec(order := order, generators := [],
                   simples_action := action, refined_partition := p,
                   used_brw_symmetry := true);
    fi;
    generators := _v5c_brw_collect_generators(p, ShallowCopy(p), N, r,
                                                opts.max_generators,
                                                H, oi);
    return rec(order := order, generators := generators,
               simples_action := action, refined_partition := p,
               used_brw_symmetry := true);
end;;

Print("Loaded aut_nt_v5c_brw.g (AutNTV5cBRW).\n");
