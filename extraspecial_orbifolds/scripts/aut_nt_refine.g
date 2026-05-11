# aut_nt_refine.g — colour refinement on fusion-row signatures.
#
# Task V-5b (issue #35, task #60). Builds on V-5a's
# `aut_nt_partition.g::InitialPartition(N, T, QD)`.
#
# Background. Computing |Aut(N, T)| with backtracking benefits from a
# pre-refinement of {1, ..., r} into an Aut(N, T)-invariant partition
# tighter than the joint (T, QD) blocks of V-5a. The classical
# colour-refinement step (a.k.a. 1-dimensional Weisfeiler–Leman) uses
# the fusion coefficients N_{ij}^k themselves: any σ ∈ Aut(N, T) must
# preserve the block-coloured fusion-row signature
#
#     sig_p(i) := sorted_multiset { [ c(j), c(k), N[i][j][k] ]
#                                   : j, k ∈ {1, ..., r} }
#
# where c(·) is the colour (block index) of a simple in the current
# partition `p`. Two simples i, i' end up in the same refined block iff
# (a) they were in the same block of `p`, and
# (b) sig_p(i) = sig_p(i').
# Iterating to fixed point yields the stable colour refinement.
#
# Globals installed by this file:
#   FusionCoefficientsFromS(S)
#       Verlinde-formula expansion N[i][j][k]; returns a 3D list of
#       non-negative cyclotomic integers. The caller is responsible for
#       sanity-checking integrality (we do so in the tests, not here).
#   ColourFromPartition(r, partition)
#       Inverse map: list of length r where colour[i] is the index of
#       the block containing i (1-based). Errors if `partition` is not
#       a partition of {1, ..., r}.
#   FusionRowSignature(i, N, colour)
#       The sorted multiset sig defined above (a GAP list, sorted).
#   RefineByFusion(partition, N)
#       The main entry point. Iterates colour refinement to a fixed
#       point; returns the refined partition, with blocks sorted by
#       their representative's signature string (deterministic) and
#       indices ascending inside each block.
#
# The output partition `q` is a refinement of the input partition `p`:
# every block of `q` is a subset of some block of `p`. The refinement
# is Aut(N, T)-invariant (any σ ∈ Aut(N, T) permutes the blocks of
# `q`), provided the input `p` was Aut(N, T)-invariant (V-5a's joint
# (T, QD) partition has that property).
#
# Acceptance criteria.
#   * D(Q_8) — modular_data/8/4/1.txt, 22 simples, V-5a partition has
#     5 blocks [8, 4, 4, 3, 3]. Stable refinement reproduces the
#     22-element fusion-T partition: every simple is its own block.
#   * D^1(E_+(2)) — modular_data/32/49/1.txt, 184 simples. Stable
#     refinement is consistent with the Verlinde fusion ring computed
#     from the on-disk S.
#
# Complexity. Each refinement pass costs O(r^3) Verlinde-coefficient
# probes plus O(r^2 log r) sorting per row. For r ≤ ~10^3 this is
# easily within seconds; backtracking (V-5c) will dominate at the
# E_+(3) scale.

# ---- Verlinde formula -----------------------------------------------
# N_{ij}^k = Σ_a (S[i][a] * S[j][a] * conj(S[k][a])) / S[1][a]
# The output is a 3D list N[i][j][k]. Caller may verify integrality.

FusionCoefficientsFromS := function(S)
    local r, N, i, j, k, a, val, s1;
    r := Length(S);
    if r = 0 then
        return [];
    fi;
    s1 := S[1];
    N := List([1 .. r],
              i -> List([1 .. r],
                        j -> ListWithIdenticalEntries(r, 0)));
    for i in [1 .. r] do
        for j in [1 .. r] do
            for k in [1 .. r] do
                val := 0;
                for a in [1 .. r] do
                    if s1[a] <> 0 then
                        val := val + S[i][a] * S[j][a]
                                     * ComplexConjugate(S[k][a]) / s1[a];
                    fi;
                od;
                N[i][j][k] := val;
            od;
        od;
    od;
    return N;
end;

# ---- Partition <-> colouring -----------------------------------------
ColourFromPartition := function(r, partition)
    local colour, b, i;
    colour := ListWithIdenticalEntries(r, 0);
    for b in [1 .. Length(partition)] do
        for i in partition[b] do
            if i < 1 or i > r then
                Error("ColourFromPartition: index ", i,
                      " out of range [1, ", r, "].");
            fi;
            if colour[i] <> 0 then
                Error("ColourFromPartition: index ", i,
                      " appears in multiple blocks.");
            fi;
            colour[i] := b;
        od;
    od;
    if ForAny(colour, c -> c = 0) then
        Error("ColourFromPartition: partition does not cover ",
              "{1, ..., ", r, "}.");
    fi;
    return colour;
end;

# ---- The row signature -----------------------------------------------
# sig(i) = sorted [ [c(j), c(k), N[i][j][k]] : j, k ∈ {1, ..., r} ].
# Returning a sorted list is enough — GAP-= is sound on integers and
# small ranks, and SortedList gives a canonical representation.

FusionRowSignature := function(i, N, colour)
    local r, sig, j, k;
    r := Length(colour);
    sig := [];
    for j in [1 .. r] do
        for k in [1 .. r] do
            Add(sig, [colour[j], colour[k], N[i][j][k]]);
        od;
    od;
    Sort(sig);
    return sig;
end;

# ---- One refinement pass --------------------------------------------
# Given a partition `p` and fusion coefficients `N`, split each block
# of `p` by the equivalence "same signature under p's colouring".
# Returns the new partition (a refinement of `p`). The output block
# order is deterministic: blocks are sorted by [old-block-index,
# signature-string], indices ascending inside.

RefineOnePass := function(partition, N)
    local r, colour, b, blk, subgroups, sigs, i, sig, j, placed, idx,
          new_partition, keyed, keys;
    r := Sum(partition, Length);
    colour := ColourFromPartition(r, partition);
    new_partition := [];
    # For determinism we also need a stable order between the new
    # sub-blocks coming from one old block. We collect (block-id,
    # signature-key, block-list) triples, then sort.
    keyed := [];
    for b in [1 .. Length(partition)] do
        blk := partition[b];
        # subgroups[j] is the j-th sig class inside block b.
        subgroups := [];
        sigs := [];
        for i in blk do
            sig := FusionRowSignature(i, N, colour);
            placed := false;
            for j in [1 .. Length(sigs)] do
                if not placed and sigs[j] = sig then
                    Add(subgroups[j], i);
                    placed := true;
                fi;
            od;
            if not placed then
                Add(sigs, sig);
                Add(subgroups, [i]);
            fi;
        od;
        for j in [1 .. Length(subgroups)] do
            Add(keyed, [b, String(sigs[j]), SortedList(subgroups[j])]);
        od;
    od;
    # Stable order: by (old-block-index, signature-string).
    Sort(keyed, function(u, v)
        if u[1] <> v[1] then return u[1] < v[1]; fi;
        return u[2] < v[2];
    end);
    return List(keyed, t -> t[3]);
end;

# ---- The fixed-point iteration ---------------------------------------
# Iterate until the partition stops changing. We need a stable
# equality check between partitions; "blocks-as-sorted-lists, partition
# as a sorted list of such" is canonical.

PartitionCanonical := function(partition)
    local sorted_blocks;
    sorted_blocks := List(partition, SortedList);
    Sort(sorted_blocks);
    return sorted_blocks;
end;

RefineByFusion := function(partition, N)
    local p, q, canon_p, canon_q, iters, max_iters, r;
    p := List(partition, ShallowCopy);
    canon_p := PartitionCanonical(p);
    # Refinement only ever splits blocks, so |partition| is monotone
    # non-decreasing and bounded by r. Iterate at most r + 1 times.
    r := Sum(p, Length);
    max_iters := r + 1;
    iters := 0;
    while iters < max_iters do
        q := RefineOnePass(p, N);
        canon_q := PartitionCanonical(q);
        if canon_q = canon_p then
            return q;
        fi;
        p := q;
        canon_p := canon_q;
        iters := iters + 1;
    od;
    # Defensive: should never reach here given the bound above.
    return p;
end;

Print("Loaded aut_nt_refine.g (RefineByFusion, RefineOnePass, ",
      "FusionRowSignature, FusionCoefficientsFromS, ",
      "ColourFromPartition, PartitionCanonical).\n");
