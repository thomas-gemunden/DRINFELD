# Per-generator transgression test on E_+(m), accelerated via BRW(m).
#
# Plain `transgression_per_generator.g` iterates all n_classes conjugacy
# classes of E_+(m). The BRW(m) outer-automorphism action partitions those
# classes into a small number of BRW-orbits. Within one orbit, the (S,T)-
# transgression questions are linked by an H^3 endomorphism: if y in BRW(m)
# maps class [g_1] to class [g_j], then the cocycle restriction c_{g_j} for
# the i-th H^3 generator equals (M_y * e_i)-projected restriction at C_{g_1}.
#
# Hence per BRW-orbit we only need:
#   - one centraliser C_{g_1} for the orbit representative,
#   - one BuildPerClassCocycleBasis cache for that centraliser,
# and we replay every (orbit-member, H^3-generator) check by a cheap
# matrix-vector product over Z (mod the H^3 torsion).
#
# Public entry point: PerGeneratorTransgressionBRW(G, i).
#   G : E_+(m) as a GAP matrix group EmGroup(m) (or any group conjugate to it
#       whose conjugacy classes / centralisers match those of the BRW model).
#   i : H^3 generator index in [1 .. setup.num_generators].
#   returns: list of length n_classes, entry j is either
#               true   if c_{g_j} for the i-th generator is a 2-coboundary,
#               false  if it is not,
#               "?"   if the orbit-of-class[j] was somehow not processed.
#
# Stage-1 scope (this file):
#   - Implement the orbit-aware loop using a Schreier-vector BFS over the
#     conjugacy-class action of BRW. For each orbit member, the H^3 image
#     vector is obtained by replaying the BFS path with h3_matrices
#     (forward composition, see H3VecAtTarget docstring for justification).
#   - Use BuildPerClassCocycleBasis from solver/snf_wrapper.g for the
#     per-orbit centraliser cache.
#   - Initial verification target: m = 2, single H^3 generator, parity
#     check against the existing baseline (transgression_per_generator.g).
#
# Read paths: this file lives in extraspecial_orbifolds/scripts/. To keep the
# code position-portable we Read by relative path under CWD-shimming, the
# same shim pattern used by solver/iscoboundary2_split.g. The required CWD
# at Read-time is .../extraspecial_orbifolds/scripts/ (so that "solver/..."
# and other sibling files resolve).
#
# Dependencies pulled in by these Reads:
#   - transgression_kernel.g  -> SetupCohomology3, StandardCocycleOf, ...
#   - brw_conjugacy_action.g  -> BRWConjugacyAction
#   - brw_h3_action.g         -> BRWH3Action, ComposeH3Endomorphism,
#                                IdH3Endomorphism, ApplyH3Endomorphism
#   - solver/snf_wrapper.g    -> BuildPerClassCocycleBasis, MakeCgFromCache,
#                                IsCoboundary2Split (via include chain)

if not IsBound(SetupCohomology3) then
    Read("transgression_kernel.g");
fi;
if not IsBound(BRWConjugacyAction) then
    Read("brw_conjugacy_action.g");
fi;
if not IsBound(BRWH3Action) then
    Read("brw_h3_action.g");
fi;
# snf_wrapper.g uses a CWD-shim that expects CWD to be one of `.`, `..`,
# or `../..` relative to `iscoboundary2_split.g`. iscoboundary2_split.g is
# at solver/iscoboundary2_split.g relative to this file. So we cd into
# solver/ for the Read, then come back.
if not IsBound(BuildPerClassCocycleBasis) then
    transgression_per_generator_brw_orig_cwd := DirectoryCurrent();;
    ChangeDirectoryCurrent("solver");
    Read("snf_wrapper.g");
    ChangeDirectoryCurrent(Filename(transgression_per_generator_brw_orig_cwd, ""));
fi;


# ----------------------------------------------------------------------
# Schreier-vector orbit traversal.
#
# Given:
#   * perm_gens : list of permutations in Sym(n) generating perm_group.
#   * n         : action-domain size.
#   * start     : starting position in [1..n].
#
# Returns a record with fields:
#   .orbit     : list of positions reachable from start (start at index 1).
#   .parent    : parent[pos] = the parent-position from which `pos` was
#                discovered (parent[start] = 0 by convention).
#   .gen_used  : gen_used[pos] = index g in [1..Length(perm_gens)] such that
#                parent[pos] ^ perm_gens[g] = pos.  gen_used[start] = 0.
#
# This is a standard BFS over the action graph. Using only forward
# generators (no inverses), so the resulting "transversal word" from
# start to any position is a product of positive powers of generators.
# ----------------------------------------------------------------------

OrbitWithSchreierVec := function(perm_gens, n, start)
    local orbit, parent, gen_used, visited, queue, head, pos, g, child;
    orbit := [start];
    parent := List([1..n], j -> -1);
    gen_used := List([1..n], j -> -1);
    parent[start] := 0;
    gen_used[start] := 0;
    visited := BlistList([1..n], [start]);
    queue := [start];
    head := 1;
    while head <= Length(queue) do
        pos := queue[head];
        head := head + 1;
        for g in [1..Length(perm_gens)] do
            child := pos ^ perm_gens[g];
            if not visited[child] then
                visited[child] := true;
                parent[child] := pos;
                gen_used[child] := g;
                Add(orbit, child);
                Add(queue, child);
            fi;
        od;
    od;
    return rec(orbit := orbit, parent := parent, gen_used := gen_used);
end;;


# ----------------------------------------------------------------------
# Compute the H^3 coordinate vector M_y . e_i where y is the BRW element
# whose perm action takes `start` to `target`, traversing via the
# Schreier vector.
#
# The Schreier path is: start = p_0 -> p_1 -> ... -> p_n = target, where
# each transition p_{k-1} -> p_k is realised by perm_gens[g_k]:
#       p_{k-1} ^ perm_gens[g_k] = p_k.
# Writing y_k for the BRW generator realising perm_gens[g_k], the full
# BRW element is y = y_1 * y_2 * ... * y_n (read left-to-right, since
# perm_{y_1 * y_2 * ... * y_n} takes start to target).
#
# Conjugation: phi_y(start_rep) = target_rep. Pullback is contravariant:
#       phi_y^* = phi_{y_n}^* ∘ ... ∘ phi_{y_1}^*
#       M_y . v = M_{y_n} . (... . (M_{y_2} . (M_{y_1} . v))...)
# So to get M_y . e_i, we apply M_{y_1} first, then M_{y_2}, ..., then
# M_{y_n}, to e_i in sequence.
#
# Equivalently, since the BFS goes start -> p_1 -> ... -> target, and we
# *apply* M_{y_k} for the k-th step in forward order, we can compute the
# vector by **walking the BFS path forward** and applying M_{gen_used[
# next_pos]} at each step. We don't even need to assemble M_y explicitly.
#
# This function returns the final vector for a single (i, target) pair,
# given a parent/gen_used array from OrbitWithSchreierVec and the precomputed
# h3_matrices indexed in the SAME order as perm_gens.
# ----------------------------------------------------------------------

H3VecAtTarget := function(start, target, parent, gen_used, h3_matrices, torsion, e_i)
    local path, pos, vec, k_step;
    if target = start then
        return ShallowCopy(e_i);
    fi;
    # Reconstruct path start -> target by walking parents from target.
    path := [target];
    pos := target;
    while parent[pos] <> start do
        pos := parent[pos];
        if pos = -1 then
            Error("H3VecAtTarget: target ", target,
                  " not reachable from start ", start);
        fi;
        Add(path, pos);
    od;
    # path is in REVERSE order (target..., last entry just after start).
    # Reverse to get start -> ... -> target sequence; we'll then apply
    # M_{gen_used[path[k]]} for each k in forward order.
    path := Reversed(path);
    vec := ShallowCopy(e_i);
    for pos in path do
        # Each `pos` was reached from parent[pos] via perm_gens[gen_used[pos]].
        k_step := gen_used[pos];
        vec := ApplyH3Endomorphism(h3_matrices[k_step], vec, torsion);
    od;
    return vec;
end;;


# ----------------------------------------------------------------------
# Main: per-generator transgression test for one H^3 generator i, using
# BRW(m) to amortise the centraliser/basis-cache cost across each orbit.
# ----------------------------------------------------------------------
#
# Behaviour summary:
#  1. Build BRWConjugacyAction(m) and BRWH3Action(m); they share an index-
#     parallel list of BRW generators (perms <-> h3_matrices).
#  2. BFS-traverse the conjugacy-class action: for each unvisited
#     start_idx in [1..n_classes], OrbitWithSchreierVec gives the orbit
#     together with a Schreier vector recording (parent, generator-used).
#  3. For each orbit:
#       - rep := Representative(classes[start_idx])
#       - C := Centralizer(G, rep)
#       - basis_cache := BuildPerClassCocycleBasis(setup, rep, C)
#       - For each target_idx in orbit:
#           * vec_target := H3VecAtTarget(start_idx, target_idx, ...)
#             which replays the BFS path forward, applying h3_matrices
#             at each step to the source e_i column. By the contravariant
#             pullback composition rule, this yields M_y . e_i where y
#             is the BRW element whose perm action walks the BFS path.
#           * c_g_table := basis_cache.table . vec_target (Z-linear).
#           * c_g closure := MakeCgFromCache(c_g_table, basis_cache).
#           * results[target_idx] := IsCoboundary2Split(C, c_g_func,
#                                                       vec_target, setup).
#  4. Return the per-class true/false list.
#
# Edge case: identity class (singleton orbit). c_g identically 0, so
# trivially a coboundary; we still process via the main loop for
# uniformity (the early-return in IsCoboundary2Split's caller handles
# the all-zero case fast).
# ----------------------------------------------------------------------

PerGeneratorTransgressionBRW := function(G, i)
    local n, m, setup, conj_action, h3_action, perm_gens, n_classes, k,
          torsion, exp, h3_matrices, classes, results, e_i,
          visited_all, orbits_seen, start_idx, sv, orbit, rep, C,
          basis_cache, target_idx, vec_target, c_g_table, c_g_func;

    # Infer m from |G| = 2^{2m+1}. For Stage-1 we require G = EmGroup(m)
    # so that ConjugacyClasses(G) and the BRW(m) action data line up.
    n := Order(G);
    m := (LogInt(n, 2) - 1) / 2;
    Assert(0, 2^(2*m + 1) = n,
           "G has order not of the form 2^{2m+1}; not an E_+(m).");

    setup := SetupCohomology3(G);
    classes := ConjugacyClasses(G);
    n_classes := Length(classes);
    torsion := setup.torsion;
    exp := setup.exponent;
    k := setup.num_generators;

    # Validate i.
    Assert(0, i >= 1 and i <= k, "i must be a valid H^3 generator index.");

    # Build BRW action data. NB: BRWConjugacyAction operates on EmGroup(m).
    # For Stage-1 we require G = EmGroup(m); the assertion below is
    # conservative but cheap.
    conj_action := BRWConjugacyAction(m);
    h3_action := BRWH3Action(m);

    if G <> conj_action.em then
        # If class counts agree, results are correct assuming identical
        # numbering; otherwise bail.
        if Length(conj_action.classes) <> n_classes then
            Error("PerGeneratorTransgressionBRW: G must be EmGroup(m) ",
                  "for the BRW-amortised path. Got ", n_classes,
                  " classes; expected ", Length(conj_action.classes));
        fi;
        Print("WARNING: G is not the identical EmGroup(m) group object; ",
              "results assume identical conjugacy class numbering.\n");
    fi;

    perm_gens := conj_action.perms;       # parallel-indexed with h3_matrices
    h3_matrices := h3_action.matrices;
    Assert(0, Length(perm_gens) = Length(h3_matrices),
           "perm_gens and h3_matrices must have the same length.");

    # e_i: unit column vector for the i-th H^3 generator.
    e_i := List([1..k], j -> 0);
    e_i[i] := 1;

    # Allocate results, default "?" to flag any unprocessed class.
    results := List([1..n_classes], j -> "?");

    # Walk classes in [1..n_classes] order, doing one BFS-orbit per unvisited
    # start. This mirrors GAP's Orbits but lets us reuse the Schreier vector
    # for the H^3-vector replay below.
    visited_all := BlistList([1..n_classes], []);
    orbits_seen := [];

    for start_idx in [1..n_classes] do
        if visited_all[start_idx] then continue; fi;

        # BFS Schreier-traversal from start_idx using BRW generator perms.
        sv := OrbitWithSchreierVec(perm_gens, n_classes, start_idx);
        orbit := sv.orbit;
        for target_idx in orbit do
            visited_all[target_idx] := true;
        od;
        Add(orbits_seen, orbit);

        # Build the centraliser cache ONCE for this orbit.
        rep := Representative(classes[start_idx]);
        C := Centralizer(G, rep);
        basis_cache := BuildPerClassCocycleBasis(setup, rep, C);

        # For each orbit member, compute vec_target = M_y . e_i where y
        # is the BRW element whose perm walks the BFS path start_idx ->
        # target_idx. We use forward composition (apply matrices in the
        # order encountered along the path), see H3VecAtTarget for the
        # convention justification.
        for target_idx in orbit do
            vec_target := H3VecAtTarget(start_idx, target_idx,
                                         sv.parent, sv.gen_used,
                                         h3_matrices, torsion, e_i);

            # Build c_g_table = basis_cache.table . vec_target (Z-linear).
            # Issue #372 (F3): compiled matvec (#370 shape) + Vec API
            # for IsCoboundary2Split (#371 shape) — skips both the
            # interpreted List+Sum dot product AND the c_g_func closure
            # whose n² dict lookups internally just rebuilt the same
            # integer table.
            c_g_table := basis_cache.table * vec_target;
            results[target_idx] :=
                IsCoboundary2SplitVec(C, c_g_table, vec_target, setup);
        od;
    od;

    return rec(
        generator := i,
        m := m,
        per_class := results,
        all_in_kernel := ForAll(results, x -> x = true),
        orbits := orbits_seen
    );
end;;


# ----------------------------------------------------------------------
# Convenience: run the orbit-aware test for every H^3 generator,
# returning a summary record akin to TestAllGenerators.
# ----------------------------------------------------------------------

TestAllGeneratorsBRW := function(G)
    local setup, k, i, r, count_in_kernel, results, witness_set, p;
    setup := SetupCohomology3(G);
    k := setup.num_generators;
    Print("\n");
    if IsBoundGlobal("_LogPhase") then
        _LogPhase("pergen-brw",
                  "=== Per-generator transgression test (BRW-amortised) ",
                  "for ", StructureDescription(G), " ===");
    else
        Print("=== Per-generator transgression test (BRW-amortised) for ",
              StructureDescription(G), " ===\n");
    fi;
    Print("|G| = ", Order(G), "\n");
    Print("|H^3(G; U(1))| = ", setup.num_h3_classes, "\n");
    Print("torsion = ", setup.torsion, "\n");
    Print("k = ", k, " generators\n");
    results := [];
    count_in_kernel := 0;
    witness_set := [];
    for i in [1..k] do
        r := PerGeneratorTransgressionBRW(G, i);
        Add(results, r);
        if r.all_in_kernel then
            count_in_kernel := count_in_kernel + 1;
            Print("  gen ", i, ": IN kernel\n");
        else
            Print("  gen ", i, ": NOT in kernel  (witnesses ",
                  Filtered([1..Length(r.per_class)],
                           j -> r.per_class[j] = false), ")\n");
            for p in [1..Length(r.per_class)] do
                if r.per_class[p] = false then AddSet(witness_set, p); fi;
            od;
        fi;
    od;
    Print("\nGenerators in kernel: ", count_in_kernel, " / ", k, "\n");
    Print("Witness classes: ", witness_set, "\n");
    return rec(results := results,
               count_in_kernel := count_in_kernel,
               witness_classes := witness_set);
end;;
