# brw_simples_action.g — BRW(m) action on the simples of D(Vec^0_{E_+(m)}).
#
# Task A-3d perf-3 (issue #241). Builds on:
#   * brw_conjugacy_action.g — BRW(m) action on E_+(m)-conjugacy classes
#     (the "class permutation" piece).
#   * brw_construction.g     — BRW(m) and EmGroup(m).
#   * untwisted_modular_data.g — BuildSimpleIndex (simple labelling
#     (g, chi) with chi in Irr(C_G(g)); global indices).
#
# Math context. The simples of the untwisted Drinfeld centre D(Vec^0_G)
# are pairs (g, chi) where g is a class representative and
# chi in Irr(C_G(g)). The Bolt-Room-Wall group BRW(m) normalises
# E_+(m) inside O(2^m) and so acts on E_+(m) by conjugation, hence on
# (class, irrep)-pairs. The induced action on global simple indices is
# the "BRW on simples" lift.
#
# Concretely. Pick a BRW generator y. For each class index i with
# representative g_i:
#   * y * g_i * y^{-1} lies in some other conjugacy class; let i' be
#     that class index (this is exactly the BRWConjugacyAction
#     permutation, perms[i] := i').
#   * Choose h_i in G with y * g_i * y^{-1} = h_i * g_{i'} * h_i^{-1}.
#     One legitimate choice: any transport element via
#     RepresentativeAction(G, g_{i'}, y*g_i*y^{-1}).
#   * The composite map psi_{y, i} : C_G(g_i) -> C_G(g_{i'}) defined
#     by c -> h_i^{-1} y c y^{-1} h_i is an iso (it is conjugation by
#     h_i^{-1} y, which sends g_i to g_{i'}).
#   * The pullback action on Irr(C_G(g_i)) -> Irr(C_G(g_{i'})) sends
#     chi to chi' where chi'(c') = chi(psi_{y, i}^{-1}(c'))
#                              = chi(y^{-1} h_i c' h_i^{-1} y).
#   * We identify chi' inside Irr(C_G(g_{i'})) by character-value
#     matching (i.e. find chi_k' in Irr(C_G(g_{i'})) with the same
#     value on every class of C_G(g_{i'}) -- equivalently the same
#     value-vector on its conjugacy class representatives).
#
# The combination (i, k) -> (i', k') gives the permutation of global
# simple indices induced by y. Since (g, chi) ~ (h g h^{-1}, chi
# pulled back through h) for any inner h, the simples action is
# well-defined modulo gauge in the sense of fusion-and-T equivalence;
# different transport choices h_i give permutations that differ only
# by an inner automorphism of Aut(N, T), which is exactly what BRW
# orbits identify.
#
# Output. BRWSimplesAction(m) returns a record with fields:
#   .m              : m
#   .em             : pc-group form of E_+(m)
#   .em_matrix      : matrix form of E_+(m)
#   .iso_em         : iso em_matrix -> em (used to translate y in BRW
#                     matrix -> the pc-form needed for the centraliser
#                     and Irr machinery).
#   .brw            : BRW(m)
#   .idx            : BuildSimpleIndex(em), the simple index.
#   .rank           : idx.rank = total # simples.
#   .gens           : GeneratorsOfGroup(brw).
#   .class_perms    : list of length-n_classes class-index image lists
#                     (one per generator). class_perms[t][i] = i'.
#   .irrep_perms    : list of length-n_classes lists of irrep-permutations
#                     (one per BRW generator, then per class). For BRW
#                     generator t and class i, irrep_perms[t][i] is a
#                     length-num_irreps[i] list with image[k] = k'.
#   .perms          : list of GAP Perms (one per BRW generator) on
#                     [1..rank], with image_list[s] = s' for global
#                     simple index s.
#   .image_lists    : the raw length-rank image lists parallel to .perms.
#   .image_subgroup : Group(perms) as a subgroup of Sym([1..rank]).
#   .orbits         : list of lists of integers (sorted, partitioning
#                     [1..rank]) -- the orbits of image_subgroup.
#   .orbit_of       : length-rank list, orbit_of[s] = orbit index
#                     containing s. (Smallest index in orbit comes first.)
#   .orbit_reps     : length-n_orbits list, the minimal element per
#                     orbit (canonical representative).
#
# Acceptance criteria (per #241):
#   * Q_8 (m=1, after switching to PC form): the action on simples is
#     ALMOST trivial in this codebase because Q_8 is not plus-type, so
#     this file Errors fast on m=0; m=1 produces the trivial subgroup
#     of Sym(simples). Q_8's plus-type analogue is E_+(1) = D_8 (order 8,
#     plus-type extraspecial). At m=1, BRW(1)/E_+(1) = O^+(2, F_2) =
#     S_2, so |image| in Sym(simples) is small.
#   * E_+(2) (m=2, rank 184): |image_subgroup| > 1, orbit count ~ 184/.
#     The exact value depends on which simples are merged by BRW; the
#     test asserts a specific count once measured.
#   * E_+(3) (m=3, rank 2272): orbit count ~22 (per #241).
#
# Globals installed by this file:
#   BRWSimplesAction(m)            — main entry.
#   _BRWSimpleAction_OnePerm(y, idx, brw_class_action, i_action)
#                                  — internal: action of single
#                                    generator y on simples.
#   _BRWSimpleAction_PullbackIrr(idx, i, i_prime, h, y, iso_em, em_pc)
#                                  — for one (y, i), return the
#                                    permutation of Irr indices.

# Follows the existing convention in this scripts/ directory: caller is
# expected to ChangeDirectoryCurrent to scripts/ before Read, so relative
# paths inside Read() resolve correctly. The driver run_e_plus_3_aut.g
# does this; tests use ChangeDirectoryCurrent (see tests/test_aut_nt_brw_symmetry.g).

if not IsBound(BRWConjugacyAction) then
    Read("brw_conjugacy_action.g");
fi;
if not IsBound(BuildSimpleIndex) then
    Read("untwisted_modular_data.g");
fi;

# -----------------------------------------------------------------
# Pullback of Irr along the iso psi_{y, i}: C_G(g_i) -> C_G(g_{i'})
# defined by c -> h_i^{-1} * (y * c * y^{-1}) * h_i, where y is a
# BRW element (a matrix) and g_i, g_{i'} are class reps in the pc
# form em_pc = Image(iso_em). The map is well-defined as a group
# iso between centralisers.
#
# IMPLEMENTATION. We evaluate every chi in Irr(C_G(g_i)) on the
# generators of C_G(g_i) (no -- on the class reps inside the
# centraliser, since Irr takes class-function values). Equivalently
# we evaluate the pulled-back character chi' on the class reps of
# C_G(g_{i'}), and compare against each chi'' in Irr(C_G(g_{i'})).
#
# Pulled-back chi' on c' in C_G(g_{i'}) is
#    chi'(c') = chi(psi^{-1}(c')) = chi(y^{-1} h_i c' h_i^{-1} y),
# where psi^{-1}(c') = (h_i^{-1} y)^{-1} c' (h_i^{-1} y) = y^{-1} h_i c' h_i^{-1} y.
# So compute u := y^{-1} h_i c' h_i^{-1} y as a matrix in E_+(m); then
# pc_form := Image(iso_em, u) and evaluate chi at pc_form via
# EvalIrr-style lookup.
# -----------------------------------------------------------------

_BRWSimpleAction_PullbackIrr := function(idx, i, i_prime, h_i, y, iso_em,
                                          centraliser_rep_mats)
    # idx                   : BuildSimpleIndex(em_pc)
    # i, i_prime            : class indices in idx.
    # h_i                   : element of em_pc (pc-form) with
    #                         h_i * g_{i'} * h_i^{-1}
    #                         = iso_em(y * iso_em^{-1}(g_i) * y^{-1}).
    # y                     : matrix in BRW.
    # iso_em                : iso em_matrix -> em_pc.
    # centraliser_rep_mats  : per-class precomputed list-of-lists; entry
    #                         [i_prime][j] is the matrix-form (em_mat)
    #                         pre-image of Representative(cc_iprime[j]).
    # Returns: a length-num_irreps[i] list `perm` with
    #          perm[k] = k', where image of (i, k) under y is (i', k').
    local cc_iprime, m, k, chi, u_mat, u_pc,
          val_chi_image, irreps_iprime, candidates, l, ok, j, perm,
          c_prime_mat, h_i_mat, y_inv, h_i_inv,
          saved_class_in_i,
          left_mat, right_mat, irrep_table, mats_iprime;
    cc_iprime := idx.cc_centraliser[i_prime];
    irreps_iprime := idx.irreps[i_prime];
    m := Length(cc_iprime);
    mats_iprime := centraliser_rep_mats[i_prime];

    y_inv := y^(-1);
    h_i_mat := PreImagesRepresentative(iso_em, h_i);
    h_i_inv := h_i_mat^(-1);

    # u := y^{-1} h_i c' h_i^{-1} y = (y^{-1} h_i) c' (h_i^{-1} y).
    left_mat := y_inv * h_i_mat;
    right_mat := h_i_inv * y;

    # Compute the j -> class-index map ONCE and reuse for all k.
    saved_class_in_i := [];
    for j in [1..m] do
        c_prime_mat := mats_iprime[j];
        u_mat := left_mat * c_prime_mat * right_mat;
        u_pc := Image(iso_em, u_mat);
        saved_class_in_i[j] := ClassIndexInCentraliser(idx, i, u_pc);
    od;

    # Per-k irrep image: read chi(u_pc) by direct array lookup.
    irrep_table := idx.irreps[i];
    perm := [];
    for k in [1..Length(irrep_table)] do
        chi := irrep_table[k];
        val_chi_image := List([1..m], j -> chi[saved_class_in_i[j]]);
        candidates := [];
        for l in [1..Length(irreps_iprime)] do
            ok := true;
            for j in [1..m] do
                if irreps_iprime[l][j] <> val_chi_image[j] then
                    ok := false;
                    break;
                fi;
            od;
            if ok then
                Add(candidates, l);
            fi;
        od;
        if Length(candidates) <> 1 then
            Error("BRWSimpleAction: irrep matching for (y, i=", i,
                  ", k=", k, ") failed; ", Length(candidates),
                  " candidates in Irr(C_G(g_", i_prime, ")).");
        fi;
        perm[k] := candidates[1];
    od;
    return perm;
end;;

# -----------------------------------------------------------------
# Compute the global-simple permutation for a single BRW generator
# y, given the pre-computed class-permutation image_list
# (a length-n_classes list with image_list[i] = i').
#
# Returns rec(class_perm := <image_list>,
#             irrep_perms := list-by-class of irrep image-lists,
#             image_list := length-rank list of global simple
#                           image indices,
#             perm := PermList(image_list)).
# -----------------------------------------------------------------

_BRWSimpleAction_OnePerm := function(y, idx, class_image_list, iso_em,
                                       class_rep_mats, centraliser_rep_mats)
    local em_pc, em_mat, n_classes, irrep_perms, i, i_prime, g_i_pc,
          g_i_mat, y_conj_pc, h_i, perm_irr, image_list, k, gi_off,
          giprime_off, p;
    em_pc := idx.group;
    em_mat := Source(iso_em);
    n_classes := Length(idx.classes);

    irrep_perms := [];
    image_list := [];
    for i in [1..n_classes] do
        i_prime := class_image_list[i];
        # Use precomputed matrix form of the class rep.
        g_i_mat := class_rep_mats[i];
        y_conj_pc := Image(iso_em, y * g_i_mat * y^(-1));
        h_i := RepresentativeAction(em_pc, idx.reps[i_prime], y_conj_pc);
        if h_i = fail then
            Error("BRWSimpleAction: y * g_", i, " * y^{-1} not in the ",
                  "claimed class ", i_prime, " (class_perm broken).");
        fi;
        perm_irr := _BRWSimpleAction_PullbackIrr(idx, i, i_prime, h_i,
                                                  y, iso_em,
                                                  centraliser_rep_mats);
        irrep_perms[i] := perm_irr;
        # Emit global-image entries.
        gi_off := idx.global_offset[i];
        giprime_off := idx.global_offset[i_prime];
        for k in [1..idx.num_irreps[i]] do
            image_list[gi_off + k] := giprime_off + perm_irr[k];
        od;
    od;
    # Validate it's a permutation.
    if Set(image_list) <> [1..idx.rank] then
        Error("BRWSimpleAction: assembled image-list is not a ",
              "permutation of [1..", idx.rank, "].");
    fi;
    p := PermList(image_list);
    if p = fail then
        Error("BRWSimpleAction: PermList failed on image_list.");
    fi;
    return rec(
        class_perm := class_image_list,
        irrep_perms := irrep_perms,
        image_list := image_list,
        perm := p
    );
end;;

# -----------------------------------------------------------------
# Orbit computation. Given a list of GAP perms on [1..rank], compute
# the orbits of the subgroup they generate. We use GAP's native
# Orbits(grp, [1..rank]); for small rank the orbit machinery is
# adequate. For larger ranks consider Orbit(grp, i) with explicit
# representative tracking.
# -----------------------------------------------------------------

_BRWSimpleAction_Orbits := function(perms, rank)
    local grp, orbs, orbit_of, orbit_reps, i, orb, idx_orb;
    if Length(perms) = 0 then
        # Trivial subgroup: every simple is its own orbit.
        orbit_of := List([1..rank], i -> i);
        orbit_reps := List([1..rank], i -> i);
        return rec(
            orbits := List([1..rank], i -> [i]),
            orbit_of := orbit_of,
            orbit_reps := orbit_reps,
            n_orbits := rank
        );
    fi;
    grp := Group(perms);
    # Orbits expects a SET-valued action on [1..rank]; we use it directly.
    orbs := Orbits(grp, [1..rank]);
    # Sort each orbit ascending, then orbits by their smallest element.
    orbs := List(orbs, SortedList);
    Sort(orbs, function(a, b) return a[1] < b[1]; end);
    orbit_of := ListWithIdenticalEntries(rank, 0);
    for idx_orb in [1..Length(orbs)] do
        for i in orbs[idx_orb] do
            orbit_of[i] := idx_orb;
        od;
    od;
    orbit_reps := List(orbs, o -> o[1]);
    return rec(
        orbits := orbs,
        orbit_of := orbit_of,
        orbit_reps := orbit_reps,
        n_orbits := Length(orbs)
    );
end;;

# -----------------------------------------------------------------
# Module-level cache: BRWSimplesAction(m) is independent of any
# cocycle, so we memoise per m.
# -----------------------------------------------------------------

_brw_simples_action_cache := rec();;

BRWSimplesAction := function(m)
    local key, conj_action, iso_em, em_pc, em_mat, brw, idx,
          n_classes, gens, n_gens, class_perms, irrep_perms,
          per_gen, perms, image_lists, t, y, info, orbit_data,
          result, class_rep_mats, centraliser_rep_mats, i, j;
    Assert(0, m >= 1, "m must be a positive integer");
    key := Concatenation("m", String(m));
    if IsBound(_brw_simples_action_cache.(key)) then
        return _brw_simples_action_cache.(key);
    fi;

    # Re-use the cached class-level action.
    conj_action := BRWConjugacyAction(m);
    iso_em := conj_action.iso_em;
    em_pc := conj_action.em;
    em_mat := conj_action.em_matrix;
    brw := conj_action.brw;
    n_classes := conj_action.n_classes;

    # Build the simple index against the pc-form (so EvalIrr et al.
    # work natively on em_pc elements).
    idx := BuildSimpleIndex(em_pc);

    # Pre-compute matrix-form lifts of every class rep (for the
    # `y * g_i * y^{-1}` per-(gen, i) conjugation) and every
    # centraliser class rep (for the inner pullback loop). This is the
    # only cross-generator data; PreImagesRepresentative on a pc-group
    # iso is cheap but adds up across the 7 * 65 outer iterations.
    class_rep_mats := List([1..n_classes],
                            i -> PreImagesRepresentative(iso_em,
                                                          idx.reps[i]));
    centraliser_rep_mats := [];
    for i in [1..n_classes] do
        _EnsureClassData(idx, i);
        centraliser_rep_mats[i] := List(idx.cc_centraliser[i],
            cl -> PreImagesRepresentative(iso_em, Representative(cl)));
    od;

    gens := conj_action.gens;
    n_gens := Length(gens);
    class_perms := conj_action.image_lists;     # one per generator

    per_gen := [];
    irrep_perms := [];
    perms := [];
    image_lists := [];
    for t in [1..n_gens] do
        y := gens[t];
        info := _BRWSimpleAction_OnePerm(y, idx, class_perms[t], iso_em,
                                          class_rep_mats,
                                          centraliser_rep_mats);
        Add(per_gen, info);
        Add(irrep_perms, info.irrep_perms);
        Add(image_lists, info.image_list);
        Add(perms, info.perm);
    od;

    orbit_data := _BRWSimpleAction_Orbits(perms, idx.rank);

    result := rec(
        m              := m,
        em             := em_pc,
        em_matrix      := em_mat,
        iso_em         := iso_em,
        brw            := brw,
        idx            := idx,
        rank           := idx.rank,
        gens           := gens,
        class_perms    := class_perms,
        irrep_perms    := irrep_perms,
        per_gen        := per_gen,
        image_lists    := image_lists,
        perms          := perms,
        image_subgroup := Group(perms),
        orbits         := orbit_data.orbits,
        orbit_of       := orbit_data.orbit_of,
        orbit_reps     := orbit_data.orbit_reps,
        n_orbits       := orbit_data.n_orbits
    );
    _brw_simples_action_cache.(key) := result;
    return result;
end;;

# Convenience for tests: orbit-statistics summary.
BRWSimplesActionStats := function(action)
    local sizes;
    sizes := List(action.orbits, Length);
    return rec(
        rank          := action.rank,
        n_orbits      := action.n_orbits,
        orbit_sizes   := Collected(sizes),
        max_orbit     := Maximum(sizes),
        min_orbit     := Minimum(sizes),
        image_order   := Size(action.image_subgroup)
    );
end;;

Print("Loaded brw_simples_action.g (BRWSimplesAction, ",
      "BRWSimplesActionStats).\n");
