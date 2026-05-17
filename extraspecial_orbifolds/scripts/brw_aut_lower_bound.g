# brw_aut_lower_bound.g  —  A-3d perf-1 (issue #239).
#
# Constructive verification of the BRW lower bound for |Aut(N^0, T^0)|
# at E_+(m). Instead of computing |Aut(N, T)| by full backtracking
# (the A-3d perf-3 path), we explicitly construct each element of
# BRW(m)/E_+(m) as a permutation of the simples and verify that it is
# a valid (N, T)-automorphism. The set of (N, T)-automorphisms is a
# group, so once we have verified that each generator of the BRW
# image preserves (N, T), every element of the generated subgroup is
# also an automorphism. We then count |<perms>| in Sym(rank) to
# confirm we have |BRW(m)/E_+(m)| distinct (N, T)-automorphisms.
#
# Math anchor (issue #45, writeup §8.3). Let phi_y : E_+(m) -> E_+(m)
# be conjugation by y in BRW(m). phi_y permutes conjugacy classes of
# E_+(m) (T-3c), and for each class i with rep g_i, phi_y restricts to
# a group isomorphism C_G(g_i) -> C_G(phi_y(g_i)); choosing a
# conjugator c_i with c_i * g_{tau(i)} * c_i^{-1} = phi_y(g_i) gives
# the bijection
#
#       C_G(g_i) ---phi_y---> C_G(phi_y(g_i)) ---conj by c_i^{-1}---> C_G(g_{tau(i)})
#       x -> c_i^{-1} * y * x * y^{-1} * c_i.
#
# This induces an irrep permutation pi_i : Irr(C_G(g_i)) -> Irr(C_G(g_{tau(i)})).
# The simples of the untwisted Drinfeld centre are pairs (g_i, chi)
# with chi in Irr(C_G(g_i)), so phi_y lifts to a permutation sigma_y
# on the rank-many simples by sigma_y(i, k) = (tau(i), pi_i(k)).
# BRW(m)/E_+(m) embeds into Aut(N^0, T^0) via y -> sigma_y; this file
# verifies that embedding constructively.
#
# Acceptance (issue #239):
#   * For each generator y_i of BRW(m), sigma_{y_i} preserves T and S
#     (equivalently N, since N is Verlinde-derived from S).
#   * |<sigma_{y_1}, sigma_{y_2}, ...>| in Sym(rank) = |BRW(m)/E_+(m)|.
#   * count_verified == |BRW(m)/E_+(m)|, count_failed == 0.
#
# At m = 3: |BRW(3)/E_+(3)| = 40320 (= GAP's |GO+(6, F_2)|) — NOT the
# 1,451,520 stated in issue #239. The issue text has a math-convention
# error; the actual quotient produced by brw_construction.g is 40320
# (verified empirically and matching test_brw_conjugacy_action.g's
# expectation for m = 3). The constructive certificate is therefore for
# 40320 (N, T)-automorphisms, not 1.45M.
#
# Exported entry points:
#   * BRWSimpleAction(m, idx)
#         Build the simple-side permutations sigma_y for every generator
#         y of BRW(m). Returns rec(perms, image_lists, class_perms,
#         conjugators, tau, brw, m, idx). `perms[i]` is a GAP `Perm`
#         on [1..idx.rank]; `image_lists[i]` is the parallel length-rank
#         image list.
#
#   * VerifyBRWAutLowerBound(md, action[, opts])
#         Run the full verification:
#           1. For each sigma in action.perms, check T- and S-preservation.
#           2. Build <action.perms> in Sym(rank), verify |.| matches
#              the expected |BRW(m)/E_+(m)| (= |O+(2m, F_2)|).
#         Returns rec(group, m, rank, brw_lower_bound, count_verified,
#         count_failed, generator_results, time, verdict, ...).
#
# Conventions. We work with the pc-group form em = Image(iso_em) of
# EmGroup(m) — same as brw_h3_action.g and brw_conjugacy_action.g.
# Conjugation by a BRW matrix y is translated through iso_em.

if not IsBound(BRWConjugacyAction) then
    Read("brw_conjugacy_action.g");
fi;
if not IsBound(BuildSimpleIndex) then
    Read("untwisted_modular_data.g");
fi;

# Local copy of brw_h3_action.g's helper (avoid pulling in the HAP /
# transgression machinery which brw_h3_action.g triggers via
# transgression_kernel.g; that resolution is unnecessary here).
if not IsBound(ConjugationAutomorphismThroughIso) then
    ConjugationAutomorphismThroughIso := function(em_pc, iso_em, y)
        local gens_pc, images_pc, phi;
        gens_pc := GeneratorsOfGroup(em_pc);
        images_pc := List(gens_pc, g_pc ->
            Image(iso_em,
                  y * PreImagesRepresentative(iso_em, g_pc) * y^(-1)));
        phi := GroupHomomorphismByImages(em_pc, em_pc, gens_pc, images_pc);
        if phi = fail then
            Error("ConjugationAutomorphismThroughIso: y not an automorphism");
        fi;
        return phi;
    end;;
fi;

# ---------------------------------------------------------------------
# Build a transport table on the pc-group form em: for each conjugacy
# class i of em, store a function `transport_to(i, a)` returning c such
# that c * reps[i] * c^(-1) = a. We need this to define the conjugator
# c_i used in the irrep permutation lift.
#
# We reuse BuildTransports from untwisted_modular_data.g via the idx
# record; idx is the same BuildSimpleIndex output the caller passes in.
# ---------------------------------------------------------------------

# Locate the index `bi` of element `a` in the precomputed transport
# table for class `i`. Returns fail if `a` is not in class i.
_BRWAutLB_ClassTransportIndex := function(transport, i, a)
    local entry, bi;
    entry := transport[i];
    bi := LookupDictionary(entry.elt_to_idx, a);
    return bi;   # may be fail
end;;

# ---------------------------------------------------------------------
# Given (idx, transport, phi, i), determine:
#   tau_i  : index of the class containing phi(reps[i]),
#   c_i    : the transport element such that
#               c_i * reps[tau_i] * c_i^(-1) = phi(reps[i]).
# The phi here is a GroupHomomorphism em -> em (pc form).
# ---------------------------------------------------------------------

_BRWAutLB_TauAndConjugator := function(idx, transport, phi, i)
    local g_i_image, t, tau_i, bi, c_i;
    g_i_image := Image(phi, idx.reps[i]);
    # Find which class g_i_image belongs to: by class size + element
    # order, then membership in the class element set. Materialise the
    # class element sets lazily; the transport table already has them.
    for tau_i in [1..Length(idx.classes)] do
        bi := _BRWAutLB_ClassTransportIndex(transport, tau_i, g_i_image);
        if bi <> fail then
            c_i := transport[tau_i].t_of[bi];   # c_i * reps[tau_i] * c_i^{-1} = g_i_image
            return rec(tau := tau_i, conjugator := c_i);
        fi;
    od;
    Error("_BRWAutLB_TauAndConjugator: phi(reps[", i,
          "]) does not lie in any conjugacy class of em (impossible).");
end;;

# ---------------------------------------------------------------------
# For class i with image class tau_i and conjugator c_i:
#   The composite map psi_i : C_G(g_i) -> C_G(g_{tau_i})
#       x -> c_i^{-1} * phi(x) * c_i
#   is a group isomorphism. We need the induced irrep permutation:
#       pi_i(k) = index j in [1..num_irreps[tau_i]] such that
#           irreps[i][k] (as a class function on C_G(g_i))
#         is the pullback (composition with psi_i^{-1}) of irreps[tau_i][j].
#
# Equivalently (and easier to compute), for each j we pull irreps[tau_i][j]
# back along psi_i: chi'(x) = irreps[tau_i][j](psi_i(x)). The resulting
# character of C_G(g_i) matches some irreps[i][k_j] (k_j is the index
# of this pullback). We then set pi_i(k_j) := j.
#
# To avoid recomputing character tables, we use existing GAP character
# objects directly via EvalIrr.
# ---------------------------------------------------------------------

_BRWAutLB_IrrepPerm := function(idx, transport, phi, i, tau_i, c_i)
    local Ni, Nj, cc_i, char_values_pullback, k, j, chi_i_values, l,
          perm, used, cn, x, psi_x, found_j;
    Ni := idx.num_irreps[i];
    Nj := idx.num_irreps[tau_i];
    if Ni <> Nj then
        Error("_BRWAutLB_IrrepPerm: |Irr(C_G(g_", i, "))| = ", Ni,
              " but |Irr(C_G(g_", tau_i, "))| = ", Nj,
              "; phi is supposed to give a group iso of centralisers.");
    fi;
    cc_i := idx.cc_centraliser[i];   # length Ni; conjugacy classes of C_G(g_i)
    # Build vectors of character values on cc_i for both:
    # (a) chi_i_values[k] := list of values irreps[i][k] takes on each cc_i[l]
    # (b) char_values_pullback[j][l] := value of irreps[tau_i][j] at
    #         c_i^{-1} * phi(x_l) * c_i, where x_l is a rep of cc_i[l].
    # Then pi_i(k) = the unique j with chi_i_values[k] = char_values_pullback[j].
    chi_i_values := List(idx.irreps[i], chi -> ShallowCopy(chi));
    # Build the pullback values. For each conjugacy class cc_i[l] of
    # C_G(g_i), pick a representative x_l, compute psi_i(x_l) =
    # c_i^{-1} * phi(x_l) * c_i, find its class in C_G(g_{tau_i}), and
    # read off each irrep value.
    char_values_pullback := List([1..Nj], j -> []);
    for l in [1..Length(cc_i)] do
        x := Representative(cc_i[l]);
        psi_x := c_i^(-1) * Image(phi, x) * c_i;
        cn := ClassIndexInCentraliser(idx, tau_i, psi_x);
        for j in [1..Nj] do
            char_values_pullback[j][l] := idx.irreps[tau_i][j][cn];
        od;
    od;
    # Match each k to the (unique) j with chi_i_values[k] = char_values_pullback[j].
    perm := [];
    used := ListWithIdenticalEntries(Nj, false);
    for k in [1..Ni] do
        found_j := fail;
        for j in [1..Nj] do
            if not used[j] and chi_i_values[k] = char_values_pullback[j] then
                found_j := j;
                used[j] := true;
                break;
            fi;
        od;
        if found_j = fail then
            Error("_BRWAutLB_IrrepPerm: irreps[", i, "][", k,
                  "] has no match among Irr(C_G(g_", tau_i,
                  ")) pullbacks; check phi and c_i.");
        fi;
        perm[k] := found_j;
    od;
    return perm;
end;;

# ---------------------------------------------------------------------
# Single-generator: build the permutation sigma_y on [1..idx.rank] for
# one BRW(m) generator y. y is a matrix in BRW(m) acting on em_matrix
# by conjugation; we translate to em (pc) via iso_em.
#
# Returns rec(image_list, perm, tau, conjugators, irrep_perms) where:
#   image_list : length-rank list; image_list[s] = sigma_y(s).
#   perm       : PermList(image_list).
#   tau        : length-|classes| list; tau[i] = class containing phi(reps[i]).
#   conjugators: length-|classes| list; conjugators[i] = c_i.
#   irrep_perms: length-|classes| list of lists; irrep_perms[i] = pi_i.
# ---------------------------------------------------------------------

BRWAutLB_BuildOneSigma := function(idx, transport, iso_em, em, y)
    local phi, n_classes, tau, conjugators, irrep_perms, image_list,
          i, info, c_i, tau_i, pi_i, k, s_target, off_i, off_tau;
    phi := ConjugationAutomorphismThroughIso(em, iso_em, y);
    n_classes := Length(idx.classes);
    tau := [];
    conjugators := [];
    irrep_perms := [];
    image_list := [];
    for i in [1..n_classes] do
        info := _BRWAutLB_TauAndConjugator(idx, transport, phi, i);
        tau[i] := info.tau;
        conjugators[i] := info.conjugator;
        c_i := info.conjugator;
        tau_i := info.tau;
        pi_i := _BRWAutLB_IrrepPerm(idx, transport, phi, i, tau_i, c_i);
        irrep_perms[i] := pi_i;
        # Lift to global indices: simple (i, k) at global_offset[i]+k goes
        # to simple (tau_i, pi_i[k]) at global_offset[tau_i]+pi_i[k].
        off_i := idx.global_offset[i];
        off_tau := idx.global_offset[tau_i];
        for k in [1..idx.num_irreps[i]] do
            image_list[off_i + k] := off_tau + pi_i[k];
        od;
    od;
    return rec(
        image_list := image_list,
        perm := PermList(image_list),
        tau := tau,
        conjugators := conjugators,
        irrep_perms := irrep_perms
    );
end;;

# ---------------------------------------------------------------------
# Top-level: build sigma_y for every generator y of BRW(m).
#
# This entry point assumes the caller has already built a BuildSimpleIndex
# `idx` and wants the BRW simple-action lifted on top. It mirrors the
# shape of BRWConjugacyAction (T-3c) and reuses its em / iso_em / brw.
#
# Returns rec with fields:
#   m              : the input m.
#   idx            : the BuildSimpleIndex passed in (verified consistent).
#   em             : pc-group form of EmGroup(m) (must equal idx.group).
#   iso_em         : the matrix-to-pc isomorphism.
#   brw            : BRW(m) (matrix group).
#   brw_gens       : GeneratorsOfGroup(brw).
#   perms          : list of Perms in Sym(idx.rank), one per BRW gen.
#   image_lists    : list of length-rank image lists.
#   per_gen        : list of records from BRWAutLB_BuildOneSigma per gen
#                    (for diagnostic / debugging use).
#   class_perms    : list of class-permutations (Perms in Sym(n_classes))
#                    induced by each generator, as a sanity hook (== the
#                    output of BRWConjugacyAction.perms).
# ---------------------------------------------------------------------

BRWSimpleAction := function(m, idx)
    local conj_action, em, iso_em, brw, brw_gens, transport, perms,
          image_lists, per_gen, class_perms, i, y, one, p_class;
    Assert(0, m >= 1, "BRWSimpleAction: m must be a positive integer");
    Assert(0, IsRecord(idx), "BRWSimpleAction: idx must be a record");
    # Use BRWConjugacyAction to get em (pc), iso_em, brw, generators
    # cached (P-5 / #114). Cheap if already built.
    conj_action := BRWConjugacyAction(m);
    em := conj_action.em;
    iso_em := conj_action.iso_em;
    brw := conj_action.brw;
    brw_gens := conj_action.gens;
    if idx.group <> em then
        Error("BRWSimpleAction: idx.group does not equal em (pc) ",
              "produced by BRWConjugacyAction(", m, "); pass a fresh ",
              "idx := BuildSimpleIndex(em).");
    fi;
    # Transports (cached on idx via BuildTransports semantics).
    transport := BuildTransports(idx);
    perms := [];
    image_lists := [];
    per_gen := [];
    class_perms := ShallowCopy(conj_action.perms);
    for i in [1..Length(brw_gens)] do
        y := brw_gens[i];
        one := BRWAutLB_BuildOneSigma(idx, transport, iso_em, em, y);
        # Sanity: the class-level permutation we computed should match
        # the BRWConjugacyAction one (independent code path).
        p_class := PermList(one.tau);
        if p_class <> conj_action.perms[i] then
            Error("BRWSimpleAction: class permutation for generator ",
                  i, " disagrees with BRWConjugacyAction (got ",
                  p_class, ", expected ", conj_action.perms[i], ").");
        fi;
        Add(perms, one.perm);
        Add(image_lists, one.image_list);
        Add(per_gen, one);
    od;
    return rec(
        m := m,
        idx := idx,
        em := em,
        iso_em := iso_em,
        brw := brw,
        brw_gens := brw_gens,
        perms := perms,
        image_lists := image_lists,
        per_gen := per_gen,
        class_perms := class_perms
    );
end;;

# ---------------------------------------------------------------------
# Per-generator (N, T) verification.
#
# Given a single permutation sigma (as an image list of length rank)
# and the modular data (S, T), check that:
#   * T[sigma[i]] = T[i] for all i.
#   * S[sigma[i]][sigma[j]] = S[i][j] for all i, j. (S preservation
#     implies N preservation via Verlinde.)
#
# We choose to verify S rather than N because (a) S has dense O(r^2)
# storage, vs N having r^3; (b) we already have S in memory at this
# point in the driver, so no re-derivation needed.
#
# Returns rec(t_ok, s_ok, t_mismatches, s_mismatches) where the
# `*_mismatches` are length-bounded sample lists for diagnostics.
# ---------------------------------------------------------------------

VerifyAutomorphismOnST := function(sigma, S, T, opts)
    local r, i, j, t_ok, s_ok, t_mismatches, s_mismatches,
          max_mismatch_log;
    if not IsBound(opts.max_mismatch_log) then
        opts := ShallowCopy(opts);
        opts.max_mismatch_log := 10;
    fi;
    max_mismatch_log := opts.max_mismatch_log;
    r := Length(T);
    t_ok := true;
    t_mismatches := [];
    for i in [1..r] do
        if T[sigma[i]] <> T[i] then
            t_ok := false;
            if Length(t_mismatches) < max_mismatch_log then
                Add(t_mismatches, rec(i := i, sigma_i := sigma[i],
                                       T_i := T[i],
                                       T_sigma_i := T[sigma[i]]));
            fi;
        fi;
    od;
    s_ok := true;
    s_mismatches := [];
    for i in [1..r] do
        for j in [1..r] do
            if S[sigma[i]][sigma[j]] <> S[i][j] then
                s_ok := false;
                if Length(s_mismatches) < max_mismatch_log then
                    Add(s_mismatches, rec(i := i, j := j,
                                          sigma_i := sigma[i],
                                          sigma_j := sigma[j],
                                          S_ij := S[i][j],
                                          S_sij := S[sigma[i]][sigma[j]]));
                fi;
                # Early-out is permitted once we have enough samples;
                # for diagnostics we keep going up to the cap.
            fi;
        od;
        if not s_ok and Length(s_mismatches) >= max_mismatch_log then
            break;
        fi;
    od;
    return rec(t_ok := t_ok, s_ok := s_ok,
               t_mismatches := t_mismatches,
               s_mismatches := s_mismatches);
end;;

# ---------------------------------------------------------------------
# Per-generator (N, T) verification using a pre-computed N (3D list).
# This is used by tests that already have N in memory (typically the
# Q_8 sanity test, where r = 22 and N is cheap to materialise).
#
# Naive O(r^3) but acceptable at r ≤ ~200; at E_+(3) (r = 2272) we
# prefer the S-preservation path.
# ---------------------------------------------------------------------

_BRWAutLB_CheckN := function(sigma, N)
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
end;;

VerifyAutomorphismOnNT := function(sigma, N, T)
    local r, i, t_ok, n_ok;
    r := Length(T);
    t_ok := true;
    for i in [1..r] do
        if T[sigma[i]] <> T[i] then
            t_ok := false;
            break;
        fi;
    od;
    n_ok := _BRWAutLB_CheckN(sigma, N);
    return rec(t_ok := t_ok, n_ok := n_ok);
end;;

# ---------------------------------------------------------------------
# Top-level lower-bound verifier.
#
# Args:
#   md         : record with fields .S, .T, .idx (output of
#                ComputeUntwistedModularData).
#   action     : output of BRWSimpleAction(m, md.idx).
#   opts       : optional record. Fields:
#                  .verbose         (default true)
#                  .group_label     (default Concatenation("E_+(", m, ")"))
#                  .expected_lb     (default |O+(2m, F_2)|; required when
#                                    md.idx.group != E_+(m) — there is
#                                    no canonical BRW for general G).
#                  .skip_subgroup_order (default false; skips the final
#                                    |<perms>| check, useful for very
#                                    quick smoke tests).
#                  .max_mismatch_log (default 10).
#
# Returns rec with fields:
#   group               : the input label.
#   m                   : m.
#   rank                : Length(md.T).
#   brw_lower_bound     : the BRW lower bound.
#   count_verified      : total elements verified (= |<perms>| when
#                         all generators pass; else the partial count).
#   count_failed        : 0 if all generators pass, otherwise # gens
#                         that failed.
#   generator_results   : list of per-generator records (with .t_ok,
#                         .s_ok, .t_mismatches, .s_mismatches).
#   subgroup_order      : |<perms>| in Sym(rank), or fail if skipped.
#   time                : total wall-clock seconds.
#   verdict             : "BOUND_VERIFIED", "GENERATOR_FAILED", or
#                         "SUBGROUP_MISMATCH".
# ---------------------------------------------------------------------

VerifyBRWAutLowerBound := function(arg)
    local md, action, opts, verbose, expected_lb, label, t_start, r,
          generator_results, count_failed, count_verified, sub_order,
          sub_grp, i, sigma, vr, verdict, m, all_ok, n_gens;
    if Length(arg) < 2 or Length(arg) > 3 then
        Error("VerifyBRWAutLowerBound: 2 or 3 arguments expected ",
              "(md, action[, opts]).");
    fi;
    md := arg[1];
    action := arg[2];
    if Length(arg) = 3 then
        opts := arg[3];
    else
        opts := rec();
    fi;
    if not IsBound(opts.verbose) then
        opts.verbose := true;
    fi;
    if not IsBound(opts.max_mismatch_log) then
        opts.max_mismatch_log := 10;
    fi;
    if not IsBound(opts.skip_subgroup_order) then
        opts.skip_subgroup_order := false;
    fi;
    if not IsBound(opts.expected_lb) then
        # Default to |BRW(m)/E_+(m)| computed directly from the group
        # orders. Matches Order(GeneralOrthogonalGroup(1, 2m, 2)) in
        # GAP's convention (which is *not* the 1,451,520 stated in
        # issue #239 — see file header).
        opts.expected_lb := Order(action.brw) / Order(action.em);
    fi;
    if not IsBound(opts.group_label) then
        opts.group_label := Concatenation("E_+(", String(action.m), ")");
    fi;
    verbose := opts.verbose;
    expected_lb := opts.expected_lb;
    label := opts.group_label;
    m := action.m;
    t_start := Runtime();
    r := Length(md.T);
    if verbose then
        Print("\n=== BRW lower-bound verifier: ", label, " ===\n");
        Print("rank = ", r, "\n");
        Print("expected lower bound = ", expected_lb, "\n");
        Print("# BRW generators = ", Length(action.image_lists), "\n");
    fi;
    n_gens := Length(action.image_lists);
    generator_results := [];
    count_failed := 0;
    for i in [1..n_gens] do
        sigma := action.image_lists[i];
        if verbose then
            Print("\n[gen ", i, "/", n_gens, "] verifying ...\n");
        fi;
        vr := VerifyAutomorphismOnST(sigma, md.S, md.T,
                                      rec(max_mismatch_log :=
                                          opts.max_mismatch_log));
        Add(generator_results, vr);
        if verbose then
            Print("  T preserved: ", vr.t_ok,
                  "  S preserved: ", vr.s_ok, "\n");
            if not vr.t_ok then
                Print("  T mismatches (sample): ",
                      vr.t_mismatches, "\n");
            fi;
            if not vr.s_ok then
                Print("  S mismatches (sample): ",
                      vr.s_mismatches, "\n");
            fi;
        fi;
        if not (vr.t_ok and vr.s_ok) then
            count_failed := count_failed + 1;
        fi;
    od;
    all_ok := (count_failed = 0);
    sub_order := fail;
    if all_ok and not opts.skip_subgroup_order then
        if verbose then
            Print("\n--- subgroup order check ---\n");
        fi;
        sub_grp := Group(action.perms);
        sub_order := Size(sub_grp);
        if verbose then
            Print("|<sigma_y : y in BRW gens>| = ", sub_order, "\n");
            Print("expected                    = ", expected_lb, "\n");
        fi;
    fi;
    if not all_ok then
        verdict := "GENERATOR_FAILED";
        count_verified := 0;
    elif opts.skip_subgroup_order then
        verdict := "BOUND_VERIFIED_NO_SUBGROUP_CHECK";
        count_verified := fail;
    elif sub_order = expected_lb then
        verdict := "BOUND_VERIFIED";
        count_verified := sub_order;
    else
        verdict := "SUBGROUP_MISMATCH";
        count_verified := sub_order;
    fi;
    return rec(
        group := label,
        m := m,
        rank := r,
        brw_lower_bound := expected_lb,
        count_verified := count_verified,
        count_failed := count_failed,
        generator_results := generator_results,
        subgroup_order := sub_order,
        time := (Runtime() - t_start) / 1000.,
        verdict := verdict
    );
end;;

# ---------------------------------------------------------------------
# Convenience driver: do the whole thing for a given m, including
# building the index, modular data, BRW simple action, and verifier.
# ---------------------------------------------------------------------

RunBRWAutLowerBound := function(arg)
    local m, opts, conj_action, idx, md, action, result;
    if Length(arg) < 1 or Length(arg) > 2 then
        Error("RunBRWAutLowerBound: 1 or 2 arguments expected ",
              "(m[, opts]).");
    fi;
    m := arg[1];
    if Length(arg) = 2 then
        opts := arg[2];
    else
        opts := rec();
    fi;
    conj_action := BRWConjugacyAction(m);
    idx := BuildSimpleIndex(conj_action.em);
    md := rec(idx := idx,
              T := ComputeUntwistedT(idx),
              S := ComputeUntwistedS(idx));
    action := BRWSimpleAction(m, idx);
    result := VerifyBRWAutLowerBound(md, action, opts);
    return rec(md := md, action := action, verification := result);
end;;

Print("Loaded brw_aut_lower_bound.g (BRWSimpleAction, ",
      "VerifyBRWAutLowerBound, RunBRWAutLowerBound, ",
      "VerifyAutomorphismOnST, VerifyAutomorphismOnNT).\n");
