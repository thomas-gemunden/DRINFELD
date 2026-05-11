# aut_nt_mod_brw.g — Aut(N, T) modulo the BRW subgroup.
#
# Task V-6 (issue #37). Builds on:
#   * aut_nt_partition.g (V-5a) — InitialPartition(N, T, QD).
#   * aut_nt_refine.g    (V-5b) — RefineByFusion(p, N), QuantumDimensionsFromS.
#   * aut_nt.g           (V-5c) — AutNT(N, T, QD[, opts]).
#
# Math context (writeup.md §8.3). For G = E_+(m), the conjugation action
# of BRW(m)/E_+(m) on simples of D^0(E_+(m)) is fusion-and-T-preserving,
# so it embeds as a subgroup of Aut(N, T). The "substantive content" is
# the quotient Aut(N, T) / BRW, which (a) discards a known symmetry that
# is identical between untwisted and Keller MTCs under c_g = 0, and
# (b) halves the search space in tier-3 comparisons.
#
# Goal. Compute |Aut(N, T) / BRW| and a set of coset representatives,
# given:
#   * (N, T, QD) — fusion ring, T-vector, quantum-dimension vector.
#   * BRW_action — the BRW subgroup of Sym(r) already lifted to act on
#     simples. Accepted as either
#         (i)  a GAP `Group` (of permutations on [1..r]), or
#         (ii) a list of length-r image lists (each list represents a
#              permutation via sigma[i] = image of i), or
#         (iii) a list of GAP `Perm` objects, or
#         (iv) `fail` or the empty list, meaning the trivial subgroup.
#
# Approach (post-hoc quotient). Per the issue: run V-5c's AutNT in full
# to obtain (|Aut|, gens), build Aut as a permutation group, build BRW
# as a permutation subgroup, divide. The "wall-clock ≤ 1/4 of V-5c on
# E_+(3)" stretch target is flagged as TODO (would require an integrated
# coset-enumerating backtracking variant of AutNT).
#
# Acceptance.
#   * D(Q_8) trivial cocycle: |Aut| = 6, BRW = trivial (Q_8 is not
#     plus-type extraspecial), quotient order = 6.
#   * D(Q_8) order-2 cocycle: |Aut| = 24, BRW = trivial, quotient = 24.
#   * D^1(E_+(2)): gated/TODO until V-5c E_+(2) ground truth lands.
#
# Globals installed by this file:
#   AutNTModBRW(N, T, QD, BRW_action[, opts])  — main entry point.
#   _aut_nt_mod_brw_normalise_brw(brw_arg, r)  — internal helper.

if not IsBound(AutNT) then
    Error("aut_nt_mod_brw.g: AutNT not loaded; Read aut_nt.g first.");
fi;

# ---- Normalise the BRW_action argument ------------------------------
# Returns a GAP Group <= Sym([1..r]). Accepts the four input shapes
# documented above.

_aut_nt_mod_brw_normalise_brw := function(brw_arg, r)
    local g, perms, p, gens;
    # Case (iv): trivial.
    if brw_arg = fail then
        return Group(());
    fi;
    if IsList(brw_arg) and Length(brw_arg) = 0 then
        return Group(());
    fi;
    # Case (i): already a group.
    if IsGroup(brw_arg) then
        return brw_arg;
    fi;
    # Case (ii) or (iii): a list of permutations.
    if IsList(brw_arg) then
        perms := [];
        for g in brw_arg do
            if IsPerm(g) then
                Add(perms, g);
            elif IsList(g) and Length(g) = r and ForAll(g, IsInt) then
                # Length-r image list. Validate it's a permutation of
                # [1..r] before converting.
                if Set(g) <> [1 .. r] then
                    Error("_aut_nt_mod_brw_normalise_brw: image list ",
                          "is not a permutation of [1..", r, "].");
                fi;
                p := PermList(g);
                if p = fail then
                    Error("_aut_nt_mod_brw_normalise_brw: ",
                          "PermList failed on image list.");
                fi;
                Add(perms, p);
            else
                Error("_aut_nt_mod_brw_normalise_brw: unrecognised ",
                      "generator type ", TNAM_OBJ(g), ".");
            fi;
        od;
        if Length(perms) = 0 then
            return Group(());
        fi;
        return Group(perms);
    fi;
    Error("_aut_nt_mod_brw_normalise_brw: argument must be `fail`, ",
          "a list of permutations / image lists, or a group; got ",
          TNAM_OBJ(brw_arg), ".");
end;

# ---- Helper: convert AutNT generators (image lists) to perms --------

_aut_nt_mod_brw_gens_to_perms := function(generator_lists, r)
    local perms, g, p;
    perms := [];
    for g in generator_lists do
        if Set(g) <> [1 .. r] then
            Error("_aut_nt_mod_brw_gens_to_perms: image list ",
                  "is not a permutation.");
        fi;
        p := PermList(g);
        if p = fail then
            Error("_aut_nt_mod_brw_gens_to_perms: PermList failed.");
        fi;
        Add(perms, p);
    od;
    return perms;
end;

# ---- Main entry point ------------------------------------------------
# AutNTModBRW(N, T, QD, BRW_action[, opts])
#
# Computes Aut(N, T) / BRW where BRW is the input subgroup of Sym(r).
#
# Returns rec with fields:
#   .order             — |Aut| / |BRW ∩ Aut|. (Equal to |Aut| / |BRW|
#                        when BRW ⊆ Aut, which is the §8.3 statement
#                        for E_+(m). When BRW is trivial, .order = |Aut|.)
#   .full              — the underlying rec returned by AutNT, with
#                        fields .order (|Aut|) and .generators.
#   .brw_order         — |BRW ∩ Aut|.
#   .brw_input_order   — |BRW| as given (before intersecting with Aut).
#   .brw_subset_of_aut — true iff BRW ⊆ Aut(N, T) (sanity-checked when
#                        opts.skip_brw_check is false).
#   .coset_reps        — list of permutations representing the cosets
#                        of BRW in <Aut.generators>. Empty if AutNT
#                        was called with skip_generators = true, or if
#                        the caller passes opts.skip_coset_reps = true.
#   .quotient_generators — list of permutations forming generators of
#                        the image of Aut → Aut/BRW. Computed as the
#                        non-identity coset reps unless skipped.
#
# Caveats.
#   - When BRW ⊄ Aut, the intersection BRW ∩ Aut is what divides; the
#     "quotient" is the right-coset space (Aut / (BRW ∩ Aut)), a set
#     not a group in general. We still report .order as |Aut| /
#     |BRW ∩ Aut| because that is the post-hoc quotient size matching
#     the issue's recommendation. .brw_subset_of_aut flags this.
#   - For E_+(m) with the correct BRW lift, BRW ⊆ Aut (writeup §8.3),
#     so the quotient is a group and .quotient_generators are honest.
#
# opts (record). Fields:
#   .max_generators        — cap on AutNT's generator collection
#                            (default 32; passed through).
#   .skip_generators       — pass-through to AutNT. If true, AutNT
#                            returns only .order and no generators; we
#                            can still report .order and .brw_order
#                            but .coset_reps and .quotient_generators
#                            will be empty.
#   .skip_brw_check        — if true, do not verify BRW ⊆ Aut. Useful
#                            when the user is confident; otherwise we
#                            check via the |BRW ∩ Aut| computation
#                            (which is a side-effect of using the
#                            transversal).
#   .skip_coset_reps       — if true, do not compute .coset_reps /
#                            .quotient_generators (saves time when
#                            only the order is needed).
#   .verbose               — if true, print progress messages.

AutNTModBRW := function(arg)
    local N, T, QD, brw_arg, opts, r, full, full_opts,
          aut_perms, aut_grp, brw_grp, brw_in_aut, brw_input_order,
          brw_order, quotient_order, brw_subset_of_aut, transversal,
          coset_reps, quotient_gens, t, sane_int;
    if Length(arg) < 4 or Length(arg) > 5 then
        Error("AutNTModBRW: expected 4 or 5 arguments ",
              "(N, T, QD, BRW_action[, opts]).");
    fi;
    N := arg[1];
    T := arg[2];
    QD := arg[3];
    brw_arg := arg[4];
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
    if not IsBound(opts.skip_brw_check) then
        opts.skip_brw_check := false;
    fi;
    if not IsBound(opts.skip_coset_reps) then
        opts.skip_coset_reps := false;
    fi;
    if not IsBound(opts.verbose) then
        opts.verbose := false;
    fi;
    r := Length(T);
    if Length(QD) <> r then
        Error("AutNTModBRW: |T| = ", r, " but |QD| = ", Length(QD), ".");
    fi;
    if Length(N) <> r then
        Error("AutNTModBRW: |T| = ", r, " but |N| = ", Length(N), ".");
    fi;
    # Normalise BRW_action to a permutation group on [1..r].
    brw_grp := _aut_nt_mod_brw_normalise_brw(brw_arg, r);
    brw_input_order := Size(brw_grp);
    if opts.verbose then
        Print("AutNTModBRW: r = ", r,
              ", |BRW_action input| = ", brw_input_order, "\n");
    fi;
    # Run AutNT.
    full_opts := rec(max_generators := opts.max_generators,
                     skip_generators := opts.skip_generators);
    if opts.verbose then
        Print("AutNTModBRW: calling AutNT...\n");
    fi;
    full := AutNT(N, T, QD, full_opts);
    if opts.verbose then
        Print("AutNTModBRW: |Aut(N, T)| = ", full.order, ", ",
              Length(full.generators), " generators.\n");
    fi;
    # Build Aut as a permutation group from its generators. If we have
    # no generators (skip_generators or Aut is trivial), Aut = <()>.
    if Length(full.generators) > 0 then
        aut_perms := _aut_nt_mod_brw_gens_to_perms(full.generators, r);
        aut_grp := Group(aut_perms);
    else
        aut_grp := Group(());
    fi;
    # If we asked AutNT to skip generators, the generators list is empty
    # but Aut is still |full.order|. We can only compute the post-hoc
    # ratio in that case (no transversal possible without group).
    if opts.skip_generators then
        # Best-effort: |Aut ∩ BRW| = |BRW| if BRW ⊆ Aut (by §8.3),
        # but we cannot verify it. Use the input |BRW| as the divisor;
        # flag .brw_subset_of_aut as fail (unknown).
        sane_int := full.order mod brw_input_order;
        if sane_int <> 0 then
            Error("AutNTModBRW: |Aut| = ", full.order,
                  " not divisible by |BRW| = ", brw_input_order,
                  " (with skip_generators=true we cannot intersect, ",
                  "so this is fatal).");
        fi;
        return rec(
            order := full.order / brw_input_order,
            full := full,
            brw_order := brw_input_order,
            brw_input_order := brw_input_order,
            brw_subset_of_aut := fail,
            coset_reps := [],
            quotient_generators := []
        );
    fi;
    # Sanity check generated subgroup order matches AutNT's claim.
    if Size(aut_grp) <> full.order then
        # This indicates the V-5c generator-collection capped before
        # enumerating all coset reps. Warn but proceed using the
        # actual generated subgroup.
        if opts.verbose then
            Print("AutNTModBRW: WARNING <generators> has order ",
                  Size(aut_grp), " but AutNT.order = ", full.order,
                  ". opts.max_generators may have been too small.\n");
        fi;
    fi;
    # Compute BRW ∩ Aut.
    brw_in_aut := Intersection(brw_grp, aut_grp);
    brw_order := Size(brw_in_aut);
    brw_subset_of_aut := (brw_order = brw_input_order);
    if (not opts.skip_brw_check) and (not brw_subset_of_aut) then
        if opts.verbose then
            Print("AutNTModBRW: WARNING BRW_action ⊄ Aut(N, T): ",
                  "|BRW| = ", brw_input_order, ", |BRW ∩ Aut| = ",
                  brw_order, "\n");
        fi;
    fi;
    # |Aut| / |BRW ∩ Aut|, computed on the actual generated subgroup.
    # Use Size(aut_grp) (not full.order) for consistency with the
    # transversal step.
    if brw_order = 0 then
        Error("AutNTModBRW: |BRW ∩ Aut| = 0 (impossible: identity is ",
              "always in the intersection).");
    fi;
    quotient_order := Size(aut_grp) / brw_order;
    # Compute coset representatives if requested.
    coset_reps := [];
    quotient_gens := [];
    if not opts.skip_coset_reps then
        if Size(aut_grp) = 1 then
            # Aut is trivial; one coset (the identity).
            coset_reps := [()];
        else
            transversal := RightTransversal(aut_grp, brw_in_aut);
            coset_reps := AsList(transversal);
            # Quotient generators: non-identity coset reps, deduped at
            # the coset level (any one rep per non-trivial coset). The
            # full list `coset_reps` already has one rep per coset.
            quotient_gens := Filtered(coset_reps, t -> t <> ());
        fi;
    fi;
    return rec(
        order := quotient_order,
        full := full,
        brw_order := brw_order,
        brw_input_order := brw_input_order,
        brw_subset_of_aut := brw_subset_of_aut,
        coset_reps := coset_reps,
        quotient_generators := quotient_gens
    );
end;

Print("Loaded aut_nt_mod_brw.g (AutNTModBRW).\n");
