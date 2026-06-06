# Closed-form conjugacy-class enumeration for E_+(m) = EmUnimodGroup(m).
#
# Issue #447 Change A.
#
# CONTEXT
# =======
# The default builder `BuildSimpleIndexLazy(G)` in untwisted_modular_data.g
# starts by calling GAP's generic `ConjugacyClasses(G)`. For
# G = EmUnimodGroup(7) (matrix group of degree 128, |G| = 2^15) this call
# has been observed to consume 19+ hours of wall time (PR #447 background).
#
# This file replaces that call with a STRUCTURAL enumeration tied to the
# extraspecial-2-group structure of E_+(m): the group has order 2^{2m+1},
# centre Z = <z> with z = -I_{2^m}, and quotient G/Z =~ F_2^{2m}.
# Each non-central coset {x, zx} of Z is a conjugacy class of size 2
# (standard extraspecial result: every commutator [g, h] lies in Z, so
# for non-central x, zx = [g, x] for some g and hence x ~ zx in G).
# The two central elements {I, z} are singleton classes.
#
# Combined with the standard four-type partition recorded in
# `brw_conjugacy_action.g::ClassifyEmConjugacyClasses` we get
#
#     id              :  1 class (rep = I_{2^m})
#     minus_one       :  1 class (rep = -I_{2^m})
#     sigma2          :  2^{2m-1} + 2^{m-1} - 1 classes  (x^2 = I, x not central)
#     sigma_1sigma_2  :  2^{2m-1} - 2^{m-1}        classes  (x^2 = -I,  order 4)
#
# (Per `compute_e_plus_7_T_analytical.g` header.)
#
# After computing class representatives in closed form, we install them on
# the group via `SetConjugacyClasses(G, classes)`. This pre-populates the
# `ConjugacyClasses` attribute so that any subsequent call (including the
# implicit one inside `CharacterTable(G)`) returns OUR list without the
# generic enumeration.
#
# CLOSED-FORM num_irreps
# ----------------------
# For E_+(m) the centraliser types are:
#
#   id, minus_one:       C = E_+(m)              -> |Irr(C)| = 4^m + 1
#   sigma2:              C = E_+(m-1) x Z_2      -> |Irr(C)| = 2 * (4^{m-1} + 1)
#   sigma_1sigma_2:      C = Z_4 o E_+(m-1)      -> |Irr(C)| = 2 * 4^{m-1} + 2
#
# (Source: `compute_e_plus_7_T_analytical.g` header, per KRR Prop 3.1.)
# These are computed analytically here; no per-class `CharacterTable`,
# `NrConjugacyClasses`, or `Centralizer` call is required to determine
# them.
#
# PUBLIC API
# ==========
#   BuildSimpleIndexEPlusClosedForm(m)
#       -> rec of the same shape as `BuildSimpleIndexLazy(EmUnimodGroup(m))`
#          (so it is a drop-in replacement on the central-class hot path
#          inside `BuildKRRSpectralCharactersSparse`).
#
# DEPENDENCIES
# ============
# Callers must load (in this order) BEFORE this file:
#   bw_lattice.g, em_construction.g, twisted_group_algebra.g
#       -> UnimodSigma, EmUnimodGroup ingredients
#   krr_spectral_characters.g
#       -> EmUnimodGroup
#   untwisted_modular_data.g
#       -> shape reference (no functions are called from it here, but the
#          consumers of the returned rec expect that file's API).


# ============================================================
# Class enumerator: walk the 2^{2m} cosets of Z = <-I> in
# EmUnimodGroup(m), pick one representative per coset, return the
# four-type partition.
# ============================================================
#
# OUTPUT shape (a record with):
#   .reps              : list of matrix representatives, one per class.
#                        The first is IdentityMat(n); the second is
#                        -IdentityMat(n); the remaining 2^{2m} - 1 are
#                        non-central representatives.
#   .types             : per-class string label ("id" | "minus_one"
#                        | "sigma2" | "sigma_1sigma_2").
#   .class_sizes       : per-class size (1 for central, 2 for non-central).
#   .num_classes       : total count = 2^{2m} + 1.
#
# COMPLEXITY
# ----------
# 2^{2m} matrix products of size 2^m x 2^m + 2^{2m} matrix squarings.
# At m = 7 this is 16383 multiplies of 128x128 matrices (~10 ms each =>
# ~2.7 min). All in compiled GAP integer matrix arithmetic.
#
# CORRECTNESS
# -----------
# We rely on two extraspecial-2-group facts:
#   (a) Every coset of Z = <z> in G has exactly two elements {x, zx},
#       which are conjugate in G (because [g, x] = z for some g ∈ G
#       whenever x is non-central, by the fact that G/Z is elementary
#       abelian with a non-degenerate commutator pairing).
#   (b) For any non-central x ∈ G, x^2 ∈ Z, so x^2 = I or x^2 = -I.
#       The order of x is 2 in the first case, 4 in the second.
#
# Both facts are verified empirically by the smoke test in
# `tests/test_buildsimpleindex_eplus_closed_form.g` for m ∈ {2, 3}.
_EnumerateEPlusClassReps := function(m)
    local n, gens, I_n, z_n, reps, types, class_sizes, ei, bits, k, x,
          a, r, idx, x_sq, num_total, sigma2_count, sigma4_count;
    n := 2^m;
    I_n := IdentityMat(n);
    z_n := -I_n;
    # Generators σ_{a,r} = UnimodSigma(m, a, r) for a in 1..m, r in 1..2.
    gens := List([1..m], a -> List([1, 2], r -> UnimodSigma(m, a, r)));
    reps := [];
    types := [];
    class_sizes := [];
    # Class 1: identity. Class 2: -I. Both central singletons.
    Add(reps, I_n);
    Add(types, "id");
    Add(class_sizes, 1);
    Add(reps, z_n);
    Add(types, "minus_one");
    Add(class_sizes, 1);
    # Non-central cosets of Z: index ei ∈ {1, ..., 2^{2m} - 1} encodes a
    # length-2m bit vector (e_{1,1}, e_{1,2}, ..., e_{m,1}, e_{m,2}) and
    # x = product of σ_{a,r} with e_{a,r} = 1. The two coset elements
    # are {x, zx}; we pick x as the canonical representative.
    sigma2_count := 0;
    sigma4_count := 0;
    for ei in [1..4^m - 1] do
        bits := EmptyPlist(2 * m);
        k := ei;
        for idx in [1..2 * m] do
            Add(bits, k mod 2);
            k := QuoInt(k, 2);
        od;
        # Build the matrix x = product_{a, r} gens[a][r]^{bits[2(a-1)+r]}.
        x := I_n;
        for a in [1..m] do
            for r in [1..2] do
                idx := 2 * (a - 1) + r;
                if bits[idx] = 1 then
                    x := x * gens[a][r];
                fi;
            od;
        od;
        # x is non-central by construction (ei != 0 means at least one σ
        # factor is present, so x is not in Z).  Classify by x^2.
        x_sq := x * x;
        Add(reps, x);
        Add(class_sizes, 2);  # All non-central E_+(m)-classes have size 2.
        if x_sq = I_n then
            Add(types, "sigma2");
            sigma2_count := sigma2_count + 1;
        elif x_sq = z_n then
            Add(types, "sigma_1sigma_2");
            sigma4_count := sigma4_count + 1;
        else
            Error("_EnumerateEPlusClassReps: rep for ei = ", ei,
                  " has unexpected square (neither I nor -I); ",
                  "the extraspecial-2-group invariant is violated.");
        fi;
    od;
    num_total := Length(reps);
    # Cross-check: counts match the closed-form formula.
    if sigma2_count <> 2^(2 * m - 1) + 2^(m - 1) - 1 then
        Error("_EnumerateEPlusClassReps: sigma2 count mismatch at m = ", m,
              ": got ", sigma2_count, ", expected ",
              2^(2 * m - 1) + 2^(m - 1) - 1, ".");
    fi;
    if sigma4_count <> 2^(2 * m - 1) - 2^(m - 1) then
        Error("_EnumerateEPlusClassReps: sigma_1sigma_2 count mismatch at m = ", m,
              ": got ", sigma4_count, ", expected ",
              2^(2 * m - 1) - 2^(m - 1), ".");
    fi;
    if num_total <> 2^(2 * m) + 1 then
        Error("_EnumerateEPlusClassReps: total class count mismatch at m = ", m,
              ": got ", num_total, ", expected ", 2^(2 * m) + 1, ".");
    fi;
    return rec(
        reps := reps,
        types := types,
        class_sizes := class_sizes,
        num_classes := num_total,
        per_type_counts := rec(
            id := 1,
            minus_one := 1,
            sigma2 := sigma2_count,
            sigma_1sigma_2 := sigma4_count
        )
    );
end;;


# ============================================================
# Analytical |Irr(C_G(rep))| for each class type.
#
# At E_+(m), the centraliser of a class representative depends only on
# its BRW-orbit type:
#   id, minus_one        :  C = G itself     ->  |Irr| = 4^m + 1
#   sigma2 (order 2 nc)  :  C = E_+(m-1) x Z_2  ->  |Irr| = 2 * (4^{m-1} + 1)
#   sigma_1sigma_2       :  C = Z_4 o E_+(m-1)  ->  |Irr| = 2 * 4^{m-1} + 2
#
# Sanity-check at m = 3:
#   id, minus_one:  4^3 + 1 = 65   (matches NrConjugacyClasses(G) = 65)
#   sigma2:         2 * (16 + 1) = 34
#   sigma_1sigma_2: 2 * 16 + 2 = 34
# Both match empirical Irr counts (verified during PR #447 design).
# ============================================================
_EPlusNumIrrepsForType := function(m, type)
    if type = "id" or type = "minus_one" then
        return 4 ^ m + 1;
    elif type = "sigma2" then
        return 2 * (4 ^ (m - 1) + 1);
    elif type = "sigma_1sigma_2" then
        return 2 * 4 ^ (m - 1) + 2;
    fi;
    Error("_EPlusNumIrrepsForType: unknown type \"", type, "\".");
end;;


# ============================================================
# BuildSimpleIndexEPlusClosedForm(m): closed-form CC enumeration that
# returns a `BuildSimpleIndexLazy`-shaped record for EmUnimodGroup(m).
#
# DROP-IN COMPATIBILITY
# ---------------------
# The returned rec has every field that `BuildSimpleIndexLazy` returns,
# in the same shape, so it can substitute on the central-class hot path
# inside `BuildKRRSpectralCharactersSparse`:
#   .group, .order, .classes, .reps, .class_sizes, .centralisers,
#   .ct_centraliser, .cc_centraliser, .irreps, .irrep_dims (all `fail`),
#   .num_irreps, .global_offset, .global_to_local, .rank, .is_lazy = true.
#
# Plus extras specific to this builder:
#   .class_types        : per-class BRW-orbit-type string label
#                          ("id"|"minus_one"|"sigma2"|"sigma_1sigma_2").
#   .source             : "closed-form-eplus" (diagnostic).
#
# NOTE on `idx.centralisers`:
#   * For the central classes (id, minus_one), the centraliser is G itself
#     — we install G directly with no Centralizer call.
#   * For non-central classes, we call `Centralizer(G, rep)`. At m = 7
#     this is 16383 such calls. They are independent and not the
#     dominant cost (the `ConjugacyClasses(G)` we replaced is the
#     bottleneck per issue #447).
#
# CONSTRUCTION ORDER
# ------------------
#   1. Enumerate per-class reps + types + sizes via _EnumerateEPlusClassReps.
#   2. Wrap each rep as a `ConjugacyClass(G, rep)` object and set its
#      cached `Size`. Then install the whole list via
#      `SetConjugacyClasses(G, classes)`. This memoises the attribute so
#      that any later `ConjugacyClasses(G)` / `CharacterTable(G)` /
#      `NrConjugacyClasses(G)` call uses OUR enumeration.
#   3. Build centralisers eagerly: G for central classes (free), and
#      `Centralizer(G, rep)` for non-central reps.
#   4. Compute `num_irreps` from the analytical type formula.
#   5. Wire up `global_offset`, `global_to_local`, `rank`, mark `.is_lazy
#      := true`, and seed the lazy CT/Irr slots with `fail`.
#
# PRE-FILLED FIELDS
# -----------------
# `idx.classes` is a list of ConjugacyClass GAP objects (so any consumer
# calling `Representative(idx.classes[i])`, `Size(idx.classes[i])`,
# `x in idx.classes[i]` works without extra setup). `idx.reps` and
# `idx.class_sizes` are the parallel lists of matrices and sizes (we
# also `SetSize(class, size)` so `Size(class)` returns immediately).
BuildSimpleIndexEPlusClosedForm := function(m)
    local n, G, enum, num_classes, classes, sizes, reps, types, i, rep,
          cl, centralisers, num_irreps, global_offset, glob_to_local,
          idx, k, rank, t0, t1;
    Assert(0, m >= 1, "m must be a positive integer");

    n := 2^m;
    G := EmUnimodGroup(m);

    # Step 1: enumerate representatives + types.
    t0 := Runtime();
    enum := _EnumerateEPlusClassReps(m);
    t1 := Runtime();
    Info(InfoWarning, 3,
         "BuildSimpleIndexEPlusClosedForm(", m,
         "): enumerated ", enum.num_classes, " classes in ",
         (t1 - t0) / 1000.0, " s");

    num_classes := enum.num_classes;
    reps := enum.reps;
    types := enum.types;
    sizes := enum.class_sizes;

    # Step 2: wrap reps in ConjugacyClass GAP objects + memoise size,
    # then install on G via SetConjugacyClasses.
    classes := EmptyPlist(num_classes);
    for i in [1..num_classes] do
        cl := ConjugacyClass(G, reps[i]);
        # SetSize avoids any future on-demand enumeration of class
        # elements when the consumer asks for Size(class).
        SetSize(cl, sizes[i]);
        Add(classes, cl);
    od;
    # Memoise ConjugacyClasses(G) -> OUR list. Subsequent calls to
    # ConjugacyClasses(G), NrConjugacyClasses(G), CharacterTable(G)
    # use this enumeration instead of GAP's generic search.
    if not HasConjugacyClasses(G) then
        SetConjugacyClasses(G, classes);
    fi;

    # Step 3: centralisers. Central classes -> G. Non-central ->
    # Centralizer(G, rep). At m = 7 this is 2 + 16383 centraliser calls;
    # the per-call cost (O(|G|)) is unrelated to the `ConjugacyClasses(G)`
    # bottleneck we replaced. Tracked separately if it becomes a
    # bottleneck of its own.
    centralisers := EmptyPlist(num_classes);
    for i in [1..num_classes] do
        if types[i] = "id" or types[i] = "minus_one" then
            Add(centralisers, G);
        else
            Add(centralisers, Centralizer(G, reps[i]));
        fi;
    od;

    # Step 4: analytical num_irreps + derived global indexing.
    num_irreps := List(types, t -> _EPlusNumIrrepsForType(m, t));
    rank := Sum(num_irreps);
    global_offset := EmptyPlist(num_classes);
    Add(global_offset, 0);
    for i in [1..num_classes - 1] do
        Add(global_offset, global_offset[i] + num_irreps[i]);
    od;
    glob_to_local := EmptyPlist(rank);
    for i in [1..num_classes] do
        for k in [1..num_irreps[i]] do
            Add(glob_to_local, [i, k]);
        od;
    od;

    # Step 5: assemble the result rec. Mirror `BuildSimpleIndexLazy`'s
    # output shape exactly so the spectral code path is a drop-in swap.
    idx := rec(
        group := G,
        order := 2 ^ (2 * m + 1),  # closed-form |G|; avoids Order(G).
        classes := classes,
        reps := reps,
        class_sizes := sizes,
        centralisers := centralisers,
        # Lazy slots — populated on first `_EnsureClassData` access.
        ct_centraliser := List([1..num_classes], _ -> fail),
        cc_centraliser := List([1..num_classes], _ -> fail),
        irreps         := List([1..num_classes], _ -> fail),
        irrep_dims     := List([1..num_classes], _ -> fail),
        num_irreps := num_irreps,
        global_offset := global_offset,
        global_to_local := glob_to_local,
        rank := rank,
        is_lazy := true,
        # Extras specific to the closed-form builder.
        class_types := types,
        per_type_counts := enum.per_type_counts,
        source := "closed-form-eplus"
    );
    return idx;
end;;
