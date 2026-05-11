# Tier 5: Integral cohomology H^n(G; Z) torsion
#
# We expose `IntegralCohomologyTorsion(G, n)` which returns the list of
# elementary divisors of H^n(G; Z) (the abelian-group invariant factors
# of the torsion part), and a convenience wrapper
# `IntegralCohomologyFromAlg(class_F2_alg, n)` for callers that already
# carry around a quillen-algebra-style record holding the group.
#
# Background and design notes (for reviewers).
#
# The Q-5 brief asked for a UCT-based implementation patterned on
# `transgression_kernel.g:SetupCohomology3`, using the Gruen/Morrison
# helper `UniversalCoefficientsTheorem(K, n)` from
# `DRINFELD/src/modular_data.g`.  That helper has a hardcoded
# `K!.dimension(3)` on line 80 that breaks it for any `n != 3`
# (it raises a "list assignments: <rhss> must have the same length"
# error inside `BaseIntersectionIntMats`).  We do NOT patch the
# upstream helper here -- patching `src/modular_data.g` is out of
# scope and could subtly perturb the precomputed (S, T) pipelines
# that depend on its n=3 behaviour.
#
# Instead we use HAP's `GroupCohomology(G, n)`, which returns exactly
# the elementary divisors of the torsion part of H^n(G; Z) for a
# finite group `G`.  Spot-checks:
#   * `GroupCohomology(SmallGroup(8, 3),  4) = [2, 2, 4]`         (D_8)
#   * `GroupCohomology(SmallGroup(32,49), 4) = [2 x 9, 8]`        (E_+(2))
# Both match published values (Adem-Milgram; Quillen).
#
# IMPORTANT NAMING.  We deliberately do NOT define a global called
# `IntegralCohomology` because HAP already has a read-only global
# `IntegralCohomology` (and a read-only `GroupCohomology`).  Our
# user-facing names are `IntegralCohomologyTorsion`,
# `IntegralCohomologyData`, and `IntegralCohomologyFromAlg`.

LoadPackage("hap");

# ---------------------------------------------------------------------
# Primitive entry point.  G a finite group, n >= 1.
# Returns the list of elementary divisors of H^n(G; Z)_tors.
# ---------------------------------------------------------------------
IntegralCohomologyTorsion := function(G, n)
    if not IsGroup(G) then
        Error("IntegralCohomologyTorsion: first arg must be a group");
    fi;
    if not (IsInt(n) and n >= 1) then
        Error("IntegralCohomologyTorsion: n must be a positive integer");
    fi;
    return GroupCohomology(G, n);
end;;

# ---------------------------------------------------------------------
# Richer entry point.  Returns a record carrying the torsion vector
# plus context (group, n, |H^n_tors|, exponent of the elementary
# divisors).
# ---------------------------------------------------------------------
IntegralCohomologyData := function(G, n)
    local divs;
    divs := IntegralCohomologyTorsion(G, n);
    return rec(
        G := G,
        n := n,
        elementary_divisors := divs,
        torsion_order := Product(divs),
        # exponent = lcm of elementary divisors = largest one (for SNF)
        exponent := Lcm(Concatenation([1], divs))
    );
end;;

# ---------------------------------------------------------------------
# Convenience wrapper.  Accepts either a raw group, a record with .G,
# a record with .group, or a record with .group_id = [n, m] for
# SmallGroup(n, m).
# ---------------------------------------------------------------------
IntegralCohomologyFromAlg := function(class_F2_alg, n)
    local G;
    if IsRecord(class_F2_alg) and IsBound(class_F2_alg.G) then
        G := class_F2_alg.G;
    elif IsRecord(class_F2_alg) and IsBound(class_F2_alg.group) then
        G := class_F2_alg.group;
    elif IsRecord(class_F2_alg) and IsBound(class_F2_alg.group_id) then
        G := SmallGroup(class_F2_alg.group_id[1], class_F2_alg.group_id[2]);
    elif IsGroup(class_F2_alg) then
        G := class_F2_alg;
    else
        Error("IntegralCohomologyFromAlg: cannot resolve G from input");
    fi;
    return rec(
        elementary_divisors := IntegralCohomologyTorsion(G, n),
        n := n,
        group_id := IdGroup(G)
    );
end;;
