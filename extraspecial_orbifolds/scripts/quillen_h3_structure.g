# quillen_h3_structure.g — Stage A of the Quillen integration roadmap.
#
# Source: docs/superpowers/plans/2026-05-15-quillen-integration.md.
#
# `QuillenH3Structure(m)` returns a record analogous to the `(torsion,
# exponent, num_generators)` triple that `SetupCohomology3` currently
# computes by running HAP's `ResolutionFiniteGroup` + UCT chain. The HAP
# path OOMs at m = 7 (~60 GB during `ResolutionFiniteGroup`), so this
# file provides an alternative source for the H^3(E_+(m); U(1)) shape.
#
# What this file does NOT provide: the cocycle-evaluator
# `StandardCocycleOf(setup, vec)` — that's Stage B and requires
# explicit bar 3-cocycle formulas (research, separate session).
#
# Mathematical source: Quillen [Q4] 1971 Theorem 4.6 + the Bockstein
# spectral sequence applied to the canonical F_2 cohomology
# presentation (Q-2a, issue #133).
#
# Current implementation: hardcoded torsion vectors anchored at the
# HAP-verified values for m = 1, 2, 3 (cross-checked against the
# kernel.g files in `computed/transgression/{2,3}/`). For m = 5, 7
# the structure is documented as TODO pending the Stage A2/A3 work
# (Bockstein spectral sequence derivation).
#
# Generator order. Inside each entry the torsion list is sorted with
# Z/2 components first and the maximum-order component (where the
# group has higher torsion) last. This matches the convention used by
# `transgression_kernel.g::SetupCohomology3`'s output (verified at
# m = 1, 2, 3 against HAP UCT.torsion sorted via Sort()).

# Known-good torsion vectors. Anchored against the kernel.g files
# (verified via the rung-3 anchor + the D_8 regression).
#
# m = 1: H^3(D_8; U(1)) = Z/2 × Z/2 × Z/4.
#        Source: `computed/transgression/2/kernel.g` predecessor +
#        AM04 Theorem IV.2.7.
# m = 2: H^3(E_+(2); U(1)) = (Z/2)^9 × Z/8.
#        Source: `computed/transgression/2/kernel.g` header.
# m = 3: H^3(E_+(3); U(1)) = (Z/2)^34 × Z/4.
#        Source: A-3a delivery for E_+(3) (kernel.g header).
_QH3S_TORSION_TABLE := rec(
    m1 := [2, 2, 4],
    m2 := [2, 2, 2, 2, 2, 2, 2, 2, 2, 8],
    m3 := Concatenation(ListWithIdenticalEntries(34, 2), [4])
    # m5, m7 deliberately omitted -- pending Stage A2 derivation via the
    # Bockstein spectral sequence on the Q-2a canonical presentation.
);;

# Public entry point. Returns rec(m, torsion, exponent, num_generators).
QuillenH3Structure := function(m)
    local key, torsion;
    if not (IsInt(m) and m >= 1) then
        Error("QuillenH3Structure: m must be a positive integer");
    fi;
    key := Concatenation("m", String(m));
    if not IsBound(_QH3S_TORSION_TABLE.(key)) then
        Error(Concatenation(
            "QuillenH3Structure: torsion for m = ", String(m),
            " not yet derived. ",
            "Available: m in {1, 2, 3}. ",
            "See docs/superpowers/plans/2026-05-15-quillen-integration.md ",
            "Stage A2 for the derivation work."));
    fi;
    torsion := _QH3S_TORSION_TABLE.(key);
    return rec(
        m              := m,
        torsion        := ShallowCopy(torsion),
        exponent       := Maximum(torsion),
        num_generators := Length(torsion),
        source         := "quillen_h3_structure (hardcoded m=1..3)"
    );
end;;

# Predicate: is m supported by the analytical path? Lets callers fall
# back to HAP gracefully when not.
QuillenH3StructureAvailable := function(m)
    return IsBound(_QH3S_TORSION_TABLE.(Concatenation("m", String(m))));
end;;

Print("Loaded quillen_h3_structure.g ",
      "(QuillenH3Structure 1..3; m=5,7 pending).\n");
