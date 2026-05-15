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
# Current implementation:
#   * m in {1, 2, 3}: hardcoded torsion vectors anchored at HAP-verified
#     values (cross-checked against kernel.g files in
#     `computed/transgression/{2,3}/`).
#   * m >= 3 (analytical fallback): derived via Harada-Kono 1987 Thm 1.1
#     (A(4) = Z/4 a priori) + Bockstein analysis of the Q-2a canonical
#     presentation (see quillen_h4_torsion.g). Loaded lazily.
#
# The m=3 derivation is verified against the hardcoded value by
# tests/test_quillen_h3_structure.g. m=5 cross-validates against A-5b's
# empirical k=165 H^3 generators (HAP-based).
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
    # m >= 5: derived analytically via _QH3S_DerivedTorsion below.
);;

# Lazy loader for the Bockstein-derived torsion (Q-int A2 / #136).
# Lives in quillen_h4_torsion.g; loaded on first non-hardcoded call.
_QH3S_DerivedTorsion := function(m)
    if not IsBoundGlobal("QuillenH4TorsionFromBockstein") then
        Read("quillen_h4_torsion.g");
    fi;
    return QuillenH4TorsionFromBockstein(m);
end;;

# Public entry point. Returns rec(m, torsion, exponent, num_generators,
# source). Source = "hardcoded" for m in {1, 2, 3}; "bockstein-derived"
# for m >= 5.
QuillenH3Structure := function(m)
    local key, torsion, source;
    if not (IsInt(m) and m >= 1) then
        Error("QuillenH3Structure: m must be a positive integer");
    fi;
    key := Concatenation("m", String(m));
    if IsBound(_QH3S_TORSION_TABLE.(key)) then
        torsion := ShallowCopy(_QH3S_TORSION_TABLE.(key));
        source  := "hardcoded";
    elif m >= 3 then
        torsion := _QH3S_DerivedTorsion(m);
        source  := "bockstein-derived";
    else
        Error("QuillenH3Structure: cannot derive torsion at m = ", m,
              " (m=2 needs β(w) which is not yet in the table; ",
              "m=1 is hardcoded). See ",
              "docs/superpowers/research/2026-05-15-integer-cohomology-extraspecial-2-groups.md");
    fi;
    return rec(
        m              := m,
        torsion        := torsion,
        exponent       := Maximum(torsion),
        num_generators := Length(torsion),
        source         := source
    );
end;;

# Predicate: is m supported (hardcoded OR derivable via Bockstein)?
QuillenH3StructureAvailable := function(m)
    if not (IsInt(m) and m >= 1) then return false; fi;
    return IsBound(_QH3S_TORSION_TABLE.(Concatenation("m", String(m))))
           or m >= 3;
end;;

Print("Loaded quillen_h3_structure.g ",
      "(QuillenH3Structure 1..3 hardcoded; m>=3 via Bockstein).\n");
