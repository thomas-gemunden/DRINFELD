# epsilon_omega.g — Tier-1 ε_ω phase callable in CGR convention.
#
# ----------------------------------------------------------------------
# Mathematical background
# ----------------------------------------------------------------------
# For a finite group G with normalised 3-cocycle ω : G^3 → Z/m, the
# twisted Drinfeld double Z(Vec^ω_G) has S-matrix
#
#   S^ω_{(g_1, χ_1), (g_2, χ_2)} = (1/|G|) ·
#       Σ_{a ∈ [g_1], b ∈ [g_2], ab = ba}
#         ε_ω(g_1, g_2, a, b) · χ_1(t_a^{-1} b t_a)^* · χ_2(s_b^{-1} a s_b)^*
#
# (the twisted Bantay / Coste–Gannon–Ruelle formula; see writeup §6.2).
# Here the section elements satisfy
#     a = t_a · g_1 · t_a^{-1}   and   b = s_b · g_2 · s_b^{-1}
# i.e. t_a = RepresentativeAction(G, g_1, a) and similarly for s_b.
#
# The phase ε_ω depends only on (g_1, g_2, a, b) (and the section
# choices t_a, s_b), not on the projective characters χ_i.  In the
# CGR2000 / DPR convention as written out in writeup §6.2 it is
#
#   ε_ω(g_1, g_2, a, b) = θ_a(t_a, g_2) · θ_b(s_b, g_1)^{-1} · β_{a,b}(g_1, g_2)^{-1}
#
# where θ_g(x, y) is the slant of ω by g and β_{a,b} collects section
# corrections.  The integer formula matched against the on-disk Q_8
# data (modular_data/8/4/2.txt) is the one already realised by
# `CoefficientSSum` in DRINFELD/src/modular_data.g lines 442–448; we
# simply name and document it.
#
# ----------------------------------------------------------------------
# Sign / cocycle convention
# ----------------------------------------------------------------------
# Source: Coste–Gannon–Ruelle, "Finite group modular data"
# (arXiv:hep-th/0001158), §4 — also used in DPR91 and NN08.
#
# In this codebase ω is represented as a callable G × G × G → Z/m
# returning the integer logarithm of a root of unity:
# the actual U(1) value is E(m)^{ω(g, h, k)} where m = UCT.exponent.
# The integer-valued slant of ω by g at (x, y) is
#
#   slant(g, x, y) := ω(g, x, y)
#                   + ω(x, y, (xy)^{-1} g (xy))
#                   - ω(x, x^{-1} g x, y)             (mod m)
#
# This matches the local `beta` defined in modular_data.g line 491
# (which reduces to writeup §6.2's θ_g for g central, and is the
# correct CGR2000 form for non-central g).
#
# Then the integer logarithm of ε_ω is
#
#   int(g_1, g_2, a, b) :=
#       slant(g_1, t_a, b) + slant(g_1, t_a · b, t_a^{-1})
#     + slant(g_2, s_b, a) + slant(g_2, s_b · a, s_b^{-1})
#     - slant(a, t_a^{-1}, t_a) - slant(b, s_b^{-1}, s_b)        (mod m)
#
# This is exactly the body of `CoefficientSSum(exponent, val, beta,
# a=g_1, b=g_2, h=a, l=b, xh=t_a, yl=s_b)` in modular_data.g.
#
# `EpsilonOmega` therefore returns the integer phase exponent in
# Z/m — i.e. the value `int` above mod m.  The actual U(1) phase is
# E(m)^{EpsilonOmega(...)}.
#
# Notes:
# * If ω = 0 (the trivial cocycle) then every slant vanishes and so
#   ε_ω ≡ 0 in Z/m, i.e. E(m)^0 = 1, as required.
# * For g_1, g_2 ∈ Z(G) and t_a = s_b = 1 the formula reduces to
#   slant(g_1, 1, g_2) + slant(g_2, 1, g_1) = 0 if ω is normalised at
#   1, recovering the structural fact in writeup §6.5 that the
#   central×central block of ε_ω is automatically trivial.
# ----------------------------------------------------------------------

# `EpsilonOmegaSlant(omega, g, x, y)`: integer slant of ω by g at (x, y).
# Matches the local `beta` of modular_data.g (the version general enough
# for non-central g; it specialises to the writeup's θ_g for g central).
EpsilonOmegaSlant := function(omega, g, x, y)
    local xy_inv_g_xy, x_inv_g_x;
    xy_inv_g_xy := (x*y)^-1 * g * (x*y);
    x_inv_g_x   := x^-1 * g * x;
    return omega(g, x, y)
         + omega(x, y, xy_inv_g_xy)
         - omega(x, x_inv_g_x, y);
end;;

# `EpsilonOmegaWithSection(omega, g1, g2, a, b, ta, sb, m)`:
# the integer ε_ω-exponent as a Z/m element, given pre-computed
# section elements ta, sb satisfying
#     a = ta · g1 · ta^{-1}    and    b = sb · g2 · sb^{-1}.
# Returned value is the integer exponent in Z/m: actual phase is
# E(m)^{return-value}.
EpsilonOmegaWithSection := function(omega, g1, g2, a, b, ta, sb, m)
    local int;
    int :=
          EpsilonOmegaSlant(omega, g1, ta, b)
        + EpsilonOmegaSlant(omega, g1, ta*b, ta^-1)
        + EpsilonOmegaSlant(omega, g2, sb, a)
        + EpsilonOmegaSlant(omega, g2, sb*a, sb^-1)
        - EpsilonOmegaSlant(omega, a, ta^-1, ta)
        - EpsilonOmegaSlant(omega, b, sb^-1, sb);
    return int mod m;
end;;

# `EpsilonOmega(G, omega, g1, g2, a, b, m)`:
# the integer ε_ω-exponent as a Z/m element; sections t_a, s_b are
# computed via `RepresentativeAction(G, g_i, ·)`.
#
# Requirements:
# * `a` must lie in the conjugacy class of `g1` in G;
# * `b` must lie in the conjugacy class of `g2` in G;
# * `a` and `b` must commute (otherwise the term is meaningless in the
#   S-formula — but `EpsilonOmega` will still return a value, so it is
#   the caller's responsibility to filter).
#
# The section choice `RepresentativeAction(G, g, h)` returns a
# t ∈ G with h = t · g · t^{-1}, matching the convention of
# `GenerateSimpleObjects` in modular_data.g.
EpsilonOmega := function(G, omega, g1, g2, a, b, m)
    local ta, sb;
    ta := RepresentativeAction(G, g1, a);
    sb := RepresentativeAction(G, g2, b);
    if ta = fail then
        Error("a is not conjugate to g1 in G");
    fi;
    if sb = fail then
        Error("b is not conjugate to g2 in G");
    fi;
    return EpsilonOmegaWithSection(omega, g1, g2, a, b, ta, sb, m);
end;;
