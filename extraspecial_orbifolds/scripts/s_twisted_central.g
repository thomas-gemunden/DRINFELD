# s_twisted_central.g — Tier-1 closed-form S^ω central-row entry.
#
# ----------------------------------------------------------------------
# What this file exports
# ----------------------------------------------------------------------
# Public callable:
#
#   STwistedCentralEntry(G, omega, m, g1, chi1, g2, chi2)
#
# returns the (g1, chi1), (g2, chi2) entry of the S-matrix of the
# twisted Drinfeld centre Z(Vec^ω_G), under the requirement that
# g1 lies in the central subgroup {1, -1} of G (i.e. g1 has order 1 or
# 2 and is central in G).
#
# An error is thrown if g1 is not central of order ≤ 2.
#
# ----------------------------------------------------------------------
# Mathematical content (writeup §6.3)
# ----------------------------------------------------------------------
# The twisted Bantay/CGR S-formula (§6.2) is
#
#   S^ω_{(g1, χ1), (g2, χ2)} = (1/|G|) ·
#       Σ_{a ∈ [g1], b ∈ [g2], ab = ba}
#         ε_ω(g1, g2, a, b) · conj(χ1(t_a^{-1} b t_a)) · conj(χ2(s_b^{-1} a s_b)).
#
# When g1 lies in the centre of G:
#   * [g1] = {g1} is a singleton — only one a contributes.
#   * We may pick t_a = 1 since g1 = 1·g1·1^{-1}; hence t_a^{-1} b t_a = b.
#   * s_b^{-1} g1 s_b = g1 because g1 is central.
#
# These reduce the formula to (§6.3):
#
#   S^ω_{((g1, χ1), (g2, χ2))} = (1/|G|) ·
#       Σ_{b ∈ [g2]} ε_ω(g1, g2, g1, b) · conj(χ1(b)) · conj(χ2(g1)).
#
# The χ2(g1) factor is independent of b, so we factor it out:
#
#   S^ω = conj(χ2(g1)) / |G| ·
#         Σ_{b ∈ [g2]} ε_ω(g1, g2, g1, b) · conj(χ1(b)).
#
# Cost: O(|[g2]|) = O(|G|/|C_G(g2)|) ε_ω-evaluations per entry,
# independent of m.
#
# In the trivial-cocycle case ω = 0, ε_ω ≡ 0 in Z/m so E(m)^{ε_ω} = 1
# and χ1 is an ordinary class function on G. Then conj(χ1(b)) = conj(χ1(g2))
# is constant on [g2], and the sum collapses:
#
#   S^0 = conj(χ2(g1)) · |[g2]| · conj(χ1(g2)) / |G|
#       = conj(χ2(g1)) · conj(χ1(g2)) / |C_G(g2)|
#       = χ2(g1) · conj(χ1(g2)) / |C_G(g2)|       [χ2(g1) is real]
#
# which is the writeup §4.3 closed form (χ2(1) = dim χ2 for g1 = 1,
# χ2(-1) ∈ {±dim χ2} for g1 = -1).
#
# ----------------------------------------------------------------------
# Argument convention
# ----------------------------------------------------------------------
# * G is a finite group.
# * omega : G × G × G → Z/m is a callable returning integer exponents
#   (the actual U(1) value is E(m)^omega(...)); matches V-1's
#   EpsilonOmega convention.
# * m is the cocycle exponent (the divisor m used in E(m)^k phases).
# * g1, g2 are elements of G; g1 must be central with Order(g1) ≤ 2.
# * chi1 is a callable G → C; the projective character of the
#   centraliser C_G(g1) = G (when g1 = 1: an ordinary irrep of G;
#   when g1 = -1: a c_{g1}-projective irrep).
# * chi2 is a callable C_G(g2) → C; the projective character of
#   C_G(g2). Only its value at g1 is used (since g1 is central).
#
# Both chi1 and chi2 may be implemented either as a callable
# (`function(x) ... end`) or as anything supporting GAP's `^j` syntax.
# For the latter, wrap as `x -> x^chi`. For dictionary-backed characters
# (as produced by `GenerateSimpleObjects`), wrap as
# `x -> LookupDictionary(dict, x)`.
#
# ----------------------------------------------------------------------
# Load order
# ----------------------------------------------------------------------
# This file expects EpsilonOmegaWithSection (from epsilon_omega.g) to
# be loaded.  Either Read("epsilon_omega.g") before reading this file,
# or change CWD to the scripts directory first.
# ----------------------------------------------------------------------

# Read epsilon_omega.g if EpsilonOmegaWithSection is not yet defined.
# This handles both `Read("scripts/s_twisted_central.g")` from the
# project root and `Read("s_twisted_central.g")` from scripts/.
if not IsBoundGlobal("EpsilonOmegaWithSection") then
    Read("epsilon_omega.g");
fi;

# `STwistedCentralEntry(G, omega, m, g1, chi1, g2, chi2)`:
# Returns S^ω_{((g1, χ1), (g2, χ2))} for g1 in the centre of G with
# Order(g1) ≤ 2.  Throws if g1 is not central or has order > 2.
STwistedCentralEntry := function(G, omega, m, g1, chi1, g2, chi2)
    local class_g2, sum, b, sb, eps_int, chi2_g1, chi1_b;

    # Sanity: g1 must be central of order ≤ 2 ("g1 ∈ {1, -1}").
    if Order(g1) > 2 then
        Error("STwistedCentralEntry: g1 must have order ≤ 2 (got order ",
              Order(g1), "); the {1, -1} central-row reduction does not ",
              "apply to higher-order central elements without further ",
              "structure.");
    fi;
    if not IsCentral(G, g1) then
        Error("STwistedCentralEntry: g1 must be central in G; the §6.3 ",
              "closed-form reduction requires C_G(g1) = G so that [g1] ",
              "is a singleton.");
    fi;

    # χ2(g1): independent of b. Computed once.
    chi2_g1 := chi2(g1);

    # Sum over b ∈ [g2].
    class_g2 := AsSSortedList(ConjugacyClass(G, g2));
    sum := 0;
    for b in class_g2 do
        # Section element s_b ∈ G with b = s_b · g2 · s_b^{-1}.
        sb := RepresentativeAction(G, g2, b);
        if sb = fail then
            Error("Internal error: b in [g2] but RepresentativeAction ",
                  "returns fail. b = ", b, ", g2 = ", g2);
        fi;
        # ε_ω(g1, g2, g1, b) with t_a = 1, s_b as above.
        eps_int := EpsilonOmegaWithSection(omega, g1, g2,
                                           g1, b, One(G), sb, m);
        chi1_b := chi1(b);
        sum := sum + E(m)^eps_int * chi1_b;
    od;

    # Multiply in the constant χ2(g1) factor, conjugate, divide by |G|.
    return ComplexConjugate(sum * chi2_g1) / Order(G);
end;;
