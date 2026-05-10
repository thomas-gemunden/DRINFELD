# fsi_agt_wrapper.g
#
# A runnable wrapper around the (broken) `FSIforAGT` plumbing in
# src/universal_coefficients.g.  Per V-8 task #55 (issue #19).
#
# This file:
#   (1) Loads `fsi_wrapper.g` (V-3 #47) so that:
#         - `hap` and `io` are loaded,
#         - src/universal_coefficients.g is Read,
#         - `ValuesOfPiSymbols` is overridden with the fixed implementation,
#         - the helpers `FSIContext`, `FSIPiValues`, `ProjectiveCharactersDirect`,
#           etc. are available.
#   (2) Re-defines `FSIforAGT` with the two surface bugs fixed (it does NOT
#       edit src/universal_coefficients.g, per the V-3 / V-4 wrapper pattern).
#   (3) Exposes a thin user-facing entry point `FSIforAGT_Fixed(G, N, omega)`
#       returning a list of FSI lists (one per (coset, irrep) pair).
#
# Background bugs in the original `FSIforAGT` (universal_coefficients.g lines 562-619):
#   1. `listG:-Enumerator(G);` (Pascal-style member access).  GAP does not parse
#      `:-`.  The intent is `listG := Enumerator(G);`.
#   2. The inner anonymous function `nu` accesses
#         `pivalues[Position(listG, Representative(class)*r)[o+RemInt(-m,o)+1]`
#      which is missing a closing bracket after the first `Position(...)`.  The
#      intended expression is
#         `pivalues[Position(listG, Representative(class)*r)][o+RemInt(-m,o)+1]`.
#   3. Stray assignment `Gaa:=list!.Gaa;` references an undeclared identifier
#      `Gaa`.  The variable is never read; it's a dead assignment.  We declare
#      `Gaa` as local to suppress the implicit-global warning.
#
# The math, per [MN05] / Mignard-Schauenburg, is otherwise correct and is left
# untouched.  In particular the unusual index `o + RemInt(-m, o) + 1` into the
# `pivalues[k]` table is INTENTIONAL: it picks `pi_x(j)` for some `j` in
# [0, 2o-1] that, modulo the period-o behaviour of pi-symbols, is the right
# index for the negative-power FS variant.  See the `ValuesOfPiSymbols`
# override in `fsi_wrapper.g`.
#
# MATHEMATICAL CAVEAT (inherited from V-3 / V-4):
#   For non-trivial omega HAP's `StandardCocycle` is not a bar-resolution
#   3-cocycle, so downstream cocycle-on-centraliser constructions are
#   mathematically invalid.  At omega = 0 everything reduces to the classical
#   AGT (algebra-group-triple) Frobenius-Schur indicators of Mignard-Nikshych.
#   Use omega = 0 for verification; treat non-trivial omega as exploratory.


# --- load the V-3 wrapper -------------------------------------------------
# The V-3 wrapper takes care of:
#   - LoadPackage("hap"), LoadPackage("io"), LoadPackage("hapco", false),
#   - locating and Reading src/universal_coefficients.g,
#   - overriding ValuesOfPiSymbols with the fixed implementation,
#   - exposing FSIContext / FSIPiValues / ProjectiveCharactersDirect.
fsiAgtWrap := fail;;
for fsiAgtCand in [".", "..", "../..", "../../..", "../../../..",
                   "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-v8",
                   "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-v3"] do
    if IsExistingFile(Concatenation(fsiAgtCand,
            "/extraspecial_orbifolds/scripts/fsi_wrapper.g")) then
        fsiAgtWrap := Concatenation(fsiAgtCand,
            "/extraspecial_orbifolds/scripts/fsi_wrapper.g");
        break;
    fi;
od;;
if fsiAgtWrap = fail then
    Error("fsi_agt_wrapper.g: could not locate fsi_wrapper.g");
fi;
Read(fsiAgtWrap);;


# --- Override FSIforAGT with the fixed body --------------------------------
#
# Signature follows the original src/universal_coefficients.g (line 562):
#     FSIforAGT := function(G, N, omega)
# where `omega` is an integer cocycle vector for the standard cocycle on R
# (already in cocycle-vector form, i.e. of length R!.dimension(3)).
#
# Returns a list of FS-indicator lists, one per (double coset, projective
# irrep) pair.  Each inner list has length `FSexp` (the exponent of the
# projective fusion category of N\G/N at the chosen omega), indexed by
# m = 0, 1, ..., FSexp - 1.
FSIforAGT := function(G, N, omega)
    local R, K, UCT, hom, FSexp, f, omega_0, omega_1,
          cosets, PC, list, result, i, j, nu, m;
    R := ResolutionFiniteGroup(G, 4);
    K := TensorWithIntegers(R);
    UCT := UniversalCoefficientsTheorem(K, 3);
    hom := (UCT!.cyclebasis * omega) mod UCT!.exponent;
    FSexp := ExponentOfPFC(G, R, K, UCT, hom);
    f := StandardCocycle(R, omega, 3, UCT!.exponent);
    omega_0 := FirstStep(G, R, N, f);
    omega_1 := SecondStep(G, R, N, omega_0);
    cosets := DoubleCosets(G, N, N);
    PC := List(cosets, g -> ProjectiveCharacters(
        Intersection(N, N^(Representative(g)^(-1))),
        function(x, y)
            return omega_1(x, y, Representative(g));
        end,
        UCT!.exponent));
    # The fixed `nu`.  Parameter `f` is the adapted (omega_1) cocycle.
    # `Gaa` is declared local only to suppress the implicit-global warning
    # for the dead assignment `Gaa := list!.Gaa;` from the original source.
    nu := function(G, UCT, N, f, class, list, i, m)
        local x, sum, S, Pf, lift, chi, listG, pivalues, r, o, Gaa;
        S := Intersection(N, N^(Representative(class)^(-1)));
        Gaa := list!.Gaa;
        lift := list!.lift;
        chi := list!.table[i];
        listG := Enumerator(G);                                  # FIX #1
        pivalues := List(listG,
                         x -> ValuesOfPiSymbols(G, R, K, UCT, x, f));
        sum := 0;
        for r in N do
            if (Representative(class) * r)^m in S then
                o := Order(Representative(class) * r);
                sum := sum
                    + (pivalues[Position(listG,
                                Representative(class) * r)][o + 1]
                        ^ (QuoInt(-m, o) - 1))
                    * pivalues[Position(listG,
                                Representative(class) * r)]    # FIX #2: closing ]
                            [o + RemInt(-m, o) + 1]
                    * lift(((Representative(class) * r)^(-m)))^chi;
            fi;
        od;
        return sum / Size(S);
    end;
    result := [];
    for i in [1..Size(PC)] do
        for j in [1..Size(PC[i]!.table)] do
            list := [];
            for m in [0..FSexp - 1] do
                Add(list, nu(G, UCT, N, omega_1, cosets[i], PC[i], j, m));
            od;
            Add(result, list);
        od;
    od;
    return result;
end;;


# --- user-facing entry point ---------------------------------------------
#
# FSIforAGT_Fixed(G, N, omega_vec_or_hom)
#
# Convenience wrapper that accepts either a hom-basis vector (length =
# Size(UCT.hombasis)) or a lifted cocycle vector (length = R!.dimension(3)),
# normalises to a cocycle vector via `FSI_LiftIfHom` (from `fsi_wrapper.g`),
# and dispatches to `FSIforAGT`.
#
# The original `FSIforAGT` requires a cocycle-vector form; this wrapper makes
# omega = 0 easy to construct: pass `[0, 0, ..., 0]` of the right length or
# a hom-vector of zeros.
FSIforAGT_Fixed := function(G, N, omega_vec_or_hom)
    local R, K, UCT, omega_vec;
    R := ResolutionFiniteGroup(G, 4);
    K := TensorWithIntegers(R);
    UCT := UniversalCoefficientsTheorem(K, 3);
    omega_vec := FSI_LiftIfHom(R, UCT, omega_vec_or_hom);
    return FSIforAGT(G, N, omega_vec);
end;;


# --- ProjectiveCharactersDirect fallback for ProjectiveCharacters ----------
#
# The original `ProjectiveCharacters` in src/universal_coefficients.g relies
# on the `hapco` package's `UnderlyingGroup` method on `CcGroup`.  On systems
# without hapco the call `UnderlyingGroup(CcGroup(A, r))` errors with
# "no 1st choice method found for `UnderlyingGroup'".  We unconditionally
# redirect `ProjectiveCharacters` to the V-3 direct implementation, which
# constructs the central extension as a concrete permutation group.  This is
# semantically equivalent (both return rec(Gaa, lift, table)) and removes
# the hapco dependency.
ProjectiveCharacters := function(G, alpha, o)
    return ProjectiveCharactersDirect(G, alpha, o);
end;;


Print("Finished loading fsi_agt_wrapper.g\n");
Print("  - FSIforAGT: overridden with fixed `:-` and missing-`]` body\n");
Print("  - FSIforAGT_Fixed(G, N, omega_vec_or_hom): user-facing entry point\n");
