# standard_bar_cocycle.g
#
# V-4a / issue #81: HAP `StandardCocycle` and the "1105/4096 violations" bug.
#
# CONCLUSION (after V-4a investigation, 2026-05-11): HAP's `StandardCocycle`
# is NOT buggy.  When given a properly-lifted UCT cocycle vector — i.e.,
# `UCT.lift * v` for `v` an element of `Z^|ZZ| = Z^|cyclebasis|` (NOT
# `Z^|hombasis|`) — the resulting function is a genuine inhomogeneous bar
# 3-cocycle and `alpha_g(omega)` is a genuine 2-cocycle on `C_G(g)`.
#
# The original "1105/4096" failure stemmed from feeding `StandardCocycle` a
# vector that was NOT in the image of the lift: namely, the unit vector
# e_1 = [1, 0, ..., 0] of length `|hombasis|`, used as the argument to
# `UCT.lift * (hom vector of length |hombasis|)`.
#
#   - On Q_8 (small group (8, 4)):
#       R := ResolutionFiniteGroup(Q_8, 4)
#       UCT.exponent = 8,  |hombasis| = 1,  |cyclebasis| = 2
#       UCT.lift is a 3 x 2 matrix (not 3 x 1!)
#       UCT.hombasis[1] = [6, 1]      (the order-8 generator of H^3(Q_8))
#       UCT.lift * [6, 1] mod 8  = [6, 1, 0]   (a valid R-cocycle)
#       UCT.lift * [1, 0] mod 8  = [1, 0, 0]   (NOT a cocycle: violates d^* = 0)
#     and the latter is what the buggy callsite was producing.  HAP then
#     happily applied its `Syzygy`-based formula to a non-cocycle, yielding
#     the 1105 violations observed.
#
# Public API in this file:
#
#   StandardBarCocycle(R, vec, n, m)
#       Wrapper around HAP's `StandardCocycle` that is fully equivalent.
#       Provided for symmetry with the bug-checking helpers below and so
#       that future call sites can use a stable name.
#
#   StandardBarCocycleFromHom(UCT, hom_vec, n, m)  [n = 3 only]
#       The recommended entry point: takes a hom vector  v in Z^|cyclebasis|
#       (e.g. v = UCT.hombasis[i] or a scalar multiple), lifts via UCT.lift,
#       reduces mod m, and returns the resulting bar cocycle function.
#       Catches the original bug at the type-level.
#
#   CheckBar3CocycleEquation(G, omega [, m])
#   CheckAlphaIs2Cocycle(G, g, omega [, m])
#       Brute-force diagnostics that iterate over G^4 and over
#       Centralizer(G, g)^3.

LoadPackage("hap");;


# Wrapper around HAP's StandardCocycle.
#
# `vec` should be a length-`R!.dimension(n)` cochain that is a genuine
# n-cocycle modulo m (i.e., `vec * K!.boundary(n+1, k) = 0 mod m` for all k).
# In practice this means producing `vec` via the UCT lift applied to an
# actual hom vector.
#
# Note `n=0` returns a constant cochain function; supported for completeness.
StandardBarCocycle := function(R, vec, n, m)
    return StandardCocycle(R, vec, n, m);
end;;


# Recommended user-facing entry point for 3-cocycles.
#
# Given a UCT record and a hom vector `hom_vec` of length `|UCT.cyclebasis|`,
# lift to an R-cocycle and return the bar cocycle function `(x, y, z) -> Z/m`.
#
# Typical callers:
#   omega := StandardBarCocycleFromHom(UCT, UCT.hombasis[1], 3, UCT.exponent);
#   omega := StandardBarCocycleFromHom(UCT, 4 * UCT.hombasis[1], 3, UCT.exponent);
#
# If the input has length `|UCT.hombasis|` we error explicitly (this catches
# the most common original-bug mistake).
StandardBarCocycleFromHom := function(R, UCT, hom_vec, n, m)
    local vec, cyclen, homn;
    cyclen := Size(UCT!.cyclebasis);
    homn := Size(UCT!.hombasis);
    if Length(hom_vec) = cyclen then
        # OK -- this is a length-|cyclebasis| vector, can be lifted directly.
    elif Length(hom_vec) = homn and cyclen <> homn then
        Error("StandardBarCocycleFromHom: hom_vec has length ", homn,
              " = |hombasis|, but UCT.lift expects a length-", cyclen,
              " vector (= |cyclebasis|).  Did you mean UCT.hombasis[i] ",
              "rather than a unit vector e_i of length |hombasis|? ",
              "(See V-4a issue #81 writeup in standard_bar_cocycle.g.)");
    else
        Error("StandardBarCocycleFromHom: hom_vec has length ", Length(hom_vec),
              "; expected ", cyclen, " (= |UCT.cyclebasis|).");
    fi;
    if m = 0 then m := UCT!.exponent; fi;
    vec := (UCT!.lift * hom_vec) mod m;
    return StandardCocycle(R, vec, n, m);
end;;


# Brute-force check: omega satisfies the inhomogeneous bar 3-cocycle equation
#
#   omega(x, y, z) - omega(w*x, y, z) + omega(w, x*y, z)
#                  - omega(w, x, y*z) + omega(w, x, y)  =  0  (mod m)
#
# Returns rec(checked, violations).  The m argument is optional; when omitted
# we don't reduce.
CheckBar3CocycleEquation := function(arg)
    local G, omega, m, elts, violations, checked, w, x, y, z, lhs;
    G := arg[1];
    omega := arg[2];
    if Length(arg) >= 3 then m := arg[3]; else m := 0; fi;
    elts := Elements(G);
    violations := 0;
    checked := 0;
    for w in elts do
        for x in elts do
            for y in elts do
                for z in elts do
                    lhs := omega(x, y, z)
                         - omega(w * x, y, z)
                         + omega(w, x * y, z)
                         - omega(w, x, y * z)
                         + omega(w, x, y);
                    if m > 0 then lhs := lhs mod m; fi;
                    if lhs <> 0 then
                        violations := violations + 1;
                    fi;
                    checked := checked + 1;
                od;
            od;
        od;
    od;
    return rec(checked := checked, violations := violations);
end;;


# Brute-force check that
#   alpha_g(x, y) := omega(x, y, g) - omega(x, y*g*y^{-1}, y)
#                                  + omega(x*y*g*y^{-1}*x^{-1}, x, y)
# is a 2-cocycle on Centralizer(G, g).  This is the convention used by
# `alphag` in src/universal_coefficients.g.
CheckAlphaIs2Cocycle := function(arg)
    local G, g, omega, m, C, elts, violations, checked, x, y, z, alpha, lhs;
    G := arg[1];
    g := arg[2];
    omega := arg[3];
    if Length(arg) >= 4 then m := arg[4]; else m := 0; fi;
    C := Centralizer(G, g);
    elts := Elements(C);
    alpha := function(x, y)
        return omega(x, y, g)
             - omega(x, y * g * y^(-1), y)
             + omega(x * y * g * y^(-1) * x^(-1), x, y);
    end;
    violations := 0;
    checked := 0;
    for x in elts do
        for y in elts do
            for z in elts do
                lhs := alpha(y, z) - alpha(x * y, z) + alpha(x, y * z) - alpha(x, y);
                if m > 0 then lhs := lhs mod m; fi;
                if lhs <> 0 then
                    violations := violations + 1;
                fi;
                checked := checked + 1;
            od;
        od;
    od;
    return rec(checked := checked, violations := violations);
end;;


Print("Finished loading standard_bar_cocycle.g\n");
Print("  - StandardBarCocycle(R, vec, n, m)            : HAP wrapper (vec must be a true cocycle)\n");
Print("  - StandardBarCocycleFromHom(R, UCT, hv, n, m) : preferred entry, lifts via UCT.lift\n");
Print("  - CheckBar3CocycleEquation(G, omega [, m])\n");
Print("  - CheckAlphaIs2Cocycle(G, g, omega [, m])\n");
