# Q-6: H^n(G; U(1)) via the iso to H^{n+1}(G; Z).
#
# For finite G, H^k(G; R) = 0 for k >= 1, so the short exact sequence
#     0 -> Z -> R -> U(1) -> 0
# induces a connecting iso
#     H^n(G; U(1)) ~= H^{n+1}(G; Z).
#
# Concretely we use Gruen's `UniversalCoefficientsTheorem(K, n+1)` from
# `DRINFELD/src/modular_data.g` (where `K := TensorWithIntegers(R)` for
# `R := ResolutionFiniteGroup(G, n+2)`).  The hombasis it returns is a
# Z/exp-basis of the torsion part of H^{n+1}(G; Z), which is exactly
# H^n(G; U(1)) for finite G.
#
# This file re-exposes that data under U(1) semantics so callers
# (e.g. transgression_kernel.g) can use it as a drop-in.
#
# WARNING: `UniversalCoefficientsTheorem` in `src/modular_data.g`
# hard-codes `K!.dimension(3)` on line 80.  That makes it safe only
# at n+1 = 3 (the brief's n=3 case for E_+(2)).  Calling this at any
# other `n` is gated below; we error out loudly rather than silently
# returning the wrong group.

LoadPackage("hap");

# ---- Locate modular_data.g lazily for UniversalCoefficientsTheorem ----
# We need the Gruen UCT helper from DRINFELD/src/modular_data.g.  Use
# INPUT_FILENAME() to locate it robustly across CWDs (matches the
# pattern in quillen_detecting_subgroup.g).
_q6_uct_loaded := IsBoundGlobal("UniversalCoefficientsTheorem");;
if not _q6_uct_loaded then
    _q6_self := INPUT_FILENAME();;
    if _q6_self <> fail and _q6_self <> "stream" then
        _q6_dir := _q6_self{[1..Length(_q6_self) -
                            Length("/quillen_h3_u1.g")]};;
        for _q6_p in [ "/../../src/modular_data.g",
                       "/../../../src/modular_data.g",
                       "/../../DRINFELD/src/modular_data.g" ] do
            if not _q6_uct_loaded then
                _q6_cand := Concatenation(_q6_dir, _q6_p);;
                if IsExistingFile(_q6_cand) then
                    Read(_q6_cand);
                    _q6_uct_loaded := true;
                fi;
            fi;
        od;
    fi;
    if not _q6_uct_loaded then
        for _q6_p in [ "../../src/modular_data.g",
                       "../../../src/modular_data.g",
                       "src/modular_data.g",
                       "DRINFELD/src/modular_data.g" ] do
            if not _q6_uct_loaded and IsExistingFile(_q6_p) then
                Read(_q6_p);
                _q6_uct_loaded := true;
            fi;
        od;
    fi;
    if not _q6_uct_loaded then
        Error("quillen_h3_u1.g: cannot locate src/modular_data.g; ",
              "UniversalCoefficientsTheorem not available.");
    fi;
fi;

# ---------------------------------------------------------------------
# UnitCircleCohomology(G, n)
#
# Returns a record with:
#   .G          -- the group
#   .n          -- the cohomological degree (in U(1) semantics)
#   .R          -- ResolutionFiniteGroup(G, n+2)
#   .K          -- TensorWithIntegers(R)
#   .UCT        -- UniversalCoefficientsTheorem(K, n+1)
#   .torsion    -- UCT.torsion (elementary divisors of H^{n+1}(G; Z)_tors)
#   .exponent   -- UCT.exponent (lcm of torsion = "m" in the convention)
#   .StandardCocycle(hom_vec)
#                -- builds the standard cocycle from a hombasis-aligned
#                   integer vector by lifting through UCT.lift and
#                   calling HAP's StandardCocycle on R at degree n+1.
# ---------------------------------------------------------------------
UnitCircleCohomology := function(G, n)
    local R, K, UCT;

    if not IsGroup(G) then
        Error("UnitCircleCohomology: first arg must be a group");
    fi;
    if not (IsInt(n) and n >= 1) then
        Error("UnitCircleCohomology: n must be a positive integer");
    fi;
    if n <> 3 then
        Error(Concatenation(
            "UnitCircleCohomology: only n = 3 is currently supported ",
            "(the upstream UCT in src/modular_data.g hardcodes ",
            "K!.dimension(3) on line 80; calling at other degrees ",
            "would silently use the wrong K_n). Got n = ", String(n)));
    fi;

    # Codebase convention: the Gruen helper `UniversalCoefficientsTheorem(K, n)`
    # returns the UCT data for H^{n+1}(G; Z), i.e. H^n(G; U(1)).  So at
    # n = 3 we build the depth-4 resolution and call the helper at degree 3.
    # This matches `transgression_kernel.g::SetupCohomology3` byte-for-byte.
    R := ResolutionFiniteGroup(G, n + 1);
    K := TensorWithIntegers(R);
    UCT := UniversalCoefficientsTheorem(K, n);

    return rec(
        G          := G,
        n          := n,
        R          := R,
        K          := K,
        UCT        := UCT,
        torsion    := UCT.torsion,
        exponent   := UCT.exponent,
        StandardCocycle := function(hom_vec)
            return StandardCocycle(R,
                                   UCT.lift * hom_vec,
                                   n,
                                   UCT.exponent);
        end
    );
end;;
