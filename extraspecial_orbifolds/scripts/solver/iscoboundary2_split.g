# iscoboundary2_split.g — public dispatcher for the torsion-split solver.
#
# Routes (vec, [g]) queries to the order-exp generator path (Z/exp fallback)
# or the order-2 generators path (mod-2 + Bockstein-image lift), based on
# whether vec touches the unique order-exp generator.
#
# Naming note from the rework spec:
#   * "Path A" — the GF(2) + Bockstein fast path (order-2 generators).
#     Implemented by IsCoboundary2Mod2WithLift.
#   * "Path Z" / "Path B" — the Z/exp fallback (order-exp generator).
#     Implemented by IsCoboundary2Zexp.
#
# Deviation from the original plan draft:
#   The original draft test for the order-exp generator was
#       vec[exp_index] mod (setup.exponent / setup.torsion[exp_index]) <> 0
#   which is degenerate when torsion[exp_index] = exponent (the canonical case
#   where the order-exp generator has order exactly equal to the exponent):
#   the divisor reduces to 1 and `mod 1` is always 0, so the Path-Z branch
#   would never be taken. Replaced with the simpler and mathematically
#   correct test
#       vec[exp_index] <> 0
#   i.e. "the order-exp coordinate is non-zero in Z/exponent".
#
# Read paths: this file is intended to be Read either directly from solver/
# or from solver/tests/. Both companion files (mod2_solver.g, z4_fallback.g)
# live next to this file, so we locate them by walking up from CWD until
# we find iscoboundary2_split.g — same shim pattern as z4_fallback.g.
ic2split_orig_dir := DirectoryCurrent();;
ic2split_target := fail;;
for ic2split_try in [".", "..", "../.."] do
    if IsExistingFile(Concatenation(ic2split_try, "/iscoboundary2_split.g")) then
        ic2split_target := ic2split_try;
        break;
    fi;
od;;
if ic2split_target = fail then
    Error("iscoboundary2_split.g: cannot locate companion files from CWD ",
          Filename(ic2split_orig_dir, ""));
fi;
ChangeDirectoryCurrent(ic2split_target);;
Read("mod2_solver.g");
Read("z4_fallback.g");
Read("iterated_bockstein.g");
ChangeDirectoryCurrent(Filename(ic2split_orig_dir, ""));;

IsCoboundary2Split := function(C, c_g, vec, setup)
    local i, exp_index, r, c_prime, k;
    # Find the index of the order-exp generator (if any). Position returns
    # the FIRST match; in the canonical case there is exactly one entry of
    # setup.torsion equal to setup.exponent, so this is unambiguous.
    exp_index := Position(setup.torsion, setup.exponent);

    # Path Z: vec touches the order-exp generator (non-zero coordinate).
    # When setup.exponent is a power of 2, route to the fast iterated
    # Bockstein solver (IsCoboundary2Z2k); otherwise fall back to the slow
    # Z/exp baseline (IsCoboundary2Zexp). The power-of-2 case covers the
    # canonical extraspecial-orbifold setting.
    if exp_index <> fail and vec[exp_index] <> 0 then
        k := LogInt(setup.exponent, 2);
        if 2^k = setup.exponent then
            return IsCoboundary2Z2k(C, c_g, k);
        else
            return IsCoboundary2Zexp(C, c_g, setup.exponent);
        fi;
    fi;

    # Path A: all non-zero coordinates are at order-2 generators.
    # Sanity-check: the rework only handles torsion shapes where every
    # sub-exponent generator has order 2.
    for i in [1..Length(vec)] do
        if vec[i] <> 0
           and setup.torsion[i] <> 2
           and setup.torsion[i] <> setup.exponent then
            Error("Mixed sub-exp torsion not yet supported (see spec §5 out-of-scope note)");
        fi;
    od;

    # Reduce c_g mod 2 after dividing out r = exponent / 2. Premise P1
    # (2-divisibility) requires c_g(h, k) to be a multiple of r; if it isn't,
    # the input wasn't a valid order-2-generator-only cochain.
    r := setup.exponent / 2;
    c_prime := function(h, k)
        local v;
        v := c_g(h, k) mod setup.exponent;
        if v mod r <> 0 then
            Error("c_g not r-divisible — premise P1 violated; see #61");
        fi;
        return (v / r) mod 2;
    end;
    return IsCoboundary2Mod2WithLift(C, c_prime);
end;;

# IsCoboundary2SplitVec(C, c_g_vec, vec, setup) — fast vectorised variant.
#
# Same as IsCoboundary2Split but takes c_g as a precomputed length-n²
# integer vector (indexed by (i-1)*n + j where elts := AsList(C)). Used by
# the A-5b sweep where the cocycle table is already in vector form from
# `basis_cache.table * vec_target`.
#
# For Path Z (order-exp generator non-zero) we route through the
# Vec API (IsCoboundary2Z2kVec / IsCoboundary2ZexpVec) to skip the
# n² closure dispatch. Issue #371: the legacy function API rebuilt
# c_table inside IsCoboundary2Z2k by calling a closure n² times, each
# call doing 2 dict lookups that returned an index we already knew.
# At m=5 this c_table build was ~5 s per call across ~1000 fail-column
# calls — the new dominant cost after PRs #368 + #370 cleared the
# prior bottlenecks. Issue #372 (F5) extends the Vec-API to the
# IsCoboundary2Zexp branch as well.
#
# For Path A (the bulk of A-5b's work) we go straight to the Vec API.
IsCoboundary2SplitVec := function(C, c_g_vec, vec, setup)
    local i, exp_index, r, k, c_prime_vec;
    exp_index := Position(setup.torsion, setup.exponent);

    if exp_index <> fail and vec[exp_index] <> 0 then
        k := LogInt(setup.exponent, 2);
        if 2^k = setup.exponent then
            # Issue #371: Vec API — c_g_vec is already in (i-1)*n+j
            # layout matching AsList(C) order (caller constructed it
            # via cache.table * vec_target_exp where cache uses the
            # same AsList(C) ordering).
            return IsCoboundary2Z2kVec(C, c_g_vec, k);
        else
            # Z/exp fallback path (non-power-of-2 exponent). Vec API
            # via #372 (F5). Not on the m ∈ {2, 3, 5, 7} hot path
            # (exp ∈ {2, 4} always hits the Z2k branch above) but
            # consistent with the rest of the Vec-API surface.
            return IsCoboundary2ZexpVec(C, c_g_vec, setup.exponent);
        fi;
    fi;

    for i in [1..Length(vec)] do
        if vec[i] <> 0
           and setup.torsion[i] <> 2
           and setup.torsion[i] <> setup.exponent then
            Error("Mixed sub-exp torsion not yet supported (see spec §5 out-of-scope note)");
        fi;
    od;

    r := setup.exponent / 2;
    # Vectorised c' = (c_g mod exponent) / r mod 2. We also need to check
    # P1 (2-divisibility) — verify on the first non-zero entry only since
    # this is a sweep hot path; the function-API version checks every cell.
    c_prime_vec := List(c_g_vec, x -> (((x mod setup.exponent) / r) mod 2));
    return IsCoboundary2Mod2WithLiftVec(C, c_prime_vec);
end;;
