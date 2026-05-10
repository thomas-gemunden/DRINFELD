# gauge_invariants_wrapper.g
#
# A runnable wrapper around the (broken) GaugeInvariants function in
# src/universal_coefficients.g.  Per V-4 (#16, task #52).
#
# Background bugs in src/universal_coefficients.g `GaugeInvariants` (lines 392-446):
#   - The local block (lines 392-416) lists `pivalues`, `listG`, etc. but does NOT
#     declare `hombasis`, which is then assigned on line 422 (`hombasis:=UCT!.hombasis`).
#     GAP rejects the function with "Variable 'hombasis' must have a value".
#   - In addition, `pivalues:=List(listG,x->ValuesOfPiSymbols(G,R,K,UCT,x,f))` on
#     line 436 calls into the broken upstream `ValuesOfPiSymbols`, whose own bugs
#     (transposed loops, undeclared `factors`) are fixed by the V-3 wrapper
#     `fsi_wrapper.g`.
#   - `ProjectiveCharacters` (line 435) uses `hapco`, which is optional; the V-3
#     wrapper provides `ProjectiveCharactersDirect` as a hapco-free replacement.
#
# What this wrapper does:
#   (1) Loads fsi_wrapper.g, which in turn loads src/universal_coefficients.g and
#       overrides ValuesOfPiSymbols.  This also gives us FSI, FSIforDoubles,
#       ProjectiveCharactersDirect, AutomorphismOrbits, UniversalCoefficientsTheorem,
#       ExponentOfPFC, Twist, alphag.
#   (2) Defines a fixed `GaugeInvariants` global with the missing locals declared
#       and ProjectiveChactersDirect substituted for ProjectiveCharacters.
#
# Returned record from `GaugeInvariants(G)`:
#   rec(
#     UCT             := UCT,
#     orbits          := list of Aut(G)-orbits on H^3(G; Z/n) hom-vectors,
#     representatives := list of lifted cocycle-vectors (one per orbit),
#     Table           := list, one entry per orbit, of the form
#                          [ cocycle_vector,
#                            FSlist (divisors of ExponentOfPFC, with 0 prepended),
#                            Collected list of [nu values + twist] per (class, chi) ]
#   )
#
# Mathematical caveat (issue #81): HAP's StandardCocycle does NOT satisfy the
# inhomogeneous bar 3-cocycle equation for non-trivial omega on Q_8 (1105 / 4096
# violations for the order-8 generator).  Consequently the central-extension
# downstream (alphag(g)(f) on C_G(g)) is not a 2-cocycle, and Stage 3 results
# for omega != 0 are diagnostic only.  Only omega = 0 is mathematically reliable
# until #81 is fixed.

# --- load the V-3 wrapper (which loads src/universal_coefficients.g) ------
gauge_wrapper := fail;;
for gauge_cand in [".", "..", "../..", "../../..", "../../../..",
                   "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-v4",
                   "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-v3"] do
    if IsExistingFile(Concatenation(gauge_cand, "/extraspecial_orbifolds/scripts/fsi_wrapper.g")) then
        gauge_wrapper := Concatenation(gauge_cand, "/extraspecial_orbifolds/scripts/fsi_wrapper.g");
        break;
    fi;
od;;
if gauge_wrapper = fail then
    Error("gauge_invariants_wrapper.g: could not locate fsi_wrapper.g");
fi;
Read(gauge_wrapper);;


# --- fixed GaugeInvariants ------------------------------------------------
#
# This is the exact body of `GaugeInvariants` from src/universal_coefficients.g
# lines 392-446, with the following changes:
#   1. `hombasis` is added to the local block.
#   2. `ProjectiveCharacters(...)` -> `ProjectiveCharactersDirect(...)` to
#      avoid the optional `hapco` dependency.  The two have the same return
#      shape (rec(Gaa, lift, table)), so downstream code is unchanged.
#   3. We use the fixed `ValuesOfPiSymbols` (already overridden in the V-3
#      wrapper).
#
# Everything else is preserved verbatim from the source.
GaugeInvariants := function(G)
    local R,
          K,
          UCT,
          n,
          hom,
          lift,
          orbits,
          representatives,
          o,
          listG,
          list,
          i,
          j,
          h,
          omega,
          f,
          exp,
          conj,
          PC,
          pivalues,
          FSlist,
          l,
          indicators,
          twist,
          columns,
          hombasis;        # <-- ADDED (V-4 fix)
    R := ResolutionFiniteGroup(G, 4);
    K := TensorWithIntegers(R);
    UCT := UniversalCoefficientsTheorem(K, 3);
    Print("Cohomology done\n\n");
    n := UCT!.exponent;
    hombasis := UCT!.hombasis;
    lift := UCT!.lift;
    orbits := AutomorphismOrbits(G, R, K, UCT);
    representatives := List([1..Size(orbits)], i -> (lift * orbits[i][1]) mod n);
    Print("automorphism orbits done\n\n");
    listG := Enumerator(G);
    list := [];
    for j in [1..Size(representatives)] do
        h := orbits[j][1];
        omega := representatives[j];
        f := StandardCocycle(R, omega, 3, n);
        exp := ExponentOfPFC(G, R, K, UCT, h);
        conj := List(ConjugacyClasses(G), x -> Representative(x));
        PC := List(conj, g -> ProjectiveCharactersDirect(Centralizer(G, g), alphag(g)(f), n));
        pivalues := List(listG, x -> ValuesOfPiSymbols(G, R, K, UCT, x, f));
        FSlist := DivisorsInt(exp);
        l := Size(FSlist);
        FSlist := Concatenation([0], FSlist{[1..l-1]});
        indicators := Concatenation(List([1..Size(PC)], i ->
                          List([1..Size(PC[i]!.table)], j ->
                              List(FSlist, m ->
                                  FSIforDoubles(G, f, conj[i], PC[i], j, n, listG, pivalues, m)))));
        twist := Concatenation(List([1..Size(PC)], i ->
                     List([1..Size(PC[i]!.table)], j ->
                         Twist(conj[i], Centralizer(G, conj[i]), PC[i]!.lift, PC[i]!.table[j]))));
        SortParallel(indicators, twist);
        columns := Size(FSlist);
        Add(list, [representatives[j], FSlist,
                   Collected(List([1..Size(indicators)], i ->
                       Concatenation(List([1..columns], j -> indicators[i][j]), [twist[i]])))]);
        Print(String(representatives[j]), " done\n\n");
    od;
    return rec(UCT := UCT, orbits := orbits, representatives := representatives, Table := list);
end;;


# --- convenience: per-orbit / per-class helper (no SortParallel collapse) -
#
# `GaugeInvariants` aggregates into Collected lists, which makes it hard to
# cross-check against per-(class, chi) FSI values.  The helper below builds
# the same `indicators` / `twist` tables but returns them un-sorted and not
# Collected, indexed by (class_index, chi_index).
#
# Returns:
#   rec(
#     omega_vec   = cocycle vector,
#     FSlist      = list of m values (0 prepended to divisors of ExponentOfPFC),
#     classes     = list of class representatives,
#     PC          = list of ProjectiveCharactersDirect(C_G(g_i), alpha_{g_i}(f), n),
#     indicators  = list[class_index][chi_index] = list[m_index] of nu_m,
#     twist       = list[class_index][chi_index] = twist value
#   )
GaugeInvariantsRaw := function(G, omega_vec_or_hom)
    local ctx, exp_pfc, FSlist, l, conj, PC, pivalues,
          indicators, twist, n, R, UCT, h, omega, j;
    ctx := FSIContext(G, omega_vec_or_hom);
    R := ctx.R;
    UCT := ctx.UCT;
    n := ctx.exp;
    # If we received a hom-vector, recover it; otherwise we don't know h and
    # call ExponentOfPFC with the lifted cocycle's image back under cyclebasis
    # is the safer convention -- but the source uses h = orbits[j][1] directly,
    # so we accept a hom-vector here.  Detect by length.
    if Length(omega_vec_or_hom) = Length(UCT!.hombasis) then
        h := omega_vec_or_hom;
    elif Length(omega_vec_or_hom) = R!.dimension(3) then
        # Try cyclebasis to project back; if cyclebasis is unavailable we set
        # h := omega_vec mod n, which is wrong-shaped for ExponentOfPFC.
        # In practice tests always pass a hom-vector.
        Error("GaugeInvariantsRaw: please pass a hom-vector (length ",
              Length(UCT!.hombasis), ") not a cocycle vector");
    fi;
    exp_pfc := ExponentOfPFC(G, R, ctx.K, UCT, h);
    FSlist := DivisorsInt(exp_pfc);
    l := Size(FSlist);
    FSlist := Concatenation([0], FSlist{[1..l-1]});
    conj := List(ConjugacyClasses(G), Representative);
    PC := List(conj, g -> ProjectiveCharactersDirect(Centralizer(G, g), alphag(g)(ctx.f), n));
    pivalues := List(ctx.listG, x -> ValuesOfPiSymbols(G, R, ctx.K, UCT, x, ctx.f));
    indicators := List([1..Size(PC)], i ->
                      List([1..Size(PC[i]!.table)], j ->
                          List(FSlist, m ->
                              FSIforDoubles(G, ctx.f, conj[i], PC[i], j, n, ctx.listG, pivalues, m))));
    twist := List([1..Size(PC)], i ->
                 List([1..Size(PC[i]!.table)], j ->
                     Twist(conj[i], Centralizer(G, conj[i]), PC[i]!.lift, PC[i]!.table[j])));
    return rec(
        omega_vec := ctx.omega_vec,
        FSlist := FSlist,
        classes := conj,
        PC := PC,
        indicators := indicators,
        twist := twist,
        ctx := ctx
    );
end;;


Print("Finished loading gauge_invariants_wrapper.g\n");
Print("  - GaugeInvariants: overridden with fixed locals + ProjectiveCharactersDirect\n");
Print("  - GaugeInvariantsRaw(G, hom_vec): per-(class, chi) un-collected helper\n");
