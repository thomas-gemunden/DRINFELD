# fsi_wrapper.g
#
# A runnable wrapper around the (broken) FSI plumbing in src/universal_coefficients.g.
# Per V-3 task #47.
#
# This file:
#   (1) Reads src/universal_coefficients.g (which still contains bugs in
#       GaugeInvariants and FSIforAGT, but defines FSIforDoubles and ProjectiveCharacters
#       correctly).
#   (2) Overwrites the broken `ValuesOfPiSymbols` with a fixed implementation.
#   (3) Exposes `FSI(G, omega_vec, g, chi_index, m)` -> rec(nu, FSlist, ...) and
#       `FSIAll(G, omega_vec, g, m_list)` for convenience.
#
# Background bugs in the original `ValuesOfPiSymbols` (universal_coefficients.g lines 312-328):
#   - `factors` is referenced but never declared as a local nor defined globally.
#   - `list2` is used before being initialised (write happens before `list2:=[1]`).
#   - The intent is two passes:
#       list1[m+1] = pi_x(m)  for m in [0..o]   with  pi_x(0)=1,
#                                                pi_x(m) = pi_x(m-1) * E(n)^f(x, x^{m-1}, x)
#       list2[j+1] = pi_x(j)  for j in [0..e]   via  pi_x(j) = pi_x(o)^{j div o} * pi_x(j mod o)
#     where o = Order(x), e = Exponent(G), n = UCT.exponent.
#   - The references `factors[Size(list2)]` should have been `list1[Size(list1)]`, and the two
#     loops were transposed in the source.  See Mignard-Schauenburg
#     (https://arxiv.org/abs/1708.06538) for the underlying definition of pi-symbols.
#
# Per CLAUDE.md the parent file uses globals `i`, `hom` inside UniversalCoefficientsTheorem;
# we accept that (single-load only).
#
# MATHEMATICAL CAVEAT (V-4a, #81) -- RESOLVED 2026-05-15
# ------------------------------------------------------
# The original wrapper produced incorrect results at omega != 0 because
# FSI_LiftIfHom used `UCT.lift * vec` to convert hom-basis coordinates to
# R^3 cocycle vectors. That call has a dimension-mismatch silently
# papered over by GAP's vector-auto-padding, producing an R^3 vector
# that does NOT satisfy the bar 3-cocycle equation -- the same 1105/4096
# violations on Q_8 ω = order-8 that gave V-4a its name. The transgression
# kernel pipeline uses UCT.cocyclebasis correctly (so it was never affected);
# the bug was confined to fsi_wrapper.g. Fix: use UCT.cocyclebasis (see
# FSI_LiftIfHom below). After the fix Q_8 ω = order-8 gives 0/4096
# violations of the bar 3-cocycle equation mod 8.
#
# Historical context (now obsolete):
#
#   - HAP's StandardCocycle(R, omega_vec, 3, n) on R = ResolutionFiniteGroup(Q_8, 4)
#     does NOT satisfy the inhomogeneous bar-resolution 3-cocycle equation
#     delta f(w,x,y,z) = 0 for non-trivial omega (1105 / 4096 violations for the order-8
#     generator of H^3(Q_8)).  HAP's f is a cocycle for HAP's projective resolution but
#     not for the bar resolution that Mignard-Schauenburg's formula `alpha_g(x,y) =
#     f(x,y,g) - f(x,g,y) + f(g,x,y)` assumes.
#   - Consequently `alphag(g)(f)` is NOT a 2-cocycle on C_G(g) (confirmed: 12/64
#     violations for g = f2 in Q_8 with the order-2 omega), and the central-extension
#     construction overshoots |C| * exp.
#
# Fix path (NOT done in this wrapper): replace `StandardCocycle` with a conversion
# from HAP's projective-resolution cocycle to a bar-resolution cocycle via an
# explicit contracting homotopy / chain map.  HAP exposes `EquivariantChainMap`
# from R to the bar resolution; running ω through that map produces a bar cocycle.
# Until that's wired up, only omega = 0 is trustworthy.  See V-4.

# --- load dependencies BEFORE reading the source --------------------------
# universal_coefficients.g uses `IsCcElement` on its very first install line.
# That symbol comes from `hap` (the file's own `LoadPackage("hapco")` is a no-op on
# systems without hapco, because GAP returns `fail` instead of erroring).  So we
# must load `hap` here.  `IO` is also required by `modular_data.g` and is harmless.
LoadPackage("hap");;
LoadPackage("io");;
# Try hapco too, but don't require it.  Without hapco, the lines in
# universal_coefficients.g that depend purely on hapco-specific exports may break;
# in practice only the OneMutable install on line 5 and CcGroup() in
# ProjectiveCharacters are used, both of which are provided by hap.
LoadPackage("hapco", false);;


# --- locate src/universal_coefficients.g -----------------------------------
# We try a list of relative paths plus one absolute fallback.  We do NOT chdir;
# we pass the resolved string straight to Read.  This avoids GAP's mismatch
# between the Directory object and ChangeDirectoryCurrent(string).
fsi_src := fail;;
for fsi_cand in [".", "..", "../..", "../../..", "../../../..",
                 "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-v3"] do
    if IsExistingFile(Concatenation(fsi_cand, "/src/universal_coefficients.g")) then
        fsi_src := Concatenation(fsi_cand, "/src/universal_coefficients.g");
        break;
    fi;
od;;
if fsi_src = fail then
    Error("fsi_wrapper.g: could not locate src/universal_coefficients.g");
fi;
Read(fsi_src);;


# --- fixed ValuesOfPiSymbols ----------------------------------------------
#
# pi_x(m) := \prod_{k=0}^{m-1}  omega(x, x^k, x)   (multiplicative form).
#
# In the source `f(x, y, z)` returns an additive Z/n exponent of the n-th root of unity,
# so omega(...) = E(n)^f(...).  Hence pi_x(m) = E(n)^(\sum_{k=0}^{m-1} f(x, x^k, x)).
#
# Returns a list of length e+1 indexed 1..e+1 with entry [j+1] = pi_x(j).
ValuesOfPiSymbols := function(G, R, K, UCT, x, f)
    local n, e, o, list1, list2, m, j;
    n := UCT!.exponent;
    e := Exponent(G);
    o := Order(x);
    # list1[m+1] = pi_x(m) for m in [0..o]
    list1 := [1];
    for m in [1..o] do
        Add(list1, list1[Size(list1)] * E(n)^f(x, x^(m-1), x));
    od;
    # list2[j+1] = pi_x(j) for j in [0..e]
    list2 := [1];
    for j in [1..e] do
        Add(list2, (list1[o+1]^QuoInt(j, o)) * (list1[RemInt(j, o)+1]));
    od;
    return list2;
end;;


# --- omega_vec sanitisation -----------------------------------------------
# A user can pass either:
#   * a hom-basis coordinate vector of length Length(UCT.hombasis), OR
#   * an already-lifted cocycle vector of length R!.dimension(3).
#
# V-4a (#81) fix: for the hom-basis input, build the cocycle representative
# by linear combination of UCT.cocyclebasis — NOT via UCT.lift. UCT.lift in
# Gruen's UCT helper has shape (R!.dimension(3) × dim-aux) where the aux
# dimension is NOT Length(UCT.hombasis) in general (e.g. for Q_8 it's
# 3 × 2 with hombasis-length 1). Doing `UCT.lift * vec` for a length-1
# hom-vec triggers GAP's silent vector-auto-padding and produces a wrong
# R^3 vector that does NOT satisfy the bar 3-cocycle equation
# (1105/4096 violations on Q_8 with the order-8 generator, mod 8).
#
# Using UCT.cocyclebasis matches the kernel-pipeline convention in
# transgression_kernel.g's StandardCocycleOf and gives a strict bar
# 3-cocycle (0/4096 violations).
FSI_LiftIfHom := function(R, UCT, vec)
    local n, v, i;
    n := UCT!.exponent;
    if Length(vec) = Length(UCT!.hombasis) then
        v := ListWithIdenticalEntries(R!.dimension(3), 0);
        for i in [1..Length(vec)] do
            v := v + vec[i] * UCT!.cocyclebasis[i];
        od;
        return v mod n;
    elif Length(vec) = R!.dimension(3) then
        return vec mod n;
    else
        Error("FSI_LiftIfHom: vec has length ", Length(vec),
              "; expected ", Length(UCT!.hombasis), " (hom) or ",
              R!.dimension(3), " (cocycle)");
    fi;
end;;


# --- core context builder --------------------------------------------------
#
# Build everything that FSIforDoubles needs for a fixed (G, omega).
# Returned record fields:
#   G, R, K, UCT, omega_vec (cocycle-vector form), f (StandardCocycle),
#   listG (a fixed Enumerator), exp (= UCT.exponent), groupExp (= Exponent(G)),
#   ResolutionFiniteGroup_arity (4).
FSIContext := function(G, omega_vec_or_hom)
    local R, K, UCT, omega_vec, f;
    R := ResolutionFiniteGroup(G, 4);
    K := TensorWithIntegers(R);
    UCT := UniversalCoefficientsTheorem(K, 3);
    omega_vec := FSI_LiftIfHom(R, UCT, omega_vec_or_hom);
    f := StandardCocycle(R, omega_vec, 3, UCT!.exponent);
    return rec(
        G := G,
        R := R,
        K := K,
        UCT := UCT,
        omega_vec := omega_vec,
        f := f,
        listG := Enumerator(G),
        exp := UCT!.exponent,
        groupExp := Exponent(G)
    );
end;;


# --- pivalues table --------------------------------------------------------
#
# P-3 (#112): the pi-values depend only on the context (G, omega), NOT
# on the class g being tested. The original `FSIAllAtClass` rebuilt
# this table on every call -- a length-|G| iteration through
# ValuesOfPiSymbols per class. Cache it on the context.
FSIPiValues := function(ctx)
    if not IsBound(ctx.pi_values_cache) then
        ctx.pi_values_cache := List(ctx.listG, x ->
            ValuesOfPiSymbols(ctx.G, ctx.R, ctx.K, ctx.UCT, x, ctx.f));
    fi;
    return ctx.pi_values_cache;
end;;


# --- projective character table at the centraliser of g -------------------
# Note: ProjectiveCharacters uses the convention that the 2-cocycle alpha on
# C_G(g) is "alpha_g(omega)(x, y) = omega(x, y, g) - omega(x, y g y^{-1}, y) +
# omega(x y g y^{-1} x^{-1}, x, y)" (see `alphag` in src/universal_coefficients.g).
#
# IMPORTANT: The original ProjectiveCharacters in src/universal_coefficients.g
# relies on the `hapco` package for `UnderlyingGroup(CcGroup(...))` and
# `Ga!.Fibre`.  On systems without hapco we provide a drop-in replacement
# `ProjectiveCharactersDirect` below that builds the central extension as a
# concrete permutation group and returns a record with the same shape:
#   rec(Gaa, lift, table)
# where:
#   Gaa     - a concrete permutation group isomorphic to the central extension
#             G_alpha of G by Z/o,
#   lift    - a function from G to Gaa that picks a (fixed) section,
#   table   - the list of projective characters of G (= those characters chi of
#             Gaa for which chi(t) / chi(1) = E(o), where t is the generator of
#             the central kernel Z/o).

# Build the central extension G_alpha as a concrete permutation group, plus
# the lift map.  alpha : G x G -> Z/o is encoded as alpha(x, y) returning
# an integer in {0, ..., o-1} (i.e. an additive Z/o exponent).
BuildCentralExtension := function(G, alpha, o)
    local elemsG, baseSize, n, t_perm, b_perms, b, b_img, i, gen, idx,
          embed, fibreElem, lift, Gaa, fibreGen;
    elemsG := Elements(G);
    baseSize := Size(G);
    n := baseSize * o;  # |G_alpha|
    # Encode the central extension on the set [1..n] = {(g, a) : g in G, a in Z/o},
    # with index (g_index - 1) * o + (a + 1).
    #
    # The action of multiplying by the central generator (1, 1) (additively a=1):
    #   (g, a) |-> (g, a+1)
    # represented as a permutation t_perm of [1..n].
    embed := function(gIdx, a)
        return (gIdx - 1) * o + (a mod o) + 1;
    end;
    t_perm := PermList(List([1..n], function(k)
        local gIdx, a;
        a := ((k - 1) mod o);
        gIdx := QuoInt(k - 1, o) + 1;
        return embed(gIdx, a + 1);
    end));
    # For each generator b of G (we use the full element list for simplicity,
    # but only need generators), the action of multiplying on the *right* by (b, 0):
    #   (g, a) |-> (g*b, a + alpha(g, b))
    b_perms := [];
    for b in GeneratorsOfGroup(G) do
        b_img := List([1..n], function(k)
            local gIdx, a, g, gb, gbIdx, exp;
            a := (k - 1) mod o;
            gIdx := QuoInt(k - 1, o) + 1;
            g := elemsG[gIdx];
            gb := g * b;
            gbIdx := Position(elemsG, gb);
            exp := alpha(g, b);
            return embed(gbIdx, a + exp);
        end);
        Add(b_perms, PermList(b_img));
    od;
    Gaa := Group(Concatenation([t_perm], b_perms));
    # Build the lift function g |-> permutation acting like (g, 0).
    lift := function(g)
        local img;
        img := List([1..n], function(k)
            local gIdx, a, g0, gg, ggIdx, exp;
            a := (k - 1) mod o;
            gIdx := QuoInt(k - 1, o) + 1;
            g0 := elemsG[gIdx];
            gg := g0 * g;
            ggIdx := Position(elemsG, gg);
            exp := alpha(g0, g);
            return embed(ggIdx, a + exp);
        end);
        return PermList(img);
    end;
    fibreGen := t_perm;  # the order-o central generator
    return rec(
        Gaa := Gaa,
        lift := lift,
        fibreGen := fibreGen,
        Base := G,
        FibreOrder := o,
        ExtensionSize := n
    );
end;;

ProjectiveCharactersDirect := function(G, alpha, o)
    local ext, ire, testpro;
    ext := BuildCentralExtension(G, alpha, o);
    ire := Irr(ext.Gaa);
    # A character chi of Gaa restricts to a *projective* character of G iff
    # chi(t) = E(o) * chi(1), where t is the central generator.
    testpro := function(charlist)
        local out, chi, target;
        out := [];
        for chi in charlist do
            target := E(o) * (One(ext.Gaa)^chi);
            if (ext.fibreGen)^chi = target then
                Add(out, chi);
            fi;
        od;
        return out;
    end;
    return rec(
        Gaa := ext.Gaa,
        lift := ext.lift,
        table := testpro(ire),
        fibreGen := ext.fibreGen,
        FibreOrder := o,
        Base := G
    );
end;;


# Pick the working implementation.  We always use the direct one to avoid hapco.
FSIProjAt := function(ctx, g)
    local C, alpha;
    C := Centralizer(ctx.G, g);
    alpha := alphag(g)(ctx.f);
    return ProjectiveCharactersDirect(C, alpha, ctx.exp);
end;;


# --- main user-facing call -------------------------------------------------
#
# FSI(ctx, g, chi_index, m)
#   ctx       : as returned by FSIContext
#   g         : a class representative (element of ctx.G)
#   chi_index : 1-based index into proj.table at the centraliser of g
#   m         : the FS power (m=2 = classical Frobenius-Schur)
#
# Returns nu_m(chi_{chi_index} at class g) as a cyclotomic.
FSI := function(ctx, g, chi_index, m)
    local proj, pivalues;
    proj := FSIProjAt(ctx, g);
    pivalues := FSIPiValues(ctx);
    return FSIforDoubles(ctx.G, ctx.f, g, proj, chi_index, ctx.exp,
                         ctx.listG, pivalues, m);
end;;


# --- batch helper: compute nu_m for all chi at a single class -------------
#
# FSIAllAtClass(ctx, g, m) -> list of nu_m values, one per chi in proj.table
FSIAllAtClass := function(ctx, g, m)
    local proj, pivalues, nvals, i;
    proj := FSIProjAt(ctx, g);
    pivalues := FSIPiValues(ctx);
    nvals := [];
    for i in [1..Size(proj!.table)] do
        Add(nvals, FSIforDoubles(ctx.G, ctx.f, g, proj, i, ctx.exp,
                                 ctx.listG, pivalues, m));
    od;
    return rec(proj := proj, nu := nvals);
end;;


Print("Finished loading fsi_wrapper.g\n");
Print("  - ValuesOfPiSymbols: overridden with fixed version\n");
Print("  - Entry points: FSIContext, FSI, FSIAllAtClass, FSIPiValues, FSIProjAt\n");
