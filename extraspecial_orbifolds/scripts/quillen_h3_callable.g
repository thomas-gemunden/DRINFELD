# quillen_h3_callable.g — Q-7 / issue #27.
#
# Public API:
#
#     StandardCocycleQuillen(class_alg)
#         For each H^3 generator (one per UCT hombasis row) build a
#         callable function (g1, g2, g3) -> Z/m_i that evaluates the
#         corresponding 3-cocycle alpha_i in H^3(G; U(1)). Returns a
#         record:
#             rec(
#                 G          := <group>,
#                 setup      := <UnitCircleCohomology(G, 3) result>,
#                 torsion    := <list of generator orders>,
#                 exponent   := <lcm of torsion>,
#                 callables  := <list of 3-arg cocycle functions>,
#                 moduli     := <list of moduli, one per callable
#                                — moduli[i] = setup.exponent always,
#                                because HAP returns cocycles with
#                                values in Z/exponent; the "true" order
#                                of the class is setup.torsion[i]>,
#                 prefer_quillen := <bool>, # always false in Path A
#                 path           := "A"     # Path A = HAP-bar wrapper
#             )
#
# This is Path A in the Q-7 plan: a thin wrapper around the existing
# `UnitCircleCohomology(G, 3)` setup from quillen_h3_u1.g (Q-6) and
# HAP's `StandardCocycle`. Acceptance for Q-7 is satisfied trivially:
#
#   1. Cocycle condition: HAP's StandardCocycle returns a true bar
#      3-cocycle by construction (verified empirically in V-4a, see
#      standard_bar_cocycle.g comments).
#   2. m=2 HAP agreement: trivial, because Path A IS the HAP path.
#   3. Performance at m=7 (E_+(7), 32768 elements): gated; see the
#      test file.
#
# Path B (Quillen-derived cocycle from class_alg's polynomial expression
# via Q-3 cup product and Q-4 Bockstein) is a substantial follow-up; it
# would be selected by setting Q7_USE_PATH_B := true before loading this
# file. Path B is NOT implemented here.
#
# Note: `class_alg` is the record returned by `QuillenPresentation(m)`
# (workstream Q-2, see quillen_presentation.g). The only field we
# consume is `class_alg.group_id` (a length-2 SmallGroup ID). All other
# fields of class_alg — `.path`, `.m`, `.sym_gens`, etc. — are ignored
# in Path A; they would be used in Path B to decode the polynomial
# expression of each H^3 generator and evaluate it via Q-9's detecting-
# subgroup data. We pass `class_alg` through unchanged in the result
# under `.class_alg` so Path-B callers can still find it.

# ---- Load Q-6 (UnitCircleCohomology) lazily ---------------------------
#
# Same INPUT_FILENAME() shim pattern used in quillen_presentation.g.

_q7_loaded_h3u1 := false;;
_q7_self_path := INPUT_FILENAME();;
if _q7_self_path <> fail and _q7_self_path <> "stream" then
    _q7_self_dir := _q7_self_path{[1..Length(_q7_self_path)
                                   - Length("/quillen_h3_callable.g")]};;
    _q7_candidate := Concatenation(_q7_self_dir, "/quillen_h3_u1.g");;
    if IsExistingFile(_q7_candidate) then
        Read(_q7_candidate);
        _q7_loaded_h3u1 := true;
    fi;
fi;
if not _q7_loaded_h3u1 then
    for _q7_p in [ "quillen_h3_u1.g",
                   "extraspecial_orbifolds/scripts/quillen_h3_u1.g",
                   "scripts/quillen_h3_u1.g" ] do
        if not _q7_loaded_h3u1 and IsExistingFile(_q7_p) then
            Read(_q7_p);
            _q7_loaded_h3u1 := true;
        fi;
    od;
fi;
if not _q7_loaded_h3u1 then
    Error("quillen_h3_callable.g: cannot locate quillen_h3_u1.g; ",
          "Read this file from extraspecial_orbifolds/scripts/ or set CWD.");
fi;


# ---- Resolve a `class_alg` record to a SmallGroup ---------------------
#
# `class_alg.group_id` is the canonical pointer (set by
# `QuillenPresentation`). Fall back to constructing the group from
# `.m` (which gives the E_+(m) SmallGroup ID) for resilience.

StandardCocycleQuillenResolveGroup := function(class_alg)
    local id;
    if IsBound(class_alg.group_id) then
        id := class_alg.group_id;
        if not (IsList(id) and Length(id) = 2
                and IsInt(id[1]) and IsInt(id[2])) then
            Error("StandardCocycleQuillen: class_alg.group_id must be a ",
                  "length-2 [n, m] SmallGroup ID; got ", id);
        fi;
        return SmallGroup(id[1], id[2]);
    fi;
    # Fallback: if `class_alg.m` is present and quillen_presentation.g
    # has been loaded (defining the global `QuillenPresentationGroupID`),
    # recover the SmallGroup ID through it. We resolve the name through
    # ValueGlobal so that this file remains parseable even when
    # quillen_presentation.g has not been read.
    if IsBound(class_alg.m) and IsBoundGlobal("QuillenPresentationGroupID") then
        id := ValueGlobal("QuillenPresentationGroupID")(class_alg.m);
        return SmallGroup(id[1], id[2]);
    fi;
    Error("StandardCocycleQuillen: class_alg has no .group_id (and no ",
          ".m we can use to recover one). Cannot resolve the underlying ",
          "group.");
end;;


# ---- Path A: build callables from UCT.hombasis ------------------------
#
# Public entry. Returns a record (see top of file).

StandardCocycleQuillen := function(class_alg)
    local G, setup, callables, i, hom_i, omega_i, moduli;

    if not IsRecord(class_alg) then
        Error("StandardCocycleQuillen: expected a record (class_alg); ",
              "got ", class_alg);
    fi;

    G     := StandardCocycleQuillenResolveGroup(class_alg);
    setup := UnitCircleCohomology(G, 3);

    # One callable per UCT.hombasis row. Each row is a vector in
    # Z^|cyclebasis| representing a generator of H^3(G; U(1)). The
    # callable returns omega(g1, g2, g3) in Z / setup.exponent.
    #
    # setup.StandardCocycle(h) returns a fully self-contained closure
    # — internally HAP's `StandardCocycle` builds and freezes a
    # cocycle table at construction time and the returned function
    # just looks values up in it. No iteration-variable aliasing risk.
    callables := [];
    moduli    := [];
    for i in [1..Length(setup.UCT.hombasis)] do
        hom_i   := setup.UCT.hombasis[i];
        omega_i := setup.StandardCocycle(hom_i);
        Add(callables, omega_i);
        Add(moduli,    setup.exponent);
    od;

    return rec(
        G              := G,
        setup          := setup,
        torsion        := setup.torsion,
        exponent       := setup.exponent,
        callables      := callables,
        moduli         := moduli,
        prefer_quillen := false,
        path           := "A",
        class_alg      := class_alg
    );
end;;


# ---- Convenience: coboundary of a 3-cochain ---------------------------
#
# For a function f : G x G x G -> Z/m the coboundary is
#
#     (df)(a, b, c, d) := f(b, c, d) - f(a*b, c, d) + f(a, b*c, d)
#                       - f(a, b, c*d) + f(a, b, c)
#
# evaluated mod m. The function is a cocycle iff df is identically zero.
# Provided here as a public diagnostic; callers can use it together with
# `Random(G)` to sample-check the cocycle condition.

CoboundaryOf3Cochain := function(f, a, b, c, d, m)
    local v;
    v :=   f(b, c, d)
         - f(a * b, c, d)
         + f(a, b * c, d)
         - f(a, b, c * d)
         + f(a, b, c);
    if m > 0 then v := v mod m; fi;
    return v;
end;;


Print("Loaded quillen_h3_callable.g (Q-7 Path A: HAP-bar callable for ",
      "H^3 generators).\n");
