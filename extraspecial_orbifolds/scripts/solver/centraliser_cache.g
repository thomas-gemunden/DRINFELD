# centraliser_cache.g — cache resolutions and Bockstein images by isomorphism type.
#
# For each conjugacy class g of G the transgression-kernel solver needs the
# centraliser C := C_G(g), a free resolution of C, and the image of the
# Bockstein β : H^1(C; F_2) -> H^2(C; F_2). For E_+(3) the 65 classes have
# centralisers of only ~4 isomorphism types, so building these once per
# iso-type and re-using them gives a ≥5× speed-up (T-4 in the design spec).
#
# Cache key: IdGroup(C), serialised via String(...) into a record-field name
# of the form "[ 16, 11 ]" (verified to work as a parenthesised record-field
# in GAP 4.15).
#
# Public globals:
#   CentraliserCache         — record; field per iso-type seen.
#   GetCentraliserData(G, g) — return the (cached) data record for C_G(g).
#                              Record fields:
#                                .C               the centraliser group
#                                .R               ResolutionFiniteGroup(C, 4)
#                                .bockstein_image BocksteinH1ToH2(C)
#                                .h2_basis        UCT setup (stub for Task 11)
#
# NOTE: the cached .C is the centraliser of the FIRST representative seen for
# each iso-type. Subsequent calls return that same C, NOT a fresh centraliser
# isomorphic to it. Callers that need the actual subgroup C_G(g) for the
# specific g (e.g. embedding maps into G) should compute Centralizer(G, g)
# directly; the cache is for invariants that depend only on the iso-type.

LoadPackage("hap");;
Read("../mod2_solver.g");

CentraliserCache := rec();;     # global cache, keyed by String(IdGroup(C)).

ProjectToH2BasisSetup := function(C)
    # Stub — Task 11 (PR1) will define what h2_basis must hold.
    return rec();
end;;

GetCentraliserData := function(G, gRep)
    local C, type_key, cached;
    C := Centralizer(G, gRep);
    type_key := String(IdGroup(C));
    if IsBound(CentraliserCache.(type_key)) then
        return CentraliserCache.(type_key);
    fi;
    cached := rec(
        C := C,
        R := ResolutionFiniteGroup(C, 4),
        bockstein_image := BocksteinH1ToH2(C),
        h2_basis := ProjectToH2BasisSetup(C)
    );
    CentraliserCache.(type_key) := cached;
    return cached;
end;;
