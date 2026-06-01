# hap_lhs_resolution.g — LHS-perturbed HAP resolution of E_+(m).
#
# Issue #238 (Q-int C-2). Parent #137 (Q-int C). Application #166 (m=7
# production), #50 (A-7a Tier-4 transgression driver), and B3-5 m=7
# cross-validation for the D-VAN Phase 2 anchor.
#
# # Why this exists.
#
# `ResolutionFiniteGroup(E_+(7), 4)` OOMs at ~60 GB. The free
# ZE-resolution built by HAP's `freeRes.gi` grows roughly proportional
# to |G|*|G|-style products of cell counts at lower degrees, so at
# |E_+(7)| = 32768 the rank already exceeds memory budget at degree 4.
#
# E_+(m) sits in a *central* extension
#
#     1 ──→ Z/2 ──→ E_+(m) ──→ V ──→ 1
#
# with V = (F_2)^{2m} elementary abelian. We can use HAP's
# `ResolutionFiniteExtension(GensE, GensV, R_V, n)` to build a much
# smaller resolution of E from resolutions of V and (internally) Z/2.
# The output cell count is O(|cells(R_V)| · |cells(R_{Z/2})|), and at
# degree 5 with V = (F_2)^14 we expect a few hundred thousand cells —
# orders of magnitude under 60 GB.
#
# # HAP API surface used.
#
# `ResolutionFiniteExtension` lives in `hap/lib/Perturbations/resFiniteExt.gi`.
# Signature:
#
#     ResolutionFiniteExtension(GensE, GensG, R_G, n [, tietze [, R_N]])
#
# - `GensE` : generators of the full group E.
# - `GensG` : their images under E → G (= E/N). Must define a valid
#             homomorphism via `GroupHomomorphismByImagesNC`.
# - `R_G`   : a HAP resolution of the *quotient* G.
# - `n`     : top degree to build.
# - `tietze`: optional bool flag (default false).
# - `R_N`   : optional resolution of the kernel N. **Caveat**: this only
#             works if `R_N!.group` is the actual kernel `Kernel(E→G)` as
#             a subgroup of E, with HAP's natural `R_N!.elts` matching
#             elements of N as elements of E. The safe path is to
#             *omit* this argument and let HAP build it via
#             `ResolutionGenericGroup(N, n)` from the internally-
#             computed kernel.
#
# Under the hood it computes the kernel N := Kernel(E→G) inside E,
# picks generators of N, builds (if not provided) R_N, and then runs
# `TwistedTensorProduct(R_G, R_N, EhomG, GmapE, NhomE, NEhomN, ...)`
# to assemble R_E.
#
# # Choice of generators for E_+(m).
#
# `ExtraspecialGroup(2^{2m+1}, "+")` returns a pc-group with generators
# `[f_1, ..., f_{2m+1}]` all of order 2. Empirically (verified for
# m ∈ {1..7}) the *last* generator `f_{2m+1}` is the central element z,
# and the first 2m generators map to the standard basis of
# V = E/Z = (F_2)^{2m}. We pass `GensE := [f_1, ..., f_{2m}]` and
# `GensV := [v_1, ..., v_{2m}]` where `v_i := nat(f_i)`.
#
# # Verification (matched on the LHS probe).
#
# At m=2, cells of LHS resolution at degrees 0..5 are [1, 5, 15, 35, 70,
# 126]. Direct ResolutionFiniteGroup gives [1, 4, 9, 16, 23, 31] — much
# smaller, since LHS is *not* the minimal resolution at small m. But
# cohomology agrees on classes:
#
#     H^2(E_+(2);Z) = (Z/2)^4          (both routes)
#     H^3(E_+(2);Z) = (Z/2)^5          (both routes)
#     H^4(E_+(2);Z) = (Z/2)^9 ⊕ Z/8   (both routes)
#
# At larger m the picture inverts: LHS cells stay polynomial in m via
# R_V's elementary-abelian compactness, while direct cells balloon with
# |G| = 2^{2m+1}.
#
# Empirical timings (Mac M2 Max, GAP 4.15.1, HAP 1.70, abelian builder
# for R_V; commit q-int-c2-lhs-resolution):
#
#   m=2, R_E n=5: ~0.05 s build, H^2..H^4 in ms
#   m=3, R_E n=5: ~0.7  s build, H^2..H^4 in ms..s
#   m=4, R_E n=5: ~6    s build, H^4 in <1 s
#   m=7, R_E n=4: ~63   s build, H^3 in 2.4 s, heap ~130 MB
#   m=7, R_E n=5: ~12 min build (728..822 s observed), H^3 in 2.5 s,
#                 H^4 in 40 s, heap 142 MB after build, 448 MB peak.
#
# So R_E builds are well within memory for m=7 — the 60 GB OOM in #137
# is fully resolved (~73x under the 32 GB target). The dominant runtime
# cost at m=7 is the TwistedTensorProduct boundary assembly (~12 min)
# and the H^4 Smith-normal-form on the 11628 × 3060 boundary matrix
# (~40 s). Both are CPU-bound, not memory-bound.
#
# # Harada-Kono cross-check pattern (informative).
#
# For m ≥ 3 the Harada-Kono / Atiyah-Hirzebruch Z/4 prediction at the
# top of H^4(E_+(m); Z) gives:
#
#     m=3: H^4 = (Z/2)^{34}  ⊕ Z/4    (verified, LHS == direct)
#     m=4: H^4 = (Z/2)^{83}  ⊕ Z/4    (verified, LHS)
#     m=7: H^4 = (Z/2)^{454} ⊕ Z/4    (verified, LHS — #136 Q-int A2)
#
# The m=3 and m=4 entries are computed by the LHS resolution above and
# agree with both the direct ResolutionFiniteGroup and Harada-Kono. The
# m=7 entry is the central acceptance of issue #238 and is verified by
# the test driver `run_e_plus_7_lhs.g` and (opt-in) by the test suite
# `tests/test_hap_lhs_resolution.g` under EPLUS7_RUN := true.
#
# Note: the issue #238 acceptance criterion refers to "Cohomology(R, 3)
# matching (Z/2)^{454} ⊕ Z/4"; that is the U(1)-coefficient statement.
# Via UCT, H^3(G; U(1)) ≅ H^4(G; Z) for finite G, so the literal HAP
# call to satisfy that acceptance is `Cohomology(HomToIntegers(R_E),
# 4)` — H^4 with integer coefficients. The test file documents and
# implements this mapping explicitly.
#
# # Reading the file.
#
# Loads `hap` (and `io` opportunistically for timing). Defines:
#
#   LHSResolutionEPlus(m, max_n)           main entry — returns R_E
#   LHSResolutionEPlusDetailed(m, max_n)   returns a record with R_E,
#                                          R_V, R_Z2, build time, etc.
#
# Both cache R_V and R_E by (m, max_n) so repeat calls are O(1).

LoadPackage("hap");;

# ---------------------------------------------------------------------
# Local helpers.
# ---------------------------------------------------------------------

# Returns ExtraspecialGroup(2^{2m+1}, "+") — the type-+ extraspecial
# 2-group of plus type. For m = 1 this is D_8; m = 2 → 2^{1+4}_+ (order
# 32); m = 7 → 2^{1+14}_+ (order 32768). Defined locally to avoid
# importing the larger `quillen_detecting_subgroup.g` whose helpers we
# do not need.
_LHSResEPlus_EPlusGroup := function(m)
    return ExtraspecialGroup(2^(2*m + 1), "+");
end;;

# Wall-clock seconds since epoch. Used for build-time annotation.
_LHSResEPlus_Now := function()
    return Float(NanosecondsSinceEpoch()) / 1.0e9;
end;;

# GAP heap (live, in MB) via GasmanStatistics. Returns -1.0 if the
# field layout is unavailable (older GAP versions). Used for memory
# reporting in the m=7 driver.
_LHSResEPlus_HeapMB := function()
    local r, s;
    r := CALL_WITH_CATCH(GasmanStatistics, []);
    if not r[1] then return -1.0; fi;
    s := r[2];
    if IsBound(s.full) and IsBound(s.full.livekb) then
        return Float(s.full.livekb) / 1024.0;
    fi;
    return -1.0;
end;;

# Per-(m, max_n) cache. Each entry is a record:
#   m, max_n, V, GensV, R_V, R_E, R_E_detailed
_LHSResEPlus_cache := [];;

_LHSResEPlus_LookupCache := function(m, max_n)
    local entry;
    for entry in _LHSResEPlus_cache do
        # NOTE: we ignore the builder discriminator here and let the
        # caller in LHSResolutionEPlusDetailed compare R_V_builder
        # against the requested builder before reusing.
        if entry.m = m and entry.max_n >= max_n then
            return entry;
        fi;
    od;
    return fail;
end;;

# ---------------------------------------------------------------------
# Main builder.
# ---------------------------------------------------------------------

# LHSResolutionEPlus(m, max_n)
#
# Returns a HAP resolution of E_+(m) up to degree `max_n`, built via
# `ResolutionFiniteExtension` from the central extension
#
#     1 → Z/2 → E_+(m) → V → 1   with V = (F_2)^{2m}.
#
# Cached by (m, max_n).

LHSResolutionEPlus := function(arg)
    local m, max_n, detailed;
    if Length(arg) < 2 then
        Error("LHSResolutionEPlus(m, max_n[, builder])");
    fi;
    m := arg[1]; max_n := arg[2];
    # NOTE: CallFuncList is a GAP kernel function; the parser warns
    # because it's not declared at parse time on some installations.
    # The reference is correct.
    detailed := CallFuncList(LHSResolutionEPlusDetailed, arg);
    return detailed.R_E;
end;;

# LHSResolutionEPlusDetailed(m, max_n)
#
# Same as LHSResolutionEPlus but returns a record with provenance
# fields and intermediate resolutions:
#
#   .m                  : the parameter m.
#   .max_n              : top degree built.
#   .G                  : E_+(m) = ExtraspecialGroup(2^{2m+1}, "+").
#   .V                  : (F_2)^{2m} = E/Z.
#   .GensE_used         : the 2m non-central generators of E used.
#   .GensV_used         : their images in V.
#   .R_V                : HAP resolution of V.
#   .R_E                : LHS resolution of E.
#   .R_V_builder        : "abelian" (default) or "finite" — which
#                         HAP function was used to build R_V.
#   .build_time_V       : wall-clock seconds spent building R_V.
#   .build_time_LHS     : wall-clock seconds spent in
#                         ResolutionFiniteExtension(...).
#   .heap_after_V_mb    : heap MB after R_V built.
#   .heap_after_LHS_mb  : heap MB after R_E built.
#
# # Optional argument: R_V_builder.
#
# `LHSResolutionEPlusDetailed(m, max_n)` accepts an OPTIONAL third
# argument `R_V_builder` ∈ {"abelian", "finite"} controlling which HAP
# function builds R_V (default "abelian"):
#
#   - "abelian" — `ResolutionAbelianGroup(V, max_n)`, the default.
#     Empirically ~300x faster than "finite" for elementary abelian V
#     and produces the same cell dimensions. Used because at m=7 the
#     "finite" route is impractical (>1 minute at m=4).
#
#   - "finite"  — `ResolutionFiniteGroup(V, max_n)`. Slower but
#     non-lazy; useful for cross-checks at small m and as a fallback
#     if a downstream consumer assumes a non-lazy `R_V!.boundary`.

LHSResolutionEPlusDetailed := function(arg)
    local m, max_n, builder, cached, G, gens, GensE, Zc, nat, V, GensV,
          t0, R_V, R_E, build_V, build_LHS,
          heap_after_V, heap_after_LHS, entry;

    if Length(arg) < 2 then
        Error("LHSResolutionEPlusDetailed(m, max_n[, builder])");
    fi;
    m := arg[1];
    max_n := arg[2];
    if Length(arg) >= 3 then
        builder := arg[3];
    else
        builder := "abelian";
    fi;
    if not builder in ["abelian", "finite"] then
        Error("LHSResolutionEPlusDetailed: builder must be \"abelian\" ",
              "or \"finite\", got: ", builder);
    fi;

    cached := _LHSResEPlus_LookupCache(m, max_n);
    if cached <> fail and cached.R_E_detailed.R_V_builder = builder then
        return cached.R_E_detailed;
    fi;

    Print("[LHSResolutionEPlus] m = ", m, ", max_n = ", max_n,
          ", builder = ", builder, "\n");

    G := _LHSResEPlus_EPlusGroup(m);
    gens := GeneratorsOfGroup(G);

    if Length(gens) <> 2*m + 1 then
        Error("LHSResolutionEPlus: unexpected #generators ",
              Length(gens), " for E_+(", m, "); expected ", 2*m + 1);
    fi;

    GensE := gens{[1..2*m]};
    Zc := Centre(G);

    # Sanity: the last generator must be the centre. This is a property
    # of ExtraspecialGroup's pc-presentation that we rely on. Fail loud
    # if a future GAP smallgrp version changes the convention.
    if not gens[2*m + 1] in Zc then
        Error("LHSResolutionEPlus: gens[", 2*m + 1,
              "] is not central; pc-presentation convention changed");
    fi;
    if Order(Zc) <> 2 then
        Error("LHSResolutionEPlus: |Z(E_+(", m, "))| = ", Order(Zc),
              ", expected 2");
    fi;

    nat := NaturalHomomorphismByNormalSubgroup(G, Zc);
    V := Image(nat);
    GensV := List(GensE, g -> Image(nat, g));

    # Optional defensive check: V is elementary abelian of order 2^{2m}.
    if not IsElementaryAbelian(V) or Order(V) <> 2^(2*m) then
        Error("LHSResolutionEPlus: V = E_+(", m, ")/Z is not (F_2)^{",
              2*m, "}: got ", StructureDescription(V));
    fi;

    Print("[LHSResolutionEPlus]   |E| = ", Order(G), ", |V| = ",
          Order(V), ", |Z| = ", Order(Zc), "\n");

    if builder = "abelian" then
        Print("[LHSResolutionEPlus]   building R_V := ",
              "ResolutionAbelianGroup(V, ", max_n, ")\n");
        t0 := _LHSResEPlus_Now();
        R_V := ResolutionAbelianGroup(V, max_n);
        build_V := _LHSResEPlus_Now() - t0;
    else
        Print("[LHSResolutionEPlus]   building R_V := ",
              "ResolutionFiniteGroup(V, ", max_n, ")\n");
        t0 := _LHSResEPlus_Now();
        R_V := ResolutionFiniteGroup(V, max_n);
        build_V := _LHSResEPlus_Now() - t0;
    fi;
    heap_after_V := _LHSResEPlus_HeapMB();
    Print("[LHSResolutionEPlus]   R_V built in ", build_V,
          " s (heap = ", heap_after_V, " MB)\n");
    Print("[LHSResolutionEPlus]   R_V!.dimension(0..", max_n, ") = ",
          List([0..max_n], d -> R_V!.dimension(d)), "\n");

    Print("[LHSResolutionEPlus]   building R_E via ",
          "ResolutionFiniteExtension(GensE, GensV, R_V, ", max_n, ")\n");
    t0 := _LHSResEPlus_Now();
    # Omitting the optional 6th arg (R_N): HAP builds R_N internally via
    # ResolutionGenericGroup(N, n) on the actual kernel subgroup. This
    # is required — supplying our own ResolutionFiniteGroup(CyclicGroup(2))
    # fails because its group is a *new* Z/2, not the kernel of E → V.
    #
    # Note: the GensV elements live in V := Image(nat); HAP's
    # ResolutionFiniteExtension uses R_V!.group as the surjection
    # target. When R_V was built via ResolutionAbelianGroup, that
    # function may return a group object equal (as a set) to V but not
    # identical (a different generated group of the same elements).
    # GroupHomomorphismByImagesNC and the subsequent Position lookups
    # still work because membership is decided element-wise; verified
    # at m ∈ {2, 3} by direct cohomology cross-check.
    R_E := ResolutionFiniteExtension(GensE, GensV, R_V, max_n);
    build_LHS := _LHSResEPlus_Now() - t0;
    heap_after_LHS := _LHSResEPlus_HeapMB();
    Print("[LHSResolutionEPlus]   R_E built in ", build_LHS,
          " s (heap = ", heap_after_LHS, " MB)\n");
    Print("[LHSResolutionEPlus]   R_E!.dimension(0..", max_n, ") = ",
          List([0..max_n], d -> R_E!.dimension(d)), "\n");

    entry := rec(
        m                 := m,
        max_n             := max_n,
        G                 := G,
        V                 := V,
        GensE_used        := GensE,
        GensV_used        := GensV,
        R_V               := R_V,
        R_E               := R_E,
        R_V_builder       := builder,
        build_time_V      := build_V,
        build_time_LHS    := build_LHS,
        heap_after_V_mb   := heap_after_V,
        heap_after_LHS_mb := heap_after_LHS
    );

    Add(_LHSResEPlus_cache, rec(
        m              := m,
        max_n          := max_n,
        R_E_detailed   := entry
    ));

    return entry;
end;;

if IsBoundGlobal("_LogStamped") then
    _LogStamped("Loaded hap_lhs_resolution.g (LHSResolutionEPlus, ",
                "LHSResolutionEPlusDetailed).");
else
    Print("Loaded hap_lhs_resolution.g (LHSResolutionEPlus, ",
          "LHSResolutionEPlusDetailed).\n");
fi;
