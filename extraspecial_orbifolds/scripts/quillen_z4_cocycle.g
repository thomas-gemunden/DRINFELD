# quillen_z4_cocycle.g — Q-int B3-5 (issue #234).
#
# QuillenZ4Cocycle(m, basis_idx) — materialise the basis_idx-th H^3
# basis cocycle on HAP's compact resolution R = HAP_PontryaginGetResolution
# (em, 5), where em = pc-form of EmGroup(m). The Z/4 unit generator
# of H^3(E_+(m); U(1)) at m >= 3 is the LAST entry (basis_idx = k =
# Length(UCT.torsion)). For m=5 this is index 165 — the single Z/4
# summand in the torsion list [(Z/2)^164, Z/4].
#
# Why is this needed?
#
# The Quillen-route kernel driver `run_e_plus_m_kernel_quillen.g` (issue
# #234) at m=5 needs to test all 165 H^3 generators including the Z/4
# one. For the 164 Z/2 generators a Quillen polynomial-derived cocycle
# (or, in Path A, a HAP-UCT cocycle reduced mod 2) suffices. For the Z/4
# generator there is no F_2-only path; we need a true Z/4 cocycle. The
# B3 chain (issues #170-#172, in main) builds one via Pontryagin-square
# integration on HAP's compact resolution. The helper
# `hap_h3_z4_generator.g` (already in main; see #164 B2-4 m=3 anchor)
# extracts that cocycle directly from UCT.cocyclebasis on R.
#
# This file is a thin facade over `HAP_Z4Generator(em, idx)` that:
#   - resolves m -> em = Image(IsomorphismPcGroup(EmGroup(m))),
#   - calls HAP_Z4Generator on em with the requested basis_idx,
#   - returns a setup-shaped record so callers (the Quillen-route driver
#     and `BuildPerClassCocycleBasis`) can plug it into the same machinery
#     as `SetupCohomology3(em)`.
#
# Independence from A-5b's HAP route:
#   The A-5b HAP-route driver anchors on R_A := ResolutionFiniteGroup(em, 4)
#   (via SetupCohomology3). The B3 chain — and therefore this helper —
#   anchors on R_B := ResolutionFiniteGroup(em, 6) (= HAP_PontryaginGetResolution
#   (em, 5)). The two resolutions produce different bases of H^3 but the
#   same abstract cohomology (UCT.torsion is identical up to ordering).
#   When the kernel computations on R_A and R_B agree, that's an
#   independent cross-validation: a basis-change-invariant property.

if not IsBoundGlobal("HAP_Z4Generator") then
    Read("hap_h3_z4_generator.g");
fi;
if not IsBoundGlobal("EmGroup") then
    Read("em_construction.g");
fi;

# ------------------------------------------------------------------
# QuillenZ4Cocycle(m[, basis_idx][, em_in])
#
# Returns a record:
#   .m            : the input m (positive integer).
#   .basis_idx    : the selected H^3 basis index (default last).
#   .em           : pc-form of EmGroup(m), |em| = 2^(2m+1). If `em_in` is
#                   passed (3-arg form), this is the SAME object as
#                   em_in; otherwise it's a fresh Image(IsomorphismPcGroup
#                   (EmGroup(m))).
#   .R            : HAP_PontryaginGetResolution(em, 5).
#   .K            : TensorWithIntegers(R).
#   .UCT          : UniversalCoefficientsTheorem(K, 3).
#   .exponent     : UCT.exponent.
#   .torsion      : UCT.torsion.
#   .order        : torsion[basis_idx] = the cyclic order of the
#                   selected generator (2 or 4 at m >= 3).
#   .vec          : the cocycle vector on R, length R!.dimension(3),
#                   entries in [0..exponent-1]. By construction
#                   (UCT.cocyclebasis), `vec` mod m_exp represents the
#                   basis_idx-th generator of H^3(em; Z/exponent).
#   .is_cocycle   : true iff δ(vec) ≡ 0 mod exponent on R (defensive check
#                   inside HAP_Z4Generator).
#   .omega        : callable (g1, g2, g3) -> Z/exponent that evaluates
#                   the cocycle via HAP's StandardCocycle(R, vec, 3,
#                   exponent). Same shape as Q-7's
#                   StandardCocycleQuillen returns per generator.
#
# At m >= 3 and basis_idx = Length(torsion), `order = 4` (the Z/4 unit
# generator) per Harada-Kono.
#
# Caching: HAP_Z4Generator caches the (R, K, UCT) triple per group, so
# repeated calls for different basis_idx values on the same em reuse the
# heavy lifting (the ResolutionFiniteGroup + UCT build is the expensive
# step). When `em_in` is supplied, it's keyed in the cache and shared
# with downstream Build/Setup-on-R consumers.
#
# Usage:
#   QuillenZ4Cocycle(m)                  - default last generator, fresh em
#   QuillenZ4Cocycle(m, basis_idx)       - specific basis index, fresh em
#   QuillenZ4Cocycle(m, basis_idx, em_in) - use caller's em (object identity)
# ------------------------------------------------------------------

QuillenZ4Cocycle := function(arg)
    local m, basis_idx, em_in, em_mat, iso_em, em, gen_data, k, omega_fn;

    if Length(arg) < 1 or Length(arg) > 3 then
        Error("QuillenZ4Cocycle: usage QuillenZ4Cocycle(m[, basis_idx[, em_in]])");
    fi;
    m := arg[1];
    if not (IsInt(m) and m >= 1) then
        Error("QuillenZ4Cocycle: m must be a positive integer, got ", m);
    fi;

    # Build pc-form of E_+(m), or use caller-supplied em for object
    # identity with the caller's BRW machinery.
    if Length(arg) >= 3 then
        em_in := arg[3];
        if not IsGroup(em_in) then
            Error("QuillenZ4Cocycle: em_in must be a group; got ", em_in);
        fi;
        if Order(em_in) <> 2^(2*m + 1) then
            Error("QuillenZ4Cocycle: em_in has order ", Order(em_in),
                  "; expected 2^(2m+1) = ", 2^(2*m + 1));
        fi;
        em_mat := fail;    # caller manages
        iso_em := fail;
        em     := em_in;
    else
        em_mat := EmGroup(m);;
        iso_em := IsomorphismPcGroup(em_mat);;
        em     := Image(iso_em);;
    fi;

    # Build / fetch the cached HAP_Z4Generator data on em.
    if Length(arg) >= 2 then
        basis_idx := arg[2];
        if not (IsInt(basis_idx) and basis_idx >= 1) then
            Error("QuillenZ4Cocycle: basis_idx must be a positive integer, ",
                  "got ", basis_idx);
        fi;
        gen_data := HAP_Z4Generator(em, basis_idx);
    else
        # Default: pick the last generator (the Z/4 summand at m >= 3).
        gen_data := HAP_Z4Generator(em);
        basis_idx := gen_data.idx;
    fi;

    k := Length(gen_data.torsion);
    if basis_idx > k then
        Error("QuillenZ4Cocycle: basis_idx = ", basis_idx,
              " > k = ", k, " (number of H^3 generators on R)");
    fi;

    # Build a callable cocycle from the integer vector. HAP's
    # StandardCocycle on a Z/exponent cochain vector produces the
    # group-theoretic 3-cocycle omega : G^3 -> Z/exponent. Same shape
    # as Q-7's StandardCocycleQuillen produces per generator.
    omega_fn := StandardCocycle(gen_data.R, gen_data.vec, 3,
                                 gen_data.exponent);

    return rec(
        m           := m,
        basis_idx   := basis_idx,
        em          := em,
        em_matrix   := em_mat,
        iso_em      := iso_em,
        R           := gen_data.R,
        K           := gen_data.K,
        UCT         := gen_data.UCT,
        exponent    := gen_data.exponent,
        torsion     := gen_data.torsion,
        order       := gen_data.order,
        vec         := gen_data.vec,
        is_cocycle  := gen_data.is_cocycle,
        omega       := omega_fn
    );
end;;

# ------------------------------------------------------------------
# QuillenSetupOnR(m[, em_in])
#
# Returns a setup-shaped record analogous to SetupCohomology3(em) but
# anchored on R = HAP_PontryaginGetResolution(em, 5) (the B3-chain R)
# rather than R_A := ResolutionFiniteGroup(em, 4) (the A-5b R).
#
# When `em_in` is supplied (2-arg form), the setup's `.group` field is
# that same object — important for object-identity consistency with the
# caller's BRW conjugacy machinery (Centralizer(em_in, rep) for rep ∈
# ConjugacyClasses(em_in) requires shared parent group identity).
#
# Fields:
#   .group           : em (pc-form of EmGroup(m); = em_in when supplied)
#   .R               : the B3-chain resolution
#   .K               : TensorWithIntegers(R)
#   .UCT             : UniversalCoefficientsTheorem(K, 3)
#   .torsion         : UCT.torsion
#   .exponent        : UCT.exponent (= lcm of torsion)
#   .num_generators  : Length(UCT.torsion)
#   .num_h3_classes  : Product(UCT.torsion)
#
# This record is byte-for-byte compatible with
# `transgression_kernel.g::SetupCohomology3(em)`'s return value, except
# that the underlying R is the B3-chain R rather than the A-5b R. Drop
# in to `BuildPerClassCocycleBasis(setup, gRep, C)`,
# `H3MatrixOfAutomorphism(setup, phi)`, `StandardCocycleOf(setup, vec)`
# unchanged.
#
# Cache: HAP_Z4Generator already caches the (R, K, UCT) triple keyed by
# group identity. We just wrap that.
# ------------------------------------------------------------------

QuillenSetupOnR := function(arg)
    local m, em_in, em_mat, iso_em, em, gen_data;

    if Length(arg) < 1 or Length(arg) > 2 then
        Error("QuillenSetupOnR: usage QuillenSetupOnR(m[, em_in])");
    fi;
    m := arg[1];
    if not (IsInt(m) and m >= 1) then
        Error("QuillenSetupOnR: m must be a positive integer, got ", m);
    fi;

    if Length(arg) >= 2 then
        em_in := arg[2];
        if not IsGroup(em_in) then
            Error("QuillenSetupOnR: em_in must be a group; got ", em_in);
        fi;
        if Order(em_in) <> 2^(2*m + 1) then
            Error("QuillenSetupOnR: em_in has order ", Order(em_in),
                  "; expected 2^(2m+1) = ", 2^(2*m + 1));
        fi;
        em_mat := fail;
        iso_em := fail;
        em     := em_in;
    else
        em_mat := EmGroup(m);;
        iso_em := IsomorphismPcGroup(em_mat);;
        em     := Image(iso_em);;
    fi;

    # HAP_Z4Generator with idx default (last) populates the cache; we
    # discard the generator-specific fields and return only the setup.
    gen_data := HAP_Z4Generator(em);

    return rec(
        group          := em,
        em_matrix      := em_mat,
        iso_em         := iso_em,
        R              := gen_data.R,
        K              := gen_data.K,
        UCT            := gen_data.UCT,
        torsion        := gen_data.torsion,
        exponent       := gen_data.exponent,
        num_generators := Length(gen_data.torsion),
        num_h3_classes := Product(gen_data.torsion)
    );
end;;

Print("Loaded quillen_z4_cocycle.g (QuillenZ4Cocycle, QuillenSetupOnR).\n");
