# Q-int A4 Route C m=5 Quillen polynomials

Per-generator Quillen polynomial-form bridge results for
H^3(E_+(5); U(1)) (G = ExtraspecialGroup(2048, "+"), |G| = 2048),
produced via the Route C (Quillen-detecting-subgroup restriction) bridge
in `extraspecial_orbifolds/scripts/cocyclebasis_quillen_bridge_routec.g`,
using the D-VAN Lagrangian enumerator (`_DETF_AllMaxEAsIn`, issue #287)
to enumerate the maximal elementary-abelian subgroups inside G without
calling `ConjugacyClassesSubgroups` (which OOMs on |G| = 2048).

## Files

  * `route_c_polys.g` — GAP-loadable record `rc_m5_results` with all
    165 per-generator polynomial-form extractions. See file header for
    the schema. Load via:

        Read("route_c_polys.g");
        # rc_m5_results.polys[1].poly_str   -> "x_2^3"
        # rc_m5_results.polys[165].bridge_kind -> "pontryagin_top"

## Sweep parameters

  * G = E_+(5), |G| = 2^{2*5+1} = 2048
  * H^3 generator count k = 165
  * H^3 generator torsion: 164 generators of order 2, one (e_165) of
    order 4. The order-4 generator is the Pontryagin top, which is
    returned with `bridge_kind = "pontryagin_top"` and a placeholder
    `poly_str = "P(generator at order 4)"` — its symbolic polynomial
    form is a Stage B2 follow-up, unchanged at m=5 vs m=2/m=3.
  * Maximal elementary-abelian (EA) subgroup count = 112
    (32 axis-aligned Lagrangians + 80 diagonal pair-swap Lagrangians,
    per the D-VAN enumerator's m >= 4 path; verified at m=5 in #287).

## Wall times

Per the GAP run that produced this file:

  * Setup phase (`SetupCohomology3(EPlusGroup(5))`): 574.4 s (~9.6 min)
  * Cache build + first extraction (e_1): 5248.1 s (~87.5 min)
    — almost all of this is the 112-EA cache build; the per-EA work
    is roughly 47s mean and is dominated by the per-EA Syzygy
    precomputation on a random sample of ~16608 triples from E^3.
  * Sweep of remaining 164 generators: 111.1 s (~1.85 min)
    — mean 0.68 s per generator post-cache.
  * Total wall: ~99 min.

## Cross-validation gaps

There is NO Route A cross-validation at m=5: Route A's
exhaustive |G|^2 coboundary enumeration is infeasible at |G| = 2048
(that's exactly why Route C exists). The Route A == Route C agreement
is established at:

  * m=2: 10/10 MATCH (anchor branch `qint-a4-route-c-with-lagrangian-eas`)
  * m=3: 35/35 MATCH (same branch)

Mathematical equivalence then carries over to m=5 by structural
parallel — Route C uses the same Quillen-restriction injectivity at
all m, and the only m-dependent component (`_DETF_AllMaxEAsIn`) was
audited at m=5 in #287.

## Caveats

  * `poly_coeffs` (the dense F_2 coefficient vector in the cubic
    monomial basis) is not present in `route_c_polys.g` — the original
    PrintTo phase of the sweep driver hit a one-arg `Concatenation`
    bug ("arguments must be lists at list.gi:2088") and crashed mid-
    write. The per-generator results were salvaged from the
    incremental-checkpoint file at `/tmp/qint_a4_rc_m5_incremental.txt`,
    which only had `poly_str` (the canonical Quillen-algebra string
    representation). `poly_str` is the load-bearing form for downstream
    use; the dense vector can be recovered if needed by parsing
    `poly_str` against `QuillenPolynomialBasisForBridge(5).candidates`.

  * The Pontryagin-top generator (e_165, order 4) passes through as
    `bridge_kind = "pontryagin_top"` with a placeholder `poly_str`.
    Its symbolic form remains a Stage B2 follow-up, consistent with
    Route A's behaviour at m=2/m=3.
