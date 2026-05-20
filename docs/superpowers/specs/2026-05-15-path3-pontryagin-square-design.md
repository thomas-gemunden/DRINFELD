# Q-int Stage B2: Cochain-Level Pontryagin Square for the Z/4 Generator of H^3(E_+(m); U(1))

**Issue:** #137 (Q-int C: Low-memory HAP resolution alternative for E_+(7)) — Path 3 (Hybrid HAP + Quillen closed-form cocycles).

**Status:** Spec, post-spike. Implementation deferred.

## Background

Path 1 (depth-3 + manual K_4 adapter) and Path 4 (sparse HAP) are eliminated or
deprioritised. Path 4 was empirically heavier than the regular HAP resolution
(`ResolutionPrimePowerGroupSparse(E_+(5), 4)` blew up to 34 GB without finishing
vs. 1.2 GB / 9 min for the dense variant — see #137 comment "Path 4 empirically
dead"). Path 3 remains the most plausible m=7 unlock.

Path 3's premise: at m ≥ 2 every F_2 cohomology class in H^3(E_+(m); F_2) is a
sum of triple cup products of degree-1 classes (Q-2a, the canonical Quillen
presentation has no degree-≤3 contribution from w). Stage B1 (`bar_cocycle.g`,
PR #135) already implements `Cup1x1x1` for the F_2 cocycle representation. The
remaining piece is the **Z/4 cocycle for the Z/4 generator** of
H^4(G; Z) ≅ H^3(G; U(1)), which Stage B1's pure F_2 toolkit cannot produce.

## Path 3 spike findings (this session)

Ran `docs/superpowers/research/2026-05-15-path3-spike-omega4-m3.g` against
HAP's `StandardCocycleOf(setup, e_{exp_index})` at m=3. Results:

| Observation | Value |
|---|---|
| `setup.exponent` | 4 |
| `setup.torsion` | `[2 × 34, 4]` (35 generators) |
| `exp_index` (Z/4 generator) | 35 |
| Distinct values of ω_4 on 5×5×5 sample of G^3 | `{0, 1, 2, 3}` (all 4) |
| Bar 3-cocycle equation violations on 3⁴=81 sample | 0 |
| F_2 reduction of ω_4 on sample | 38/125 ones, 87/125 zeros — non-trivial |
| Values of 2·ω_4 mod 4 on sample | `{0, 2}` (2-torsion) |

**Critical fact:** ω_4 takes the value `2` mod 4. This is mathematically
significant — it means ω_4 is NOT in the image of `IntegralBockstein` alone
(which only produces values in `{-1, 0, 1}` mod 4 ⊂ `{0, 1, 3}`). The order-4
generator genuinely requires a Pontryagin-square-style construction.

**HAP's internal mechanism** uses its resolution-specific `Syzygy` to compute
ω_4 against `UCT.lift · vec`. This is not portable to a HAP-free pipeline at
m=7 where HAP can't run at all.

## Mathematical formula to implement

At m ≥ 3, Harada-Kono 1987 Theorem 1.1 + standard Pontryagin square theory:

**Theorem (Harada-Kono / Steenrod 1947).** The Z/4 generator of H^4(E_+(m); Z)
at m ≥ 3 equals the Pontryagin square P(Q) under the natural inclusion
H^4(Z) ↪ H^4(Z/4), where Q ∈ H²(G; F_2) is the Quillen quadratic form

Q(g, h) = Σᵢ xᵢ(g) · x_{m+i}(h)   mod 2.

The cochain-level Pontryagin square (Steenrod 1947), normalised for the bar
resolution: given a F_2 2-cocycle α and its set-theoretic lift α̃: G² → {0, 1} ⊂ Z,

```
P(α)(g₁, g₂, g₃, g₄) = α̃(g₁, g₂) · α̃(g₃, g₄)
                       + α̃(g₁, g₂ g₃) · ∪₁(g₂, g₃, g₄)   mod 4,
```

where the Steenrod cup-1 product ∪₁ on bar cochains is the standard
non-symmetric correction (see Steenrod 1947 §6, or Whitehead "Elements of
Homotopy Theory" Ch. III §6). This gives a Z/4-valued 4-cocycle.

**The 3-cocycle.** For the transgression-kernel infrastructure we need a Z/4
3-cocycle f: G^3 → Z/4 with `δf̃ = P(Q)` mod 4 (where f̃: G^3 → Z is a lift).
Equivalently, f is the image of the Z/4 generator under the connecting
homomorphism δ⁻¹: H^4(Z) → H^3(Z/4) coming from 0 → Z →⁴ Z → Z/4 → 0.

Concretely, **integration**: find f̃: G^3 → Z whose coboundary equals P(Q)
times an appropriate scaling. Per linear algebra on the bar complex,
finite-dimensional once G is fixed. For |G| = 128 (m=3) this is tractable; for
|G| = 32768 (m=7) it is a large but bounded computation (|G|³ = 3.5×10¹³
4-cochain values — would require a smarter algorithm than brute solve).

**Alternative formulation (preferred for implementation):** Some references give
a DIRECT Z/4-valued 3-cocycle for the Z/4 generator without going through the
4-cocycle. One candidate from the Cohomology-of-extraspecial literature
(Quillen 1971 / Harada-Kono 1987):

```
f(g₁, g₂, g₃) = α̃(g₁, g₂) · ε(g₃) + β̃(α)(g₁, g₂, g₃)   mod 4
```

for specific α ∈ H²(F_2) and a specific character ε. This is a Pontryagin-
square-relative-degree-1 construction. We did NOT verify this candidate this
session — to be checked next time against HAP's empirical ω_4.

## Acceptance criteria

1. **m=3 anchor:** the constructed Z/4 3-cocycle f equals HAP's
   `StandardCocycleOf(setup, e_{35})` up to a Z/4 3-coboundary at m=3.
   Verification: compute [f − ω_4] in H^3(G; Z/4) and check it's zero. For
   |G|=128 this is direct linear algebra.

2. **m=2 anchor:** at m=2, the cyclic summand is Z/8 (not Z/4 — h(Q)=2 branch
   of H-K Theorem 1.1). The construction extends to Z/8 via P²(α) — possibly
   out of scope for Stage B2 v1.

3. **m=5 cross-check:** compute the Z/4 3-cocycle, plug into the existing
   `TransgressionKernelExact` solver, compare kernel verdict against A-5b
   (assuming A-5b finishes).

4. **m=7 production:** at m=7 the construction must NOT require HAP. All
   computations should be expressible in terms of:
   - Group elements (just `g₁ * g₂` etc.)
   - F_2 homomorphisms x_i (built via `GroupHomomorphismByImages` + abelianisation)
   - Cup products and Steenrod cup-1 products at the bar-cochain level

## Implementation tasks (next session)

- **T-B2-1: Steenrod ∪₁ product** on bar 2-cochains × bar 3-cochains → bar
  4-cochains. New file `extraspecial_orbifolds/scripts/steenrod_cup1.g`.
- **T-B2-2: Pontryagin square** `PontryaginSquare(alpha_F2)` returning the
  Z/4-valued 4-cocycle. Test: equation `dP(α) ≡ 0 mod 4` for sample α.
- **T-B2-3: Integration to 3-cocycle**. Two sub-options:
  - **T-B2-3a (linear solve):** Given P(Q) as a 4-cocycle, find f: G^3 → Z/4
    with df̃ = P(Q) using linear algebra over Z/4. Tractable at m=3, may not
    scale to m=7.
  - **T-B2-3b (direct formula):** Look up and verify a direct cochain-level
    formula for f from references (e.g., Adem-Milgram §IV, Brumfiel-Morgan
    1973, Pham Anh Minh 2001 §3). Preferred if a clean formula exists.
- **T-B2-4: m=3 anchor test.** Compute f via the new code; check class equality
  against HAP's ω_4 up to coboundary.
- **T-B2-5: A-5c integration.** Plug into `run_e_plus_m_kernel_quillen.g` to
  cover the Z/4 unit generator alongside the F_2 generators already handled.
- **T-B2-6: m=7 production run.** Run on E_+(7) — the actual m=7 unlock.

## Out of scope

- Z/8 cocycle construction (m=2). Different Steenrod operation (P²). Defer.
- Higher Pontryagin squares (degree 8, 16, ...). Not needed for our problem at
  any tested m.
- A clean theoretical write-up of the integration step. Practical
  implementation first; write-up later if needed.

## References

- Steenrod, N. "Products of cocycles and extensions of mappings". *Ann. Math.*
  48 (1947), 290–320. — Original Pontryagin square construction at cochain
  level.
- Harada, M. & Kono, A. "On the integral cohomology of extraspecial 2-groups".
  *J. Pure Appl. Algebra* 44 (1987), 215–219. — Theorem 1.1 (A(k) = Z/2^{a(k,Q)}).
- Pham Anh Minh. "Essential cohomology and extraspecial p-groups". *Trans. AMS*
  353 (2001), 1937–1957. §3 has explicit cocycle formulas (verify applicability).
- Brumfiel-Morgan. "Quadratic functions, the index modulo 8, and a
  Z/4-Hirzebruch formula". *Topology* 12 (1973), 105–122. — Pontryagin-square
  setup in a related context; may have a direct cocycle formula.
- Local: `docs/superpowers/research/2026-05-15-integer-cohomology-extraspecial-2-groups.md`
  (H-K synthesis), `docs/superpowers/research/2026-05-15-path3-spike-omega4-m3.g`
  (empirical fingerprint).

## Empirical fingerprint (spike output)

From `docs/superpowers/research/2026-05-15-path3-spike-omega4-m3.g`:

```
=== Path 3 spike: HAP's Z/4 3-cocycle at m=3 ===
  |G| = 128
  SetupCohomology3 wall: 13.037 s
  setup.exponent = 4
  setup.torsion (sorted) = [ 2 × 34, 4 ]
  num H^3 generators = 35
  exp_index = 35 (the Z/4 generator)
  values seen (sample): { 0, 1, 2, 3 }
  bar 3-cocycle equation violations on 3^4 = 81 sample: 0
  2 * omega4 distinct values on sample: { 0, 2 }
  F_2 reduction of omega4: 87 zeros, 38 ones (out of 125)
```

Re-runnable at `cd extraspecial_orbifolds/scripts && gap -q -b /tmp/path3_spike_m3.g`
(or after this PR merges, `docs/superpowers/research/2026-05-15-path3-spike-omega4-m3.g`).
