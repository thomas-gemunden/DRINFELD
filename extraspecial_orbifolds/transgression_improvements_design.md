# Improvements to the transgression-kernel computation

This document records a design for upgrading the Tier-4 transgression-
kernel pipeline (`scripts/transgression_kernel.g` and
`scripts/transgression_per_generator.g`) so that the kernel of
$$
\mathrm{Tr} \colon H^3(E_+(m); U(1)) \;\longrightarrow\; \bigoplus_{[g] \in \mathrm{Cl}(E_+(m))} H^2(C_{E_+(m)}(g); U(1))
$$
is decidable in routine wall-clock for $m \in \{3, 5\}$ and reachable
by a focused effort for $m = 7$. The decision-theoretic motivation is
recorded in `writeup.md` §5.1: $\ker \mathrm{Tr} = 0$ implies the
Keller–Roberts–Roberts $c_g = 0$ evidence is sufficient for the
$\omega = 0$ conjecture.

## 1. Current state

Implementation: `scripts/transgression_kernel.g` (brute force, capped
at $|H^3| \le 1024$) and `scripts/transgression_per_generator.g`
(linear-algebra reduction over $H^3$ generators).

Status:

| group | $|G|$ | $|H^3|$ torsion | reachable today |
|---|---:|---|---|
| $E_+(1) = D_8$ | 8 | $[8]$ | $\ker \mathrm{Tr} = 0$ via brute force |
| $E_+(2)$ | 32 | $[2^9, 8]$ | per-generator complete, every $\mathrm{Tr}(e_i) \ne 0$; SNF pending |
| $E_+(3)$ | 128 | $[2^{34}, 4]$ | per-generator deferred behind algorithmic improvement |
| $E_+(5)$ | 2 048 | not yet computed | resolution setup not yet attempted |
| $E_+(7)$ | 32 768 | not yet computed | `ResolutionFiniteGroup` and `ConjugacyClasses` both fail at 60 GB heap |

Per-call bottleneck: the augmented integer system in
`IsCoboundary2`. At $|C_G(g)| = n$ this is an
$n^2 \times (n + n^2)$ `SolutionIntMat` invocation. Empirically:
~30 s at $n = 64$ ($E_+(3)$ non-central centraliser), $\sim 8$ min at
$n = 1024$ ($E_+(5)$ non-central centraliser), prohibitive at
$n = 16{,}384$ ($E_+(7)$ non-central centraliser).

## 2. Cross-cutting improvements

These apply at every $m$ and should be implemented before the
$m$-specific work.

### 2.1 HAP-native coboundary decision

Replace `IsCoboundary2`'s `SolutionIntMat` with HAP's resolution-based
decision. Once a free $\mathbb Z H$-resolution
$R \to \mathbb Z$ of length $\ge 3$ is in hand for the centraliser
$H = C_G(g)$, the cocycle $c_g$ pushes forward to a 2-cochain on the
bar resolution; HAP's `Cocycle(R, c_g, 2)` constructs it and
`StandardCocycle`/`IsCocycleACoboundary` (HAP utilities, [Ell08])
decide exactness in time linear in the resolution dimensions, not in
$|H|^2$. Expected speedup at $n = 64$ is $10^1$–$10^2 \times$.

The resolution of $H$ is a one-time setup cost; subsequent
coboundary checks for varying $c_g$ are cheap.

### 2.2 Per-generator $\to$ Smith Normal Form wrapper

Wrap `transgression_per_generator` so it accumulates the integer matrix
$$
M \in \mathrm{Mat}\!\left(k \times \textstyle\sum_{[g]} k_{C_g}; \mathbb Z\right),
\qquad
M_{i, *} = \mathrm{Tr}(e_i),
$$
relative to fixed bases of $H^3(G; U(1))$ and the cohomology targets
$H^2(C_G(g); U(1))$. Compute $\ker M$ via `NormalFormIntMat(M, 4)`,
then intersect with the source torsion lattice
$\prod \mathbb Z/d_i$ to obtain $\ker \mathrm{Tr}$ exactly.

Cost: $O(k^3)$ in the source rank, negligible against the per-call
coboundary work. Closes the gap from "necessary for $\ker = 0$" to
"exactly $\ker$".

### 2.3 Centraliser-type reduction

For an extraspecial 2-group, conjugacy classes of $E_+(m)$ fall into
four types under $\mathrm{BRW}(m)$-conjugation
([writeup.md §2.4]; [KRR24, Prop. 3.1]):

| BRW orbit | order | centraliser | $|C_G(g)|$ |
|---|---:|---|---:|
| identity | 1 | $E_+(m)$ | $2^{2m+1}$ |
| centre $-1$ | 2 | $E_+(m)$ | $2^{2m+1}$ |
| $\sigma_2$-type | 2 | $\mathbb Z_2 \times E_+(m-1)$ | $2^{2m}$ |
| $\sigma_1\sigma_2$-type | 4 | $\mathbb Z_4 \circ E_+(m-1)$ | $2^{2m}$ |

The setup cost for `IsCoboundary2` (HAP-native or otherwise) on a
centraliser depends only on the *isomorphism type*, not on the
particular conjugacy-class representative. Caching one resolution per
distinct centraliser type reduces the resolution count from
$|\mathrm{Cl}(G)| \approx 4^m + 1$ to $4$ at every $m$.

### 2.4 BRW-orbit reduction on conjugacy classes

The transgression has a covariance property under
$\mathrm{BRW}(m)$-conjugation: for $y \in N_{O(2^m)}(E_+(m))$ with
$\alpha_y(g) = h$,
$$
\mathrm{Tr}_h(\omega) \;=\; \alpha_y^{*}\!\left(\mathrm{Tr}_g\!\left((\alpha_y^{-1})^{*} \omega\right)\right),
$$
which gives
$$
\ker \mathrm{Tr}_h \;=\; \alpha_y^{*}\!\left(\ker \mathrm{Tr}_g\right)
\;\subset\; H^3(G; U(1)).
$$
Hence
$$
\ker \mathrm{Tr} \;=\; \bigcap_{[g] \in \mathrm{Cl}(G)} \ker \mathrm{Tr}_g
\;=\; \bigcap_{O \in \mathrm{Orb}_{\mathrm{BRW}}(\mathrm{Cl}(G))}
\;\bigcap_{[h] \in O} \alpha_{y_{g \to h}}^{*}\!\left(\ker \mathrm{Tr}_{g_O}\right).
$$
Concretely: compute $\ker \mathrm{Tr}_{g_O}$ for one $g_O$ per BRW
orbit (4 orbit representatives in total), and pull back to the other
classes in the orbit by the $\mathrm{BRW}$-action on $H^3(G; U(1))$.
The latter is a permutation-with-signs of $\prod \mathbb Z/d_i$,
computable once.

This reduces the *per-class* loop from $|\mathrm{Cl}(G)|$ to 4
representatives, with the savings coming from skipping the inner
$k$-many `IsCoboundary2` calls on classes inside the same orbit.

| $m$ | $|\mathrm{Cl}(G)|$ | reduction factor |
|---|---:|---:|
| 3 | 65 | $\sim 16\times$ |
| 5 | 1 025 | $\sim 256\times$ |
| 7 | 16 385 | $\sim 4 \cdot 10^3\times$ |

The pull-back step relies on knowing the $\mathrm{BRW}(m)$-action on
$H^3(E_+(m); U(1))$. For the present purpose only its action on the
generators $e_i$ in fixed coordinates is needed; this can be
extracted from the explicit BRW description in
`scripts/em_construction.g` plus the lift map produced by
`UniversalCoefficientsTheorem`.

### 2.5 Caching

Persist the following across runs:

* The resolution `ResolutionFiniteGroup(G, 4)` for each $G$ used.
* The four centraliser resolutions (one per type, §2.3).
* The lift matrix and torsion vector returned by
  `UniversalCoefficientsTheorem`.
* The standard-cocycle realisations of $e_1, \ldots, e_k$.
* The per-generator matrix $M$ accumulated so far.

Storage layout: `computed/transgression/<m>/{resolution_G.g,
resolution_central.g, resolution_sigma2.g, resolution_sigma1sigma2.g,
uct.g, M.g}`.

Resumption: a partial run (some generators evaluated, others not)
should append rows to $M$ rather than restart.

## 3. $m = 3$ plan: make Tier 4 routine

State: $|G| = 128$, $H^3(G) \cong \mathbb Z/2^{34} \oplus \mathbb Z/4$,
$k = 35$ generators, 65 conjugacy classes (4 BRW orbits), centraliser
sizes 64 or 128. Resolution exists; the question is wall-clock.

### Goal

Full $\ker \mathrm{Tr}$ for $E_+(3)$ in under one hour on a single
CPU.

### Steps

1. Implement §2.1 (HAP-native `IsCoboundary2`). Validate against
   existing brute-force result on $D_8$ (kernel must remain trivial).
2. Implement §2.2 (SNF wrapper). Validate on $E_+(2)$: rerun the
   in-memory per-generator output and confirm the SNF kernel agrees
   with the brute-force enumeration of 4096 classes (independent test
   in the existing `test_transgression_e_plus_2_3.g` provides
   ground truth).
3. Implement §2.3 (centraliser-type caching). At $m = 3$ this saves
   one resolution computation per non-canonical class — about 60×
   for the resolution build.
4. Implement §2.4 (BRW-orbit reduction). At $m = 3$ this is a
   $\sim 16\times$ saving on the per-class loop, on top of (1)–(3).
5. Run end-to-end and read off $\ker \mathrm{Tr}$.

### Cost estimate

At $n = 64$, HAP-native coboundary at ~0.3 s/call, 35 generators × 4
BRW representatives = 140 calls, total ~40 s of inner-loop work.
SNF on a $35 \times \sum k_{C_g}$ matrix is sub-second. Including
resolution setup (~5 min of HAP work), full pipeline runs in
$\sim 10$ min wall-clock.

### Cross-checks

* $E_+(2)$: the SNF of $M$ from the existing per-generator data must
  produce the same kernel as brute-force enumeration of 4096 classes.
* $E_+(3)$ partial validation: with BRW-orbit reduction off, run the
  per-class loop on a subset of classes (e.g. five non-canonical ones
  per BRW orbit) and confirm the resulting $\mathrm{Tr}$ values
  match what the BRW-pullback predicts from the orbit representative.

## 4. $m = 5$ plan: handle $|G| = 2048$ setup

State: $|G| = 2048$, 1025 conjugacy classes (4 BRW orbits),
centraliser sizes 1024 or 2048. Resolution and conjugacy-class
computations have not been attempted in HAP at this size; they are
expected to succeed but with substantial wall-clock.

### Goal

Establish whether HAP can produce `ResolutionFiniteGroup(E_+(5), 4)`
within a heap budget of 60 GB and acceptable wall-clock (single-day
target). If so, run the full Tier-4 pipeline using the §2 stack;
otherwise, fall back on the $m = 7$ plan (§5).

### Steps

1. Inherit all infrastructure from §3 (cross-cutting + $m = 3$
   validation complete).
2. Attempt `ResolutionFiniteGroup(E_+(5), 4)` with 60 GB heap and
   record wall-clock plus peak resident memory. Expected: hours
   rather than minutes.
3. On success: store the resolution, run UCT, identify the torsion
   vector $H^3(E_+(5); U(1)) \cong \prod_i \mathbb Z/d_i$.
4. Build per-orbit centraliser resolutions: one for $E_+(5)$, one
   for $\mathbb Z_2 \times E_+(4)$, one for $\mathbb Z_4 \circ E_+(4)$.
   These are size 2048, 1024, 1024 respectively.
5. Run §2.1 + §2.2 + §2.4 to produce $M$ and $\ker M$.

### Cost estimate

If `ResolutionFiniteGroup(E_+(5), 4)` succeeds in $\le 4$ h, total
$\le 1$ day. If not, transition to §5.

### Cross-checks

* Centraliser of $1$ in $E_+(5)$ is $E_+(5)$ itself; the partial
  cocycle $c_1 = \omega(\cdot, \cdot, \cdot) - \omega(\cdot, \cdot, \cdot)
  \equiv 0$ should be detected as trivially exact for every
  generator.
* $T$-multiset prediction is independent of $\omega$ and matches the
  analytical prediction from `predict_e_plus_m.g` — orthogonal sanity
  check on the resolution-correctness.

### Fallback

If HAP fails: skip directly to the §5 analytical machinery and
inherit it for $m = 5$. The Quillen-based presentation works at any
$m \ge 1$; the only reason to prefer HAP at $m = 5$ is reduced
implementation effort, not correctness.

## 5. $m = 7$ plan: bypass HAP entirely

State: `ResolutionFiniteGroup(E_+(7), 4)` and
`ConjugacyClasses(E_+(7))` both OOM at 60 GB heap. The size of
$|H^3(E_+(7); U(1))|$ is structurally large but not the proximate
blocker for the kernel test; the proximate blocker is the
infeasibility of HAP's general-purpose resolution for a group of
order $32{,}768$ with PCG complexity $2^{2m+1}$.

### Goal

Replace each piece of the HAP-supplied input — the torsion vector,
the lift map, the centraliser cohomology — with an analytical or
restriction-based construction that does not require a free
resolution of $E_+(7)$ itself.

### Two complementary routes

**Route A: Quillen analytical $H^*$.** Use Quillen's polynomial-times-exterior
presentation [Qui71]
$$
H^*(E_+(m); \mathbb F_2) \;\cong\; \mathbb F_2[c_2, x_1, \ldots, x_{2m}] \otimes \Lambda(y_1, \ldots, y_{2m}),
$$
with explicit relations expressing $c_2$ in terms of the $x_i, y_j$
([Qui71, Thm. 5.4]; [AM04, IV.7]), together with the Bockstein
spectral sequence relating $H^*(G; \mathbb F_2)$ to $H^*(G; \mathbb Z)$
([AM04, Ch. III.3]) and the connecting homomorphism
$H^*(G; U(1)) \cong H^{*+1}(G; \mathbb Z)$ (since $H^*(G; \mathbb R) = 0$
for finite $G$). This yields:

* $H^3(E_+(7); U(1)) \cong H^4(E_+(7); \mathbb Z)$ as a finite abelian
  group;
* explicit cocycle representatives for each generator, expressible as
  cup products and Bocksteins of the $x_i, y_j$ — evaluable on
  triples $(g_1, g_2, g_3) \in E_+(7)^3$ via the standard cup product
  on the bar resolution restricted through the abelianisation map
  $E_+(7) \to (\mathbb F_2)^{2m}$.

The non-trivial part of Route A is implementing the Bockstein and cup
product at the cochain level; both are standard but require care with
sign conventions.

**Route B: detecting subgroup.** Identify a subgroup $H \le E_+(7)$
for which $\mathrm{res}^G_H \colon H^3(E_+(7); U(1)) \to H^3(H; U(1))$
is injective on the relevant subspace ([AM04, V.6]). Candidate
detecting families for extraspecial 2-groups are recorded in
[AM04, Ch. IV.7] and consist of a maximal elementary abelian subgroup
$(\mathbb F_2)^{m+1}$ together with an order-$2^3$ extraspecial
section. For these subgroups HAP's `ResolutionFiniteGroup` is
tractable; one then computes
$\ker \mathrm{Tr}_G \le \mathrm{res}^{-1}(\ker \mathrm{Tr}_H)$ and
upgrades by checking the additional constraint coming from the
non-detected part.

### Steps

1. Decide route (A vs B vs both) — see §7.
2. (Route A.) Implement the Quillen presentation as a GAP module:
   data structure for the polynomial ring with the Quillen relations,
   evaluator on group triples via the bar / abelianisation cup
   product. Cross-check at $m = 2, 3$ against HAP's
   `UniversalCoefficientsTheorem` torsion outputs.
3. (Route A.) Implement the Bockstein and read off the torsion of
   $H^3(E_+(7); U(1))$ from the Quillen description.
4. (Route A.) Realise each $H^3$ generator as an explicit cocycle
   `omega: G x G x G -> Z/m`, callable in `CGCocycleFunc`.
5. Centralisers of $E_+(7)$ have order 16 384 or 32 768. HAP can
   in principle resolve them (one type at a time), but the
   centraliser-type reduction (§2.3) plus a fresh attempt with
   improved memory practices is needed. If HAP fails on the
   centralisers too, Route A applies recursively: each centraliser
   is itself an extraspecial-or-near-extraspecial 2-group with a
   Quillen-style presentation.
6. Apply §2.1 + §2.2 + §2.4 to produce $M$ and $\ker M$.

### Cost estimate

Implementation is the dominant cost: Route A needs ~1–2 weeks of
focused work (Quillen presentation, Bockstein, cup product). Once
implemented it transfers to $m = 5$ and $m = 3$ as cross-checks.

### Cross-checks

* Quillen's presentation must reproduce the HAP torsion outputs at
  $m = 2$ ($[2^9, 8]$) and $m = 3$ ($[2^{34}, 4]$) byte-for-byte.
* The number of generators $k$ predicted by Quillen for $E_+(7)$
  should match an independent count: each elementary-abelian
  generator $x_i, y_j$ contributes a known number of $H^3$ classes,
  and the Quillen relations cut down to the actual count.
* For at least one $H^3$ generator at $m = 7$, evaluate it on a
  small subgroup $H$ where HAP works, restrict, and confirm the
  restriction matches a HAP-produced $H^3(H; U(1))$ generator.

## 6. Risks and open questions

* **The $\mathrm{BRW}$-action on $H^3$ may not be free of subtleties.**
  The covariance argument in §2.4 relies on $\mathrm{BRW}(m)$
  normalising $E_+(m)$ inside $O(2^m, \mathbb R)$, which is true; the
  pullback action on $H^3(E_+(m); U(1))$ is then induced by outer
  automorphisms in $\mathrm{Out}(E_+(m))$. Computing the action
  explicitly on the lift basis requires either a direct evaluation
  of $\alpha_y^*$ on standard cocycles (HAP's
  `EquivariantHomotopy` or manual construction) or a representation-
  theoretic shortcut. Should be validated at $m = 2$ before relying
  on it at $m = 5, 7$.
* **Quillen's relations are stated mod 2.** Lifting to integer
  coefficients introduces Bockstein corrections that must be tracked
  carefully; an arithmetic error here is the most likely source of
  bugs in Route A.
* **Centraliser cohomology at $m = 7$.** The non-central centralisers
  have order 16 384, of the form $\mathbb Z_2 \times E_+(6)$ or
  $\mathbb Z_4 \circ E_+(6)$. HAP may or may not handle these — needs
  empirical testing.
* **Definition of "the" $\omega_{\mathrm{Keller}}$.** Even if
  $\ker \mathrm{Tr}$ is non-trivial, settling the conjecture means
  showing the *specific* class $[\omega_{\mathrm{Keller}}]$ is
  zero — and this class is not directly extracted from KRR's
  pipeline at present. The $\ker \mathrm{Tr} = 0$ outcome dodges
  this issue; the $\ker \mathrm{Tr} \ne 0$ outcome forces it.

## 7. Recommended execution order

1. **Cross-cutting infrastructure (§2).** Days, not weeks. Validates
   on $D_8$ and $E_+(2)$.
2. **$m = 3$ end-to-end (§3).** Settles the $E_+(3)$ kernel one way
   or the other. Independent of any analytical cohomology work.
3. **$m = 5$ feasibility (§4).** A timed `ResolutionFiniteGroup`
   attempt; outcome dictates whether to invest in §5 first or stick
   with HAP.
4. **$m = 7$ analytical infrastructure (§5).** Long-pole. Worth the
   investment regardless of $m = 5$'s feasibility because Route A
   transfers to $m = 5$ as a cross-check and to all future $m$ as a
   primary tool.

A reasonable parallel plan: pursue §3 and the early stages of §5
simultaneously, since they share §2.1 and §2.2 but diverge from §2.3
onwards.
