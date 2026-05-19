# 3. Cross-cutting infrastructure (the upgraded Tier-4 pipeline)

This section documents the cross-cutting computational infrastructure
that the kernel computation of §4 and the modular-data construction
of §5 both share. The pipeline has been through several rebuilds; the
version described here is the one that produced
$\ker(\mathrm{Tr})$ for $E_+(2)$ in ${\sim}\,75\,$ s of GAP wall time
and is the basis for the $E_+(3)$ kernel run. Each subsection names
the script files implementing the component, so the §3 abstractions
map onto identifiable code.

---

## 3.1 Setup: the augmented-$\mathbb Z$ bottleneck

Recall the kernel problem of §2: given a basis
$\{e_1, \ldots, e_k\}$ of $H^3(G;\, U(1))$ with coordinate
$v \in \prod_i \mathbb Z / d_i$ where $\{d_i\}$ are the elementary
divisors of the torsion subgroup, we need to test, for each
conjugacy class $g$ and each candidate $v$, whether the restriction
2-cocycle

$$
c_g(h_1, h_2) \;=\; \omega_v(g, h_1, h_2) \;+\; \omega_v(h_1, h_2, g)
\;-\; \omega_v(h_1, g, h_2)
\qquad (h_1, h_2 \in C_G(g))
$$

is a 2-coboundary in $H^2(C_G(g);\, U(1))$. The naive algorithm
builds the linear system $d\beta = c_g$ over the augmented integers
$\mathbb Z \oplus \mathbb Z\cdot 1/m$ where $m = \exp(H^3(G))$, and
asks for an integer solution. This is the contents of the prior
`IsCoboundary2` routine [see `extraspecial_orbifolds/scripts/transgression_kernel.g`,
function `IsCoboundary2`]. It is mathematically transparent — it tests
exactly the coboundary equation — but operationally catastrophic:
the augmented-$\mathbb Z$ matrix at $E_+(3)$ has shape
$|C_G(g)|^2 \times |C_G(g)|$ entries and the per-call cost is
dominated by `SolutionIntMat` over a matrix with $128 \cdot 128 = 16384$
rows when $g$ is central. Profiling on $E_+(3)$ (driver
`run_e_plus_3_kernel.g` at commit `9bffebb`) showed 0 of 35 generators
completed in $3\!:\!13\!:\!52$ wall clock at $29\,$GB RSS, with
${\sim}44\%$ of CPU time in GAP's `CollectBags`. The bag-collector
spilling was the proximate cause; the underlying issue is that the
augmented-$\mathbb Z$ system never exploits the torsion structure of
$H^2(C_G(g);\, U(1))$. The rest of §3 develops the four components
that do exploit it (T-1 through T-4), plus the bookkeeping needed
to run the resulting per-generator sweep crash-safely (T-5).

## 3.2 Torsion-split solver (T-1)

The torsion subgroup of $H^2(C_G(g);\, U(1)) \cong H^3(C_G(g);\, \mathbb Z)$
for $g \in E_+(m)$ is in every case a 2-group, by Adem–Milgram
[AM04, §IV.4--§IV.5 (Thm 4.3, Thm 5.6)], and almost always splits as
a direct sum of cyclic
2-groups of small exponent. We replace the unified
augmented-$\mathbb Z$ test with a dispatcher
`IsCoboundary2Split` [`extraspecial_orbifolds/scripts/solver/iscoboundary2_split.g`]
that routes each call to the cheapest available path:

* **Order-2 path B1: $\mathbb F_2$-linear algebra.** If the relevant
  component of $H^2$ has exponent $2$, the question reduces to
  whether $c_g \bmod 2$ is the image of the mod-$2$ coboundary
  map. This is straight Gaussian elimination over
  $\mathrm{GF}(2)$, implemented in
  `iscoboundary2_mod2.g::IsCoboundary2Mod2`. Cost: $O(|C|^3)$ bits;
  for $|C| = 64$ this is sub-second.

* **Order-2 path B2: Bockstein-image lift.** If $c_g \bmod 2 = 0$ at
  the chain level but the lift to a $\mathbb Z/4$ cochain is not a
  $\mathbb Z/4$-cocycle, the actual class in $H^2(C;\, U(1))$ is in
  the image of the Bockstein
  $\beta\colon H^1(C;\, \mathbb F_2) \to H^2(C;\, \mathbb F_2)$.
  Computing the image once (per centraliser type, see §3.5) lets us
  decide the coboundary question for *every* $\mathbb F_2$-zero cochain
  in constant time. Implemented in
  `iscoboundary2_mod2.g::BocksteinH1ToH2` and the lift variant
  `IsCoboundary2Mod2WithLift`.

* **$\mathbb Z/m$ fallback for elementary $m$.** When the relevant
  component of $H^2$ is cyclic of order $m$ with $m \le 8$, we fall
  back to a direct $\mathbb Z/m$-linear test with a tabulated
  cochain basis. This is essentially the original `IsCoboundary2`
  restricted to a known small modulus; it never sees the
  augmented-$\mathbb Z$ blowup. Code: `solver/z4_fallback.g`.

* **Iterated Bockstein for $\mathbb Z/2^k$, $k \ge 2$.** When the
  $H^2$ component is cyclic of order $2^k$, the Bockstein-image
  test of B2 generalises: a mod-$2$ cocycle representing
  $c_g \bmod 2$ admits a $\mathbb Z/2^k$ lift if and only if its
  image under the *iterated* Bockstein $\beta_{k}$ vanishes. The
  iterated Bockstein is built by composing $k-1$ successive
  $\beta\colon H^j(\,\cdot\,;\, \mathbb Z/2^j) \to H^{j+1}(\,\cdot\,;\, \mathbb Z/2)$
  evaluations. Implemented in `solver/bockstein_iterated.g`. This
  is the path used for the single $\mathbb Z/4$-generator of
  $E_+(3)$ where $k = 2$.

The dispatcher inspects `IdGroup(C)` and the elementary divisors of
the $H^2(C;\, U(1))$ torsion (cached per centraliser type, §3.5)
and picks the appropriate path. A typical mix on $E_+(3)$ is
$\sim 95\%$ path B1, ${\sim}\,4\%$ path B2, $< 1\%$ iterated
Bockstein. The amortised per-class wall time drops from a few
seconds (augmented-$\mathbb Z$) to a few milliseconds.

## 3.3 SNF wrapper (T-2)

The dispatcher of §3.2 tests one coboundary at a time. The kernel
problem asks for the *space* of $v$ producing all-zero
restrictions. We assemble the answer by collecting, for each $g$,
the linear map

$$
\Phi_g\colon \mathbb Z / d_1 \times \cdots \times \mathbb Z / d_k
\;\longrightarrow\;
H^2(C_G(g);\, U(1)), \qquad v \;\mapsto\; [c_g(\omega_v)],
$$

then taking the intersection $\bigcap_g \ker \Phi_g$ via Smith
Normal Form (SNF) over $\mathbb Z$. The wrapper
`TransgressionKernelExact` [`extraspecial_orbifolds/scripts/solver/snf_wrapper.g`]
performs this assembly: per orbit representative $g$ it builds a
basis for $H^2(C_G(g);\, U(1))$ from a HAP `ResolutionFiniteGroup`,
projects each generator $e_i$ through the cocycle restriction
$c_g$, and stacks the resulting matrices over the $\Phi_g$. SNF
reduces the stack to elementary divisors; the kernel is the right
null-block. Output is an explicit $\mathbb Z$-generator list whose
$\mathbb Z$-span (mod torsion) equals $\ker(\mathrm{Tr})$. This is
the "exact" half of the pipeline name: even when individual
$\Phi_g$ tests use the cheap mod-$2$ path of §3.2, the assembled
kernel is the actual integral kernel.

## 3.4 BRW symmetry reduction (T-3a/b/c/d)

The Bolt–Room–Wall (BRW) group $\mathrm{BRW}(m)$ is the outer
normaliser of $E_+(m)$ inside $O(2^m)$: an extension
$1 \to E_+(m) \to \mathrm{BRW}(m) \to O^+(2m, \mathbb F_2) \to 1$.
By the construction of $\omega$ as a pullback from a Lyndon–Hochschild–Serre
class, every $y \in \mathrm{BRW}(m)$ acts:

1. **On conjugacy classes** $[g] \mapsto [y g y^{-1}]$, permuting them.
2. **On $H^3(E_+(m);\, U(1))$** as a $\mathbb Z$-linear endomorphism
   $M_y$ of $\mathbb Z / d_1 \times \cdots \times \mathbb Z / d_k$.

Crucially, these two actions are *compatible*: if $y$ takes
$[g_1]$ to $[g_j]$, then the cocycle restriction $c_{g_j}$ for
$\omega_v$ equals $c_{g_1}$ for $\omega_{M_y v}$, up to the
centraliser isomorphism induced by conjugation. Compatibility means
the transgression test for the $j$-th class against the $i$-th
generator can be replayed from the test for the $1$st class against
the $M_y$-image generator — a single matrix-vector product over
$\mathbb Z / m$ instead of a fresh SNF resolution.

The implementation splits across four files. `brw_construction.g`
(T-3a) constructs $\mathrm{BRW}(m)$ as a permutation group on the
generators of $E_+(m)$; we use the explicit Adem–Milgram extension
description rather than a presentation by relators, because
HAP's group-theoretic primitives (`Centralizer`, `ConjugacyClasses`)
are fastest when the input is a `GroupByGenerators` and not a
finitely presented quotient. `brw_conjugacy_action.g` (T-3b)
computes the induced permutation of $\mathrm{Conj}(E_+(m))$ — a
single pass over the orbits suffices. `brw_h3_action.g` (T-3c)
computes the matrices $M_y$ by chain-level pullback through
the bar resolution: each $y$ lifts to a $\mathbb Z[E_+(m)]$-chain
endomorphism, and its degree-3 component, restricted to the
$H^3$-cycle basis, gives $M_y$ over $\mathbb Z / m$. Finally
`transgression_per_generator_brw.g` (T-3d) is the driver: a
Schreier-vector breadth-first search over the BRW action on
conjugacy classes, with each orbit traversal accumulating
$M_y \in \mathrm{End}(H^3)$ along the BFS path so the
$j$-th class's per-generator boolean is a matrix-vector replay
of the orbit representative's boolean. On $E_+(3)$ this collapses
$65$ conjugacy classes into $4$ BRW orbits, with respective sizes
$1$, $35$, $28$, $1$. The expensive HAP work — building a basis
for $H^2(C_G(g);\, U(1))$ — happens once per orbit, not once per
class.

## 3.5 Centraliser-type cache (T-4)

Two distinct conjugacy classes can have centralisers of the same
GAP isomorphism type (`IdGroup`). In $E_+(m)$ this collapse is
substantial: $E_+(3)$ has 65 conjugacy classes but only 4 or 5
isomorphism types of centraliser (depending on $m$-parity and the
specific generator type). Building a HAP `ResolutionFiniteGroup`
for a centraliser is the single most expensive step in the
pipeline — for $|C| = 64$ it dominates the wall clock at
${\sim}\,1$ minute per build. Doing it once per *iso-class* rather
than once per *class* therefore yields a $\sim 13\times$ saving
on $E_+(3)$. The cache is keyed by `IdGroup(C)` and stores the
resolution, the $H^2$ basis, and the Bockstein-image data needed by
the §3.2 dispatcher. Implementation:
`extraspecial_orbifolds/scripts/solver/centraliser_cache.g`. The
cache is populated lazily on the first probe for each iso-type
and persists for the lifetime of the GAP session; downstream
callers receive an opaque handle that they pass to
`BuildPerClassCocycleBasis` (in `solver/snf_wrapper.g`) and to
`IsCoboundary2Split` (in `solver/iscoboundary2_split.g`).

## 3.6 Resumable per-generator state (T-5)

The $E_+(3)$ kernel sweep touches 35 generators × 65 classes; with
the §3.2–3.5 optimisations each generator-orbit pair takes on the
order of seconds to minutes, and the full sweep is wall-clock
bounded by ${\sim}\,1$ hour. We do not want a $59$-minute crash to
cost an hour. The resumable state module
[`extraspecial_orbifolds/scripts/transgression_resume.g`] interposes
on the per-generator loop:

* After each generator $i$ finishes its 4-orbit sweep, the
  per-class boolean vector is appended to a state file via
  `AppendTo` as a GAP source line `state[i] := [...]`.
* On restart the state file is parsed by `LoadResumeState`, which
  populates an in-memory record and returns the set of completed
  generator indices.
* The main loop skips already-completed indices on resume.

GAP's `AppendTo` introduces a backslash–newline line-wrapping at
the 80-column boundary which breaks the parser if not undone; the
loader handles this with a literal `ReplacedString(bytes, "\\\n", "")`
pre-pass. The state file is plain GAP source so the user can also
read or edit it by hand to invalidate a specific generator's row
for re-computation.

## 3.7 Verified anchor: $\ker(\mathrm{Tr}) = 2048$ on $E_+(2)$

The end-to-end driver `run_e_plus_2_kernel.g` exercises every
component of §3.2–3.6 against $E_+(2)$, for which the kernel was
also computed independently by brute-force enumeration of all
$4096$ classes in $H^3(E_+(2);\, U(1))$ (Adem–Milgram method, the
A-2 ground truth). Both routes agree on
$|\ker(\mathrm{Tr})| = 2048$, and the integer-generator list
produced by the SNF wrapper matches the brute-force kernel as a
subgroup of $(\mathbb Z/2)^9 \oplus \mathbb Z/8$. The new pipeline
completes the computation in $1\!:\!15$ of wall time and peak RSS
of $\sim 250\,$MB on a 2024 laptop. Compared with the
augmented-$\mathbb Z$ baseline of §3.1, which timed out without
completing a single generator after $3\!:\!13\!:\!52$ at $29\,$GB,
this is a speedup of more than two orders of magnitude (and a
RSS reduction of two orders of magnitude). The corresponding
$E_+(3)$ driver `run_e_plus_3_kernel.g` uses identical
infrastructure and is the subject of §4.

---
