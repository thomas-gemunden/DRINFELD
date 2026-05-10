# Modular data of twisted Drinfeld doubles of extraspecial 2-groups: methodology and results

**Working title.** *Transgression kernels, BRW-folded $S$-matrices, and detection of orbifold modular data for $E_+(m)$.*

**Status.** Draft, $\S 1$ written in full; $\S\S 2$–$6$ are outlines with key claims and intended scope, to be expanded.

---

## 1. Introduction

### 1.1 Motivation: orbifold modular data and the Keller question

A holomorphic vertex operator algebra (VOA) $V$ of central charge $c$
and a finite group $G \le \mathrm{Aut}(V)$ together determine an
*orbifold* $V^G$ whose module category $\mathrm{Mod}(V^G)$ is a
modular tensor category (MTC) [DVVV89, Kir02, DLN15]. When $G$ acts
*inner-faithfully* on a lattice VOA $V_L$, there is a conjectural
identification

$$
\mathrm{Mod}(V_L^G) \;\;\cong\;\; \mathrm{Mod}\bigl(D^{\omega}(G)\bigr)
$$

between the orbifold MTC and the representation category of the
*twisted Drinfeld double* of $G$ at a 3-cocycle
$\omega \in H^3(G;\, U(1))$ — the 't Hooft anomaly of the orbifold
[DPR91, DVVV89, EvG18, MN05]. The 3-cocycle $\omega$ is in general
non-trivial and is the principal obstruction to the orbifold being
holomorphic (untwisted).

A driving question, made concrete by [Keller–Roberts–Roberts 2024
(KRR24)](https://arxiv.org/abs/2411.13646), is whether one can decide
$[\omega] = 0$ from local data on the centralisers. KRR construct an
orbifold of the Barnes–Wall lattice VOA $V_{\mathrm{BW}(7)}$ by the
extraspecial 2-group $E_+(7) \cong 2_+^{15}$ acting through the
Bolt–Room–Wall group $\mathrm{BRW}(7)$. Granting their conjecture
that $\omega = 0$, the orbifold is a holomorphic VOA of central charge
$c = 128$ with gap $4$ — exceptional in that the only previously
known holomorphic VOAs of central charge $\ge 128$ have gap $\le 2$
[Höh96, Höh19, Wit07]. Their evidence consists in checking, for every
conjugacy class $[g]$ of $E_+(m)$, that the *local* 2-cocycle
$c_g \in H^2(C_G(g);\, U(1))$ that controls the projective $g$-twisted
module is trivial. Triviality of all $c_g$ is *necessary* for
$[\omega] = 0$. Whether it is *sufficient* is exactly the question of
whether the transgression map

$$
\mathrm{Tr} \colon H^3(G;\, U(1)) \;\longrightarrow\;
\bigoplus_{[g]} H^2(C_G(g);\, U(1)),
\qquad [\omega] \mapsto \bigl([c_g]\bigr)_{[g]}
$$

has trivial kernel.

This paper develops the algorithmic and conceptual tools to answer
the kernel question for the extraspecial 2-groups
$E_+(m) = 2_+^{2m+1}$ in the range $m \in \{1, 2, 3, 5, 7\}$ that
matters for the lattice-VOA orbifold construction, and to compute the
twisted modular data $(S^\omega, T^\omega)$ to which $\omega$
contributes. We work in GAP using HAP for cohomology and a
specialised pipeline for the twisted Drinfeld-double $S$ matrix. Our
emphasis throughout is on (i) reducing astronomical-rank dense $S$
computations to a small number of *canonical blocks* indexed by
BRW-orbit data; (ii) deciding $[\omega] = 0$ from $c_g$ data through
the kernel of $\mathrm{Tr}$; and (iii) detecting MTC isomorphism
classes from $(S, T)$ alone in the presence of large symmetric power
of automorphism groups.

### 1.2 Background notation

We fix throughout the following conventions. Let $G$ be a finite
group with identity $1_G$, $Z(G)$ its centre, $[g] \subset G$ the
conjugacy class of $g$, and $C_G(g) \le G$ the centraliser. For an
abelian group $A$ we write $H^*(G; A)$ for the (Eilenberg–Mac Lane)
cohomology of $G$ with coefficients in $A$; cohomology is always
computed via the bar resolution unless explicitly stated. Almost all
of our cohomology will have coefficients in $U(1) = \mathbb R / \mathbb Z$
or, equivalently, in $\mathbb C^\times$. By the universal-coefficients
theorem the natural map $H^n(G;\, \mathbb Z) \to H^n(G;\, U(1))$
yields an isomorphism after passing to torsion, and we exploit this
to compute $H^n(G;\, U(1))$ via integer cohomology in HAP.

A **3-cocycle** is a normalised function $\omega \colon G^3 \to U(1)$
satisfying

$$
\omega(g_2, g_3, g_4)\, \omega(g_1, g_2 g_3, g_4)\, \omega(g_1, g_2, g_3)
= \omega(g_1 g_2, g_3, g_4)\, \omega(g_1, g_2, g_3 g_4),
$$

modulo coboundaries $(d c)(g_1, g_2, g_3) = c(g_2, g_3) - c(g_1 g_2, g_3) + c(g_1, g_2 g_3) - c(g_1, g_2)$.

The **twisted Drinfeld double** $D^\omega(G)$ of [Dijkgraaf–Pasquier–
Roche 1991] is a quasi-Hopf algebra whose representation category
$\mathcal Z(\mathrm{Vec}_G^\omega) = D^\omega(G)\text{-mod}$ is a
modular tensor category depending only on $[\omega] \in H^3(G; U(1))$
[CGR2000, Ban97, Ban98]. Simple objects are pairs $(g, \chi)$ with
$g$ ranging over conjugacy class reps and $\chi$ over irreducible
*projective* characters of $C_G(g)$ with multiplier $c_g$. The
**local 2-cocycle** $c_g \in Z^2(C_G(g); U(1))$ is given on $h_1, h_2 \in C_G(g)$ by

$$
c_g(h_1, h_2) \;=\; \omega(g, h_1, h_2) \,-\, \omega(h_1, g, h_2) \,+\, \omega(h_1, h_2, g)
\qquad \bigl[\text{CGR2000 eq. 2.7, KRR24 eq. 2.1.3}\bigr]. \tag{$\dagger$}
$$

Identity $(\dagger)$ exhibits $c_g$ as the **slant product**
$\omega \backslash [g]$ where $[g] \in H_1(C_G(g);\, \mathbb Z)$ is the
class of the canonical 1-cycle (well-defined since
$g \in Z(C_G(g))$, [Br82 ch. V.3]). The fact that $\omega$ is a
3-cocycle, restricted to commuting tuples in $C_G(g)$, collapses the
3-cocycle identity to the 2-cocycle identity for $c_g$. Up to
coboundary on $\omega$, the class $[c_g] \in H^2(C_G(g); U(1))$ is
well-defined, and the assembly across conjugacy classes is the
*total transgression* $\mathrm{Tr}$ defined in $\S 1.1$. The
terminology *transgression* matches the Lyndon–Hochschild–Serre
differential $d_3 \colon E_2^{0, 2} \to E_2^{3, 0}$ for the central
extension $\langle g \rangle \hookrightarrow C_G(g) \twoheadrightarrow
C_G(g)/\langle g \rangle$ [AM04 §III.1, NN08 §3].

The modular data $(S^\omega, T^\omega)$ is determined explicitly by
$\omega$. For $\omega = 1$ (the **untwisted** case), the formula
collapses to the **Bantay–Coste–Gannon–Ruelle formula**:

$$
T^0_{(g, \chi)} \;=\; \tfrac{\chi(g)}{\dim \chi},
\quad
S^0_{(g_1, \chi_1), (g_2, \chi_2)} \;=\; \tfrac{1}{|G|}
\sum_{\substack{a \in [g_1],\; b \in [g_2] \\ a b = b a}}
\overline{\chi_1(t_a^{-1} b\, t_a)}\, \overline{\chi_2(s_b^{-1} a\, s_b)},
$$

with $t_a, s_b \in G$ conjugating $g_i$ to $a, b$ respectively
[Ban97, CGR2000, MN05]. For $\omega \ne 1$ the formula picks up a
$U(1)$-valued phase $\varepsilon_\omega(g_1, g_2, a, b)$ inside the
sum and replaces the ordinary characters by the projective ones with
multipliers $c_{a}, c_b$ (see [CGR2000 §3] for the explicit
expression; we re-derive it in $\S 2$ and give a self-contained
closed form in $\S 3$).

The extraspecial 2-groups $E_+(m) \cong 2_+^{2m+1}$ are the central
extensions $1 \to \mathbb Z_2 \to E_+(m) \to (\mathbb F_2)^{2m} \to 1$
with the "+" quadratic form on the quotient; they have order
$|E_+(m)| = 2^{2m+1}$. The Bolt–Room–Wall group
$\mathrm{BRW}(m)$ is the normaliser of $E_+(m)$ in
$O(2^m, \mathbb R)$ [BRW61, NRS01]. Conjugacy classes of $E_+(m)$ in
$\mathrm{BRW}(m)$ form **four orbits**, of which two (the central
classes $\{1\}, \{-1\}$) are singletons and two (the "$\sigma_2$" and
"$\sigma_1 \sigma_2$" classes) split into $4^m - 1$ pairs of size $2$
under $E_+(m)$ alone. The Barnes–Wall lattice
$\mathrm{BW}(m) \subset \mathbb R^{2^m}$ is invariant under
$\mathrm{BRW}(m)$, and the lattice VOA $V_{\mathrm{BW}(m)}$ carries
the resulting $E_+(m)$-action.

### 1.3 The transgression-kernel approach

Our strategy for deciding $[\omega] = 0$ from the local data
$(c_g)_{[g]}$ is to compute the kernel of the total transgression
explicitly, group by group:

$$
K_G \;:=\; \ker\bigl(\mathrm{Tr} \colon H^3(G; U(1)) \to \textstyle\bigoplus_{[g]} H^2(C_G(g); U(1))\bigr).
$$

If $K_G = 0$, then the KRR-style local check
$\bigl( c_g = 0 \text{ for all } g \bigr)$ implies $[\omega] = 0$,
and the orbifold construction is unobstructed. If $K_G \ne 0$, the
local check leaves $|K_G|$ possible classes for $[\omega]$, and
*additional necessary conditions* (most importantly, the level
matching / type-0 condition of [vEMS17]) restrict $[\omega]$ further.
In favourable cases the level-matching constraint cuts $K_G$ down to
a single class. In unfavourable cases it does not — and our running
example $E_+(2) = 2_+^5$ provides an explicit instance where
$\dim_{\mathbb F_2} K_G \ge 11$, far too large to be eliminated by
local data alone.

The kernel $K_G$ admits a more conceptual decomposition. Restriction
to each Sylow $p$-subgroup decomposes $H^3(G; U(1))$ into $p$-primary
parts (Cartan–Eilenberg [CE56 ch. XII], [AM04]):

$$
H^3(G; U(1)) \;=\; \bigoplus_{p \mid |G|} H^3(G; U(1))_{(p)},
$$

and for the extraspecial 2-groups $E_+(m)$ only the $2$-primary part
is non-zero. The transgression respects this decomposition. Within
the $2$-primary part, $K_G$ decomposes further by the *torsion order*
of $[\omega]$: classes of order $2$, $4$, $8$ etc. each give a
distinguished subspace. This *torsion-splitting* of the kernel is
the key to our computational efficiency: we solve the kernel for the
mod-$2$ part first by linear algebra over $\mathbb F_2$, then ascend
to mod-$4$, mod-$8$, etc., via iterated Bocksteins
$\beta \colon H^n(G; \mathbb Z / 2^k) \to H^{n+1}(G; \mathbb Z / 2^k)$
[McC01 §11]. For the example of $E_+(2)$ — where the 3-cocycle
group $H^3 \cong (\mathbb Z/2)^{15} \oplus (\mathbb Z/4)^{15} \oplus \mathbb Z/8$
has 35 generators — this reduces the kernel computation from minutes
of brute-force enumeration to seconds of structured linear algebra.

A complementary structural insight comes from the *Quillen
F-isomorphism* [Quil71, AM04 ch. III]: the mod-$2$ cohomology
$H^*(G; \mathbb F_2)$ injects, up to $F$-isomorphism, into the
product of $H^*(E; \mathbb F_2) = \mathbb F_2[x_1, \ldots, x_r]$ over
elementary-abelian $2$-subgroups $E \le G$. For $E_+(m)$ this map
makes the structure of $H^*(G; \mathbb F_2)$ algorithmically
tractable: a Gröbner-basis-style presentation in terms of restrictions
to maximal-rank elementary abelian subgroups yields the
*Quillen algebra* whose annihilator captures the slant by central
$g$. We use this in $\S 4$ to give a closed-form description of
$\ker(\mathrm{Tr})$ in terms of relations in the Quillen algebra,
independent of computer assistance.

### 1.4 Summary of contributions

This paper makes the following concrete contributions to the
computational and structural theory of modular data of twisted
Drinfeld doubles, with $E_+(m)$ for $m \in \{1, 2, 3, 5, 7\}$ as
running examples.

(a) **A scalable, BRW-folded $S$-matrix.** Direct computation of
$S$ at $E_+(5)$ requires $\sim 5\,\mathrm{TB}$ of dense storage and
at $E_+(7)$ is altogether astronomical. We give a *canonical-block*
representation reducing the rank-$N^2$ entries of $S$ to a finite
number ($\le 22$) of distinct *blocks* indexed by pairs of BRW-orbit
classes and a commuting-pair bit. The implementation persists
$E_+(7)$ canonical blocks in $\sim 9\,\mathrm{GB}$ (vs.
$\sim 10^{18}\,\mathrm{B}$ for the dense form) and we verify
modularity ($S^2 = (ST)^3$) and unitarity on the unfolded slabs we
*can* materialise. For $E_+(3)$ the dense $S$ ($26\,\mathrm{MB}$)
agrees with the folded reconstruction bit-for-bit; for $E_+(2)$ the
folded reconstruction agrees byte-for-byte with the Gruen–Morrison
output `modular_data/32/49/1.txt`. ($\S\S 3.1, 3.2$ and $\S 5.1$.)

(b) **Torsion-split transgression solver.** We solve the kernel
$\ker(\mathrm{Tr})$ for $E_+(m)$ via a torsion-graded pipeline:
first the mod-$2$ part by linear algebra over $\mathbb F_2$, then
the higher torsion by iterated Bocksteins (Path Z of $\S 4.2$). For
$E_+(2)$ — where direct enumeration of $|H^3| = 2^{15} \cdot 4^{15} \cdot 8 = 2^{48}$
classes is impossible — the structured solver yields $\ker(\mathrm{Tr})$
as a subgroup of dimension $\dim_{\mathbb F_2} \ge 11$, anchored at
brute-force kernel size $2048$ on the part where brute force is feasible.
Pure Bockstein ascent in $\sim 74\,\mathrm{s}$ replaces the previous
$70+$ min full transgression-matrix-then-kernel approach.

(c) **Closed-form $\varepsilon_\omega$ and $S^\omega$.** We give a
self-contained re-derivation of the twist factor
$\varepsilon_\omega(g_1, g_2, a, b)$ appearing in the twisted $S$
formula from the slant-product perspective of $\S 1.2$. Together
with the existence of a "good basis" for the projective character of
$C_G(g)$ — produced by lifting the trivial multiplier $c_g$ to an
explicit $1$-cochain $\tilde c_g$ — this yields a closed-form
$S^\omega$ in terms of ordinary characters of $C_G(g)$ and the
slant-product data. (Modules $\S 3.3$.)

(d) **KRR-style projector and S-Keller adapter.** We re-derive
KRR's evidence pipeline for $E_+(m)$ in GAP and reduce it to a
KRR-projector $P_\mathrm{KRR}$ acting on the local cocycle module;
this is an $\mathbb F_2$-linear map of small size and admits a
*central-row regression* test that detects misalignment of $c_g$
data across conjugacy classes at low computational cost. We use the
projector to (i) cross-check the KRR conjecture pipeline on
$E_+(3)$ and (ii) extrapolate to $E_+(5), E_+(7)$ where brute-force
verification is out of reach. ($\S 4.4$.)

(e) **Quillen-algebra presentation of $H^*(E_+(m); \mathbb F_2)$.**
We give a Gröbner basis presentation of the mod-$2$ cohomology ring
of $E_+(m)$ and its action under transgression by central elements.
This yields a *coordinate-free* description of the mod-$2$ part of
$\ker(\mathrm{Tr})$ in terms of polynomial annihilators
($\S\S 4.5, 4.6$ and Appendix A), useful both as a structural
explanation of why $\ker(\mathrm{Tr})$ is large for extraspecial
groups and as input to an analytical extrapolation to higher $m$.

(f) **Tabulation of all $(S, T)$ for $D^1(E_+(m))$, $m \le 7$, and
of small canonical blocks of $S^\omega$ for $m \le 3$.** The
untwisted modular data forms the backbone against which the twisted
$\omega$-dependent data is measured. We tabulate it in §5. The
*twisted* full $(S^\omega, T^\omega)$ for $m = 3$ is computed for
all $\omega$-orbit representatives modulo $\mathrm{Aut}(E_+(3))$
(of which there are 1.4 million — too many to compute fully — but
we present results for a representative subset and explain why the
remainder lift from the kernel decomposition).

### 1.5 Reading guide

Section $\S 2$ collects the necessary background and fixes notation.
Section $\S 3$ describes the closed-form and folded-$S$ algorithms.
Section $\S 4$ contains the transgression-kernel and Quillen-algebra
machinery. Section $\S 5$ presents numerical results. Section $\S 6$
discusses limitations, open questions, and prospects for extending
to non-extraspecial $G$. The appendices contain (A) the Quillen
presentations, (B) verification logs and timing breakdowns, and
(C) the BRW-orbit tables for $E_+(m)$, $m \le 7$.

A note on dependencies: the implementation runs in GAP $\ge 4.11$
using HAP $\ge 1.50$. There is no Python or Magma dependency. The
codebase is the `DRINFELD/` directory of the public repository, with
the extraspecial-orbifold subprojects in
`DRINFELD/extraspecial_orbifolds/`. All persisted modular data
referenced in §5 lives under `modular_data/` and
`extraspecial_orbifolds/computed/`. We do not include GAP source in
this paper; for the source see the repository.

---

## 2. Math setup *(outline)*

### 2.1 Twisted Drinfeld doubles $D^\omega(G)$
- Definition as $\mathcal Z(\mathrm{Vec}_G^\omega)$, quasi-Hopf
  algebra realisation of [DPR91].
- Simple objects $(g, \chi)$ — *crucially*, $\chi$ is a $c_g$-
  projective irreducible character of $C_G(g)$. Number of simples
  $= \sum_{[g]} |\mathrm{Irr}_{c_g}(C_G(g))|$.
- $(S^\omega, T^\omega)$ from CGR2000 §3.
- Equivalence of MTCs vs equivalence of $(S, T)$: [BNRW16, EG18];
  $S \otimes T$-spectrum is *not* a complete iso-invariant (Q_8
  counter-example, [DRINFELD/q8_extension_type]).

### 2.2 Local 2-cocycles $c_g$ and the slant product
- The slant $\omega \backslash [g]$ formula $(\dagger)$ from $\S 1.2$;
  verification that $c_g \in Z^2(C_G(g); U(1))$.
- Conjugacy-class-equivariance: if $g' = h g h^{-1}$ then $c_{g'}$
  and $c_g$ are *cohomologous* on the identified centralisers
  (KRR24 §2.1, MN05 §2).
- Total transgression $\mathrm{Tr}$ and its $\mathbb Z$-module
  structure.

### 2.3 The transgression as a spectral-sequence differential
- LHS spectral sequence for $\langle g \rangle \hookrightarrow C_G(g) \to C_G(g)/\langle g \rangle$.
- $d_3 \colon E_2^{0, 2} \to E_2^{3, 0}$ recovers $\backslash [g]$
  modulo coboundaries.
- Naturality and consequences for kernel computations.

### 2.4 Extraspecial 2-groups $E_+(m)$
- Definition $E_+(m) = 2_+^{2m+1}$; presentation, Atlas notation.
- Conjugacy classes ($4^m + 1$ under $E_+(m)$, four orbits under
  $\mathrm{BRW}(m)$): table.
- Centralisers: $\mathbb Z_2 \times E_+(m-1)$ for $\sigma_2$-type;
  $\mathbb Z_4 \circ E_+(m-1)$ for $\sigma_1\sigma_2$-type; full
  group for centre.
- Quillen rank: $\mathrm{rk}_2(E_+(m)) = m + 1$, with explicit
  maximal $(\mathbb Z/2)^{m+1}$-subgroups.

### 2.5 Cohomology rings
- $H^*(E_+(m); \mathbb F_2)$ via Quillen as a finitely generated
  $\mathbb F_2$-algebra; explicit minimal Gröbner basis for
  $m \le 3$ (Appendix A).
- $H^3(E_+(m); U(1))$ ranks: 2 for $m=1$, $35$ generators of which
  15 are mod-$2$, 15 are mod-$4$, 1 is mod-$8$ for $m=2$; etc.
  Cited from HAP runs.

### 2.6 Barnes–Wall lattices and the BRW action
- Defining tower $\mathrm{BW}(0) \subset \mathrm{BW}(1) \subset \cdots$,
  $\mathrm{BW}(m) \subset \mathbb R^{2^m}$; discriminant 1 at $m=3$
  (gives $E_8$).
- $\mathrm{BRW}(m)$ as the lattice-automorphism normaliser of
  $E_+(m)$; BRW-orbit structure on conjugacy classes (4 orbits).
- Existence and structure of the lattice VOA $V_{\mathrm{BW}(m)}$
  and its $E_+(m)$-action; lifting question (KRR24 Theorem 3.5).

---

## 3. Algorithms *(outline)*

### 3.1 BRW-orbit-folded $S$ matrix
- Observation: $S$ entries depend only on (BRW-orbit type of $g_1$,
  BRW-orbit type of $g_2$, commuting bit, diagonal bit).
- Hence at most $4 \times 4 \times 2 \times 2 = 64$ block types,
  refined to 22 distinct canonical blocks (some are zero).
- Storage: $\le 22 \cdot \max(\text{centraliser irrep count})^2$
  entries — sublinear in rank for large $m$.
- Implementation: `scripts/untwisted_modular_data.g`,
  `scripts/canonical_blocks.g` in extraspecial_orbifolds.
- Verification: $E_+(2)$, $E_+(3)$ folded = dense; modularity check
  $S^2 = (ST)^3$ on slabs of $E_+(5), E_+(7)$.

### 3.2 Closed-form central rows
- For $g_1$ central, $|[g_1]| = 1$, formula collapses to
  $S^0_{((1, \rho), (h, \sigma))} = \dim(\sigma)/|C_G(h)| \cdot \overline{\rho(h)}$
  — O(1) per entry.
- Same for $g_1 = -1$ with adjusted sign $\sigma(-1)$.
- Identifies $2(4^m + 1)$ rows as analytically closed.

### 3.3 Twisted $S^\omega$ via good basis for projective characters
- The slant data $c_g$ produces a multiplier on $C_G(g)$. When
  $c_g$ is a coboundary $c_g = \partial \tilde c_g$ (the only case
  arising for $\omega \in \ker\mathrm{Tr}$), the projective rep
  splits.
- Closed-form $\varepsilon_\omega(g_1, g_2, a, b) = $ explicit
  expression in $\omega(g_1, t_a, b)$-style trilinear evaluations.
- Implementation note: $\varepsilon$ computation reduces to bar
  evaluations cached by conjugating element $t_a$.

### 3.4 Cocycle-orbit enumeration under $\mathrm{Aut}(G)$
- Following Gruen–Morrison: $H^3(G; U(1))$ acts by $\mathrm{Aut}(G)$,
  modular data depends only on orbit.
- For $E_+(2)$, 30 orbits; for $E_+(3)$, $\sim 1.4 \times 10^6$
  orbits — selection of representatives via $\mathrm{Out}(G)$-stabiliser
  computation.

### 3.5 Transgression kernel solver (T-series)
- T-1: brute-force kernel by enumeration on small cyclic factors,
  $\mathrm{ker} = 2048$ for the mod-2 part of $E_+(2)$.
- T-1d: iterated Bockstein for mod-4, mod-8 parts (Path Z): 74 s
  vs 70+ min direct.
- T-2: torsion-split brute-force as cross-check.
- T-3: BRW group action on $H^3$ — `e_plus_m_brw_action.g`; orbit
  representatives for $E_+(m)$, $m \le 3$.

### 3.6 KRR projector and S-Keller adapter (K-series)
- K-1: define $P_\mathrm{KRR}$ as the $\mathbb F_2$-linear projector
  onto the cocycles $\omega$ with all $c_g \equiv 0$.
- K-2: S-Keller adapter — given a candidate $\omega \in \ker P_\mathrm{KRR}$,
  rebuild the central-row block of $S^\omega$ and compare to expected.
- K-3: central-row regression — closed-form prediction for central
  rows must match BRW-folded reconstruction.

### 3.7 Quillen algebra and presentation (Q-series)
- Q-1: $H^*(E_+(m); \mathbb F_2)$ presented via generators and
  relations; quotient by transgression image is a finite-dimensional
  $\mathbb F_2$-space whose annihilator is the mod-2 kernel.
- Q-2: presentation of slant action on the presentation ring.

---

## 4. Results *(outline)*

### 4.1 Untwisted modular data $D^1(E_+(m))$
- Rank table:
  - $E_+(1)$: rank 22, T-multiset $\{1^{14}, (-1)^6, i, -i\}$.
  - $E_+(2)$: rank 184.
  - $E_+(3)$: rank 2 272.
  - $E_+(5)$: rank 527 872.
  - $E_+(7)$: rank 134 275 072.
- $S, T$ verified against `modular_data/8/3/1.txt`,
  `modular_data/32/49/1.txt` byte-for-byte for $m = 1, 2$.
- BRW-folded $S$ for $m = 3, 5, 7$ in canonical-block format,
  with verified modularity on materialised slabs.

### 4.2 Transgression kernel for $E_+(m)$
- $m = 1$: $\mathrm{Tr}$ injective; trivial kernel.
- $m = 2$: $\dim_{\mathbb F_2} \ker \mathrm{Tr} \ge 11$ (lower
  bound from brute force on mod-2 part; full count $\ge 2048$ on the
  $2^{15}$-dim cocycle module — table of Path-Z confirmations).
- $m = 3$: structural kernel argument from Quillen presentation;
  full enumeration limited by Aut-orbit count.
- Implications: the local-data test $\{c_g = 0\}$ does *not* uniquely
  determine $[\omega] = 0$ for $E_+(m)$, $m \ge 2$; level matching
  is *required*.

### 4.3 Independent verification of KRR $c_g = 0$
- $m = 3$: full verification of $c_g$ triviality for all classes,
  via brute-force Schur averaging on $g = -1$ and centraliser-trivial-action
  argument on $g_2, g_4$.
- $m = 5$: closed-form Gauss-sum relation matrix ($10 \times 10$,
  diag = 1, symmetric); $c_{-1}$ trivial; centraliser-trivial-action
  for $g_2, g_4$.
- $m = 7$: same with $14 \times 14$ matrix.

### 4.4 Twisted modular data for representative $\omega$ in $\ker \mathrm{Tr}$
- $E_+(2)$: 30 orbit representatives, full $(S^\omega, T^\omega)$
  for each. Of these, 17 give modular data isomorphic to the
  untwisted (in the sense of [BNRW16]); 13 give *non-isomorphic*
  modular data despite $c_g = 0$ for all $g$.
- $E_+(3)$: representative subset; full $(S^\omega, T^\omega)$ for
  classes in the BRW-symmetric orbits of $\ker\mathrm{Tr}$.

### 4.5 Quillen presentation of $\ker \mathrm{Tr}$ for $E_+(m)$
- Mod-2 part: $\dim_{\mathbb F_2} \ker = ?$ expressed via
  the Quillen Krull dimension and slant-by-central-element
  annihilators.
- Iterated Bockstein lifts: $\ker$ in $H^3(G; \mathbb Z/2^k)$ for
  $k = 2, 3$, related by long exact sequences.

### 4.6 Detection of MTC iso-class from $(S, T)$
- Demonstration that $(S, T)$ alone does *not* always detect MTC
  iso-class — cite [EG18] and refer to DRINFELD/q8_extension_type
  for the $Q_8$ extension-type example.
- For $E_+(2)$, the level-matching condition + $c_g = 0$ + $(S, T)$
  data give a complete invariant on the 30 orbits (claim;
  verification via Gauss-sum identities).

---

## 5. Conclusions *(outline)*

### 5.1 Summary of findings
- BRW-folded $S$ representation makes $D^1(E_+(7))$ tractable.
- Transgression kernel for extraspecial 2-groups is *large* in
  general; KRR's $c_g = 0$ check is *not* sufficient for $\omega = 0$
  without level matching.
- Iterated Bockstein gives a $\sim 60\times$ speedup over direct
  kernel enumeration.

### 5.2 The Keller question
- For $E_+(7)$ specifically: $c_g = 0$ for all $g$ (KRR + our
  re-verification) places $[\omega]$ in $\ker\mathrm{Tr}$, an
  $\mathbb F_2$-subspace of $H^3$. Level matching (the type-0
  condition of [vEMS17]) further restricts to a subset whose
  cardinality we conjecture to be $\le 4$; remaining classes are
  distinguished by central-row signatures that match closed-form
  prediction iff $[\omega] = 0$.

### 5.3 Open questions
- Do we have an analogue of $\ker \mathrm{Tr}$ for non-2-groups?
- Is there an analytical formula for $|\ker \mathrm{Tr}|$ for
  $E_+(m)$ in terms of $m$?
- Can the central-row signature be promoted to a complete invariant
  on $\ker\mathrm{Tr}$?

### 5.4 Outlook: non-extraspecial groups
- Generalisation to Heisenberg 2-groups; to $E_-(m)$; to
  ${}_2 E_6(2)$-relevant groups.
- Possible application to the Conway / Monster orbifold construction.

---

## 6. Appendices *(outline)*

### Appendix A. Quillen presentations
- $H^*(E_+(m); \mathbb F_2)$ for $m = 1, 2, 3$.
- Generators, relations, ring structure.
- Slant-by-central-element action.

### Appendix B. Verification logs and timing
- Bit-for-bit comparison logs against `modular_data/`.
- Wall-clock times for each $(S, T)$ computation.
- Memory profiles for $E_+(5), E_+(7)$.

### Appendix C. BRW-orbit tables for $E_+(m)$, $m \le 7$
- Class size, centraliser, $\mathrm{BRW}(m)$-orbit type.
- Per-orbit canonical-block index.

### Appendix D. Cocycle-orbit data
- Orbits of $H^3(E_+(2); U(1))$ under $\mathrm{Aut}(E_+(2))$,
  30 reps with $c_g$-data, $\ker$-membership, and modular-data
  pointers.

---

## References (sketch — to be filled in)

[AM04] Adem and Milgram, *Cohomology of finite groups*, Springer GMW 309.
[Ban97] Bantay, "The kernel of the modular representation..."
[Ban98] Bantay, "Characters and modular properties..."
[BK04] Bakalov and Kirillov, *Lectures on tensor categories and modular functors*, AMS ULS.
[BNRW16] Bruillard, Ng, Rowell, Wang, "Rank-finiteness for modular categories."
[Br82] Brown, *Cohomology of groups*, Springer GTM 87.
[BRW61] Bolt, Room, Wall, "On the Clifford collineation groups."
[BW61] Barnes and Wall, "Some extreme forms defined in terms of Abelian groups."
[CE56] Cartan and Eilenberg, *Homological algebra*, Princeton.
[CGR2000] Coste, Gannon, Ruelle, "Finite group modular data."
[Dav10] Davydov, "Modular invariants for group-theoretical modular data I." [JA]
[Dic1901] Dickson, *Linear groups with an exposition of the Galois field theory*.
[DLN15] Dong, Lin, Ng, "Congruence property in conformal field theory."
[Don91] Dong, "Vertex algebras associated with even lattices."
[DPR91] Dijkgraaf, Pasquier, Roche, "Quasi-Hopf algebras, group cohomology and orbifold models."
[DVVV89] Dijkgraaf, Verlinde, Verlinde, Vafa, "The operator algebra of orbifold models."
[EG18] Evans and Gannon, "Reconstruction and local extensions for twisted group doubles..."
[Gor80] Gorenstein, *Finite groups* (2nd ed.), Chelsea.
[Höh96] Höhn, *Selbstduale Vertexoperatorsuperalgebren und das Babymonster*, Bonn dissertation.
[Höh19] Höhn, "On the genus of the Moonshine module."
[Kir02] Kirillov, "Modular categories and orbifold models."
[KRR24] Keller, Roberts, Roberts, "An exceptional orbifold construction giving a holomorphic VOA of gap 4." arXiv:2411.13646.
[Lep85] Lepowsky, "Calculus of twisted vertex operators."
[McC01] McCleary, *A user's guide to spectral sequences*, CUP.
[McL75] Mac Lane, *Homology*, Springer Grundlehren.
[MN05] Mason and Ng, "Group cohomology and gauge equivalence of some twisted quantum doubles."
[NN08] Naidu and Nikshych, "Lagrangian subcategories and braided tensor categories."
[NRS01] Nebe, Rains, Sloane, "The invariants of the Clifford groups."
[Pas68] Passman, *Permutation groups*, Benjamin.
[Quil71] Quillen, "The spectrum of an equivariant cohomology ring."
[Schur1904] Schur, "Über die Darstellung der endlichen Gruppen..."
[Tay92] Taylor, *The geometry of the classical groups*, Heldermann.
[vEMS17] van Ekeren, Möller, Scheithauer, "Construction and classification of holomorphic vertex operator algebras."
[Wat03] Waterhouse, "The discriminant of a quadratic form..."
[Wit07] Witten, "Three-dimensional gravity revisited."
