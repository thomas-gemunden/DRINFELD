# Mod(D¹(E_+(m))) and the Keller–Roberts–Roberts orbifold conjecture

This directory records two intertwined investigations:

1. A complete Magma → GAP port of the
   [Keller–Roberts–Roberts](https://arxiv.org/abs/2411.13646)
   supplement, reproducing in GAP their evidence that the Barnes–Wall
   lattice VOA orbifold by $E_+(m)$ ($m = 3, 5, 7$) has trivial
   2-cocycles $c_g$ on each $g$-twisted module — necessary conditions
   for the 't Hooft anomaly $\omega \in H^3(E_+(m); U(1))$ to vanish.

2. A scalable computation of the *untwisted* modular data of
   $\mathrm{Mod}(D^1(E_+(m)))$ — the modular tensor category Keller
   et al.\ conjecture is also the modular data of their orbifold
   construction — built directly from GAP's character tables and
   bypassing the cohomology pipeline of Gruen–Morrison.

Together these give an end-to-end reproducible target: the modular
data of $\mathrm{Mod}(D^1(E_+(m)))$ as it would be if the conjecture
holds. The remaining open question — which we discuss in detail in
[`strategy_local_discriminators.md`](strategy_local_discriminators.md)
— is whether the verified $c_g = 0$ for all $g$ implies $\omega = 0$,
or only that $\omega$ lies in the kernel of a specific cohomology
transgression.

## 1. Background and motivation

[Keller, Roberts and Roberts, arXiv:2411.13646](https://arxiv.org/abs/2411.13646)
[KRR24] construct an orbifold of the Barnes–Wall lattice VOA
$V_L$ in dimension $d = 128$ by the extraspecial 2-group
$E_+(7) \cong 2_+^{15}$ acting as lattice automorphisms. Granting
their conjecture that $\omega \in H^3(E_+(7); U(1))$ vanishes, the
orbifold admits a holomorphic extension $V_L^{\mathrm{orb}(E_+(7))}$
which is a holomorphic CFT of central charge $c = 128$ and gap $4$ —
the first such example known with gap larger than $2$ (cf.
Höhn [Höh96, Höh19], Witten [Wit07]).

Their evidence for $\omega = 0$ has two parts:

1. **Level matching** (the *type-0* condition of van Ekeren–Möller–
   Scheithauer [vEMS17]): the restriction of $\omega$ to every cyclic
   subgroup $\langle g\rangle$ is trivial. For $E_+(7)$ this is read
   off from the integer-valued conformal weights $\rho_g$ of the
   $g$-twisted modules of the lattice VOA (KRR24, Prop. 3.1).
2. **Triviality of the multipliers $c_g$**: for every $g$, the
   2-cocycle $c_g$ of the projective representation
   $\phi_g \colon C_G(g) \to \mathrm{PGL}(W_g)$ on the $g$-twisted
   module is trivial as a class in $H^2(C_G(g); U(1))$. They verify
   this for $m = 3, 5, 7$ via Schur averaging on the *defect
   representation* $\Omega_0$ of $N = L_g^\perp / L(1-g)$.

Both conditions are *necessary* but, in general, not *sufficient*
for $\omega = 0$ in $H^3(E_+(m); U(1))$.

## 2. Mathematical setup

### 2.1 Untwisted and twisted Drinfeld doubles

For a finite group $G$, the **untwisted Drinfeld double** $D(G)$ is
the (Hopf algebra associated to the) modular tensor category
$\mathcal Z(\mathrm{Vec}_G) \cong D(G)\text{-mod}$, where
$\mathrm{Vec}_G$ is the pointed fusion category of $G$-graded vector
spaces. Drinfeld constructed $\mathcal Z(\mathcal C)$ as a "centre"
in [Dr89]; for the special case $\mathcal C = \mathrm{Vec}_G$ this
reproduces the classical group-theoretic description.

Given a 3-cocycle $\omega \in Z^3(G; U(1))$, one twists the
associativity of $\mathrm{Vec}_G$ to a *quasi-fusion* category
$\mathrm{Vec}_G^\omega$. Its centre $D^\omega(G) := \mathcal Z(\mathrm{Vec}_G^\omega)$
is a modular tensor category whose isomorphism class depends only on
$[\omega] \in H^3(G; U(1))$. The original physical construction is
due to **Dijkgraaf–Pasquier–Roche** [DPR91], who gave an explicit
quasi-Hopf algebra realising $D^\omega(G)$ and computed its
representation theory. Modern accounts are in
**Coste–Gannon–Ruelle** [CGR2000] and **Bantay** [Ban97, Ban98].

### 2.2 Simple objects and modular data of $D^\omega(G)$

The simple objects of $D^\omega(G)$ are pairs $(g, \chi)$ where:

- $g$ ranges over conjugacy class representatives of $G$;
- $\chi \in \mathrm{Irr}_{c_g}(C_G(g))$ is an irreducible projective
  character of the centraliser, with multiplier $c_g$ — a
  $U(1)$-valued 2-cocycle on $C_G(g)$ given explicitly by

$$
c_g(h_1, h_2) \;=\; \omega(g, h_1, h_2) \,+\, \omega(h_1, h_2, g) \,-\, \omega(h_1, g, h_2),
\qquad h_1, h_2 \in C_G(g) \quad
[\text{KRR24 eq.~2.1.3; CGR2000 eq.~2.7}].
$$

The right-hand side is well-defined because $h_1, h_2$ commute with
$g$, so the standard cocycle identity for $\omega$ collapses to the
above.

The modular data $(S, T)$ of $D^\omega(G)$ is determined by the same
group-cohomology data:

$$
T_{(g, \chi)} \;=\; \frac{\chi(g)}{\dim \chi} \cdot e^{2\pi i \rho_g}
\qquad
(\text{up to normalisation; } \rho_g \text{ encodes the conformal
weight when the MTC is Mod}(V_L^G))
$$

and

$$
S_{(g_1, \chi_1), (g_2, \chi_2)}
\;=\; \tfrac{1}{|G|}
\sum_{\substack{a \in [g_1],\; b \in [g_2] \\ ab = ba}}
\varepsilon_\omega(g_1, g_2, a, b) \cdot \overline{\chi_1(t_a^{-1} b\, t_a)} \cdot
\overline{\chi_2(s_b^{-1} a\, s_b)},
$$

where $t_a, s_b \in G$ satisfy $t_a g_1 t_a^{-1} = a$ and
$s_b g_2 s_b^{-1} = b$, the bar denotes complex conjugation, and
$\varepsilon_\omega \in U(1)$ is a phase factor determined by $\omega$
(it is $1$ for $\omega = 1$). For untwisted $D(G) = D^1(G)$, the
$\chi_i$ are *ordinary* characters and $\varepsilon \equiv 1$, giving
the classical Bantay/CGR formula

$$
\boxed{\;
T_{(g, \chi)} \;=\; \chi(g)/\dim \chi,
\qquad
S^{0}_{(g_1, \chi_1), (g_2, \chi_2)}
\;=\; \tfrac{1}{|G|}
\sum_{\substack{a \in [g_1],\; b \in [g_2] \\ ab = ba}}
\overline{\chi_1(t_a^{-1} b\, t_a)} \cdot
\overline{\chi_2(s_b^{-1} a\, s_b)} \;
}
\quad [\text{Ban97, CGR2000, MN05}].
$$

### 2.3 The transgression $\mathrm{Tr}\colon H^3(G) \to \bigoplus H^2(C_G(g))$

Coboundary changes of $\omega$ change $c_g$ only by 2-coboundaries on
$C_G(g)$. So the assignment $\omega \mapsto c_g$ descends to a
homomorphism of finite abelian groups

$$
\mathrm{Tr}_g \colon H^3(G; U(1)) \;\longrightarrow\; H^2(C_G(g); U(1)),
$$

and assembling these over all conjugacy classes gives the **total
transgression**

$$
\mathrm{Tr} \colon H^3(G; U(1)) \;\longrightarrow\; \bigoplus_{[g]} H^2(C_G(g); U(1)),
\qquad [\omega] \mapsto \bigl([c_g]\bigr)_{[g]}.
$$

The map $\mathrm{Tr}_g$ factors as

$$
H^3(G) \;\xrightarrow{\mathrm{res}_g}\; H^3(C_G(g)) \;\xrightarrow{\,\backslash [g]\,}\; H^2(C_G(g))
$$

where $\mathrm{res}_g$ is the cohomological restriction induced by
inclusion $C_G(g) \hookrightarrow G$ and $\backslash [g]$ is the
**slant product** with the canonical 1-cycle
$[g] \in H_1(C_G(g); \mathbb Z)$. The slant product is well-defined
because $g \in Z(C_G(g))$. See **Brown** [Br82, Chapter V.3] or
**Mac Lane** [McL75, Chapter VIII] for the standard treatment.

The terminology *transgression* is consistent with the spectral-sequence
usage: for the central extension $\langle g \rangle \hookrightarrow
C_G(g) \twoheadrightarrow C_G(g)/\langle g \rangle$, the
Lyndon–Hochschild–Serre differential $d_3 \colon E_2^{0,2} \to E_2^{3,0}$
recovers, on the classes detected by $g$, the slant of $\omega$ by
$[g]$ at the cochain level [AM04, §III.1; NN08, §3]. The closed-form
expression for $c_g$ is precisely this slant on the inhomogeneous bar
resolution; the alternating signs come from the simplicial sign rule
applied to the boundary of the 1-simplex represented by $g$.

The Keller–Roberts–Roberts evidence consists of verifying
$c_g = 0 \in H^2(C_G(g); U(1))$ for every conjugacy class $[g]$ —
i.e. $\mathrm{Tr}([\omega]) = 0$. Their conjecture is
$[\omega] = 0 \in H^3(G; U(1))$. The question

$$
\boxed{\quad c_g = 0 \;\forall g \;\stackrel{?}{\Longrightarrow}\; \omega = 0 \quad}
\qquad\text{is exactly}\qquad
\boxed{\quad \ker \mathrm{Tr} \stackrel{?}{=} 0. \quad}
$$

If $\ker\mathrm{Tr} = 0$, the conjecture follows automatically from
the verified $c_g = 0$. If $\ker\mathrm{Tr} \ne 0$, additional
necessary conditions (e.g. level matching) restrict $[\omega]$
further, but a complete proof needs more.

### 2.4 The Barnes–Wall / extraspecial geometry

For $m \ge 1$, the Barnes–Wall lattice $\mathrm{BW}(m)$ in dimension
$2^m$ has automorphism group $\mathrm{BRW}(m)$ which contains the
extraspecial 2-group $E_+(m) \cong 2_+^{2m+1}$ as a subgroup
[NRS01, BW61]. $E_+(m)$ acts on the lattice VOA $V_{\mathrm{BW}(m)}$
through this lattice action lifted to $V_L$
[Don91, Lep85, KRR24 §3.3]. The lifting is non-trivial in general,
but Keller–Roberts–Roberts show (Theorem 3.5) that the lift of $E_+(m)$
remains isomorphic to $E_+(m)$ (no order-doubling) for $m \ge 3$.

Conjugacy classes of $E_+(m)$ under $\mathrm{BRW}(m)$ fall into 4
types (KRR24 Prop. 3.1):

| representative | order | size in $E_+(m)$ | centraliser |
|---|---|---|---|
| $1$ | $1$ | $1$ | $E_+(m)$ |
| $-1$ | $2$ | $1$ | $E_+(m)$ |
| $\sigma_2 \otimes I^{\otimes (m-1)}$ | $2$ | $2$ | $\mathbb Z_2 \times E_+(m-1)$ |
| $\sigma_1\sigma_2 \otimes I^{\otimes (m-1)}$ | $4$ | $2$ | $\mathbb Z_4 \circ E_+(m-1)$ |

Under $E_+(m)$-conjugation the non-central classes split into class
size 2 each (one each for the element and its negative), giving
$4^m + 1$ conjugacy classes total. The two centralisers of non-central
elements have the same order $|G|/2 = 2^{2m}$ and the same number of
irreducible characters $|\mathrm{Irr}| = 2 \cdot 4^{m-1} + 2$.

## 3. Part I — Magma → GAP port (paper's own pipeline)

Status of the port (every section verified end-to-end):

| Magma section | Lines | Our GAP file | Verified |
|---|---:|---|---|
| 2: $E(m)$, $\mathrm{BRW}(m)$, $C(m)$ | ~170 | `scripts/em_construction.g` | $E_+(m)$ identifies with `ExtraspecialGroup(2^{2m+1}, "+")` for $m=1,2,3$ |
| 3: $\mathrm{BBW}_{2^m}$, $\mathrm{BW}_{2^m}$ | ~60 | `scripts/bw_lattice.g` | Discriminant of $\mathrm{BW}(3) = 1$ (so it is $E_8$); shortest squared length $= 2^{\lfloor m/2 \rfloor}$ |
| 4: twisted group algebra, $u_g$ | ~150 | `scripts/twisted_group_algebra.g` | Theorem 3.5 of [KRR24]: 0 errors across 64 ($m=2$), 288 ($m=3$), 1024 ($m=4$) checks |
| 5: $\mathbb F_2$ quadratic forms | ~170 | `scripts/qforms_f2.g` | All 7 hand-built test cases pass |
| 6 brute-force core | ~250 | `scripts/defect_rep_minus_id.g` | $m=3$: $T_{a,r}^2 = 256\cdot I$, $[T_{a,r}, T_{b,s}] = 0$, trace distribution on $(\mathbb Z/2)^6$ matches paper exactly |
| 6 closed-form Gauss sum | ~600 | `scripts/defect_rep_minus_id_optim.g` | $m=3$ single-entry cross-check: 1536 / 1536 entries agree with brute force; $m=3$ product cross-check: 9216 / 9216 entries agree with direct matrix product |
| 7: other conjugacy classes | ~100 | `scripts/defect_rep_other.g` | For $m=3$ and $m=5$, every element of $C_{E_+(m)}(g)$ acts trivially on $N_\theta$ for both $g_2 = \Sigma_{1,1}$ and $g_4 = \Sigma_{1,1}\Sigma_{1,2}$ |

### 3.1 Independent reproduction of $c_g = 0$

The substantive paper claims for all three non-trivial $m$:

- $m = 3$: full $c_g$ triviality for *every* conjugacy class
  ($g = -1$ via brute-force Schur averaging; $g_2$ and $g_4$ via the
  centraliser-trivial-action argument).
- $m = 5$: $c_{-1}$ triviality via the closed-form Gauss-sum
  relation matrix (10×10, diag = 1, symmetric, so $T_{a,r}^2$ =
  scalar·I and $[T_{a,r}, T_{b,s}] = 0$, hence $c_{-1}$ trivial).
  $c_{g_2}, c_{g_4}$ triviality from centraliser-trivial-action.
- $m = 7$: same for $c_{-1}$ via the 14×14 closed-form relation
  matrix.

The literal entries of our $m=5, 7$ relation matrices differ from
the published eq (4.4.9), (4.4.10) of [KRR24] because our
`SymplecticBasisF2` and Magma's `WittDecomposition` pick different
symplectic bases of $N = L/2L$. The abstract intertwiner
representations are the same; the trace distribution on
$(\mathbb Z/2)^{2m}$ is identical at $m=3$ (verified) and the
substantive properties (diag = 1, symmetric) hold at $m=5,7$.

### 3.2 Mathematical content of the Schur-averaging algorithm

The defect representation $\rho \colon N \to \mathrm{GL}(\Omega_0)$ is
the unique irreducible projective representation of
$N := L_g^\perp / L(1-g)$ with skew-form $C(\alpha, \beta) = (-1)^{\langle \alpha g \mid \beta \rangle}$
and dimension $\sqrt{|N|}$ ([Dav10, Theorem]; [KRR24 §2.3];
[Lepowsky's lattice construction Lep85, BK04]). Here $L$ is the
underlying lattice and the inner product is induced from the lattice
form.

For $h$ in the centraliser of the lift $\hat g$, the composition
$\rho \circ h$ is again a projective rep of $N$ with the same skew
form, hence projectively equivalent to $\rho$ via an intertwiner
$T_h \in \mathrm{GL}(\Omega_0)$:

$$
T_h \, \rho(h(\alpha))\, T_h^{-1} \;=\; B_h(\alpha)\, \rho(\alpha) \quad \forall \alpha \in N.
$$

The $T_h$ are constructed via **Schur averaging** (Schur's lemma
applied at the projective level — see [Schur1904], [Pas68]):

$$
T_h \;=\; \frac{1}{\sqrt{|N|}} \sum_{a \in N} (-1)^{\Phi_h(a)} \rho(a),
$$

for an explicit quadratic form $\Phi_h$ on $N$ over $\mathbb F_2$
([KRR24 §4.1; eq.~(4.1.5)]). This sum is a Gauss sum and admits a
closed-form evaluation in terms of the Witt decomposition of $\Phi_h$
([Dic1901]; [Tay92, Chapter 11]; [Wat03]). The closed form lets us
compute single matrix entries $(T_h)_{c,d}$ in $O(\dim_{\mathbb F_2} N)$
work without touching the $\sqrt{|N|}$-dim matrix as a whole — this
is exactly the optimisation pipeline KRR ported in their Magma code
and we mirror in `defect_rep_minus_id_optim.g`.

The substantive property $T_h^2 = \lambda \cdot I$ and
$T_{h_1} T_{h_2} = \mu T_{h_2} T_{h_1}$ (both *scalar*, not just
projective) certifies that the cocycle $c_g$ representing the
$\mathrm{PGL}$-class of $\rho$ on $\hat g$'s centraliser is trivial as
a class in $H^2(C_{E_+(m)}(g); U(1))$.

## 4. Part II — Direct untwisted modular data of $\mathrm{Mod}(D^1(E_+(m)))$

If the Keller conjecture holds, the resulting modular tensor category
is *exactly* $\mathrm{Mod}(D^1(E_+(m)))$ — the Drinfeld double of the
*untwisted* group algebra. That category has well-defined modular
data $(S, T)$ depending only on $E_+(m)$, computable via the closed
form (§2.2) without needing the cocycle ω at all.

### 4.1 Library

`scripts/untwisted_modular_data.g` computes $(S, T)$ for any finite
group $G$ directly from `ConjugacyClasses(G)`, `Centralizer(G, ·)`
and `CharacterTable(·)`. Bypasses Gruen–Morrison's pipeline (no
`ResolutionFiniteGroup`, no `IsomorphismFpGroup` of centralisers, no
projective-character extension): the trivial cocycle case admits the
direct formula of §2.2.

For $E_+(m)$ each conjugacy class has size $\le 2$, so the inner sum
in the $S$ formula has at most 4 terms — the cost is in the SHEER
NUMBER of entries.

### 4.2 Per-sector / analytic prediction

`scripts/predict_e_plus_m.g` derives the rank and T-eigenvalue
multiset analytically from the centraliser character tables. For
all $m$:

| $m$ | $\lvert G \rvert$ | rank | T-multiset |
|---|---:|---:|---|
| 1 | 8 | 22 | $\{1^{14}, (-1)^6, i, -i\}$ |
| 2 | 32 | 184 | $\{1^{102}, (-1)^{70}, i^6, (-i)^6\}$ |
| 3 | 128 | 2 272 | $\{1^{1172}, (-1)^{1044}, i^{28}, (-i)^{28}\}$ |
| 5 | 2 048 | 527 872 | $\{1^{264464}, (-1)^{262416}, i^{496}, (-i)^{496}\}$ |
| 7 | 32 768 | 134 275 072 | $\{1^{67145792}, (-1)^{67113024}, i^{8128}, (-i)^{8128}\}$ |

The same predictor matches the precomputed Gruen modular data for
$E_+(1)$ (`modular_data/8/3/1.txt`) and $E_+(2)$
(`modular_data/32/49/1.txt`) byte-for-byte.

The rank formula is

$$
\mathrm{rank}\bigl(\mathrm{Mod}(D^1(E_+(m)))\bigr)
\;=\; 2(4^m + 1) + (4^m - 1) \cdot (2 \cdot 4^{m-1} + 2),
$$

reflecting the conjugacy class decomposition of §2.4 and the fact
$|\mathrm{Irr}(\mathbb Z_2 \times E_+(m-1))| = |\mathrm{Irr}(\mathbb Z_4 \circ E_+(m-1))| = 2 \cdot 4^{m-1} + 2$
(both centralisers have $|G|/2$ elements with the same character
table size; this reflects a coincidence specific to extraspecial
2-groups, see [Gor80, Theorem 5.3.6]).

### 4.3 Closed-form central rows

For any $m$, the rows associated to the central elements admit a
closed form (`scripts/closed_form_central.g`):

$$
\boxed{\;S^0_{((1, \rho), (h, \sigma))} = \frac{\dim \sigma}{|C_G(h)|}\,\overline{\rho(h)}\;}
\qquad
\boxed{\;S^0_{((-1, \rho), (h, \sigma))} = \frac{\sigma(-1)}{|C_G(h)|}\,\overline{\rho(h)}\;}
$$

(derived in §2.2 by specialising to $g_1$ central and noting
$|[g_1]| = 1$, $\tau_{g_1}$ trivial). Each entry is **O(1)** given
the character tables, so the whole $2(4^m + 1)$ central rows are
computable per-row in O(rank) without iterating over commuting pairs.
Verified against the direct `ComputeSBlock` on $E_+(2)$: 1472 / 1472
entries agree (8 rows × 184 columns).

### 4.4 Computed data on disk

Under `extraspecial_orbifolds/computed/`:

| Group | Output | Wall | Status |
|---|---|---|---|
| $E_+(2)$ | full $(S, T)$, rank 184 | 0.36 s | rerun-on-demand; matches `modular_data/32/49/1.txt` byte-for-byte |
| $E_+(3)$ | full $(S, T)$, rank 2272, $S$ 26 MB; 22 canonical $S$-blocks (337 KB) | 7 m 30 s dense; 0.3 s structural | persisted to `E_plus_3/{S, T, manifest}.g` and `E_plus_3/structural/canonical_blocks.g` |
| $E_+(5)$ | $T$ only (full $S$ would be ~5 TB), 1025 sector chunks; 22 canonical $S$-blocks (94 MB) | 100 s $T$; 26 s structural $S$ | persisted to `E_plus_5/T/sector_*.g` and `E_plus_5/structural/canonical_blocks.g` |
| $E_+(7)$ | $T$ multiset analytical (full vector astronomical); 9 canonical non-zero $S$-blocks (8.7 GB) + 3 closed-form O(1) blocks + 6 zero blocks | $T$: ~ms; $S$ blocks: ~16 min | persisted to `E_plus_7/manifest.g` and `E_plus_7/structural/{manifest.g, canonical_blocks.g}` (the 8.7 GB blocks file is gitignored — re-create via `run_e_plus_7_canonical.g`) |

For each completed instance: rank matches the analytical prediction,
T-multiset matches exactly, modularity $S^2 = (ST)^3$ verified
exactly (in $E_+(3)$), unitarity $\sum_a \lvert S_{ia}\rvert^2 = 1$
verified on sample rows.

### 4.5 BRW-orbit-folded structural S representation (Phase E_BRW)

For $m \in \{3, 5, 7\}$ the dense $S$ is too big to store at $m \ge 5$.
A drastically more compact representation comes from observing that
$E_+(m)$ is an index-(power-of-2) subgroup of its normaliser
$\mathrm{BRW}(m)$ in $O(2^m, \mathbb R)$, and conjugacy classes of
$E_+(m)$ under $\mathrm{BRW}(m)$ form just **four orbits** (KRR Prop
3.1): $\{1\}$, $\{-1\}$, $\sigma_2$-type, $\sigma_1\sigma_2$-type.
The S-formula entries depend only on:

1. The pair of BRW-orbit types of the two arguments, $(\mathrm{type}_i, \mathrm{type}_j)$;
2. Whether the class representatives commute, $\omega(\bar g_i, \bar g_j) \in \{0, 1\}$ in $E_+(m)/Z \cong (\mathbb F_2)^{2m}$;
3. Whether the pair is "diagonal" $i = j$ as $E_+(m)$-classes or off-diagonal $i \neq j$.

So $S$ has, modulo per-class irrep relabellings, only **22 distinct
canonical blocks** (more precisely: 22 refined groups, of which 6 are
the all-zero non-commuting blocks that don't need materialisation).
This is independent of $m$.

#### Canonical blocks computed

`scripts/compute_canonical_blocks.g` computes the 22 canonical blocks
by direct evaluation of `ComputeSBlock` at one canonical pair per
refined group. Cross-checked byte-for-byte for $m = 3$ against the
dense $S$ already on disk: every canonical block matches the
corresponding submatrix of the dense $S$.

For $m = 5, 7$ no dense $S$ exists; this is the only way we get $S$
data at those orders.

| $m$ | wall | non-zero canonical blocks | structural storage | dense (hypothetical) |
|---|---:|---:|---:|---:|
| 3 | 0.3 s | 22 (16 non-zero + 6 zero) | 337 KB | 26 MB |
| 5 | 25.8 s | 22 | 94 MB | ~5 TB |
| 7 | ~16 min | 9 of 22 (3 fully-central are O(1) closed-form, 6 zero) | 8.7 GB | ~3 · 10¹⁷ B |

Compression ratios: ~80× ($m=3$), ~5 · 10⁴× ($m=5$),
~3.5 · 10⁷× ($m=7$).

#### How the $E_+(7)$ blocks were computed despite the OOM on `ConjugacyClasses`

For $E_+(7)$ the OOM-on-`ConjugacyClasses(E_+(7))` (under any heap
budget tested, including 60 GB) is bypassed in three ways:

1. **`Centralizer(E_+(7), x)`** for non-central $x$ has order
   $16384$, and `CharacterTable` on it works comfortably (~40 s) —
   so we get full $\mathrm{Irr}(C_x)$ data for non-central canonical
   classes via standard GAP.
2. **$\mathrm{Irr}(E_+(7))$** itself is bypassed analytically: the
   16384 linear characters factor through $E_+(7)/Z = (\mathbb F_2)^{14}$
   (computable via PC exponent vectors with `ExponentsOfPcElement`),
   plus 1 faithful character of dim $2^7 = 128$ with values
   $128, -128, 0$ at $1, z$, non-central respectively. This is used
   for central sector evaluations without any GAP `CharacterTable`
   call on $E_+(7)$.
3. **Closed-form Phase-D formula** for (central, non-central) blocks:
   $S_{((1, \rho), (h, \sigma))} = \dim \sigma / |C_G(h)| \cdot \overline{\rho(h)}$
   (and the analogous form for $-1$). 4 such canonical blocks
   computed in 13–21 s each.
4. **Class-element-to-class-index dictionary** (`NewDictionary`) on each
   centraliser, eliminating the $O(|C|)$ per-evaluation cost in the
   inner loop of `ComputeSBlock`. Without this, naive class-membership
   checks dominated; with it, non-central blocks compute in 130–150 s.

#### What's NOT in the canonical-block representation alone

To reconstruct any specific block $S(i, j)$ (for non-canonical
$(i, j)$) from the canonical block of its refined group, we would need
**per-class irrep relabellings $\sigma_i$**. We attempted to compute
these by row-matching `block(canonical, anchor)` against `block(i, anchor)`
using the dense $S$ for $m = 3$. The naive form fails empirically
(61/61 non-canonical $E_+(3)$ classes failed) because

> $\mathrm{BRW}(m)$ is the **outer** normaliser of $E_+(m)$: its
> conjugation by $x_i \in \mathrm{BRW}(m)$ permutes $E_+(m)$-conjugacy
> classes (different from the inner ones), and hence permutes
> $\mathrm{Irr}(E_+(m))$. So when comparing
> `block(canonical, j_anchor)` to `block(i, j_anchor)`, the column
> axis (indexed by $\mathrm{Irr}(C_{j_{\mathrm{anchor}}})$) also
> permutes — a row-only relabelling does not suffice.

To recover the full per-class machinery we would need to construct
$\mathrm{BRW}(m)$ explicitly as a matrix subgroup of $O(2^m, \mathbb R)$
following KRR Section 3.1 (using $H$, $D$, $\mathrm{GL}(m, 2)$,
plus the $\sigma$ generators) and use `RepresentativeAction(\mathrm{BRW}(m), g_{\mathrm{canonical}}, g_i)`
to find $x_i$. Then $x_i$'s induced permutations on each centraliser
character table can be computed canonically.

This is **deferred** as future work; it is not needed for the use
case that motivates this whole investigation.

#### Practical workflow for Keller-style comparison

For comparing single $S$-entries against an alternative pipeline
(e.g. the one Keller-Roberts-Roberts would produce if they computed
the full twisted modular data of their $E_+(7)$ orbifold):

1. Decode global indices $(i, j)$ to $(\mathrm{class}_i, \mathrm{irrep}_i),\;
   (\mathrm{class}_j, \mathrm{irrep}_j)$.
2. Identify the refined group $g = (\mathrm{type}_i, \mathrm{type}_j, \mathrm{commute}, \mathrm{diag/off})$.
3. If non-commuting: return 0.
4. Otherwise: compute $C_{\mathrm{class}_i}$, $C_{\mathrm{class}_j}$
   (cheap via `Centralizer` even for $E_+(7)$), then
   `ComputeSBlock` at $(\mathrm{class}_i, \mathrm{class}_j)$ and read
   off the entry. ~Seconds per query.

The 22 canonical blocks are then a **structural baseline**: any
on-demand block must agree with its group's canonical up to row+col
permutations on the irrep axes. This is the entry-by-entry comparison
target.

## 5. Tier-4 transgression-kernel test: theory and computation

This section gives the precise content of the kernel test introduced
in §2.3, the algorithmic shape of its current implementation in
`scripts/transgression_kernel.g`, the linearity reduction that avoids
enumerating $H^3$ classes wholesale, and the empirical status across
$m \in \{1, 2, 3, 7\}$. A more detailed informal companion is recorded
in [`strategy_local_discriminators.md`](strategy_local_discriminators.md).

### 5.1 Decision-theoretic role

KRR's published evidence is precisely the assertion
$\mathrm{Tr}([\omega]) = 0$. Their conjecture is $[\omega] = 0 \in H^3(G; U(1))$.
The implication is therefore controlled entirely by $\ker \mathrm{Tr}$:

| $\ker \mathrm{Tr}$ | Consequence |
|---|---|
| $0$ | KRR's $c_g = 0$ proves $[\omega] = 0$. No further direct comparison required. |
| Killed by level-matching | KRR + level-matching are jointly sufficient (as in [vEMS17]'s type-0 condition). |
| Non-trivial after level-matching | KRR is consistent with both $[\omega] = 0$ and a non-empty subgroup of $H^3$. A direct discriminator (Tier 1, 3, or 5) is required. |

Tier 4 thus either settles the conjecture without further modular-data
work, or replaces "all of $H^3(G; U(1))$" with an explicit subgroup
that a direct discriminator must rule out — pruning the falsification
problem to a finite, often very small, subset of $H^3$.

### 5.2 Algorithmic structure

The current implementation `scripts/transgression_kernel.g` realises
the test as follows. Let $G$ be a finite group, $R \to \mathbb Z$ a
free $\mathbb Z G$-resolution of length $\ge 4$, and
$K = R \otimes_{\mathbb Z G} \mathbb Z$ the resulting cellular chain
complex.

1. **Cohomology setup.** `SetupCohomology3(G)` invokes
   `ResolutionFiniteGroup(G, 4)` (HAP [Ell08]) and Gruen's
   `UniversalCoefficientsTheorem(K, 3)` to obtain
   $H^3(G; U(1)) \cong \prod_{i=1}^{k} \mathbb Z/d_i$
   together with an explicit lift
   $L \colon \prod \mathbb Z/d_i \to Z^3(G; \mathbb Z/m)$
   where $m = \mathrm{lcm}(d_i)$, and an evaluator
   `StandardCocycle` mapping a $Z^3$-element to a function
   $G^3 \to \mathbb Z/m$.

2. **Transgressed cocycle.** For each conjugacy-class representative
   $g \in G$ and each $H^3$-class encoded by $v \in \prod \mathbb Z/d_i$,
   `CGCocycleFunc(\omega_v, g)` realises
   $$
   c_g \colon C_G(g) \times C_G(g) \longrightarrow \mathbb Z/m,
   \qquad
   c_g(h_1, h_2) = \omega_v(g, h_1, h_2) + \omega_v(h_1, h_2, g) - \omega_v(h_1, g, h_2).
   $$

3. **Coboundary test.** `IsCoboundary2(C_G(g), c_g, m)` decides
   whether there exists $\beta \colon C_G(g) \to \mathbb Z/m$ with
   $$
   \beta(h_1) - \beta(h_1 h_2) + \beta(h_2) \equiv c_g(h_1, h_2) \pmod m
   \qquad \forall\, h_1, h_2 \in C_G(g).
   $$
   The unknown system has $|C_G(g)|^2$ equations in $|C_G(g)|$
   integer unknowns; the modular constraint is encoded by augmenting
   the coefficient matrix with $-m \cdot I_{|C_G(g)|^2}$, yielding an
   $|C_G(g)|^2 \times (|C_G(g)| + |C_G(g)|^2)$ integer matrix on
   which GAP's `SolutionIntMat` certifies solvability.

4. **Kernel membership.** A class $v$ lies in $\ker \mathrm{Tr}$ if
   and only if $c_{g_i}$ is exact on $C_G(g_i)$ for every conjugacy
   class representative $g_i$.

The dominant cost is step 3. At $|C_G(g)| = n$ the augmented matrix is
$n^2 \times (n + n^2)$; for $E_+(3)$ non-central centralisers ($n = 64$)
this is $4096 \times 4160$ and `SolutionIntMat` requires ~30 s per call.

### 5.3 Linearity and the SNF reduction

The full cohomology group is *not* required to certify $\ker \mathrm{Tr} = 0$.
The transgression $\mathrm{Tr}$ is a homomorphism between finite
abelian groups; once a basis of $H^3(G; U(1))$ and bases of the
targets $H^2(C_G(g); U(1))$ are fixed, the kernel is determined by
the integer matrix
$$
M \;\in\; \mathrm{Mat}\!\left(k \,\times\, \sum_{[g]} k_{C_g}\,;\, \mathbb Z\right),
\qquad
M_{i, *} \;=\; \bigl(\mathrm{Tr}(e_i)\bigr)_{[g]} \;\in\; \bigoplus_{[g]} H^2(C_G(g); U(1)),
$$
where $e_1, \ldots, e_k$ are the standard generators of
$\prod \mathbb Z/d_i$ and $k_{C_g}$ is the number of cyclic factors of
$H^2(C_G(g); U(1))$. The kernel is computed exactly via Smith Normal
Form (`NormalFormIntMat(M, 4)` in GAP) of $M$ together with the source
torsion vector $(d_1, \ldots, d_k)$. No enumeration of $H^3$ classes
is needed; only:

* the **torsion vector** $(d_1, \ldots, d_k)$ of $H^3(G; U(1))$,
* a **basis-realising lift** $L$, and
* the matrix entries $M_{i, *}$, computable one generator at a time.

The script `scripts/transgression_per_generator.g` produces the rows
of $M$. Run alone, it admits three outcomes:

| Per-generator output | Implication for $\ker \mathrm{Tr}$ |
|---|---|
| $\mathrm{Tr}(e_i) = 0$ for every $i$ | $\mathrm{Tr} \equiv 0$, so $\ker \mathrm{Tr} = H^3(G; U(1))$ in full — Tier 4 vacuous |
| $\mathrm{Tr}(e_i) \ne 0$ for some $i$ | $e_i \notin \ker \mathrm{Tr}$, but integer combinations such as $e_1 + 2 e_2$ may still lie in the kernel |
| Smith Normal Form of $M$ has trivial kernel modulo source torsion | $\ker \mathrm{Tr} = 0$ exactly |

The current $E_+(2)$ data place that case in the second regime. The
third regime — the only one that decides the conjecture — is reached
without further cohomology computation: the per-generator output
already constitutes the rows of $M$, and the SNF wrapper is
$O(k^3)$ in the source rank, negligible compared to evaluation cost.

The role of the resolution `ResolutionFiniteGroup(G, 4)` in the
current implementation is therefore purely instrumental. If the
torsion vector and the standard cocycles representing each generator
$e_i$ are obtained from another source (e.g. a closed-form
presentation of $H^*(G; \mathbb F_2)$ together with the Bockstein
spectral sequence for $\mathbb F_2 \leftrightarrow U(1)$), the
resolution is unnecessary.

### 5.4 Empirical status

> **2026-05-08 correction.** All earlier $\ker \mathrm{Tr}$ numbers
> reported in this section were contaminated by a bug in
> `StandardCocycleOf` (use of `setup.UCT.lift * vec` instead of
> `setup.UCT.cocyclebasis[i]`), which produced a Hom-vector outside
> $\ker \partial_4^*$ — so the resulting `StandardCocycle` output was
> not a real bar 3-cocycle. Empirically $942 / 4096$ random 4-tuples
> on $D_8$ violated $\delta\omega \equiv 0 \pmod{\exp}$. The fix
> uses `UCT.cocyclebasis[i]` directly. After the fix every generator
> passes $0/n^4$ cocycle violations on $D_8$ and $E_+(2)$. The
> corrected results are tabulated below; previous-state claims of
> "trivial kernel for $D_8$" and "every $\mathrm{Tr}(e_i) \ne 0$ for
> $E_+(2)$" should be discarded.

| group | $|H^3(G; U(1))|$ torsion | $\ker \mathrm{Tr}$ structure | $|\mathrm{coker}\,\mathrm{Tr}|$ | how |
|---|---|---|---:|---|
| $E_+(1) = D_8$ | $[2, 2, 4]$ (order 16) | $(\mathbb Z/2)^2$ (order 4) | 4 | brute-force `test_transgression_d8.g` |
| $E_+(2)$ | $[2^9, 8]$ (order 4096) | $(\mathbb Z/2)^9 \times \mathbb Z/4$ (order 2048) | 2 | per-generator (9 of 10 in kernel) + brute-force on $\langle e_{10} \rangle$; `test_transgression_kernel_e2.g` |
| $E_+(3)$ | $[2^{34}, 4]$ (order $\sim 7 \cdot 10^{10}$) | not yet computed | — | per-generator pending algorithmic improvement |
| $E_+(7)$ | not yet computed via HAP | not yet computed | — | setup blocked: `ResolutionFiniteGroup` fails at $|G| = 32{,}768$ at 60 GB heap |

For $E_+(2)$, $|\ker \mathrm{Tr}| = 2048 = |H^3| / 2$: half of all
3-cocycle classes have $c_g = 0$ for every $g$. So Keller–Roberts–
Roberts–style $c_g = 0$ evidence is **far** from sufficient for
$\omega = 0$ in this case — the transgression detects only one bit
of obstruction. For $D_8$, $|\ker \mathrm{Tr}| = 4 = |H^3| / 4$:
likewise non-trivial.

The $E_+(2)$ kernel structure $(\mathbb Z/2)^9 \times \mathbb Z/4$
sits inside $H^3(E_+(2); U(1)) = (\mathbb Z/2)^9 \times \mathbb Z/8$
as the index-2 subgroup that vanishes on $\mathrm{Tr}(e_{10})$.
Specifically $\mathrm{Tr}(e_{10})$ has order $2$ in
$\bigoplus_{[g]} H^2(C_G(g); U(1))$.

The $E_+(3)$ row is the next concrete frontier: per-generator
evaluation requires the algorithmic improvements in §5.5 to be
practical. Once $\mathrm{Tr}(e_i)$ is computed for $i = 1, \ldots, 35$
the SNF wrapper of §5.5 step 2 returns the kernel as a finite abelian
group.

### 5.5 Upgrade roadmap

Three improvements take Tier 4 from "tested at $m = 1$, partially
tested at $m = 2$" to "operative at $m \in \{2, 3, 5, 7\}$":

1. **Faster `IsCoboundary2`.** Replace the integer augmented-system
   solve with HAP's native `Cohomology(R, 2)` and `IsBoundary` calls
   on the centraliser, reusing the bar-resolution boundary maps
   already constructed for $G$. Expected speedup at $n = 64$ is
   $10\!-\!100\times$, since HAP works in row-echelon form rather
   than re-solving from scratch each call.

2. **SNF wrapper on the per-generator output.** Accumulate
   $M \in \mathrm{Mat}_{k \times \sum k_{C_g}}(\mathbb Z)$ from
   per-generator integer-coordinate evaluations of $\mathrm{Tr}(e_i)$
   in a fixed basis of each $H^2(C_G(g); U(1))$, and invoke
   `NormalFormIntMat(M, 4)`. Closes the gap from "necessary" to
   "exactly $\ker \mathrm{Tr}$".

   Caveat discovered while implementing on $E_+(2)$: the obvious
   choice of basis — Gruen's `UCT.cocyclebasis` at $n = 2$ — spans
   $H^2(C; U(1)) \cong H_2(C; \mathbb Z)$, which differs from
   $H^2(C; \mathbb Z/\exp)$ when $\mathrm{Tor}(H^3(C; \mathbb Z), \mathbb Z/\exp)$
   is non-zero. Concretely, on $E_+(2)$'s class-2 centraliser
   ($|C| = 16$, $H^2$ torsion $[2, 2, 2]$ in Gruen's UCT), the c_g
   produced by the order-8 generator $e_{10}$ is *not* a mod-$\exp$
   coboundary nor cohomologous to any of Gruen's three basis
   cocycles — it lives in the Tor part of $H^2(C; \mathbb Z/\exp)$
   that Gruen's basis does not capture. The basis must be extended
   to span the full $H^2(C; \mathbb Z/\exp)$ (the natural target of
   the slant operation on integer cocycles) for the SNF approach to
   produce coordinates for every $\mathrm{Tr}(e_i)$. The pragmatic
   workaround used to settle $E_+(2)$ — brute-forcing the cyclic
   subgroup generated by the unique non-in-kernel generator — does
   not generalise to $E_+(3)$ where multiple generators are expected
   to have non-trivial $\mathrm{Tr}$.

3. **Bypass HAP at $|G| = 32{,}768$.** Two routes:
   * Use Quillen's polynomial-times-exterior presentation [Qui71] of
     $H^*(E_+(m); \mathbb F_2)$ together with the Bockstein long
     exact sequence relating $\mathbb F_2$ and $U(1)$ coefficients.
     The torsion of $H^3(E_+(7); U(1))$ is then obtained analytically;
     standard cocycles representing each generator are constructed
     directly without `ResolutionFiniteGroup`.
   * Use a *detecting subgroup* $H \le E_+(7)$ for which
     $\mathrm{res}^G_H \colon H^3(G) \to H^3(H)$ is injective on the
     subspace of $H^3(G)$ that survives transgression-restriction
     ([AM04, V.6]). For an extraspecial 2-group the elementary
     abelian quotient $E_+(7) \twoheadrightarrow (\mathbb F_2)^{14}$
     alone is too lossy (the Frattini subgroup is non-trivial), but
     the diagonal $\mathbb Z/2$ together with one extraspecial section
     is detecting in this sense.

After (1)–(3) the matrix $M$ for $E_+(3)$ becomes tractable in hours,
and analytical setup at $E_+(7)$ becomes the only remaining cost.

### 5.6 References

* Brown [Br82, Ch. V.3] — slant product as a chain-level operation.
* Mac Lane [McL75, Ch. VIII] — slant product and pairing operations.
* Adem–Milgram [AM04, Ch. III.1, V.6] — transgression in the LHS
  spectral sequence; detecting subgroups for cohomology of finite
  groups.
* Quillen [Qui71] — analytical presentation of $H^*(E_+(m); \mathbb F_2)$.
* Naidu–Nikshych [NN08, §3] — kernel-of-transgression in the
  twisted-double / Lagrangian-subcategory context.
* Karagueuzian–Symonds, online tables (`http://groupcohomology.org/`)
  — explicit $H^*(E_+(2); \mathbb Z)$ and $H^*(E_+(3); \mathbb Z)$ for
  cross-checks.
* Ellis [Ell08] — HAP package; `ResolutionFiniteGroup`, `Cohomology`,
  `StandardCocycle`.

## 6. Tier-1 closed-form one-entry tests

### 6.1 Decision-theoretic role

Tier 1 is the cheapest entry-level discriminator between the modular
data of $D^\omega(G)$ and $D^0(G)$ for a fixed group $G$ and candidate
3-cocycle $\omega$. It compares the $S$-matrix at one chosen index
pair $\bigl((g_1, \chi_1), (g_2, \chi_2)\bigr)$. A single non-zero
discrepancy falsifies the assertion that $[\omega]$ and $0$ produce
the same MTC; agreement on a finite list of entries gives evidence
but not proof.

Tier 1 is per-$\omega$, not structural. Its strategic role in the
KRR programme is therefore as a **closer**: after Tier 4 narrows the
candidate cocycles to $\ker \mathrm{Tr} \le H^3(G; U(1))$, Tier 1
dispatches the surviving members one by one in $O(1)$ each.

### 6.2 The twisted $S$-formula and the $\varepsilon_\omega$ phase

The twisted Bantay/Coste–Gannon–Ruelle formula (§2.2) is
$$
S^{\omega}_{(g_1, \chi_1), (g_2, \chi_2)} \;=\; \frac{1}{|G|}
\sum_{\substack{a \in [g_1],\; b \in [g_2] \\ ab = ba}}
\varepsilon_\omega(g_1, g_2, a, b)\;
\overline{\chi_1(t_a^{-1} b\, t_a)}\;
\overline{\chi_2(s_b^{-1} a\, s_b)}.
$$
The phase $\varepsilon_\omega \in U(1)$ is computable in $O(1)$ from
$\omega$ regarded as a callable $G^3 \to \mathbb Z/m$. In the
convention-clean form of [CGR2000, §4],
$$
\varepsilon_\omega(g_1, g_2, a, b) \;=\;
\frac{\theta_a(t_a, g_2)\,\theta_b(s_b, g_1)^{-1}}{\beta_{a, b}(g_1, g_2)},
$$
where $\theta_g(x, y) = \omega(g, x, y)\,\omega(x, y, g)\,\omega(x, g, y)^{-1}$
is the slant of $\omega$ by $g$ at $(x, y)$ and $\beta_{a, b}$
collects the section-choice corrections. Different references write
$\varepsilon$ in superficially different forms; precise statements
appear in [DPR91; CGR2000, §4; NN08, eq. (2.8)].

Two structural facts:
* $\varepsilon_\omega \equiv 1$ when $\omega$ is trivial, so
  $S^\omega = S^0$ identically.
* $\varepsilon_\omega$ depends on $(g_1, g_2, a, b)$ only and is
  independent of the projective characters $\chi_i$. Entry-level
  discrepancies between $S^\omega$ and $S^0$ therefore decouple, one
  index pair at a time.

### 6.3 Closed-form central rows revisited

For $g_1 \in \{1, -1\} \subset E_+(m)$ the conjugacy class $[g_1]$ is
a singleton, so the sum in §6.2 collapses. Combined with the
closed-form expression of §4.3 for the untwisted central rows,
$$
S^\omega_{((-1, \rho), (h, \sigma))} \;=\; \frac{1}{|G|}
\sum_{b \in [h]} \varepsilon_\omega(-1, h, -1, b)\,
\overline{\rho(b)}\,\sigma(-1),
$$
with $|[h]| \in \{1, 2\}$ in $E_+(m)$. Two cocycle evaluations and
two character evaluations per entry, independent of $m$.

### 6.4 Practical protocol

Given the cross-cutting infrastructure of §5.5 and a callable for
$\varepsilon_\omega$:

1. Pick $m$ and a candidate $[\omega] \in H^3(E_+(m); U(1))$ to test.
2. Pick a target index $((g_1, \chi_1), (g_2, \chi_2))$ with
   $g_1 \in \{1, -1\}$ and $g_2$ non-central, and $\chi_1, \chi_2$
   chosen to keep the right-hand sides numerically simple.
3. Evaluate $S^0$ via the closed form of §4.3.
4. Evaluate $S^\omega$ via the formula of §6.3.
5. Compare. Any $|S^\omega - S^0| > 10^{-12}$ at the entry forces
   $[\omega] \ne 0$ in the MTC sense.

The optional comparison against KRR's pipeline output requires the
projector formula [KRR24, eq. (2.1.2)] assembling intertwiner
matrices into $S$-matrix entries; this is the
"Keller-pipeline-to-$S$-entry adapter" gap recorded in
[`strategy_local_discriminators.md`](strategy_local_discriminators.md).

### 6.5 Strengths, limits, and engineering gap

Strengths:
* **Cost asymmetry.** The untwisted side is $O(1)$ in $m$. Only the
  abstract $\omega$-evaluation contributes to test cost.
* **Localised falsification.** A single non-zero discrepancy at any
  sampled entry suffices.
* **No labelling ambiguity.** Both sides label simples by
  $(\text{conjugacy class}, \chi)$ identically; no permutation
  search.
* **Composes with Tier 4.** Reduces to $O(\#\text{candidates in } \ker \mathrm{Tr})$
  evaluations once $\ker \mathrm{Tr}$ is in hand.

Limits:
* **One-way.** Agreement on any finite list of entries does not
  prove MTC equivalence.
* **Section-dependence.** $\varepsilon_\omega$ depends on the section
  $G \to G/\langle g_i \rangle$. Under KRR's hypothesis $c_g = 0$ the
  section is trivial up to coboundary, but a sign error in
  implementation can yield false-positive disagreements; validation
  against $Q_8$ (where ground-truth modular data is on disk) is
  mandatory before reporting an $E_+(m)$ result.
* **Empty central×central block.** For both $g_1, g_2 \in \{1, -1\}$
  the phase $\varepsilon_\omega$ is automatically trivial; only
  central×non-central or non-central×non-central entries are
  informative.
* **KRR-pipeline adapter not yet built.** Required only if comparing
  against KRR directly rather than against an abstract $\omega$.

### 6.6 References

* [DPR91] — original $\varepsilon$-derivation.
* [CGR2000, §4] — convention-clean form of $\varepsilon_\omega$ and
  the slant $\theta_g$.
* [Ban97, Ban98] — orbifold-VOA viewpoint.
* [NN08, eq. (2.8)] — Hopf-algebra restatement.
* [EG18, §2] — VOA-orbifold context KRR cite.
* [KRR24, §2.1] — projector formula needed for the optional Keller
  comparison.

## 7. Tier-5 Frobenius–Schur indicators

### 7.1 Decision-theoretic role

The higher Frobenius–Schur indicator $\nu_n(X)$ of a simple object
$X = (g, \chi) \in D^\omega(G)$ is a categorical invariant — an
$(S, T)$-determined number, by [Bantay97; NgS07] — and admits a
closed-form group-theoretic expression for $D^\omega(G)$ via
[Iovanov–Mason–Ng, IMN14, Thm. 4.1]. As a test, FS indicators are
structurally analogous to Tier 1: per-$\omega$, falsification-only,
but with the additional feature of being **basis-free**. No section
choice, no permutation alignment.

Crucially, FS indicators see $\omega$-data that the slant
transgression does not: the $\Phi_\omega$-phase in the IMN formula
evaluates $\omega$ at triples that do not factor through the slant.
A class $[\omega] \in \ker \mathrm{Tr}$ — invisible to KRR's $c_g$
test — may still produce non-trivial $\nu_n$ values, falsifying its
equivalence with $\omega = 0$ at the MTC level.

### 7.2 The IMN closed form

For a simple $X = (g, \chi) \in D^\omega(G)$ and $n \ge 0$,
$$
\nu_n\!\left((g, \chi)\right) \;=\; \frac{1}{|C_G(g)|}
\sum_{\substack{x \in C_G(g) \\ (gx)^n = 1}}
\Phi_\omega(g, x; n)\,\chi(x^n),
$$
where $\Phi_\omega(g, x; n)$ is an explicit $U(1)$-phase, computable
from $O(n)$ evaluations of $\omega$ along the cocycle path from $1$
to $(gx)^n$ inside $\langle g, x \rangle$. Up to convention,
$$
\Phi_\omega(g, x; n) \;=\; \prod_{j=0}^{n-1}
\frac{\omega\bigl(g,\,(gx)^j x,\,gx\bigr)}{\omega\bigl((gx)^j,\,gx,\,g\bigr)}
$$
(precise form in [IMN14, eq. (4.5)]). For $\omega \equiv 0$,
$\Phi_\omega \equiv 1$ and the indicator reduces to the classical
character-table formula
$\nu_n(\rho) = (1/|G|) \sum_g \chi_\rho(g^n)$ specialised to
centralisers.

The cost of one $\nu_n$ evaluation is $O(|C_G(g)| \cdot n)$ — linear
in centraliser size, linear in $n$, independent of every other
simple object.

### 7.3 Why FS indicators see what $c_g$ does not

KRR's $c_g = 0$ evidence asserts the slant of $\omega$ by every $g$
vanishes:
$\theta_g(x, y) = \omega(g, x, y)\,\omega(x, y, g)\,\omega(x, g, y)^{-1}$
is a 2-coboundary on $C_G(g)$ for every conjugacy class $[g]$. The
$\Phi_\omega$-phase, in contrast, evaluates $\omega$ on triples like
$(g, (gx)^j x, gx)$ where the factor $(gx)^j x$ is not a single group
element on which the slant acts — it lies in the inner factor of the
3-cocycle's domain. So $\Phi_\omega$ is, in general, not a function
of $c_g$ alone; it is independent gauge-invariant data.

Consequently, FS indicators provide an obstruction
$[\omega] = 0$ that lives **on $\ker \mathrm{Tr}$** rather than on
its complement. This is the precise sense in which Tiers 4 and 5
are complementary.

### 7.4 Existing implementation and bugs

`DRINFELD/src/universal_coefficients.g` carries three FS-indicator
functions:

* `FSIforDoubles(G, f, class, proj, i, n, listG, pivalues, m)` —
  single $\nu_m$ value for one simple of $D^\omega(G)$. Implements
  IMN via the projective-character helpers (`alphag`, `pivalues`).
  As-written runnable.
* `GaugeInvariants(G)` — top-level driver enumerating one $\omega$
  per `AutomorphismOrbits` representative, computing the full
  $\nu$-table per simple. **Broken**: references `hombasis` (line
  ~422) without declaring it in the `local` block.
* `FSIforAGT(G, N, omega)` — adaptated-cocycle indicators for
  almost-group-theoretical fusion subcategories. **Broken**: parser
  errors (`listG:-Enumerator`; missing brackets in inner `nu`).

The recommended path forward is to bypass the broken wrappers and
call `FSIforDoubles` directly with $f = $ standard cocycle of a
chosen $\omega$, looping over a chosen subset of simples and a
chosen subset of $n$-values. Fixing `GaugeInvariants` to add the
missing locals is a separate, ~5-line task valuable for batch use.

### 7.5 Cost and protocol

| $m$ | $|C_G(g)|$ (non-central) | per indicator | per candidate $\omega$ |
|---|---:|---|---|
| 3 | 64 | sub-second | $\sim 1$ s |
| 5 | 1 024 | seconds | minutes |
| 7 | 16 384 | $\sim 1$ min | hours |

The "per candidate" cost above sweeps $n$ up to the FS-exponent
(divides the order of $T$, hence $\le 4$ for $E_+(m)$ at $m \le 7$
since $T$-multiset is $\{1, -1, i, -i\}$) and one chosen
$(g, \chi)$.

Combined with Tier 4, the protocol is:

1. Run Tier-4 SNF (§5) to obtain $\ker \mathrm{Tr}$ as an explicit
   subgroup of $H^3(G; U(1))$.
2. For each non-zero $[\omega] \in \ker \mathrm{Tr}$:
   a. Pick a simple $(g, \chi)$ — typically $g$ non-central with
      smallest centraliser, $\chi$ of small dimension.
   b. For $n \in \{2, 3, 4\}$, evaluate $\nu_n((g, \chi); \omega)$
      and $\nu_n((g, \chi); 0)$ via `FSIforDoubles`.
   c. Any disagreement eliminates $[\omega]$ and the conjecture
      receives positive evidence at that class.
3. If every candidate $[\omega]$ in $\ker \mathrm{Tr}$ is eliminated
   except $[\omega] = 0$ itself, KRR's $c_g = 0$ evidence is
   sufficient for the conjecture *modulo* the standard caveat that
   FS indicators are necessary but not sufficient invariants.

### 7.6 Strengths and limits

Strengths:
* **Categorical invariance.** No section choice, no permutation
  alignment.
* **Closed-form on the abstract side.** No KRR pipeline required.
* **Independent obstruction from $c_g$.** Detects classes in
  $\ker \mathrm{Tr}$.
* **Already partially implemented.** `FSIforDoubles` is the right
  primitive; only the wrappers need fixing.

Limits:
* **One value at a time.** Disagreement at one $(g, \chi, n)$
  suffices, but the search across $(g, \chi, n)$ is heuristic; a
  carelessly-chosen tuple may give agreement even for non-zero
  $\omega$.
* **Confirmation is weak.** Like Tier 1, agreement on a finite list
  is evidence, not proof.
* **Parity with KRR's pipeline.** KRR's Schur-averaging machinery
  ([KRR24, §4.4]) is structurally an FS-indicator computation; a
  direct cross-check of $\nu_n$ values against KRR's published
  intertwiner traces is feasible without an additional projector
  step. This is in fact the cleanest comparator with KRR's outputs.

### 7.7 References

* [Ban97] — original $(S, T)$-formula for $\nu_2$ in MTC.
* [MN05] — first explicit closed form for $D^\omega(G)$.
* [NgS07] — defines $\nu_n$ for general pivotal categories;
  $(S, T)$-determination theorem.
* [NgS10] — Frobenius–Schur exponent and its relation to the order
  of $T$.
* [IMN14] — closed-form formula used by `FSIforDoubles`.
* [EG18] — uses FS indicators as obstruction to extension type — the
  precise context for the Keller question.
* [MS18] — modular categories not determined by $(S, T)$;
  FS indicators as part of the missing data.
* [KRR24, §4.4] — Schur averaging as FS-indicator computation.

## 8. Tier-3 $\mathrm{Aut}(N, T)$ discriminator

### 8.1 Decision-theoretic role

For an MTC $\mathcal{C}$ of rank $r$, the group
$$
\mathrm{Aut}(N, T) \;:=\; \bigl\{\pi \in S_r \,:\, N_{\pi(i)\,\pi(j)}^{\pi(k)} = N_{ij}^k \text{ for all } i, j, k,\;\; T_{\pi(i)} = T_i \text{ for all } i \bigr\}
$$
is the group of permutations of simples that preserve the fusion ring
*and* the T-vector simultaneously. As an isomorphism invariant of the
labelled pair $(K(\mathcal{C}), T)$ — strictly weaker than the full
$(S, T)$ — it gave the cleanest discrimination in the
$Q_8$ investigation [`q8_extension_type/writeup.md`]: the trivial
cocycle and the order-2 cocycle on $Q_8$ produced $|\mathrm{Aut}(N, T)| = 6$
and $24$ respectively, certifying inequivalence even though the
fusion ring alone and the T-multiset alone each failed to separate
the two.

In the KRR programme, the Tier-3 test serves as a falsifier
analogous to Tier 1 and Tier 5: pick a candidate
$[\omega] \in \ker \mathrm{Tr}$ surviving Tier 4, compute
$|\mathrm{Aut}(N^\omega, T^\omega)|$, and compare with
$|\mathrm{Aut}(N^0, T^0)|$. Inequality eliminates $[\omega]$. Equality
is one piece of evidence and not a proof.

### 8.2 The cost primitives

Computing $|\mathrm{Aut}(N, T)|$ requires:

1. **Storage** of the fusion ring $N$, an integer 3-tensor of shape
   $r \times r \times r$, typically sparse with $\sim r^2 \cdot \overline{N}$
   non-zero entries ($\overline{N}$ the average multiplicity, usually
   $O(1)$ for $D^\omega(G)$).
2. **A query primitive** for $N_{ij}^k$. Either a pre-stored sparse
   table, or on-demand via Verlinde
   $N_{ij}^k = \sum_a S_{ia} S_{ja} \overline{S_{ka}} / S_{0a}$, with
   per-query cost $O(r)$ multiplied by the cost of a single
   $S$-entry lookup.
3. **A backtracking search** for permutations preserving $(N, T)$,
   refined by the T-eigenvalue partition, the quantum-dimension
   partition, the self-fusion signature $\{N_{ii}^k\}_k$, and
   recursive refinements within blocks.

At rank $r$ the dominant axis is storage and the per-query cost,
not the search itself: modern colour-refinement engines (`bliss`,
`nauty`, GAP's automorphism utilities) handle $r \sim 10^7$
routinely once the refinement is set up.

### 8.3 The BRW symmetry: lower bound and quotient

For $G = E_+(m)$ embedded as a normal subgroup of $\mathrm{BRW}(m)$,
the outer-automorphism action of $\mathrm{BRW}(m)/E_+(m)$ on simples
of $D^0(E_+(m))$ permutes conjugacy classes within each of the four
BRW orbits (§4.5) and acts on $\mathrm{Irr}(C_G(g))$ via the induced
isomorphism on centralisers. This action is fusion-and-T-preserving,
giving an explicit subgroup
$$
\mathrm{BRW}(m)/E_+(m) \hookrightarrow \mathrm{Aut}(N, T).
$$
Two consequences:

1. $|\mathrm{Aut}(N, T)|$ is bounded below by the order of
   $\mathrm{BRW}(m)/E_+(m)$ at every $m$.
2. The substantive content is the quotient
   $\mathrm{Aut}(N, T)/\mathrm{BRW}$, the *outer* automorphism group
   of the labelled fusion–T pair. Comparison of $|\mathrm{Aut}(N, T)|$
   between untwisted and Keller MTCs is equivalent to comparison of
   the quotients, since the BRW factor is identical on both sides
   under KRR's $c_g = 0$ hypothesis.

The quotient framing also makes the Tier-3 test computationally
lighter: the same quotient is detectable on a $\mathrm{BRW}$-orbit
sample of simples rather than on the full simple set.

### 8.4 $m = 3$, $r = 2272$: feasible end-to-end

State of inputs: dense $S$ on disk (26 MB,
`computed/E_plus_3/S.g`), $T$ in hand, full character-table data.

Costs:
* Materialising $N$ via Verlinde: $r^3 \cdot O(r) = 2272^4 \approx 2.7 \cdot 10^{13}$
  multiplications unoptimised, $\sim 10^{10}$ with sparse-row
  optimisations standard in `Verlinde`-style code. Storage of
  non-zero entries: $\sim 10^7$ for $D(G)$ on a group of this size,
  $\sim 100$ MB.
* T-block sizes: $\{1^{1172}, (-1)^{1044}, i^{28}, (-i)^{28}\}$
  (§4.2). Backtracking domain factorises immediately as
  $S_{1172} \times S_{1044} \times S_{28} \times S_{28}$.
* Quantum-dimension partition halves the $T = 1$ block.
* Expected $|\mathrm{Aut}(N, T)|$ is moderately large but tractable;
  empirically (cf. $Q_8$ where $|\mathrm{Aut}|$ was 6 and 24), expect
  a finite explicit number.

Conclusion: full $|\mathrm{Aut}(N, T)|$ at $m = 3$ is feasible in
days of single-CPU work. The right place to develop the methodology
and validate against $m = 2$ ($r = 184$).

### 8.5 $m = 5$, $r = 527{,}872$: feasible only on chosen subsets

State of inputs: $T$ in hand (sector-chunked), $S$ stored as 22
BRW-canonical blocks (94 MB, `computed/E_plus_5/structural/`). No
dense $S$. Per-entry $S$ recoverable in $O(1)$ via canonical-block
lookup once per-class permutations are computed; in $O(\text{seconds})$
via `ComputeSBlock` otherwise.

Costs:
* $r^3 \approx 1.5 \cdot 10^{17}$ — full $N$ unstorable.
* Verlinde-on-demand at $r \sim 5 \cdot 10^5$: per-coefficient cost
  $O(r)$ multiplications $\times$ $O(1)$ $S$-lookup. Single
  $N_{ij}^k$ query: $\sim$ ms with canonical-block infrastructure,
  $\sim$ seconds without.
* Materialising $N$ on a chosen subset $\mathcal{S} \subset \mathrm{Simp}(\mathcal{C})$
  of size $s$: $s^3 \cdot r$ multiplications.
  $s = 100$: $5 \cdot 10^{11}$ — days.
  $s = 10^3$: $5 \cdot 10^{14}$ — infeasible.
  $s = 10^4$: infeasible.

The natural subsets:
* **Central simples alone** ($2(4^5 + 1) = 2050$): forms a tensor
  sub-MTC with fusion ring computable in closed form from
  $\mathrm{Rep}(E_+(5))$. Aut on this sub-ring is identical between
  untwisted and Keller MTCs under $c_g = 0$, so does *not* discriminate.
* **Central plus one non-central conjugacy class** ($\sim 3000$
  simples): non-central simples carry the discriminating information.
  Tractable subset for full-$N$ materialisation.
* **One $T$-block at a time** (e.g. $\{T = i\}$, size $\sim 496$):
  Aut on each $T$-block, preserving fusion *into* the block, is a
  partial invariant. Cheap, partial, valuable.

Conclusion: $|\mathrm{Aut}(N, T)|$ at $m = 5$ is computable only on
small subsets. The right choice is "central + one non-central class"
or "one $T$-block + its fusion neighbourhood", with the
canonical-block infrastructure supplying per-query $S$.
Wall-clock days, engineering effort non-trivial.

### 8.6 $m = 7$, $r \approx 1.34 \cdot 10^8$: only the central sub-MTC is reachable, and uninformative

State of inputs: $T$ analytical, 9 of 22 canonical $S$-blocks (8.7
GB), 13 either zero or closed-form $O(1)$. No dense data of any
kind.

Costs:
* $r^3 \approx 2.4 \cdot 10^{24}$ — no full $N$, even sparse.
* Verlinde-on-demand at $r \sim 1.34 \cdot 10^8$: per-coefficient
  $O(r)$ multiplications $\times$ canonical-block $S$-lookup. Single
  $N_{ij}^k$: $\sim$ seconds. $r^2$ queries (one row of $N$):
  $\sim 2 \cdot 10^{16} \cdot$ seconds — infeasible.
* Aut on the central sub-MTC, $r_{\mathrm{central}} = 2(4^7+1) = 32{,}770$:
  $r_{\mathrm{central}}^3 \approx 3.5 \cdot 10^{13}$ entries, far too
  many even at the closed-form character-product cost; storage
  $\sim 280$ GB sparse.

The central sub-MTC has fusion determined by $\mathrm{Rep}(E_+(7))$,
combinatorially tractable per-entry but storage-bound at the
$N$-tensor level. Even paying that cost: the central sub-Aut does
not discriminate untwisted from Keller's MTC under $c_g = 0$, so it
gains no falsification.

Conclusion: full $|\mathrm{Aut}(N, T)|$ at $m = 7$ is infeasible,
and the easily-reachable central sub-Aut is uninformative. Tier 3
is not a usable Keller-discriminator at $m = 7$ without further
structural compression of $N$ analogous to §4.5's compression of
$S$ — and no such compression is presently known.

### 8.7 Net assessment and strategic role

| $m$ | full $\mathrm{Aut}(N, T)$ | sub-MTC $\mathrm{Aut}$ | role in the KRR programme |
|---|---|---|---|
| 3 | feasible (days) | redundant | full discriminator if Tier 4 fails to settle |
| 5 | infeasible | feasible on chosen subsets | subset discriminator; needs canonical-block per-query infrastructure |
| 7 | infeasible | infeasible-or-uninformative | not viable as a primary discriminator |

Tier 3 stays in the strategic toolkit at $m = 3$ and at $m = 5$ on
subsets, but is essentially absent at $m = 7$. The $m = 7$
falsification programme leans on Tiers 1, 4, and 5; Tier 3 is
methodologically valuable mainly as a stress-test of the
Tier-4 → Tier-{1, 5} pipeline at $m = 3$, where ground truth from
the dense $S$ is available.

### 8.8 Composition with Tier 4

If Tier 4 produces $\ker \mathrm{Tr} = 0$, KRR's evidence proves the
conjecture and Tier 3 is moot. If $\ker \mathrm{Tr} \ne 0$, Tier 3
distinguishes $D^\omega(G)$ from $D^0(G)$ for one specific
$\omega \in \ker \mathrm{Tr}$ at a time — replacing the candidate
space "all of $H^3$" with "the explicit subgroup $\ker \mathrm{Tr}$".
Without the Tier-4 reduction the candidate space is $|H^3|$, which
is $7 \cdot 10^{10}$ at $m = 3$ and astronomical beyond, and Tier 3
cannot scan over candidates of that size in reasonable time.

### 8.9 References

* [Q_8 writeup, this repository] — empirical $|\mathrm{Aut}(N, T)| = 6$
  vs $24$ separation for the trivial vs order-2 cocycle on $Q_8$.
* [CGR2000] — modular-data framework and the $(S, T)$-permutation
  symmetry group of $D^\omega(G)$.
* [MS18] — modular categories not determined by $(S, T)$;
  $\mathrm{Aut}(N, T)$ as part of the missing data.
* [BNRW16] — Bruillard, Ng, Rowell, Wang. *Rank-finiteness for
  modular categories.* J. AMS **29** (2016) 857.
  arXiv:[1310.7050](https://arxiv.org/abs/1310.7050). Uses
  $(N, T)$-rigidity in classification.
* [ENO10] — Etingof, Nikshych, Ostrik. *Fusion categories and
  homotopy theory.* Quantum Topol. **1** (2010) 209.
  arXiv:[0909.3140](https://arxiv.org/abs/0909.3140). Categorical
  framework for $\mathrm{Aut}_\otimes(\mathcal{C})$ as a categorical
  group; $\mathrm{Aut}(N, T)$ is its image at the decategorified,
  T-decorated level.
* [EG18] — Evans–Gannon; "extension type" as the property tested by
  Tier 3 in $Q_8$.

## 9. Verification ladder

| Property | $m=3$ | $m=5$ | $m=7$ | How |
|---|---|---|---|---|
| rank matches predictor | ✓ | ✓ | ✓ (analytical) | direct lib + analytical |
| T-multiset matches predictor | ✓ | ✓ | ✓ (analytical) | direct lib + analytical |
| modularity $S^2 = (ST)^3$ | ✓ | (full S not computed) | (impossible at full size) | direct |
| canonical block matches dense $S$ | ✓ (byte-for-byte) | (no dense $S$) | (no dense $S$) | `compute_canonical_blocks.g` |
| canonical blocks computed | 22 | 22 | 9 (+ 6 zero, + 3 closed-form O(1)) | structural rep |
| $c_g$ trivial for $g = -1$ | ✓ | ✓ | ✓ | Magma port (brute-force + closed-form) |
| $c_g$ trivial for $g = g_2$ | ✓ | ✓ | (m=7 not run; same argument applies) | centraliser acts trivially on $N_\theta$ |
| $c_g$ trivial for $g = g_4$ | ✓ | ✓ | (same) | same |
| level matching $\omega\rvert_{\langle g \rangle} = 0$ | (paper) | (paper) | (paper, $\rho_g \in \mathbb Z$) | from $\rho_g$ values |
| $\ker \mathrm{Tr}$ computed | pending | — | — | per-generator + SNF (§5.4–§5.5) |
| $\ker \mathrm{Tr} = 0$ | (likely no — see $E_+(2)$) | — | — | predicted from $E_+(1), E_+(2)$ trend |

For $m = 1, 2$ the kernel of $\mathrm{Tr}$ is non-trivial of order $4$
and $2048$ respectively (§5.4); the trend strongly suggests
$\ker \mathrm{Tr} \ne 0$ at $m = 3, 5, 7$ as well, in which case
KRR's $c_g = 0$ evidence is necessary but not sufficient and the
conjecture must be settled by an additional discriminator from
Tiers 1, 3, or 5 evaluated on each non-zero element of $\ker \mathrm{Tr}$.

## 10. Scaling caveats discovered along the way

* **GAP `ConjugacyClasses(E_+(7))` exhausts memory.** Even with the
  heap raised to 32 GB and 60 GB, `ClassesSolvableGroup` on
  $|G| = 32{,}768$ exhausts memory while building the induced PCG
  structure for class enumeration. The bottleneck is GAP's
  general-purpose algorithm; for an extraspecial 2-group the conjugacy
  classes are known structurally ($4^m + 1$ of them, sizes 1 or 2).
  **Bypassed in Phase E_BRW** (§4.5): instead of asking for the full
  conjugacy class list, we compute centralisers of canonical class
  representatives directly via `Centralizer(G, x)` — these have order
  $|G|/2 = 16384$ and GAP handles them comfortably — together with a
  closed-form structural description of $\mathrm{Irr}(E_+(7))$ that
  avoids `CharacterTable(G)` entirely. See §4.5 for the full pipeline.

* **Brute-force enumeration of $H^3$ classes is hopeless for $m \ge 2$.**
  $|H^3(E_+(2); U(1))| = 4096$ (UCT torsion $[2^9, 8]$);
  $|H^3(E_+(3); U(1))| \approx 7 \times 10^{10}$ (torsion
  $[2^{34}, 4]$); $|H^3(E_+(7); U(1))|$ astronomical. Tier-4 must
  use the linearity of $\mathrm{Tr}$: evaluate on each generator,
  assemble the kernel via Smith Normal Form.

* **`IsCoboundary2(H, c, m)` is the slow inner loop.** For
  centraliser of order $n$, builds an $n^2 \times (n + n^2)$
  augmented integer matrix and asks `SolutionIntMat`. At $n = 64$
  ($E_+(3)$ non-central centraliser) this is a $4096 \times 4160$
  matrix per query and ~30 s per call. With 35 generators × 65
  classes = 2275 queries, the full $E_+(3)$ Tier-4 sweep is many
  hours. Tractable but slow; an HAP cohomology-of-cochains
  formulation should be faster but needs careful conventions.

## 11. Reproducing

```sh
cd extraspecial_orbifolds/scripts
# Magma->GAP port verification
gap -q -b -c 'Read("test_em_and_bw.g");'
gap -q -b -c 'Read("twisted_group_algebra.g");'
gap -q -b -c 'Read("test_qforms_f2.g");'
gap -q -b -c 'Read("test_defect_rep_m3.g");'
gap -q -b -c 'Read("test_defect_rep_other.g");'
gap -q -b -c 'Read("test_defect_rep_optim.g");'      # m=3, 5, 7 c_g triviality

# Direct untwisted modular data
gap -q -b -c 'Read("test_untwisted_md_e_plus_2.g");' # E_+(2): library smoke test
gap -q -b -c 'Read("compute_e_plus_3_full.g");'      # E_+(3) full (S, T)
gap -q -b -c 'Read("compute_e_plus_5_T.g");'         # E_+(5) T-vector
gap -q -b -o 60G -c 'Read("compute_e_plus_7_T.g");'  # E_+(7) T-vector (memory!)
gap -q -b -c 'Read("test_closed_form_central.g");'   # closed-form central rows

# Phase E_BRW: structural canonical-block S representation
gap -q -b -c 'Read("run_e_plus_3_canonical.g");'     # 22 canonical blocks for m=3 (~0.3 s)
gap -q -b -c 'Read("run_e_plus_5_canonical.g");'     # 22 canonical blocks for m=5 (~26 s, 94 MB)
gap -q -b -o 60G -c 'Read("run_e_plus_7_canonical.g");'  # 9 canonical blocks for m=7 (~16 min, 8.7 GB)
gap -q -b -c 'Read("per_class_perms_e_plus_3.g");'   # documents the per-class-perms failure

# Tier 4: transgression kernel
gap -q -b -c 'Read("test_transgression_d8.g");'                 # full enumeration on D_8 (kernel order 4)
gap -q -b -c 'Read("test_transgression_per_gen_e2.g");'         # per-generator on E_+(2) (9 of 10 in kernel)
gap -q -b -c 'Read("test_transgression_kernel_e2.g");'          # full ker Tr for E_+(2) (order 2048)
```

All `.g` files in `scripts/` are pure GAP libraries (no `QUIT;` at end);
test/driver scripts begin with `test_` or `compute_` prefixes.
Computed outputs land under `extraspecial_orbifolds/computed/`.

## 12. References

Primary motivation:
- **[KRR24]** C. A. Keller, A. W. Roberts, J. Roberts. *CFTs with
  large gap from Barnes-Wall lattice orbifolds.*
  arXiv:[2411.13646](https://arxiv.org/abs/2411.13646), 2024.

Modular tensor categories of group-cohomology origin:
- **[Dr89]** V. G. Drinfeld. *Quasi-Hopf algebras.* Leningrad Math.
  J. **1** (1990), 1419–1457.
- **[DPR91]** R. Dijkgraaf, V. Pasquier, P. Roche. *Quasi-Hopf
  algebras, group cohomology and orbifold models.* Nucl. Phys. B
  Proc. Suppl. **18B** (1990) 60–72; Comm. Math. Phys. **129** (1990).
- **[Ban97]** P. Bantay. *Frobenius–Schur indicators, the
  Klein-bottle amplitude, and the principle of orbifold covariance.*
  Phys. Lett. B **394** (1997) 87–88.
- **[Ban98]** P. Bantay. *The Frobenius-Schur indicator in conformal
  field theory.* Phys. Lett. B **394** (1997) 87.
- **[CGR2000]** A. Coste, T. Gannon, P. Ruelle. *Finite group modular
  data.* Nucl. Phys. B **581** (2000) 679–717.
  arXiv:[hep-th/0001158](https://arxiv.org/abs/hep-th/0001158).
- **[MN05]** G. Mason, S.-H. Ng. *Group cohomology and gauge
  equivalence of some twisted quantum doubles.* Trans. Amer. Math.
  Soc. **353** (2001) 3465–3509.
- **[NgS07]** S.-H. Ng, P. Schauenburg. *Higher Frobenius–Schur
  indicators for pivotal categories.* Contemp. Math. **441** (2007)
  63–90. arXiv:[math/0605226](https://arxiv.org/abs/math/0605226).
  Defines $\nu_n$ for general pivotal categories and proves the
  $(S, T)$-determination theorem.
- **[NgS10]** S.-H. Ng, P. Schauenburg. *Frobenius–Schur indicators
  and exponents of spherical categories.* Adv. Math. **211** (2007)
  34–71. arXiv:[math/0601012](https://arxiv.org/abs/math/0601012).
  Frobenius–Schur exponent and its relation to the order of $T$.
- **[IMN14]** M. Iovanov, G. Mason, S.-H. Ng. *Frobenius–Schur
  indicators for some families of quasi-Hopf algebras.* J. Algebra
  **425** (2015) 89–118. arXiv:[1305.1297](https://arxiv.org/abs/1305.1297).
  Closed-form formula used by `FSIforDoubles`.
- **[NN08]** D. Naidu, D. Nikshych. *Lagrangian subcategories and
  braided tensor equivalences of twisted quantum doubles of finite
  groups.* Comm. Math. Phys. **279** (2008) 845–872.
  arXiv:[0705.0665](https://arxiv.org/abs/0705.0665).
- **[EG18]** D. E. Evans, T. Gannon. *Reconstruction and local
  extensions for twisted group doubles, and permutation orbifolds.*
  arXiv:[1804.11145](https://arxiv.org/abs/1804.11145), 2018.
- **[ENO10]** P. Etingof, D. Nikshych, V. Ostrik. *Fusion categories
  and homotopy theory.* Quantum Topol. **1** (2010) 209–273.
  arXiv:[0909.3140](https://arxiv.org/abs/0909.3140). Categorical
  framework for $\mathrm{Aut}_\otimes(\mathcal C)$ as a categorical
  group; $\mathrm{Aut}(N, T)$ is its image at the decategorified,
  $T$-decorated level.
- **[BNRW16]** P. Bruillard, S.-H. Ng, E. Rowell, Z. Wang.
  *Rank-finiteness for modular categories.* J. Amer. Math. Soc.
  **29** (2016) 857–881.
  arXiv:[1310.7050](https://arxiv.org/abs/1310.7050). Uses
  $(N, T)$-rigidity in the classification of low-rank MTCs.

Lattice VOAs and twisted modules:
- **[BW61]** E. S. Barnes, G. E. Wall. *Some extreme forms defined in
  terms of Abelian groups.* J. Aust. Math. Soc. **1** (1959/60) 47–63.
- **[NRS01]** G. Nebe, E. M. Rains, N. J. A. Sloane. *The invariants
  of the Clifford groups.* Designs Codes Cryptogr. **24** (2001).
- **[Lep85]** J. Lepowsky. *Calculus of twisted vertex operators.*
  Proc. Nat. Acad. Sci. USA **82** (1985) 8295.
- **[Don91]** C. Dong. *Vertex algebras associated with even
  lattices.* J. Algebra **161** (1993) 245–265.
- **[BK04]** B. Bakalov, V. G. Kac. *Twisted modules over lattice
  vertex algebras.* in Lie theory and its applications in physics, V
  (2004) 3–26.
- **[Dav10]** A. A. Davydov. *Twisted automorphisms of group
  algebras.* arXiv:[0708.2664](https://arxiv.org/abs/0708.2664).
- **[vEMS17]** J. van Ekeren, S. Möller, N. R. Scheithauer. *Construction
  and classification of holomorphic vertex operator algebras.*
  arXiv:[1507.08142](https://arxiv.org/abs/1507.08142).

Cohomology of finite groups:
- **[Br82]** K. S. Brown. *Cohomology of Groups.* Graduate Texts in
  Mathematics 87. Springer, 1982.
- **[McL75]** S. Mac Lane. *Homology.* Grundlehren 114. Springer, 1975.
- **[Qui71]** D. Quillen. *The mod-2 cohomology rings of
  extra-special 2-groups and the spinor groups.*
  Math. Ann. **194** (1971) 197–212.
- **[KS]** D. B. Karagueuzian, P. Symonds. *Cohomology of small
  finite groups.* Online database, `http://groupcohomology.org/`.
  Explicit $\mathbb Z$-cohomology tables for groups of order
  dividing $128$, including $E_+(2)$ and $E_+(3)$.
- **[AM04]** A. Adem, R. J. Milgram. *Cohomology of Finite Groups.*
  Grundlehren 309, Springer, 2nd ed. 2004.
- **[Gor80]** D. Gorenstein. *Finite Groups.* Chelsea, 2nd ed., 1980.
- **[Tay92]** D. E. Taylor. *The Geometry of the Classical Groups.*
  Heldermann Verlag, 1992 (esp. Chapter 11 on Witt's theorem and
  $\mathbb F_2$-quadratic-form classification).
- **[Dic1901]** L. E. Dickson. *Linear Groups, with an Exposition of
  the Galois Field Theory.* Teubner, 1901.
- **[Wat03]** W. Waterhouse. *The discriminant of a quadratic form
  over a field of characteristic 2.* Linear Algebra Appl. **385**
  (2004) 75–80.

Computational:
- **[Ell08]** G. Ellis. *HAP — Homological Algebra Programming.* GAP
  package. <https://gap-packages.github.io/hap/>
- **[Höh96]** G. Höhn. *Selbstduale Vertexoperatoralgebren und das
  Babymonster.* Bonner Math. Schr. **286** (1996); also
  arXiv:[0706.0236](https://arxiv.org/abs/0706.0236).
- **[Höh19]** G. Höhn. *On the genus of the Moonshine module.*
  Festschrift for I. Frenkel (2019).
- **[Wit07]** E. Witten. *Three-dimensional gravity revisited.*
  arXiv:[0706.3359](https://arxiv.org/abs/0706.3359).
- **[Schur1904]** I. Schur. *Über die Darstellung der endlichen
  Gruppen durch gebrochene lineare Substitutionen.* J. Reine
  Angew. Math. **127** (1904) 20–50.
- **[Pas68]** D. S. Passman. *Permutation Groups.* W. A. Benjamin,
  1968. (Reference for projective characters & Schur cocycles.)
- **[Gru17]** A. Gruen. *Computing modular data for Drinfeld centres
  of pointed fusion categories.* B.Phil. thesis, ANU, 2017.
  Available at <https://tqft.net/web/research/students/AngusGruen/thesis.pdf>.
- **[GrM18]** A. Gruen, S. Morrison. *Computing modular data for
  pointed fusion categories.*
  arXiv:[1808.05060](https://arxiv.org/abs/1808.05060).
- **[MS17]** M. Mignard, P. Schauenburg. *Modular categories are not
  determined by their modular data.* Lett. Math. Phys. **108** (2018).
  arXiv:[1708.02796](https://arxiv.org/abs/1708.02796).
