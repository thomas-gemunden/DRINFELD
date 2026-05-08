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

## 5. Tier-4 transgression-kernel test

The technique itself is described in detail in §2.3 above and in the
companion strategy document
[`strategy_local_discriminators.md`](strategy_local_discriminators.md).
Here we record the empirical findings.

* $E_+(1) = D_8$: brute-force enumeration of all 16 H^3 classes
  shows kernel is **trivial**. So for $D_8$, the c_g triviality
  evidence is actually *sufficient* for $\omega = 0$.
* $E_+(2)$: $|H^3| = 4096$. Brute force borderline; per-generator
  test ran on all 10 generators of $H^3$ in 60 GB heap;
  **every generator has $\mathrm{Tr}(e_i) \neq 0$** (witnesses span
  16/17 conjugacy classes). Necessary but not sufficient for
  $\ker = 0$; needs the full SNF of the Tr matrix to upgrade.
* $E_+(3)$: $|H^3| \approx 7 \times 10^{10}$. Per-generator test
  expected to take many hours due to the
  $n^2 \times (n + n^2)$ augmented-system inner loop at $n = 64$.
  Deferred behind an HAP cohomology-of-cochains formulation.
* $E_+(7)$: centraliser data for canonical classes (orders $16384$)
  is now available — see §4.5; centraliser computation per non-canonical
  class is also fast (`Centralizer(G, x)` works fine on $E_+(7)$). The
  blocker for Tier-4 here is no longer centralisers but the size of
  $H^3(E_+(7); U(1))$ itself, which makes per-generator iteration
  costly even with the augmented-system optimisation.

## 6. Verification ladder

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
| $\ker \mathrm{Tr} = 0$ | (in progress) | — | — | per-generator + SNF |

## 7. Scaling caveats discovered along the way

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

## 8. Reproducing

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
gap -q -b -c 'Read("test_transgression_d8.g");'           # full enumeration on D_8
gap -q -b -o 60G -c 'Read("test_transgression_per_gen_e2.g");'  # per-generator on E_+(2)
```

All `.g` files in `scripts/` are pure GAP libraries (no `QUIT;` at end);
test/driver scripts begin with `test_` or `compute_` prefixes.
Computed outputs land under `extraspecial_orbifolds/computed/`.

## 9. References

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
- **[NN08]** D. Naidu, D. Nikshych. *Lagrangian subcategories and
  braided tensor equivalences of twisted quantum doubles of finite
  groups.* Comm. Math. Phys. **279** (2008) 845–872.
  arXiv:[0705.0665](https://arxiv.org/abs/0705.0665).
- **[EG18]** D. E. Evans, T. Gannon. *Reconstruction and local
  extensions for twisted group doubles, and permutation orbifolds.*
  arXiv:[1804.11145](https://arxiv.org/abs/1804.11145), 2018.

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
