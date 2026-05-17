# K-4a and D-VAN: two independent witnesses for the Keller question

**Status.** Draft section for the methodology paper of the `DRINFELD` codebase. Slots after
the kernel-of-transgression section ($\S 4$ in the W-1a outline) and before the
numerical-results compendium ($\S 5$). Cross-references the W-1a outline at
`writeup/methodology.md`, the long-form mathematical writeup at
`extraspecial_orbifolds/writeup.md`, the $Q_8$ case study at `q8_extension_type/writeup.md`,
and the design specs for D-VAN (2026-05-15) and K-4a Phase 2 (2026-05-17) under
`docs/superpowers/specs/`.

---

## 1. The Keller question, restated for the general reader

In [KRR24] Keller, Roberts and Roberts construct an orbifold of the Barnes–Wall lattice
vertex operator algebra $V_{\mathrm{BW}(m)}$ by the extraspecial 2-group
$E_+(m) \cong 2_+^{2m+1}$ acting through (the lift of) its embedding into the
Bolt–Room–Wall group $\mathrm{BRW}(m) \le O(2^m, \mathbb R)$. The case
$m = 7$ would, granting their conjecture, produce a holomorphic VOA of central charge
$c = 128$ and gap $4$ — the first such example with gap larger than $2$
[Höh96, Höh19, Wit07]. The cases $m = 3$ (where the underlying lattice is $E_8$, so the
ambient lattice VOA is $V_{E_8}$ at $c = 8$, and the orbifold is well-understood) and $m = 5$
(at $c = 32$) are intermediate anchors.

Whether the orbifold $V_{\mathrm{BW}(m)}^{E_+(m)}$ is *untwisted* — that is, whether its
module category is equivalent to $\mathrm{Mod}(D^1(E_+(m)))$ rather than to
$\mathrm{Mod}(D^\alpha(E_+(m)))$ for some non-trivial 3-cocycle $\alpha \in H^3(E_+(m); U(1))$ —
is encoded by the obstruction class

$$
[\alpha] \;\in\; H^3(E_+(m);\, U(1)).
$$

When $[\alpha] = 0$ the orbifold is genuinely untwisted and the module category is the standard
quantum double of $E_+(m)$; the orbifold is a holomorphic VOA in the strict sense.
When $[\alpha] \ne 0$, the modular tensor category is the twisted double
$\mathrm{Mod}(D^\alpha(E_+(m)))$, which is still a perfectly good MTC but no longer
$D(E_+(m))$-mod, and the orbifold construction is a more delicate object (a *holomorphic
extension* in the language of [vEMS17] still exists, but the class of the extension is
encoded by $\alpha$).

**Keller's open question** ([KRR24] §1.4; also see [Keller24, arXiv:2410.18638]) asks whether
$[\alpha] = 0$ for $m = 5$ and $m = 7$. At $m = 3$, KRR verify $[\alpha] = 0$ directly by
producing the untwisted holomorphic VOA. At $m = 5, 7$ they verify *necessary* conditions
(triviality of the local 2-cocycles $c_g$ on every conjugacy class of $E_+(m)$, plus level
matching) and conjecture that those conditions are sufficient.

The conjecture would follow tautologically if the *total transgression* map
(see [methodology.md §1.1])

$$
\mathrm{Tr} \colon\; H^3(E_+(m); U(1)) \;\longrightarrow\; \bigoplus_{[g]} H^2(C_G(g); U(1)),
\qquad [\omega] \;\mapsto\; \bigl([c_g]\bigr)_{[g]}
$$

were injective. But it is not: the writeup at `extraspecial_orbifolds/writeup.md` and the
analysis in $\S 4$ of the W-1a outline show that $\ker(\mathrm{Tr})$ is in general non-trivial
for $E_+(m)$ with $m \ge 2$. Triviality of all $c_g$ pins $[\omega]$ into $\ker(\mathrm{Tr})$
but does not, on its own, force $[\omega] = 0$.

The present section describes two independent computational pipelines — K-4a and D-VAN —
that *do* let us decide $[\alpha] = 0$ vs $[\alpha] \ne 0$ at $m = 5, 7$, without computing
$H^3(E_+(m); U(1))$ explicitly and without enumerating its $\sim 2^{36}$ elements (at $m = 3$)
or vastly more (at $m \ge 5$).

## 2. Why the question is hard at $m = 5$ and $m = 7$

The order of the group is
$$
|E_+(m)| \;=\; 2^{2m+1}
\;=\; \begin{cases} 2\,048 & m = 5,\\ 32\,768 & m = 7.\end{cases}
$$
Worse, the 3-cohomology group $H^3(E_+(m); U(1))$ grows much faster than this. By the
universal coefficient theorem applied to the short exact sequence
$0 \to \mathbb Z \to \mathbb R \to U(1) \to 0$ and the vanishing of
$H^k(BG; \mathbb R)$ for $k \ge 1$ and $G$ finite, one has a natural isomorphism
$H^3(G; U(1)) \cong H^4(G; \mathbb Z)$. The integral 4-cohomology of $E_+(m)$ is computed
by [HaradaKono1987, Theorem 1.1] (see [R1-detecting-family]; for clarity we will
write $H^3$ throughout in $U(1)$ coefficients but use the identification with $H^4(-;\mathbb Z)$
when convenient). Its torsion structure is

$$
H^3(E_+(m); U(1))_{\text{tors}}
\;\cong\;
(\mathbb Z/2)^{r(m)} \;\oplus\; A(4),
\qquad
A(4) \;=\;
\begin{cases}
\mathbb Z/8 & m = 2,\\
\mathbb Z/4 & m \ge 3,
\end{cases}
$$

where the rank $r(m)$ of the elementary-abelian 2-part grows polynomially in $m$; HAP
computations give $r(2) = 9$ and $r(3) = 34$ for the cases we have explicit ground truth.
Consequently $|H^3(E_+(2); U(1))| = 2^{12}$ and $|H^3(E_+(3); U(1))| = 2^{36}$; at $m = 5, 7$
the order is correspondingly much larger and grows polynomially-many bits in $m$ — many orders
of magnitude beyond what can be enumerated.

Two routes present themselves.

**Route A (naive).** Compute $H^3(E_+(m); U(1))$ in full via HAP, find KRR's specific class
$\alpha$ as a coordinate vector, and read off whether the vector is zero. This is
computationally infeasible already at $m = 3$: the bar resolution at this depth is too large
to load into memory, and even the HAP-style finitely-generated chain-complex approach takes
several minutes to deliver $H^3$ at $m = 3$ and bogs down at $m = 5$ (the resolution at
$m = 5$ took 9 minutes wall and 1.2 GB RSS in our run; see issue #138). At $m = 7$ the
resolution is out of reach without dramatic algorithmic improvements (Q-int Path 3 / Pontryagin
square on the HAP compact resolution; see `docs/superpowers/specs/2026-05-16-path3-hap-resolution-redesign.md`).
Moreover, identifying KRR's specific $\alpha$ as a cohomology class from their VOA construction
requires either solving the kernel problem from local data (which is degenerate, since
$\ker(\mathrm{Tr})$ is large) or running a separate explicit cohomology pipeline. Either way,
the work is dominated by computing on $E_+(m)$ at scale.

**Route B (D-VAN).** Replace $H^3(E_+(m); U(1))$ with $H^3$ of carefully chosen subgroups
$H \le E_+(m)$ small enough to compute on. By a Quillen-style detection theorem (see $\S 3$)
the restriction map

$$
\mathrm{res}_{\{E,\, D_8,\, Q_8\}} \colon\;
H^3(E_+(m); U(1)) \;\longrightarrow\;
H^3(E; U(1)) \;\oplus\; H^3(D_8; U(1)) \;\oplus\; H^3(Q_8; U(1))
$$

is injective for $m \ge 2$ when $E$ ranges over (any one) maximal elementary abelian subgroup
and $D_8, Q_8$ are appropriately chosen rank-2 sections. The subgroup cohomology is small —
$|E| = 2^{m+1} \le 256$ for $m \le 7$, and $|D_8| = |Q_8| = 8$ always — so one HAP run on
each of $E, D_8, Q_8$ suffices to build the restriction matrices, and from then on every test
of an explicit $\omega$ is integer linear algebra on vectors of length at most a few dozen.

**Route C (K-4a).** Bypass the cohomology presentation of $\omega$ entirely. KRR's lattice
construction gives, for every conjugacy class representative $g \in E_+(m)$, a *projective
representation* $\phi_g \colon C_G(g) \to \mathrm{PGL}(W_g)$ on the $g$-twisted module $W_g$,
together with explicit lattice intertwiners $T_h \in \mathrm{GL}(W_g)$ for $h \in C_G(g)$.
The 2-cocycle of $\phi_g$ is $c_g$, which KRR have shown is trivial *as a class*; in fact a
stronger fact holds in KRR's setup, namely that $\beta_g$ (the cochain-level cocycle from
the $T_h$, see [CGR2000 §5.2]) is identically $1$ as a cochain — the so-called *CT case* of
[CGR2000]. By [CGR2000, equation (5.18)] this forces the 1-cochain trivialisation
$\varepsilon_g \colon C_G(g) \to U(1)$ of $\beta_g$ to be a character of $C_G(g)$, and
equations (5.20)+(5.21) of [CGR2000] then give a closed-form expression for the modular
matrices $(S^\alpha, T^\alpha)$ of $\mathrm{Mod}(D^\alpha(E_+(m)))$ purely in terms of
$\varepsilon$. So given KRR's lattice data we can compute $(S^\alpha, T^\alpha)$ directly,
without ever materialising $\alpha$ as a cocycle vector, and then check whether the resulting
modular data agrees with the untwisted $(S^0, T^0)$ — up to a *gauge* (permutation of sectors,
which is the only equivalence relation an MTC's $(S, T)$ admits up to MTC isomorphism for
$|G| < 32$; [Mignard-Schauenburg18]).

Routes B and C are independent in two senses. Algorithmically: B operates on cocycle vectors
and only ever invokes integer linear algebra over $\mathbb{Z}/\exp$; C operates on the
projective representations and invokes the modular-data closed-form of [CGR2000]. They share
no code paths and depend on different mathematical ingredients (Quillen detection for B; the
CT-case CGR formula for C). Epistemically: they answer Keller's question with different input.
B accepts an explicit 3-cocycle $\omega$ as input and returns "trivial" or "explicit non-zero
restriction"; C accepts KRR's lattice intertwiners as input and returns the modular data
itself. Cross-validation is essential precisely because they share no critical path.

## 3. The detecting family $\{E, D_8, Q_8\}$ — math foundation

The mathematical backbone of D-VAN (Route B) is the following:

**Claim.** For $G = E_+(m)$ and $m \ge 2$, the restriction map

$$
\mathrm{res} \colon\; H^3(G; U(1)) \;\longrightarrow\; H^3(E; U(1)) \;\oplus\; H^3(D_8; U(1)) \;\oplus\; H^3(Q_8; U(1))
$$

is injective, where $E$ is any maximal elementary abelian 2-subgroup of $G$, $D_8$ is any
dihedral-type rank-2 subgroup containing $Z(G)$, and $Q_8$ is any quaternion-type rank-2
subgroup containing $Z(G)$. Such $D_8$ and $Q_8$ exist for $m \ge 2$ by the central-product
decomposition $E_+(m) \cong D_8 * Q_8 * D_8^{*(m-2)}$ of [AM04, Remark IV.2.13].

No single paper states this claim in exactly this form. R-1 (issue #193, see
`docs/superpowers/research/2026-05-17-detecting-family-literature.md`) surveys the literature
and reports **Verdict B**: the claim is a routine assembly of three published results, with no
single citation but a clean two-page proof from the literature. The three ingredients are:

**Quillen 1971, Theorem 5.10** [Quillen1971]. The map
$H^*(E_+(m); \mathbb F_2) \to \prod_{W} H^*(\widetilde{W^\perp}; \mathbb F_2)$ is injective,
where the product is over maximal $Q$-isotropic subspaces $W$ of the symplectic
$\mathbb F_2$-vector space $V = E_+(m)/Z$ and $\widetilde{W^\perp}$ is the preimage of
$W^\perp$ in $E_+(m)$ (a maximal elementary abelian 2-subgroup of $E_+(m)$). This is the
*mod-2 detection theorem*: every mod-2 cohomology class of $E_+(m)$ is determined by its
restrictions to maximal elementary abelians.

**Harada–Kono 1987, Theorem 1.1** [HaradaKono1987]. The integral cohomology
$H^k(E_+(m); \mathbb Z)$ decomposes (modulo 2-torsion, in the relevant degrees) as
$A(k) \oplus V$, where $V$ is elementary abelian 2-torsion (captured by Quillen's mod-2
detection above) and $A(k)$ is a *cyclic* summand of order $2^{a(k, Q)}$ for $k \equiv 0 \pmod 4$
and zero otherwise. For $k = 4$ (which is the relevant degree, since $H^3(-; U(1)) \cong H^4(-; \mathbb Z)$):

- $A(4) \cong \mathbb Z/8$ at $m = 2$ (since $a(4, Q) = h(Q) + 1 = 3$ when $h(Q) = 2$);
- $A(4) \cong \mathbb Z/4$ at $m \ge 3$ (since $a(4, Q) = n(4) = 2$ when $h(Q) \ge 3$).

Here $h(Q) = m$ is the codimension of the maximal $Q$-isotropic subspace for the real-type
quadratic form, and $n(k)$ is the 2-adic valuation of $k$.

**Pham 2000** [Pham2000] (citing Adem–Karagueuzian [AdemKaragueuzian1997] for the structural
result). $Q_8$ is the *unique* finite 2-group with non-zero essential cohomology — i.e. the
unique 2-group in which every element of order 2 is central. Concretely $H^*(Q_8; \mathbb F_2)$
contains a degree-4 essential class $e_4$ not in the image of restriction from any proper
subgroup. This class lifts to a generator of the $\mathbb Z/8$ summand of $H^4(Q_8; \mathbb Z)$.

**Synthesis** (proved in R-1's note, §"Synthesis"). The elementary abelian summand $V$ of
$H^4(E_+(m); \mathbb Z)$ is detected by restriction to a maximal $E \subset E_+(m)$ by
Quillen 1971. The cyclic summand $A(4)$, which Quillen's mod-2 theorem cannot see, is detected
by restriction to either $D_8$ or $Q_8$: both have $H^4(\cdot;\mathbb Z) \supseteq \mathbb Z/8$
generated by their central-$\mathbb Z/4$ Pontryagin-square class, and the inclusion
$\langle z \rangle \le D_8$ or $\langle z \rangle \le Q_8$ (where $z$ generates the centre of
$E_+(m)$, which lies inside the central $\mathbb Z/4$ of each rank-2 section) is detection-faithful
on $A(4)$. We include both $D_8$ and $Q_8$ in the family for redundancy: each individually
should suffice at $m \ge 2$, but the empirical D-VAN-FIX investigation in issue #151 found a
configuration in which the $D_8$-only family failed to detect a specific class, and the
$Q_8$ addition fixed it.

The Quillen 1971 detection extends to all degrees, but at *integer* coefficients the cyclic
summand $A(k)$ for $k \equiv 0 \pmod 4$ is the obstruction; for our application $k = 4$, which
is precisely such a degree. For the mod-2 part Adem–Milgram [AM04, §IV.4–IV.5] gives the
F-isomorphism framework. (R-1's note flags a misattribution in earlier internal documents to
"AM04 IV.7"; the correct references are AM04 §IV.4–IV.5 plus Quillen 1971 plus Harada–Kono
1987; see `docs/superpowers/research/2026-05-17-detecting-family-literature.md`, §"Notes for
the methodology paper".)

A precedent for the same $\{E, D_8, Q_8\}$ detecting family appears in
[CarlsonThevenaz2005]: the group $T(G)$ of endo-trivial modules over a noncyclic finite
2-group is detected by restriction to the family of elementary abelian rank-2 subgroups and
(almost) extraspecial subgroups, which includes both $D_8$ and $Q_8$. The detection happens
in a different category, but the structural reason is the same: $Q_8$'s essential cohomology
is the unique obstruction to elementary-abelian-only detection.

For a sketch of the detection mechanism through the explicit ring structure of
$H^*(Q_8; \mathbb F_2)$ and $H^*(D_8; \mathbb F_2)$, see [AM04, Theorems IV.2.7 and IV.2.9].

## 4. D-VAN: algebraic approach via restriction maps

D-VAN (the *Detecting-family VANishing test*) is specified in the design document
`docs/superpowers/specs/2026-05-15-detecting-family-vanishing-test-design.md` (with the
$Q_8$-extension addendum in issue #153 / dvan-q8-extension branch). The public API is

```
ResIsTrivialOnDetectingFamily(m, omega_vec) -> rec(
    trivial    : bool,
    res_E_vec  : coordinate vector in H^3(E;   U(1)),
    res_D8_vec : coordinate vector in H^3(D_8; U(1)),
    res_Q8_vec : coordinate vector in H^3(Q_8; U(1)),
    f_E, f_D8, f_Q8 : callables (g1, g2, g3) -> root of unity,
    source     : "hap" | "quillen"
)
```

The implementation works in two phases.

### 4.1 Phase 1 — HAP-based, $m \in \{2, 3, 5\}$

The pre-computed object is the *restriction matrix* $M_H$ for each $H \in \{E, D_8, Q_8\}$,
expressed in terms of a hom-basis on $H^3(G; U(1))$ and a hom-basis on $H^3(H; U(1))$:

$$
M_H \colon\; H^3(G; U(1)) \;\longrightarrow\; H^3(H; U(1)),
\qquad
[\omega] \;\mapsto\; [\omega|_H].
$$

The matrix is built by:

1. Computing the HAP resolutions of $G$ and $H$ to degree 4.
2. Lifting the inclusion $H \hookrightarrow G$ to a chain map via `EquivariantChainMap`.
3. Pulling back a basis of degree-3 cocycle classes on $G$ to $H$ along the chain map.
4. Reducing each pullback into the hom-basis on $H$ (with appropriate rescaling when the
   exponents of $H^3(G; U(1))$ and $H^3(H; U(1))$ differ; see the partial-fix commit
   `c1d7390` and the Q_8 generalisation in `913c73e`).

Once the matrix is built — a one-time cost — every subsequent test on a candidate $\omega_{\mathrm{vec}}$
is a single matrix–vector product followed by a zero-check:

$$
\mathrm{trivial} \;:=\; M_E\,\omega_{\mathrm{vec}} \equiv 0 \pmod{\exp_E}
\;\wedge\;
M_{D_8}\,\omega_{\mathrm{vec}} \equiv 0 \pmod{\exp_{D_8}}
\;\wedge\;
M_{Q_8}\,\omega_{\mathrm{vec}} \equiv 0 \pmod{\exp_{Q_8}}.
$$

The empirical anchors validating the restriction-matrix construction are documented in the
spec's test ladder (Gate 1A): on a hom-basis $\{e_i\}$ of $H^3(E_+(m); U(1))$ at $m = 2$ and
$m = 3$, the D-VAN verdict on each $e_i$ agrees with what is independently computed by
restricting $e_i$ through HAP. (The detection theorem of $\S 3$ says D-VAN's `trivial = true`
is equivalent to $[\omega] = 0$ in $H^3(G; U(1))$ itself — strictly stronger than
$[\omega] \in \ker(\mathrm{Tr})$, but the two have the same empirical behaviour on the basis
vectors at these $m$'s, since the kernel of $\mathrm{Tr}$ at these $m$'s is generated by
*relations among* basis vectors rather than by individual basis vectors.)  At $m = 2$ this
is 10 cases (10/10 agreement); at $m = 3$ it is 35 cases (35/35 agreement). Gate 1B specifically
exercises the $\mathbb Z/8$ summand of $A(4)$ at $m = 2$: its order-8 generator must restrict
non-trivially to $D_8$ or $Q_8$ (it cannot restrict trivially to elementary abelians alone),
which is the load-bearing test that elementary-abelian-only detection fails. The $m = 5$
anchor (Gate 1E) is gated on issue #47 (A-5b's kernel-of-transgression ground truth at $m = 5$)
and will be tested when that arrives.

### 4.2 Phase 2 — Quillen-based, $m = 7$

At $m = 7$ the HAP resolution of $E_+(7)$ is not currently within reach (the resolution
at $m = 5$ took 9 minutes and 1.2 GB; at $m = 7$ the projected memory cost is on the order
of TB, beyond what is feasible without a different algorithmic approach — Q-int Path 3 is
exploring this; see `docs/superpowers/specs/2026-05-16-path3-hap-resolution-redesign.md`).
Phase 2 avoids the HAP resolution by computing $M_H$ analytically from the canonical Quillen
presentation of $H^*(E_+(m); \mathbb F_2)$ (Q-2a, see `scripts/quillen_canonical_presentation.g`),
pulled back along the inclusions of generating sets, and then lifted to $H^4(-; \mathbb Z)$
via the Bockstein spectral sequence (Q-int A1; see `scripts/quillen_bockstein.g`). Phase 2
cross-validates against Phase 1 byte-for-byte at $m = 2, 3, 5$ before going live at $m = 7$;
this is Gate 2A of the D-VAN spec.

### 4.3 Strengths and weaknesses of D-VAN

**Strengths.**

- *Fast.* After the one-time restriction-matrix build, every $\omega$-test is a sub-millisecond
  matrix-vector product.
- *Algebraic.* No modular-data machinery is required: the test operates entirely on cocycle
  coordinate vectors, and the answer is "yes/no/here is the explicit non-zero restriction".
- *Faithful to the kernel question.* D-VAN tests injectivity of $\mathrm{res}$, which is the
  cohomology-level question. A "non-trivial" verdict from D-VAN comes with an explicit
  coordinate vector in $H^3$ of one of the detecting subgroups; this is meaningful structural
  information, not just a boolean.

**Weaknesses.**

- *Requires $\omega$ as a cocycle vector.* D-VAN's input is $\omega \in H^3(E_+(m); U(1))$
  in some basis (hom-basis or R-basis). KRR do not give us $\omega$ as a cocycle vector;
  they give us a lattice orbifold. Extracting $\omega$ from KRR's data would amount to running
  the inverse cohomology problem on $E_+(m)$ (the "D-INV" workstream, currently parked at
  issue #140 pending Q-int and D-VAN Phase 2). So D-VAN's primary use case for the Keller
  question is *not* on KRR's $\omega$ directly, but on:
  - Specific candidate $\omega$'s nominated by external means (e.g. an explicit guess
    derived from the level-matching constraint of [vEMS17]).
  - The *kernel question itself*: by running D-VAN over a basis of $H^3(E_+(m); U(1))$ we
    can map out the entire kernel of the relevant restriction, independent of any specific
    application. This is "D-INV" downstream.
- *Doesn't see the lattice.* D-VAN is a test on $H^3(E_+(m); U(1))$ as an abstract finite
  abelian group. It has no access to KRR's lattice intertwiners or to the VOA-specific
  structure that determines $\alpha$. If two different VOA orbifolds happened to share the
  same $E_+(m)$-cocycle $\omega$, D-VAN would not distinguish them — they are the same
  question from D-VAN's perspective.

## 5. K-4a: modular-data approach via CGR §5.2

K-4a (the *Modular-data witness*) is specified in the K-4a Phase 2 implementation spec
at `docs/superpowers/specs/2026-05-17-k4a-phase2-implementation-spec.md` (after Phase 1
infrastructure, which produced the K-1 projector, K-2 S-Keller adapter, K-3 closed-form
central rows, and the K-4a-T1 / K-4a-T3 / K-4a-T4a math derivations). The public API is

```
K4aClassify(m) -> rec(
    m, group,
    epsilon_data,
    E_class    : rec from ClassifyOnAbelianE,
    D8_class   : rec from ClassifyOnD8,
    Q8_class   : rec from ClassifyOnQ8,
    trivial    : bool,
    verdict    : "trivial" | "non-trivial" | "incomplete"
)
```

### 5.1 KRR's lattice intertwiners and the CT case of [CGR2000]

KRR's construction provides, for every conjugacy class representative $g \in E_+(m)$, a
projective representation $\phi_g \colon C_G(g) \to \mathrm{PGL}(W_g)$ on the $g$-twisted
module $W_g$ of the lattice VOA $V_{\mathrm{BW}(m)}$. The structure is more refined than a
generic projective representation: lattice intertwiners $T_h \in \mathrm{GL}(W_g)$ for
$h \in C_G(g)$ are produced explicitly by Schur averaging on the defect representation, with
closed-form Gauss-sum evaluations (see `extraspecial_orbifolds/writeup.md §3` for the math
and `defect_rep_minus_id_optim.g` for the implementation).

The 2-cocycle $\beta_g$ of the projective representation $\phi_g$ — equivalently, the
2-cocycle that the intertwiners $T_h$ satisfy on $C_G(g)$ — is the *cochain-level* version of
the cohomology class $[c_g] \in H^2(C_G(g); U(1))$ from $\S 1.2$ of the methodology paper.
For Keller's orbifold KRR have verified more than just $[c_g] = 0$: they have shown that
$\beta_g \equiv 1$ as a *cochain*, not just up to coboundary. This is the so-called *CT case*
in [CGR2000 §5.2]: the projective representation lifts not just to a genuine representation
in some basis, but to one obtained from the explicit lattice intertwiners with no residual
cocycle.

When $\beta_g \equiv 1$ as a cochain, [CGR2000, equation (5.18)] states that the 1-cochain
trivialisation

$$
\varepsilon_g \colon\; C_G(g) \;\longrightarrow\; U(1),
\qquad
\delta \varepsilon_g \;=\; \beta_g \;=\; 1,
$$

is itself a *character* of $C_G(g)$ (rather than just a 1-cochain). This is a non-trivial
structural simplification: an arbitrary 1-cochain trivialising a coboundary cocycle has a
linear-algebra-degree of freedom; insisting that it is a character cuts the freedom down to
just a choice of character among $|\widehat{C_G(g)}|$ possibilities.

### 5.2 CGR's closed-form $(S^\alpha, T^\alpha)$ from $\varepsilon$

With $\varepsilon$ in hand, [CGR2000, equations (5.20) and (5.21)] give the modular matrices
of $\mathrm{Mod}(D^\alpha(E_+(m)))$ in closed form. Writing simple objects as $(a, \chi)$
with $a$ ranging over conjugacy class representatives and $\chi$ over $\mathrm{Irr}(C_G(a))$
(genuine characters, since $\beta_a$ is trivial as a cochain), the $T$-matrix is

$$
T^\alpha_{(a, \chi),\, (a, \chi)} \;=\; \frac{\chi(a)}{\chi(e)} \cdot \varepsilon_a(a)
\qquad [\text{CGR2000 eq.~(5.21)}],
$$

and the $S$-matrix is (see [CGR2000 eq.~(5.20)], adapted to our notation)

$$
S^\alpha_{(a, \chi),\, (b, \rho)}
\;=\;
\frac{1}{|G|}
\sum_{\substack{x \in [a],\; y \in [b] \\ xy = yx}}
\sigma(x \mid y)^* \;\overline{\chi(t_x^{-1}\, y\, t_x)} \;\overline{\rho(s_y^{-1}\, x\, s_y)},
$$

with the phase $\sigma(x \mid y) := \varepsilon_x(y) \cdot \varepsilon_y(x)$ (CGR §5.2 eq.~(5.22)).
The asterisk denotes complex conjugation, and $t_x, s_y \in G$ are conjugating elements
$t_x g_1 t_x^{-1} = x$, $s_y g_2 s_y^{-1} = y$. For trivial $\varepsilon$ ($\equiv 1$) the
$\sigma$ factor disappears and this reduces to the Bantay–Coste–Gannon–Ruelle formula for the
*untwisted* $S^0$ ([methodology.md §1.2]).

### 5.3 Restriction to the detecting subgroup

Given the $\varepsilon$ on $G = E_+(m)$, we restrict to a detecting subgroup $H \in \{E, D_8, Q_8\}$
by the obvious mechanism:

1. Build $H$'s own simple-object index `BuildSimpleIndex(H)`.
2. For each $H$-class representative $r \in H$, find the $G$-class of $r$ (call it $[a_G]$)
   and a conjugating element $\tau$ with $\tau\, r\, \tau^{-1} = a_G$.
3. Define $\varepsilon^H_r(h) := \varepsilon^G_{a_G}(\tau\, h\, \tau^{-1})$ for $h \in C_H(r)$.

The CT property is preserved by restriction (a coboundary cocycle that is trivial as a cochain
on $G$ restricts to a coboundary cocycle that is trivial as a cochain on $H$), so we can feed
the restricted $\varepsilon^H$ into [CGR2000] equations (5.20)+(5.21) on $H$ to compute the
modular data $(S^\alpha|_H, T^\alpha|_H)$. This is `RestrictEpsilonToSubgroup` followed by
`ComputeCTModularData` in the K-4a Phase 2 spec.

### 5.4 Classification on each $H$

The modular data $(S^\alpha|_H, T^\alpha|_H)$ is then compared against the precomputed library
of modular data for $D^\omega(H)$ ranging over $\omega \in H^3(H; U(1))/\mathrm{Aut}(H)$. The
library lives under `modular_data/8/3/` for $D_8$ and `modular_data/8/4/` for $Q_8$
(precomputed via the Gruen–Morrison pipeline in `src/modular_data.g`); for the elementary
abelian $E$, we bypass the modular-data comparison entirely and use the closed-form
Eilenberg–Mac Lane structure of $H^3((\mathbb Z/2)^{m+1}; U(1))$ — for the abelian case,
the modular data is degenerate (every simple has dimension 1) and $\varepsilon$ alone is
the discriminating invariant (T-3 of the K-4a Phase 2 spec).

For $D_8$ and $Q_8$ the comparison is done by the *joint $(S, T)$-permutation matcher* of
$\S 7$ below. The result, for each $H$, is one of:

- *trivial*: $(S^\alpha|_H, T^\alpha|_H)$ is permutation-equivalent to $(S^0|_H, T^0|_H)$, the
  untwisted modular data of $D^1(H)$. This corresponds to $[\alpha|_H] = 0$ in $H^3(H; U(1))$.
- *non-trivial with explicit class*: $(S^\alpha|_H, T^\alpha|_H)$ is permutation-equivalent
  to $(S^{\omega_k}|_H, T^{\omega_k}|_H)$ for some $k$ indexing a non-trivial Aut-orbit of
  3-cocycles on $H$. This identifies the specific class $[\alpha|_H] \in H^3(H; U(1))$.
- *incomplete*: the matcher returns no match. This indicates either an implementation bug
  (most likely a sector-ordering inconsistency) or that $\alpha|_H$ lies outside the precomputed
  library, which would be a strong signal something is wrong upstream.

The triviality verdict at $E_+(m)$ is the conjunction over $H$:
$[\alpha] = 0 \iff [\alpha|_E] = 0 \wedge [\alpha|_{D_8}] = 0 \wedge [\alpha|_{Q_8}] = 0$.
By the detecting-family injectivity claim of $\S 3$, the implication is bidirectional.

### 5.5 Strengths and weaknesses of K-4a

**Strengths.**

- *Works directly from KRR's lattice data.* No need to materialise $\alpha$ as a cocycle
  vector. The pipeline ingests KRR's $T_h$ (or equivalently, the lattice 2-cocycle on
  $L_g^\perp / L(1-g)$) and produces modular data downstream.
- *Identifies the specific class on each $H$.* When $[\alpha|_H] \ne 0$, the K-4a output names
  the Aut$(H)$-orbit of $\alpha|_H$, not just "non-zero". This is more informative than D-VAN's
  coordinate vector (which gives the explicit cocycle, but at the cost of a basis choice that
  needs interpretation).
- *Closer to the physics.* The modular data $(S^\alpha, T^\alpha)$ is the actual object the
  VOA orbifold construction produces. K-4a's verdict at $H$ is about the literal modular tensor
  category $\mathrm{Mod}(D^\alpha(H))$.

**Weaknesses.**

- *Requires KRR-style lattice construction.* K-4a is not applicable to a generic
  $\omega \in H^3(E_+(m); U(1))$. It requires the CT case ($\beta_g \equiv 1$ as a cochain),
  which is special to lattice orbifolds.
- *Modular-data permutation-matching is non-trivial.* Even with rank 22 at $D_8$ and $Q_8$,
  matching $(S^\alpha|_H, T^\alpha|_H)$ against a stored $(S^{\omega_k}|_H, T^{\omega_k}|_H)$
  is a backtracking search over permutations of simples that fix the vacuum. See $\S 7$.
- *Untwisted = closed-form bypass at $E$.* The classifier on $E$ (abelian, all simples of
  dimension 1) is purely cohomological, not modular-data-matching. K-4a's claim "modular-data
  approach" is in some sense only true at the non-abelian sections; at $E$ we are doing
  algebra on $\varepsilon$ directly.

## 6. Cross-validation: K-4a and D-VAN as twin witnesses

The two pipelines admit a clean cross-validation protocol at fixed $m$.

### 6.1 $m = 3$ anchor

At $m = 3$ the underlying lattice is $E_8$ and the orbifold of $V_{E_8}$ by $E_+(3)$ is
expected to be untwisted ($[\alpha] = 0$); this is the known anchor against which Keller's
conjecture for $m = 5, 7$ is calibrated, and it is verified in [Keller24, §6].
(See `extraspecial_orbifolds/writeup.md` for the GAP-side reproduction of KRR's
$c_g = 0$ evidence at $m = 3$.)

The acceptance protocol at $m = 3$ is:

- D-VAN: `ResIsTrivialOnDetectingFamily(3, omega_KRR_vec)` returns `trivial = true`, where
  `omega_KRR_vec` is the zero vector (since $[\alpha] = 0$). This is a tautology and serves
  as a sanity check on the pipeline plumbing — not a non-trivial test of the math.
  A more interesting test is to run D-VAN on every $\omega$ in a hom-basis of
  $H^3(E_+(3); U(1))$ and confirm agreement with `computed/transgression/3/kernel.g`'s
  ground-truth $\ker(\mathrm{Tr})$ — this is Gate 1A of the D-VAN spec, currently passing.
- K-4a: `K4aClassify(3)` returns `verdict = "trivial"`. This is a non-trivial test of the
  K-4a pipeline: KRR's lattice $\varepsilon$ at $m = 3$ is constructed from the actual defect
  representation, fed through the CGR §5.2 formula, restricted to the three subgroups, and
  matched against the untwisted modular data. The verdict has to come out trivial.
  This is T7 of the K-4a Phase 2 spec.

Both verdicts at $m = 3$ are required before applying the pipelines at $m = 5$ or $m = 7$.
At the time of writing the K-4a $m = 3$ anchor (T7) is gated on the completion of T4b
(the implementation of the $\varepsilon_a$ recipe from T4a, issue #196 / #197), and the
D-VAN $m = 3$ anchor is passing (Gate 1A, 35 cases agreement).

### 6.2 $m = 5$, $m = 7$ verdicts and the consistency check

Once both anchors pass at $m = 3$, the production runs at $m = 5$ and $m = 7$ produce verdicts.
There are three possible outcomes per $m$, and the appropriate response to each is:

1. **Jointly trivial.** Both K-4a and D-VAN report $[\alpha] = 0$. This is strong evidence
   that Keller's orbifold is untwisted at this $m$, since the two pipelines share no critical
   path. The remaining doubt is whether the detecting-family injectivity (the load-bearing
   theorem of $\S 3$) really holds in this specific form — but R-1's literature survey gives
   a clean proof from Quillen 1971 + Harada–Kono 1987, so this doubt is small.

2. **Jointly non-trivial.** Both K-4a and D-VAN report $[\alpha] \ne 0$, and ideally agree on
   *which* cohomology class. This is strong evidence of a non-zero $\alpha$, and a research
   surprise: KRR's local conditions ($c_g$ trivial, level matching) would no longer be
   sufficient, and a careful inspection of which class was detected would yield a precise
   counterexample to "local data determines $[\omega]$".

3. **Disagreement.** One pipeline reports trivial and the other non-trivial. This is the
   *informative failure case*: it cannot be a true property of the orbifold (the modular
   data is uniquely determined by KRR's construction up to MTC isomorphism, and the
   cohomology class of $\alpha$ is uniquely determined by the modular data up to permutation
   of sectors). So a disagreement points to:

   - A bug in one or both pipelines: the most likely source. K-4a has more moving parts
     ($\varepsilon$ extraction, restriction, modular-data computation, permutation matcher);
     D-VAN has fewer (restriction matrix build, matrix-vector product, zero check). But D-VAN
     depends on a non-trivial mathematical claim (detection injectivity) and on the HAP-based
     restriction matrix construction being correct; K-4a depends on the CT case being
     correctly identified and the CGR closed-form being implemented faithfully.
   - A subtle assumption violation: e.g. KRR's setup is *not* the CT case (some $\beta_g$ is
     non-trivial as a cochain, even though the cohomology class is trivial). K-4a would need
     to extend beyond [CGR2000 §5.2]; D-VAN would continue to work as specified.
   - A detection-family failure: $\mathrm{res}_{\{E, D_8, Q_8\}}$ is not injective at this
     specific $m$ for this specific class. This would contradict R-1's synthesis and would
     be a substantial mathematical surprise. The fail-safe is to add more subgroups to the
     family until injectivity is restored.

   In all three disagreement subcases, the resolution path is the same: investigate the
   smaller of the two pipelines first (D-VAN), confirm its verdict against `computed/transgression/m/kernel.g`
   on a basis (the kernel-of-Tr ground truth at $m \le 5$), then either fix the K-4a bug or
   escalate to a math review.

The two routes also let us identify *which* specific cohomology class is responsible for
any non-trivial verdict, in two slightly different ways. D-VAN names the class by its
coordinate vector in $H^3(H; U(1))$ for $H \in \{E, D_8, Q_8\}$. K-4a names the class by
its Aut$(H)$-orbit index in the precomputed library `modular_data/8/3/` or `modular_data/8/4/`.
These two namings are interchangeable via a one-time table lookup; their agreement is itself
a cross-validation gate.

## 7. The joint matcher and sector reordering

Both K-4a and the underlying modular-data library face the same technical question: given two
modular-data pairs $(S, T)$ and $(S', T')$ of rank $N$, decide whether there is a permutation
$\pi$ of $\{1, \ldots, N\}$ fixing $\pi(1) = 1$ (the vacuum sector) such that

$$
T'_{\pi(i)} \;=\; T_i \qquad \forall i,
\qquad
S'_{\pi(i),\, \pi(j)} \;=\; S_{i,\, j} \qquad \forall i, j.
$$

This is the natural notion of equivalence: any MTC iso between $\mathrm{Mod}(D^{\omega}(H))$
and $\mathrm{Mod}(D^{\omega'}(H))$ has to permute the simples, with the vacuum fixed.
[Mignard-Schauenburg18, Theorem 5.4] establishes that for $|H| < 32$ this permutation
equivalence is a *complete* invariant of $\mathrm{Mod}(D^\omega(H))$ — i.e. modular data
determines the MTC up to braided fusion equivalence. So matching $(S^\alpha|_H, T^\alpha|_H)$
against the precomputed library is equivalent to identifying the MTC isomorphism class.

Naive search is infeasible already at rank 22 ($N! \approx 10^{21}$); a backtracking matcher
with sensible pruning is required. Borrowing the structure from the $Q_8$ work
(`q8_extension_type/scripts/find_permutation.g` and the writeup at
`q8_extension_type/writeup.md`):

**Bucketing.** Partition the simples of $(S, T)$ into buckets indexed by the joint invariant
$(d_i, T_i)$, where $d_i = S_{i,1}/S_{1,1}$ is the quantum dimension and $T_i$ is the
$T$-eigenvalue. Any valid $\pi$ has to permute buckets to themselves. At $D_8$ and $Q_8$ the
bucket structure is fine: in the $Q_8$ case study the buckets cut the search space from
$22!$ down to under $2^{16}$ before backtracking.

**Colour refinement.** Within each bucket, compute the multiset of $S$-row entries
$(S_{i,j})_j$ projected onto the unmatched indices. Two simples in the same bucket but with
distinct row multisets cannot map to each other. Iterate until the refinement stabilises.
For $D_8$ and $Q_8$ at small rank, colour refinement typically singles out most of the
permutation; backtracking handles the residual ambiguity.

**Backtracking.** Pick the smallest-fanout bucket, branch over the choices, propagate the
$T$-equality constraint and the $S$-equality constraint for all already-matched indices,
prune. The $Q_8$ case study reports backtracking with these prunes runs in milliseconds at
rank 22.

For the elementary abelian $E$, the simples of $D^\omega(E)$ are pairs $(a, \chi)$ with
$a \in E$ and $\chi \in \widehat{E}$, and the modular data is degenerate (all simples of
dimension 1, $T$-eigenvalues constrained by the explicit Eilenberg–Mac Lane formula). The
classification reduces to identifying $\omega$ as an element of $H^3(E; U(1)) \cong
H^4(E; \mathbb Z) \cong \mathbb Z/2^{?} \oplus \cdots$ directly via [DPR91] (which gives an
explicit isomorphism $H^3(E; U(1)) \to \text{set of MTCs of pointed type with structure constants
$\omega$}$). No backtracking is needed; T-3 of the K-4a Phase 2 spec handles this.

**Galois action.** Note that we are testing $(S, T)$-equivalence as *raw cyclotomic data*,
not up to Galois conjugation of the cyclotomic field. This is the *stronger* test: different
Galois conjugates of the same nominal MTC are genuinely different MTCs (different $S$-matrices),
and the orbifold-VOA construction produces a specific Galois conjugate. Reading equivalence
modulo Galois would be too coarse for our application; see [Mignard-Schauenburg18 §6] for
discussion. This is also why the $Q_8$ extension-type investigation in
`q8_extension_type/writeup.md` reports "*no Galois match either*": the raw-cyclotomic test
already separates the two classes, and Galois conjugation does not bridge them.

The matcher implementation lives at `extraspecial_orbifolds/scripts/joint_permutation_matcher.g`
(K-4a-T1, issue #192). The K-4a Phase 2 D_8 classifier (T2, issue #194) is a near-mechanical
clone parameterised by group choice.

## 8. The acceptance protocol

We collect the steps into an explicit protocol for declaring a verdict on Keller's question
at fixed $m$.

**Step 0 — Anchor at $m = 3$.** Both `K4aClassify(3)` and
`ResIsTrivialOnDetectingFamily(3, omega_KRR_3)` must return verdicts of `trivial`. This is
the bidirectional sanity check: K-4a's full pipeline correctly identifies a known-untwisted
orbifold; D-VAN's restriction infrastructure correctly identifies a known-zero class.

**Step 1 — Compute on the target $m$.** Run `K4aClassify(m)` and
`ResIsTrivialOnDetectingFamily(m, omega_candidates)`, where `omega_candidates` is whatever set
of candidate 3-cocycles is most useful (typically: zero, plus a basis of $H^3(E_+(m); U(1))$
to map out the relevant subspace; or the specific class identified by K-4a if non-trivial).

**Step 2 — Read verdicts.**

- *Both trivial.* Strong evidence Keller's orbifold is untwisted at this $m$. The verdict is
  "untwisted, contingent on the detecting-family injectivity of $\S 3$." For $m = 5, 7$ this
  is the conjectured outcome.
- *Both non-trivial, agreeing on the class.* Strong evidence of a non-zero $\alpha$. The verdict
  is "twisted, with $[\alpha|_H]$ in the orbit indicated, for each $H \in \{E, D_8, Q_8\}$."
- *Both non-trivial, disagreeing on the class.* This would be a contradiction; one of them is
  buggy. The disagreement should be triaged according to the protocol of $\S 6.2$.
- *Disagreement (one trivial, one non-trivial).* As in $\S 6.2$, investigate D-VAN first.
  If D-VAN's verdict matches the kernel-of-Tr ground truth (at $m = 3, 5$), the bug is in K-4a.
  Otherwise the bug is in D-VAN.
- *Incomplete (K-4a).* The K-4a permutation matcher returned no match; this is a clear bug
  signal. Investigation should not block on K-4a's incomplete verdict — D-VAN's verdict is the
  primary input until K-4a is fixed.

**Step 3 — Document.** Whatever the verdict, record:
- The exact GAP, HAP, and `modular_data/` library versions used.
- The full output of both pipelines (`epsilon_data`, `E_class`, `D8_class`, `Q8_class` from
  K-4a; `res_E_vec`, `res_D8_vec`, `res_Q8_vec`, `f_E`, `f_D8`, `f_Q8` from D-VAN).
- The exact subgroup choices (which Aut-orbit of $D_8$ and $Q_8$; which maximal $E$).
- The agreement (or disagreement) cross-table, for archival.

This protocol is deliberately conservative: at $m = 5, 7$ we do *not* declare Keller's
conjecture proven on the strength of either pipeline alone. The two routes are designed
specifically to fail differently, so that a unified verdict carries weight that a single
pipeline cannot.

## 9. Open questions and limitations

We close with a register of caveats and pending work.

**Detecting-family injectivity.** The load-bearing claim is that
$\mathrm{res}_{\{E, D_8, Q_8\}}$ is injective on $H^3(E_+(m); U(1))$ for $m \ge 2$. R-1
(issue #193, `docs/superpowers/research/2026-05-17-detecting-family-literature.md`) reports
that this is "Verdict B": no single citation, but a routine assembly of Quillen 1971,
Harada–Kono 1987, and the universal coefficient theorem. For this paper, our recommended
form is to state the claim explicitly (as in $\S 3$ above), sketch the two-page proof from
the three sources, and flag that no published paper makes the assembly. This is the right
level of qualification — readers can verify the claim independently from the cited sources
without taking it on faith. The "Open questions" of R-1's note flag that the Aut$(G)$-equivariance
of restriction (which we use implicitly when reducing cocycles modulo Aut) should be made
explicit if a referee asks.

**CT case only.** K-4a's pipeline requires KRR's CT condition: $\beta_g \equiv 1$ as a cochain,
not just as a cohomology class. This is automatic for KRR's specific lattice intertwiners
at $m = 3, 5, 7$ (as they explicitly verify by Schur averaging; see
`extraspecial_orbifolds/writeup.md §3`). For a *generic* twisted orbifold where $\beta_g$ is
only trivial up to coboundary, [CGR2000 §5.2] does not directly apply, and a more general form
of the modular-data formula (using a 1-cochain $\varepsilon$ that is not a character) would be
needed. The K-4a workstream does not currently handle this case. The D-VAN pipeline is unaffected:
it operates directly on $H^3(G; U(1))$ and is indifferent to whether the cocycle is realized
by a CT-case lattice construction or anything else.

**Detection injectivity at higher degree.** Quillen 1971 holds in all degrees mod-2, and
Harada–Kono 1987 Theorem 1.1 gives the cyclic $A(k)$ summand for all $k \equiv 0 \pmod 4$
(zero otherwise). So the detecting-family argument extends in principle to $H^k(G; U(1))$ for
any $k$ with $k + 1 \equiv 0 \pmod 4$. For our application $k = 3$ is the only relevant case
(twisted Drinfeld doubles are classified by $H^3$). Generalisations to module-category twists
or higher-form symmetries would need degrees $k \ne 3$ and the detection argument would have
to be revisited. R-1's note flags this as future work; we do not pursue it here.

**Galois action.** As noted in $\S 7$, the matcher tests $(S, T)$-equivalence as raw cyclotomic
data, *not* up to Galois conjugation of the cyclotomic field. This is the stronger test —
different Galois conjugates are genuinely different MTCs (different $S$-matrices) — and is the
correct one for our application, since the orbifold VOA construction produces a specific
Galois conjugate. If a future application asked for the *Galois-quotient* MTC isomorphism class,
the matcher would need to be relaxed to allow $\pi$-induced Galois action on cyclotomic entries.
We do not implement this. (See `q8_extension_type/writeup.md`'s "Galois twist $i \leftrightarrow -i$"
row in the equivalence ladder for an explicit case where Galois conjugation could in principle
identify two classes but does not, because the underlying classes are not Galois conjugates of
one another.)

**$D_8$-only vs $\{D_8, Q_8\}$ redundancy.** R-1's note flags that the empirical D-VAN-FIX
failure at $m = 3$ (issue #151), which motivated adding $Q_8$ to the detecting family, may
have been an implementation-specific Aut$(G)$-equivariance issue rather than a genuine
mathematical failure of the $\{E, D_8\}$-only family. The mathematical synthesis in R-1
suggests both $D_8$ and $Q_8$ should individually carry the relevant $\mathbb Z/4$ summand
of $A(4)$ for $m \ge 3$, so either alone might suffice. We keep both in the K-4a / D-VAN
pipelines for redundancy and as a hedge against this question; the small overhead of including
both is negligible compared to the cost of triaging a misdiagnosed empirical failure later.
This is a methodology choice rather than a mathematical necessity, and a future cleanup
(documented in R-1's TODO list) could drop one of $D_8$, $Q_8$ if a careful re-examination
of #151 reveals the issue was implementation-specific.

**Cross-validation in the disagreement case.** $\S 6.2$ describes how to triage a disagreement
between K-4a and D-VAN. We have *not* exercised this protocol on a real disagreement, by design:
both pipelines are still being built out, and the $m = 3$ anchor is the first place a genuine
double-pipeline check can occur. The protocol is therefore aspirational at the time of writing,
to be refined as actual data accumulates.

**Inverse cohomology problem.** Going from KRR's lattice $\varepsilon$ back to an explicit
$\omega$-vector in $H^3(E_+(m); U(1))$ — the "D-INV" workstream (issue #140) — is currently
blocked on Q-int Phase 2 and the full D-VAN restriction infrastructure. We do not need it for
the verdict at Keller's question (both K-4a and D-VAN as specified bypass this step), but
it would let us *name* the specific class $[\alpha]$ in $H^3(E_+(m); U(1))$ if one turns out
to be non-zero. Without D-INV, we identify $[\alpha]$ only by its restrictions to each $H$.

## References

We use the existing reference convention of `writeup/methodology.md` (Author Year-style keys,
with full BibTeX-style entries below). Entries appearing already in `writeup/methodology.md`
are not duplicated here; see that file for [AM04], [Ban97], [BK04], [BNRW16], [Br82], [BRW61],
[BW61], [CE56], [CGR2000], [DPR91], [DVVV89], [DLN15], [EG18], [Höh96], [Höh19], [Kir02],
[KRR24], [Lep85], [McC01], [McL75], [MN05], [NN08], [NRS01], [Quil71] (now
[Quillen1971] in our extended bibliography), [vEMS17], [Wit07], etc.

Additional citations introduced in this section:

```bibtex
@article{HaradaKono1987,
  author  = {Harada, Masana and Kono, Akira},
  title   = {On the integral cohomology of extraspecial 2-groups},
  journal = {Journal of Pure and Applied Algebra},
  volume  = {44},
  year    = {1987},
  pages   = {215--219},
  doi     = {10.1016/0022-4049(87)90025-9},
}

@article{Pham2000,
  author  = {Pham, Anh Minh},
  title   = {Essential Cohomology and Extraspecial $p$-Groups},
  journal = {Transactions of the American Mathematical Society},
  volume  = {353},
  number  = {5},
  year    = {2000},
  pages   = {1937--1957},
  doi     = {10.1090/S0002-9947-00-02689-1},
}

@article{Quillen1971,
  author  = {Quillen, Daniel},
  title   = {The Mod 2 Cohomology Rings of Extra-special 2-groups and the Spinor Groups},
  journal = {Mathematische Annalen},
  volume  = {194},
  year    = {1971},
  pages   = {197--212},
  doi     = {10.1007/BF01350050},
}

@article{AdemKaragueuzian1997,
  author  = {Adem, Alejandro and Karagueuzian, Dikran},
  title   = {Essential Cohomology of Finite Groups},
  journal = {Commentarii Mathematici Helvetici},
  volume  = {72},
  year    = {1997},
  pages   = {101--109},
  note    = {Hosted at \url{https://personal.math.ubc.ca/~adem/essential.pdf}.},
}

@article{CarlsonThevenaz2005,
  author  = {Carlson, Jon F. and Th{\'e}venaz, Jacques},
  title   = {The Classification of Torsion Endo-Trivial Modules},
  journal = {Annals of Mathematics},
  volume  = {162},
  number  = {2},
  year    = {2005},
  pages   = {823--883},
  doi     = {10.4007/annals.2005.162.823},
}

@article{MignardSchauenburg18,
  author  = {Mignard, Michael and Schauenburg, Peter},
  title   = {Modular categories are not determined by their modular data},
  journal = {Letters in Mathematical Physics},
  year    = {2021},
  volume  = {111},
  number  = {3},
  doi     = {10.1007/s11005-021-01410-4},
  note    = {Earlier preprint at \url{https://arxiv.org/abs/1708.06538}.},
}

@misc{Keller24,
  author = {Keller, Christoph A.},
  title  = {Talks and notes on the {Barnes--Wall} orbifold construction},
  year   = {2024},
  note   = {arXiv:2410.18638 and references therein.},
}
```

**Internal cross-references** (documents in this repository, not part of the formal
bibliography but cited inline for the reader following along):

- `writeup/methodology.md` — W-1a outline of the overall methodology paper (introduction;
  notation; transgression kernel; algorithms; results).
- `extraspecial_orbifolds/writeup.md` — long-form mathematical writeup, including the
  Magma → GAP port of [KRR24]'s evidence pipeline and the Schur-averaging closed-form.
- `q8_extension_type/writeup.md` — $Q_8$ extension-type case study at the order-2 cocycle,
  demonstrating that fusion-ring data alone is insufficient to detect MTC isomorphism but
  full $(S, T)$ data is.
- `docs/superpowers/specs/2026-05-15-detecting-family-vanishing-test-design.md` — D-VAN
  design specification (Phase 1 HAP; Phase 2 Quillen).
- `docs/superpowers/specs/2026-05-17-k4a-phase2-implementation-spec.md` — K-4a Phase 2
  implementation specification (T2 D_8 classifier, T4b $\varepsilon$ recipe, T5a restriction,
  T5b CGR closed-form, T6 orchestrator, T7 $m = 3$ anchor).
- `docs/superpowers/research/2026-05-17-detecting-family-literature.md` — R-1 literature
  survey synthesising the detection theorem for $\{E, D_8, Q_8\}$.

[R1-detecting-family] is shorthand throughout for the latter; in a formal version of this
paper the synthesis would be inlined or extracted to an appendix.
