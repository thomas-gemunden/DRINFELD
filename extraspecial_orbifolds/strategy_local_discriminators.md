# Strategy: detecting $S_{\mathrm{Keller}} \ne S_{\mathrm{untwisted}}$ without the full S

The user's framing: "*we aren't interested in the S matrix per se, but only if it is distinct from the untwisted S matrix up to relevant permutation. Perhaps we can show that they are different without having to compute to full thing.*"

This is the right framing. For $E_+(7)$ the full $S$ matrix is $\sim 10^8 \times 10^8$ entries, fundamentally beyond storage. But to **disprove** the conjecture $\omega = 0$, we only need to find ONE distinguishing feature; we never need the full thing.

## The decision problem

Given:
- $S_{\mathrm{untwisted}}$ — the modular data of $\mathrm{Mod}(D^1(E_+(m)))$. We have a complete library (`untwisted_modular_data.g` + closed-form central rows) that computes any entry in $O(1)$ given the character tables.
- $S_{\mathrm{Keller}}$ — the modular data of the orbifold MTC $\mathrm{Mod}(V_L^{E(7)})$. Keller's pipeline can compute single entries (or single rows) on demand, using the closed-form Gauss-sum machinery we ported in `defect_rep_minus_id_optim.g`.

The user wants to test:
$$
S_{\mathrm{Keller}} \stackrel{?}{=} \pi \cdot S_{\mathrm{untwisted}} \cdot \pi^{-1}
\qquad
\text{for some permutation } \pi.
$$

If the conjecture $\omega = 0$ holds, equality holds with $\pi$ the natural identification of simples (both pipelines pick the same conjugacy classes and irreps, modulo a section choice in the projective rep — but $c_g = 0$ has been verified, so the section is trivial up to coboundary).

If $\omega \ne 0$, equality fails and there is some entry that disagrees up to any permutation.

## What's already known to MATCH (every $m \in \{3, 5, 7\}$)

Pinned down by the c_g triviality + paper's analytic structure:

1. **Rank.** $2(4^m + 1) + (4^m - 1)(2 \cdot 4^{m-1} + 2)$. (`predict_e_plus_m.g`.)
2. **Per-sector rank.** Each non-central sector has $|\mathrm{Irr}(\mathbb Z_2 \times E_+(m-1))| = |\mathrm{Irr}(\mathbb Z_4 \circ E_+(m-1))| = 2 \cdot 4^{m-1} + 2$ irreps. (Forced by $c_g = 0$.)
3. **Per-sector irrep dimension multiset.** $4^{m-1}$ ones, plus two of dim $2^{m-1}$ (in non-central sectors). (Forced by $c_g = 0$ and the centraliser structure.)
4. **Quantum dimension multiset.** $d_{(g, \rho)} = |[g]| \cdot \dim \rho$, so $\{1^{4^m}, 128, 1^{4^m}, 128, \;\;\text{order-2 sectors}: 2^{4^{m-1}}, 128, 2^{4^{m-1}}, 128, \;\;\text{order-4 sectors}: \text{same shape}\}$ aggregating to a fully-determined multiset.
5. **Total quantum dimension squared.** $\mathcal D^2 = |G| = 2^{2m+1}$.
6. **T-eigenvalue multiset.** For $m = 7$ all the $\rho_g$ are integers, so $T_{\mathrm{Keller}} = T_{\mathrm{untwisted}}$ as multisets. (Multiplicities $\{1^{67145792}, (-1)^{67113024}, i^{8128}, (-i)^{8128}\}$ — see `predict_e_plus_m.g`.)
7. **Modularity** $S^2 = (ST)^3$. (Holds in any MTC; not a discriminator.)
8. **Categorical central charge** $c_{\mathrm{top}} \pmod 8$. For *any* untwisted Drinfeld double $D^0(G)$ this is $0$. For Keller's MTC, $c_{\mathrm{top}} = 128 \pmod 8 = 0$. Match — but doesn't discriminate.

So if we are to find a discriminator, it has to use *more* than the global numerical invariants; it has to involve specific entries.

## What changes between untwisted and twisted at a given entry?

For untwisted:
$$
S^{0}_{(g_1, \rho_1), (g_2, \rho_2)} \;=\; \tfrac{1}{|G|}
\sum_{\substack{a \in [g_1],\; b \in [g_2] \\ ab = ba}}
\overline{\rho_1(t_a^{-1} b\, t_a)}\,\overline{\rho_2(s_b^{-1} a\, s_b)}.
$$

For twisted with cocycle $\omega$ (and $c_g = 0$ everywhere, so projective characters reduce to ordinary characters under section choice):
$$
S^{\omega}_{(g_1, \rho_1), (g_2, \rho_2)} \;=\; \tfrac{1}{|G|}
\sum_{\substack{a \in [g_1],\; b \in [g_2] \\ ab = ba}}
\varepsilon_\omega(g_1, g_2, a, b)\;
\overline{\rho_1(t_a^{-1} b\, t_a)}\,\overline{\rho_2(s_b^{-1} a\, s_b)}.
$$

Here $\varepsilon_\omega(g_1, g_2, a, b)$ is a $|U(1)|$-valued phase computable from $\omega$. Explicitly,
$$
\varepsilon_\omega(g_1, g_2, a, b)
\;=\; \omega(g_1, g_2, a^{-1}b a)\,\omega(g_2, b, a)^{-1}\,\omega(b, a, b^{-1}g_1 b)
\;\;\;\text{(or some variant; conventions differ)}
$$

Crucially:
- If $\omega = 0$ (constant 1), $\varepsilon \equiv 1$ and $S^{\omega} = S^0$.
- If $\omega \ne 0$, $\varepsilon$ is generically a non-trivial phase.

The $\varepsilon$ values are *labels of cells* in $S$ — the SAME entry in $S^0$ and $S^\omega$ differs by a single phase factor (per commuting pair, summed).

## Local discriminators we can deploy

### Tier 1 — closed-form one-entry tests (cheapest)

For ANY central pair $(g_1, g_2) \in \{1, -1\}^2$ with $g_1 \ne 1$ or $g_2 \ne 1$:

We have a *closed form* for $S^0$ on those rows, no iteration. For $S^\omega$, the same formula evaluates with $\varepsilon$ inserted; the only data needed to compute $\varepsilon_\omega(g_1, g_2, a, b)$ is the cocycle $\omega$ at the four arguments.

**Cheapest single test.** Pick $g_1 = -1$, $g_2 = $ any non-central element. Evaluate $\varepsilon_\omega(-1, g_2, -1, b)$ for $b \in [g_2]$. If non-trivial for any $b$, $S^\omega \ne S^0$ in that entry.

Computational cost in Keller's pipeline: their `ShortComputeInterTwineref` already gives single-entry costs of ~75 ms for $m = 7$. From a single entry the phase $\varepsilon$ is recovered up to a known untwisted reference value.

### Tier 2 — sample row + multiset compare

Take one specific row of $S^\omega$ — say the $(1, \mathrm{trivial})$ row (the "vacuum row", whose entries are quantum dimensions divided by $\mathcal D$). Compute it via Keller's pipeline (rank entries, ~$10^8$ for $m=7$, but at 75 ms each that is ~$\sim 10^7$ s = months).

So *not* whole-row at $m = 7$. Tractable at $m = 5$ ($5\cdot 10^5$ entries × 2 ms = 1000 s = 17 min — easy).

Then sort and compare multisets. If quantum dimension multiset disagrees with the analytical untwisted prediction, $\omega \ne 0$.

### Tier 3 — symmetry test using known automorphisms

The S-matrix of $\mathrm{Mod}(D^1(E_+(m)))$ has automorphisms (induced by outer automorphisms of $E_+(m)$). These are computable.

Some of these automorphisms FIX the simples that come from central conjugacy classes. Their action on the $(-1, \cdot)$-th row should be a known permutation.

If $S^\omega$ has a different automorphism group structure on that row, the MTCs differ.

Concrete: compute $\mathrm{Aut}(N_{\mathrm{untwisted}})$ acting on the $(-1, \cdot)$ row — count fixed points / cycle structure. Compare to Keller's row (one row × |Out(G)| automorphism applications). Different fixed-point count → different MTCs.

This is what worked for the $Q_8$ investigation: $|\mathrm{Aut}(N, T)| = 6$ vs $24$. **Direct local invariant of the data, no full $S$ needed.**

### Tier 4 — kernel of the cohomology transgression

This is the most theoretically powerful test. If we can show the
relevant kernel is trivial, then the Keller conjecture
$\omega = 0$ follows *automatically* from their published evidence
$c_g = 0$, with no further computation required.

#### What is "the transgression" here?

In Dijkgraaf–Pasquier–Roche's construction of the twisted Drinfeld
double $D^\omega(G)$ [DPR91], the simple objects are pairs $(g, \chi)$
where $g$ ranges over conjugacy class representatives and $\chi$ is a
$c_g$-projective character of the centraliser $C_G(g)$. The 2-cocycle
$c_g \in Z^2(C_G(g); U(1))$ controlling that projective representation
is given explicitly in terms of $\omega$ (DPR91, eq. (2.7); also Coste–
Gannon–Ruelle [CGR2000], eq. (2.7); Evans–Gannon [EG18], eq. (2.1.3)):

$$
c_g(h_1, h_2) \;=\; \omega(g, h_1, h_2) \,+\, \omega(h_1, h_2, g) \,-\, \omega(h_1, g, h_2),
\qquad h_1, h_2 \in C_G(g).
$$

Because $g$ commutes with both $h_1$ and $h_2$ (they are in $C_G(g)$),
the ordinary cocycle condition for $\omega$ guarantees that $c_g$ is a
2-cocycle on $C_G(g)$. Coboundary changes of $\omega$ change $c_g$
only by 2-coboundaries on $C_G(g)$. So the assignment
$\omega \mapsto c_g$ descends to a homomorphism of abelian groups

$$
\mathrm{Tr}_g \colon H^3(G; U(1)) \;\longrightarrow\; H^2(C_G(g); U(1)),
$$

and assembling these over all conjugacy classes gives the **total
transgression**

$$
\mathrm{Tr} \colon H^3(G; U(1)) \;\longrightarrow\; \bigoplus_{[g]} H^2(C_G(g); U(1)),
\qquad
\mathrm{Tr}([\omega]) = \bigl([c_g]\bigr)_{[g]}.
$$

#### Why is $\mathrm{Tr}$ called a "transgression"?

The map $\mathrm{Tr}_g$ is the composition

$$
H^3(G) \;\xrightarrow{\mathrm{res}_g}\; H^3(C_G(g)) \;\xrightarrow{\,\backslash [g]\,}\; H^2(C_G(g))
$$

where $\mathrm{res}_g$ is the cohomological restriction induced by the
inclusion $C_G(g) \hookrightarrow G$ and $\backslash [g]$ is the
**slant product** with the canonical 1-cycle $[g] \in H_1(C_G(g); \mathbb Z)$
(well-defined because $g \in Z(C_G(g))$ — the centre of its own
centraliser). The slant product

$$
H^n(K; M) \;\otimes\; H_p(K; \mathbb Z) \;\longrightarrow\; H^{n-p}(K; M)
$$

is a standard operation in group cohomology; see Brown's textbook
[Br82, Chapter V.3] or McLane [McL75, Chapter VIII]. The closed form
$c_g(h_1, h_2) = \omega(g, h_1, h_2) + \omega(h_1, h_2, g) - \omega(h_1, g, h_2)$
is exactly the slant of $\omega$ by the 1-cycle $g$ at the cochain level.

This same construction appears in the literature on group-theoretic
modular data:
- **Dijkgraaf–Pasquier–Roche** [DPR91] introduced $D^\omega(G)$ and
  the projective characters with cocycle $c_g$.
- **Bantay** [Ban97, eq. 2.7] gives a clean version of the formula in
  the context of orbifold characters.
- **Coste–Gannon–Ruelle** [CGR2000] systematise the modular data.
- **Mason–Ng** [MN05] discuss when the resulting modular data depends
  on $\omega$ vs only on its image in subgroup cohomology.
- **Evans–Gannon** [EG18] — the paper Keller et al. cite — restate
  the formula in this context.
- **Naidu–Nikshych** [NN08] study Morita equivalence of pointed
  fusion categories in terms of (in particular) the kernel of related
  transgression-like maps.

#### Why the kernel matters

The Keller-Roberts-Roberts evidence consists, exactly, of verifying
that $c_g = 0$ in $H^2(C_G(g); U(1))$ for every conjugacy class
$[g]$ — i.e., $\mathrm{Tr}([\omega]) = 0$. Their conjecture is that
$[\omega] = 0$ in $H^3(G; U(1))$.

The question "does $c_g = 0\;\forall g$ imply $\omega = 0$?" is
exactly:

$$
\boxed{\;\;\ker \mathrm{Tr} \;\;=\;\; 0\;\; \text{?}\;\;}
$$

If the kernel is trivial, the implication holds and the conjecture
**follows automatically** from the verified $c_g = 0$ data — no
additional checks needed.

If the kernel is non-trivial, the c_g triviality data is consistent
with both $[\omega] = 0$ and certain non-zero classes; the conjecture
needs additional input.

#### Computational form

For a finite group $G$, $H^3(G; U(1))$ is a finite abelian group of
order $\prod_i d_i$ where $d_i$ are the invariant factors (UCT.torsion
in our code; computed by HAP's `GroupCohomology` via the Eilenberg–
MacLane / Cartan–Eilenberg machinery, [Ell08, HAP package
documentation]). Similarly each $H^2(C_G(g); U(1))$ is finite abelian.

$\mathrm{Tr}$ is a homomorphism between two finite abelian groups,
fully encoded by its matrix in fixed bases. Once that matrix is in
hand, the kernel is computed by Smith Normal Form over $\mathbb Z$ —
this is exactly what `NormalFormIntMat` in GAP does.

The cost is therefore split between

1. **Setup** — one resolution per centraliser (HAP
   `ResolutionFiniteGroup`) to get the basis of $H^2(C_G(g))$, plus
   one resolution of $G$ to get the basis of $H^3(G)$. For $E_+(7)$
   this is the bottleneck due to $|G| = 32{,}768$ and the fact that
   GAP's `ConjugacyClasses` for that order currently exhausts memory
   even at 60 GB; see the writeup's "Scaling caveats" section.

2. **Per-generator evaluation** — for each of the $k = $
   `Length(UCT.hombasis)` generators of $H^3(G; U(1))$, build the
   transgressed 2-cocycle $c_g$ on each centraliser, project onto
   $H^2(C_G(g))$. Total work scales like
   $k \cdot \#\{[g]\} \cdot $ (per-call cost).

3. **Linear algebra** — Smith Normal Form of an integer matrix
   whose row count is $k$ (the number of $H^3$ generators) and whose
   column count is $\sum_{[g]} k_{C_g}$ (sum of $H^2$-generator
   counts). Cheap relative to the setup.

For $E_+(m)$ with $m \le 3$ the setup is fast (minutes); $m = 5, 7$
need workarounds for `ConjugacyClasses` and `ResolutionFiniteGroup`.

#### Bibliographic references

* [DPR91] R. Dijkgraaf, V. Pasquier, P. Roche. *Quasi-Hopf algebras,
  group cohomology and orbifold models.* Nucl. Phys. B Proc. Suppl.
  **18B** (1990) 60–72; Comm. Math. Phys. **129** (1990).
* [Br82] K. S. Brown. *Cohomology of Groups.* Graduate Texts in
  Mathematics 87. Springer, 1982.
* [McL75] S. Mac Lane. *Homology.* Grundlehren der mathematischen
  Wissenschaften 114. Springer, 1975.
* [Ban97] P. Bantay. *Frobenius–Schur indicators, the Klein-bottle
  amplitude, and the principle of orbifold covariance.*
  Phys. Lett. B **394** (1997) 87–88.
* [CGR2000] A. Coste, T. Gannon, P. Ruelle. *Finite group modular
  data.* Nucl. Phys. B **581** (2000) 679–717. arXiv:hep-th/0001158.
* [MN05] G. Mason, S.-H. Ng. *Group cohomology and gauge equivalence
  of some twisted quantum doubles.* Trans. Amer. Math. Soc. **353**
  (2001) 3465–3509.
* [NN08] D. Naidu, D. Nikshych. *Lagrangian subcategories and braided
  tensor equivalences of twisted quantum doubles of finite groups.*
  Comm. Math. Phys. **279** (2008) 845–872. arXiv:0705.0665.
* [EG18] D. E. Evans, T. Gannon. *Reconstruction and local extensions
  for twisted group doubles, and permutation orbifolds.*
  arXiv:1804.11145.
* [Ell08] G. Ellis. *HAP — Homological Algebra Programming.* GAP
  package, 2004– .
* [Qui71] D. Quillen. *The mod-2 cohomology rings of extra-special
  2-groups and the spinor groups.* Math. Ann. **194** (1971) 197–212.
  Useful for the structure of $H^*(E_+(m); \mathbb F_2)$.
* [AM04] A. Adem, R. J. Milgram. *Cohomology of Finite Groups.*
  Grundlehren 309, Springer, 2nd ed. 2004. Reference for the
  cohomology ring structure of $E_+(m)$.

#### Computational state in this repository

* $D_8 = E_+(1)$: full brute-force enumeration of all 16 H^3 classes;
  $\ker \mathrm{Tr} = 0$. So the c_g triviality test is *sufficient*
  for $\omega = 0$ on $D_8$.
* $E_+(2)$: $|H^3| = 4096$. Per-generator linearity-based test
  ran on all 10 generators of $H^3$; **every generator has
  $\mathrm{Tr}(e_i) \neq 0$**. So $\ker \mathrm{Tr}$ contains no
  free generator — necessary but not sufficient for $\ker = 0$. To
  upgrade to "kernel exactly trivial" we still need the full Smith
  Normal Form of the $\mathrm{Tr}$ matrix (in progress).
* $E_+(3)$: $|H^3| \approx 7 \cdot 10^{10}$. Per-generator test
  expected to take many hours due to the
  $n^2 \times (n + n^2)$ augmented-system inner loop at $n = 64$.
  Deferred behind algorithmic improvement (HAP-based cohomology of
  cochains rather than the brute-force linear algebra solver).
* $E_+(7)$: $|H^3|$ astronomical; per-generator evaluation requires
  the centraliser character tables for all 16385 conjugacy classes,
  which currently runs into GAP's `ConjugacyClasses` memory ceiling.

### Tier 5 — Frobenius–Schur indicators

The FS indicators $\nu_n(X)$ are MTC invariants. For any simple $X$,
$$
\nu_n(X) = (1/|G|) \sum_{g \in G} \chi_X(g^n).
$$

For untwisted $D^1(G)$ this is computable from the character tables. For Keller's MTC, it's an output of their Schur-averaging pipeline (they may have already computed it for spot checks).

If FS indicators disagree on any one simple, the MTCs are distinct.

## Recommended order of attack

1. **Compute the untwisted $\mathrm{Aut}(N, T)$ structure for $E_+(m)$** at $m = 3$ first (full $(N, T)$ available) and tabulate it. This gives a baseline structural invariant we expect Keller's MTC to share if $\omega = 0$.
2. **Sanity-check on $E_+(2)$**: $\mathrm{Aut}(N, T)$ for the $E_+(2)$ untwisted center; compute via the full $S, T$ we already have. (Should match the untwisted center's known structure.)
3. **Tier 4**: compute the transgression kernel $H^3(E_+(3); U(1)) \to \bigoplus H^2(C_g)$ in HAP. Even at $m = 3$ this might already settle the conjecture for $m = 3, 5, 7$ via a comparable calculation, depending on whether the kernel is trivial.
4. **Tier 1 / Tier 5 spot checks**: pick one or two specific entries (or one FS indicator) where the closed-form untwisted value is easy and Keller's pipeline can be coaxed to give a single number. Compare.

## Caveats

- We have *not* yet built a concrete Keller-pipeline → S-entry adapter. The closed-form Gauss-sum library `defect_rep_minus_id_optim.g` gives single intertwiner entries; there is more work to assemble those into S-matrix entries. The relation between the intertwiner entries and the S-matrix needs the projector formula (2.1.2) of the paper.
- Tier 4 (the transgression kernel) is a known-finite calculation but its size at $m = 7$ is a real concern. Worth scoping before committing.
- "Permutation $\pi$" in the question ranges over relabelings of simples. The natural labelling on both sides is `(class of g, irrep of C_G(g))`, computed under the same `ConjugacyClasses(G)` ordering. Provided both pipelines pin down that ordering identically (we should verify), $\pi$ can be taken to be the identity for the cross-check, with no labelling search needed.

## What I propose we do next

Pick one of the recommended phases above. My ranking:

1. **Tier 4**, computing the kernel via HAP for $m = 3$, is the cleanest and may settle the question theoretically.
2. **Tier 1**, picking one specific entry and computing $\varepsilon_\omega$ directly from Keller's setup, would be the most direct.

Either is concrete this-session work.
