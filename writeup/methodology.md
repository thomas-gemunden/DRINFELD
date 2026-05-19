# Modular data of twisted Drinfeld doubles of extraspecial 2-groups: methodology

**Working title.** *Twin witnesses for the Keller orbifold question: detecting-family restriction and CT-twisted modular data for the Barnes–Wall extraspecial 2-group orbifolds.*

**Status.** Draft, methodology consolidation. Supersedes the §1 introduction outline and the K-4a/D-VAN section that previously lived at `writeup/methodology_section_k4a_dvan.md`. Verification ground truth is anchored to the issue/PR numbers cited inline.

---

## 1. Introduction

### 1.1 The Keller question

A holomorphic vertex operator algebra (VOA) \(V\) of central charge \(c\) and a finite group \(G \le \mathrm{Aut}(V)\) together determine an *orbifold* \(V^G\) whose module category \(\mathrm{Mod}(V^G)\) is a modular tensor category (MTC) [DVVV89, Kir02, DLN15]. When \(G\) acts inner-faithfully on a lattice VOA \(V_L\), there is a conjectural identification
\[
  \mathrm{Mod}(V_L^G) \;\cong\; \mathrm{Mod}\bigl(D^{\omega}(G)\bigr)
\]
between the orbifold MTC and the representation category of the *twisted Drinfeld double* of \(G\) at a 3-cocycle \(\omega \in H^3(G;\, U(1))\) — the 't Hooft anomaly of the orbifold [DPR91, DVVV89, EvG18, MN05]. The class \([\omega]\) is in general non-trivial and is the principal obstruction to the orbifold being holomorphic (untwisted).

Keller, Roberts and Roberts [KRR24] (arXiv:2411.13646) study orbifolds of the Barnes–Wall lattice VOA \(V_{\mathrm{BW}(m)}\) by the extraspecial 2-group \(E_+(m) \cong 2_+^{2m+1}\) acting through (the lift of) its embedding into the Bolt–Room–Wall group \(\mathrm{BRW}(m) \le O(2^m, \mathbb R)\). Their main contribution is **Conjecture 5.2 (§5.3)** at \(m = 7\): granting that a certain anomaly 3-cocycle \(\omega \in H^3(E_+(7); U(1))\) vanishes, the holomorphic \(E(7)\)-orbifold of \(V_{\mathrm{BW}(7)}\) gives a holomorphic CFT of central charge \(c = 128\) with gap \(4\) — the first example with gap larger than \(2\) [Höh96, Höh19, Wit07]. The cases \(m = 3\) (underlying lattice \(E_8\), ambient lattice VOA \(V_{E_8}\) at \(c = 8\), orbifold work in [GK19, GK21]) and \(m = 5\) (at \(c = 32\), orbifold work in [MR24]) are intermediate anchors — KRR cite these prior works rather than redoing the construction.

**The Keller question** (our research framing, informed by KRR's necessary-condition checks) asks whether the obstruction class \([\alpha] \in H^3(E_+(m); U(1))\) controlling \(\mathrm{Mod}(V_{\mathrm{BW}(m)}^{E_+(m)})\) vanishes for \(m = 5\) and \(m = 7\). What KRR themselves verify:

- *Cochain-level intertwiner-2-cocycle triviality* (§4.4, eqs 4.4.3–4.4.10), at \(m \in \{3, 5, 7\}\). This is one necessary condition for \([\alpha] = 0\).
- *Level-matching / type-0 condition* of [vEMS17], at **\(m = 7\) only** (§5.3).

KRR's formal conjecture (Conjecture 5.2) applies only at \(m = 7\); they make no positive claim about \([\alpha] = 0\) at \(m = 3\) or \(m = 5\). The "Keller question" at \(m \in \{5, 7\}\) is our own framing, motivated by KRR's necessary-condition checks.

### 1.2 Notation and the local-cocycle obstruction

We fix conventions. Let \(G\) be a finite group with identity \(1_G\), centre \(Z(G)\), conjugacy class \([g] \subset G\) and centraliser \(C_G(g) \le G\). Group cohomology \(H^*(G; A)\) is taken with respect to the bar resolution unless stated. Almost all of our cohomology has coefficients in \(U(1) = \mathbb R/\mathbb Z\) or, equivalently, in \(\mathbb C^\times\). The universal-coefficient theorem (UCT) applied to \(0 \to \mathbb Z \to \mathbb R \to U(1) \to 0\), together with \(H^k(BG; \mathbb R) = 0\) for finite \(G\) and \(k \ge 1\), gives a natural isomorphism \(H^3(G; U(1)) \cong H^4(G; \mathbb Z)\); we use the two interchangeably, with restriction respected.

A 3-cocycle is a normalised \(\omega \colon G^3 \to U(1)\) satisfying
\[
  \omega(g_2, g_3, g_4) \cdot \omega(g_1, g_2 g_3, g_4) \cdot \omega(g_1, g_2, g_3)
  = \omega(g_1 g_2, g_3, g_4) \cdot \omega(g_1, g_2, g_3 g_4),
\]
modulo coboundaries \((d c)(g_1, g_2, g_3) = c(g_2, g_3) \cdot c(g_1 g_2, g_3)^{-1} \cdot c(g_1, g_2 g_3) \cdot c(g_1, g_2)^{-1}\). The **twisted Drinfeld double** \(D^\omega(G)\) of [DPR91] is a quasi-Hopf algebra whose representation category \(\mathcal Z(\mathrm{Vec}_G^\omega) = D^\omega(G)\text{-mod}\) is a modular tensor category depending only on \([\omega] \in H^3(G; U(1))\) [CGR2000, Ban97, Ban98]. Simple objects are pairs \((g, \chi)\) with \(g\) a conjugacy class representative and \(\chi\) an irreducible \(c_g\)-projective character of \(C_G(g)\). The **local 2-cocycle** \(c_g \in Z^2(C_G(g); U(1))\) is given on \(h_1, h_2 \in C_G(g)\) by the slant product
\[
  c_g(h_1, h_2) \;=\; \omega(g, h_1, h_2) \,\cdot\, \omega(h_1, h_2, h_2^{-1} h_1^{-1} g h_1 h_2) \,\cdot\, \omega(h_1, h_1^{-1} g h_1, h_2)^{-1}
  \tag{\(\dagger\)}
\]
[CGR2000 eq. 2.7, KRR24 eq. 1.3.1, AM04 §III.1]. Identity (\(\dagger\)) collapses to the standard expression \(\omega(g, h_1, h_2) - \omega(h_1, g, h_2) + \omega(h_1, h_2, g)\) when \(h_1, h_2 \in C_G(g)\) (so \(h_i g h_i^{-1} = g\)). Up to coboundary on \(\omega\), the class \([c_g] \in H^2(C_G(g); U(1))\) is well-defined; assembly across conjugacy classes gives the **total transgression**
\[
  \mathrm{Tr}\colon H^3(G; U(1)) \;\longrightarrow\; \bigoplus_{[g]} H^2(C_G(g); U(1)),
  \qquad [\omega] \mapsto \bigl([c_g]\bigr)_{[g]}.
\]
The terminology *transgression* matches the Lyndon–Hochschild–Serre differential \(d_3 \colon E_2^{0,2} \to E_2^{3,0}\) for the central extension \(\langle g \rangle \hookrightarrow C_G(g) \twoheadrightarrow C_G(g)/\langle g \rangle\), c.f. [AM04 §III.1, NN08 §3].

The KRR evidence is, in this language, that each \([c_g] = 0\) in the appropriate \(H^2(C_G(g); U(1))\), i.e. \([\alpha] \in \ker(\mathrm{Tr})\). The orbifold is genuinely untwisted iff \([\alpha] = 0\) outright. So the *Keller question is precisely whether the KRR-class lies in the kernel or at the origin of that kernel*. If \(\ker(\mathrm{Tr}) = 0\), the two coincide. If \(\ker(\mathrm{Tr}) \neq 0\), additional information is needed.

### 1.3 Why the question is hard at \(m = 5\) and \(m = 7\)

The order grows polynomially in \(2^m\):
\[
  |E_+(m)| = 2^{2m+1} = \begin{cases} 2048 & m = 5, \\ 32768 & m = 7. \end{cases}
\]
But \(H^3(E_+(m); U(1)) \cong H^4(E_+(m); \mathbb Z)\) grows much faster. The integral 4-cohomology decomposes [HaradaKono1987, Thm 1.1] as
\[
  H^4(E_+(m); \mathbb Z)_{\mathrm{tors}} \;\cong\; (\mathbb Z/2)^{r(m)} \oplus A(4),
  \qquad
  A(4) \cong \begin{cases} \mathbb Z/8 & m = 2, \\ \mathbb Z/4 & m \ge 3, \end{cases}
\]
where \(r(m)\) is the rank of the elementary-abelian 2-part; HAP runs give \(r(2) = 9\), \(r(3) = 34\), and \(r(m)\) growing polynomially in \(m\) thereafter. So \(|H^3(E_+(2); U(1))| = 2^{12}\), \(|H^3(E_+(3); U(1))| = 2^{36}\); at \(m = 5, 7\) the order is many orders of magnitude beyond what can be enumerated.

Two naive routes both fail:

- **Brute enumeration of \(H^3\).** Computationally infeasible already at \(m = 3\): an HAP resolution at \(m = 5\) took 9 minutes wall and 1.2 GB RSS in our run (issue #138). At \(m = 7\) the resolution memory cost is projected on the order of TB, beyond reach without algorithmic redesign (the Q-int Path 3 / Pontryagin-square reformulation, `docs/superpowers/specs/2026-05-16-path3-hap-resolution-redesign.md`).

- **Just verifying \(\ker(\mathrm{Tr})\).** The kernel is in general non-trivial. For \(E_+(2)\) we have \(\dim_{\mathbb F_2} \ker(\mathrm{Tr}) \ge 11\) (from \(|\ker| \ge 2048\) on the mod-2 part); for \(E_+(m)\) with \(m \ge 3\) the kernel is plausibly larger again. So \([c_g] = 0\) for all \(g\) pins \([\alpha]\) into \(\ker(\mathrm{Tr})\) but does *not* force \([\alpha] = 0\). The KRR evidence at \(m = 5, 7\) is then necessary but not sufficient by itself.

### 1.4 The twin-witness strategy

We resolve Keller's question at \(m = 5, 7\) by running two *independent* computational pipelines, each producing a verdict on \([\alpha] \stackrel{?}{=} 0\) without ever materialising \([\alpha]\) as a coordinate vector in \(H^3(E_+(m); U(1))\) (which we cannot compute at \(m = 7\)):

**D-VAN** (the *Detecting-family VANishing test*) tests the algebraic question
\[
  \mathrm{res} \colon H^3(E_+(m); U(1)) \to H^3(E; U(1)) \oplus H^3(D_8; U(1)) \oplus H^3(Q_8; U(1))
\]
for injectivity on a cocycle vector. By the detection theorem of §3, this map is injective for \(m \ge 2\), and \([\alpha] = 0\) iff its restrictions to \(E\), \(D_8\) and \(Q_8\) are all trivial. Subgroup orders are bounded: \(|E| = 2^{m+1} \le 256\) for \(m \le 7\) and \(|D_8| = |Q_8| = 8\) always, so one HAP run per subgroup suffices.

**K-4a** (the *modular-data witness*) bypasses the cohomology presentation of \(\alpha\) entirely. From KRR's explicit lattice intertwiners on the \(g\)-twisted modules, the so-called *CT case* (cohomologically trivial — \(\beta_g \equiv 1\) as a cochain, not just as a class) of [CGR2000 §5.2] gives a closed-form expression for the modular data \((S^\alpha, T^\alpha)\). We compute this on each detecting subgroup and match against the precomputed library of modular data for \(D^\omega(H)\), \(\omega \in H^3(H; U(1))/\mathrm{Aut}(H)\). The matcher is the joint \((S, T)\)-permutation matcher of §7, which is the *complete* invariant in the rank range we use by [MignardSchauenburg18, MignardSchauenburg21].

The two pipelines are independent algorithmically (no shared code paths) and epistemically (different mathematical ingredients: Quillen-type detection for D-VAN; the CGR §5.2 closed-form for K-4a). They are designed specifically to fail differently, so that a unified verdict carries weight that no single pipeline can. The acceptance protocol of §8 makes the cross-validation explicit and requires both to pass an \(m = 3\) anchor before applying to \(m = 5, 7\).

### 1.5 Reading guide

§2 is mathematical background: twisted Drinfeld doubles, modular data, transgression. §3 develops the mathematical foundation underlying D-VAN: the detection theorem for \(\{E, D_8, Q_8\}\) from Quillen 1971 + Harada–Kono 1987 + the Adem–Karagueuzian / Pham essential-cohomology argument, with R-1's literature synthesis (issue #193, PR #205) and R-1 follow-up's correction (issue #215, PR #219) integrated. §4 describes D-VAN: the restriction-matrix construction (Phase 1 HAP, Phase 2 Quillen), the verdict, and the gating tests. §5 describes K-4a: KRR's CT condition, the CGR §5.2 closed-form, restriction to detecting subgroups, the classifier on each subgroup. §6 explains the T4a finding that \(\varepsilon \equiv 1\) is the correct CGR gauge (issue #196, PR #206). §7 covers the joint \((S, T)\) matcher (signature pruning + backtracking with online consistency checks) and the Mignard–Schauenburg completeness it implements. §8 is the acceptance protocol: the \(m = 3\) anchor, the \(m = 5, 7\) verdict triage, and the cross-validation cases. §9 records current status (K-3 anchor and its full \(S\) + \(T\) extension verified; K-4a Phase 2 \(m = 3\) anchor passes end-to-end at 39/39 assertions in 3.4 s; \(m = 5\) production blocked on the sparse-trace replacement #220 and the lifting of the \(m \le 3\) cap in `k4a_classify.g`; \(m = 7\) future) and open questions. References follow.

The infrastructure underpinning the kernel computation itself — torsion-split solver, BRW-symmetry reduction, centraliser-type caching, and resumable per-generator state — is documented in `writeup/section_3_infrastructure.md`; for the methodology paper it is treated as a black box delivering the empirical \(\ker(\mathrm{Tr})\) ground truth at \(m \le 3\) referenced throughout.

---

## 2. Mathematical setup

### 2.1 Twisted Drinfeld doubles \(D^\omega(G)\)

For a finite group \(G\) and \(\omega \in Z^3(G; U(1))\), the **twisted Drinfeld double** \(D^\omega(G)\) is the quasi-Hopf algebra of [DPR91] whose representation category is \(\mathcal Z(\mathrm{Vec}_G^\omega)\). As an MTC, \(\mathrm{Mod}(D^\omega(G))\) depends only on \([\omega] \in H^3(G; U(1))\), and simple objects are pairs \((g, \chi)\) with \(g\) a class representative and \(\chi\) an irreducible \(c_g\)-projective character of \(C_G(g)\) [CGR2000 §3, MN05 §2, BK04 §3.5]. The number of simples is \(\sum_{[g]} |\mathrm{Irr}_{c_g}(C_G(g))|\).

For \(\omega \equiv 1\) (untwisted), each \(c_g\) is trivial and \(\chi\) is an ordinary character. The modular matrices collapse to the **Bantay–Coste–Gannon–Ruelle formula** [Ban97, CGR2000, MN05]
\[
  T^0_{(g, \chi)} \;=\; \frac{\chi(g)}{\dim \chi},
  \qquad
  S^0_{(g_1, \chi_1), (g_2, \chi_2)} \;=\; \frac{1}{|G|}
  \sum_{\substack{a \in [g_1],\; b \in [g_2] \\ ab = ba}}
  \overline{\chi_1(t_a^{-1} b\, t_a)} \,\overline{\chi_2(s_b^{-1} a\, s_b)},
\]
with \(t_a, s_b \in G\) any conjugating elements (\(t_a g_1 t_a^{-1} = a\), \(s_b g_2 s_b^{-1} = b\)). For \(\omega \neq 1\) the formula picks up a \(U(1)\)-valued phase \(\varepsilon_\omega(g_1, g_2, a, b)\) inside the sum and replaces the ordinary characters by projective ones with multipliers \(c_a, c_b\). The CGR §5.2 closed form for the CT case (which is what KRR provide) is the subject of §5.2 below.

A foundational fact we use throughout: when \(|G| < 32\), the modular data \((S, T)\) is a *complete* invariant of \(\mathrm{Mod}(D^\omega(G))\) up to MTC isomorphism, i.e. up to permutation of the simples fixing the vacuum [MignardSchauenburg18 Thm 5.4, MignardSchauenburg21]. For \(D_8\) and \(Q_8\) (orders 8 < 32) this is what makes the K-4a matcher work. Beyond \(|G| = 32\), \((S, T)\) is no longer complete in general — Mignard–Schauenburg exhibit explicit pairs of inequivalent MTCs with identical modular data — but for the detecting subgroups \(E, D_8, Q_8\) used in the K-4a / D-VAN pipelines the inequality \(|H| \le 8\) holds strictly and completeness applies.

### 2.2 Local 2-cocycles and the slant product

For \(g \in G\) and \(h_1, h_2 \in C_G(g)\), the slant identity (\(\dagger\)) defines \(c_g \in Z^2(C_G(g); U(1))\), the *local 2-cocycle* (multiplier) of the projective representation \(\phi_g \colon C_G(g) \to \mathrm{PGL}(W_g)\) on the \(g\)-twisted sector \(W_g\). If \(g' = h g h^{-1}\) is in the same conjugacy class, the centralisers \(C_G(g)\) and \(C_G(g')\) are conjugate-isomorphic via \(h\), and \(c_{g'}\) is cohomologous to \(c_g\) under that identification [MN05 §2]; the class \([c_g] \in H^2(C_G(g); U(1))\) is therefore a conjugacy-class invariant.

The total transgression \(\mathrm{Tr}\) of §1.2 sends \([\omega]\) to the tuple \(([c_g])_{[g]}\). \(\mathrm{Tr}\) factors through \(H^3(G; U(1))\), is \(\mathbb Z\)-linear, and is the *kernel obstruction* of the KRR evidence chain: KRR's verification that all \(c_g\) are trivial says \([\alpha] \in \ker(\mathrm{Tr})\), nothing more.

The kernel \(\ker(\mathrm{Tr})\) is in general non-trivial. For \(E_+(2)\) the brute-force enumeration of the \(2^{12}\) classes of \(H^3(E_+(2); U(1))\) gives \(|\ker(\mathrm{Tr})| = 2048\); the structured Bockstein-based solver (T-1 through T-5 of `writeup/section_3_infrastructure.md`) reproduces this number on \(E_+(2)\) and extends to \(E_+(3)\), where direct enumeration of \(2^{36}\) classes is impossible. Two distinct routes converge on the same kernel size at \(E_+(2)\), giving the kernel computation an anchor that propagates to higher \(m\) via the per-orbit replay machinery of `transgression_per_generator_brw.g` (T-3d). At \(m = 3\) the kernel is large; at \(m = 5, 7\) its determination is not on the critical path of the Keller question, *precisely because* D-VAN and K-4a bypass the kernel question.

### 2.3 Extraspecial 2-groups \(E_+(m)\)

The extraspecial 2-groups \(E_+(m) \cong 2_+^{2m+1}\) (real type, plus signature) are the central extensions
\[
  1 \to \mathbb Z_2 \to E_+(m) \to (\mathbb F_2)^{2m} \to 1
\]
with the *plus* (real-type) quadratic form on the quotient; their order is \(|E_+(m)| = 2^{2m+1}\). The Bolt–Room–Wall group \(\mathrm{BRW}(m)\) is the normaliser of \(E_+(m)\) in \(O(2^m, \mathbb R)\) [BRW61, NRS01]; under \(\mathrm{BRW}(m)\), the conjugacy classes of \(E_+(m)\) collapse to four orbits: the two singleton central classes \(\{1\}\) and \(\{-1\}\), and two large orbits indexed by \(\sigma_2\)-type and \(\sigma_1\sigma_2\)-type, of size \(4^m - 1\) each. Centralisers fall into types: the full group at central elements; \(\mathbb Z_2 \times E_+(m-1)\) at \(\sigma_2\)-type; \(\mathbb Z_4 \circ E_+(m-1)\) at \(\sigma_1\sigma_2\)-type [AM04 §IV.2 Remark 2.13]. The Quillen rank (maximum rank of an elementary-abelian 2-subgroup) is \(m + 1\).

Two structural facts about \(E_+(m)\) are load-bearing for §3. First, the Adem–Milgram decomposition: every extraspecial 2-group is a central product of \(D_8\) and \(Q_8\) factors, and the real-type structure of \(E_+(m)\) gives
\[
  E_+(m) \;\cong\; D_8 * D_8 * \cdots * D_8 \quad (m\text{ factors})
  \;\cong\; Q_8 * Q_8 * D_8 * \cdots * D_8 \quad (m \ge 2)
\]
via the standard isomorphism \(D_8 * D_8 \cong Q_8 * Q_8\) [AM04 §IV.2 Remark 2.13]. Second, the Quillen rank-2 sections: any 2-dimensional \(\mathbb F_2\)-subspace \(W \subset E_+(m)/Z\) on which the quadratic form is isotropic gives a \(D_8\) section (preimage of \(W\) in \(E_+(m)\)); any anisotropic 2-dimensional \(W\) gives a \(Q_8\) section. Both types exist for \(m \ge 2\), and we exploit both in the detecting-family argument.

### 2.4 Cohomology of \(E_+(m)\)

The mod-2 cohomology of \(E_+(m)\) was computed by Quillen [Quillen1971 Thm 4.6]: as an \(\mathbb F_2\)-algebra,
\[
  H^*(E_+(m); \mathbb F_2) \;\cong\; S(V^*) / J \;\otimes_{\mathbb F_2}\; \mathbb F_2[w_{2^h}],
\]
where \(V = E_+(m)/Z\), \(S(V^*)\) is the symmetric algebra on its dual, \(J\) is the ideal generated by an explicit regular sequence \(\{Q(x), B(x, x^2), \dots, B(x, x^{2^{h-1}})\}\) controlled by the symplectic form on \(V\), and \(w_{2^h}\) is a polynomial generator of degree \(2^h\) with \(h = m\). The integral cohomology is given by Harada–Kono [HaradaKono1987 Thm 1.1]: in degrees \(k \equiv 0 \pmod 4\),
\[
  H^k(E_+(m); \mathbb Z) \;=\; A(k) \;\oplus\; V_k,
\]
where \(V_k\) is elementary abelian 2-torsion and \(A(k)\) is *cyclic* of order \(2^{a(k, Q)}\). The exponent \(a(k, Q)\) is governed by the codimension \(h(Q) = m\) of a maximal \(Q\)-isotropic subspace: \(a(k, Q) = n(k)\) if \(n(k) \le h(Q) - 1\), else \(a(k, Q) = h(Q) + 1\), where \(n(k)\) is the 2-adic valuation of \(k\). At \(k = 4\) (= \(H^3\) with \(U(1)\)-coefficients via UCT), \(n(4) = 2\), giving \(A(4) \cong \mathbb Z/8\) at \(m = 2\) and \(A(4) \cong \mathbb Z/4\) at \(m \ge 3\). In degrees \(k \not\equiv 0 \pmod 4\), \(A(k) = 0\).

For our application, the key consequence is that \(H^3(E_+(m); U(1))\) is the direct sum of a cyclic 2-torsion summand \(A(4)\) (order 8 at \(m = 2\), order 4 at \(m \ge 3\)) and an elementary-abelian 2-torsion summand \(V_4\) whose rank is the \(r(m)\) of §1.3 (\(r(2) = 9\), \(r(3) = 34\), etc.). The two summands play different roles in detection: \(V_4\) is captured by restriction to maximal elementary-abelians (Quillen 1971), while \(A(4)\) requires the \(D_8 \cup Q_8\) refinement (the §3 main result).

---

## 3. The detecting family \(\{E, D_8, Q_8\}\)

This section establishes the mathematical foundation of D-VAN: the restriction map to a small explicit family of rank-2 subgroups is injective on \(H^3(E_+(m); U(1))\). The result is not a single citation; it is a clean two-page assembly of Quillen 1971 + Harada–Kono 1987 + the Adem–Karagueuzian / Pham essential-cohomology framework + the universal coefficient theorem. R-1's literature survey (issue #193, PR #205) collected the sources; R-1's follow-up investigation (issue #215, PR #219) verified empirically that \(Q_8\) is genuinely required.

### 3.1 Statement

**Claim.** For \(G = E_+(m)\) with \(m \ge 2\), the restriction map
\[
  \mathrm{res}\colon H^3(G; U(1)) \;\longrightarrow\;
  H^3(E; U(1)) \oplus H^3(D_8; U(1)) \oplus H^3(Q_8; U(1))
\]
is injective, where:

- \(E \le G\) is *any* maximal elementary abelian 2-subgroup of rank \(m + 1\) (the preimage in \(G\) of a maximal \(Q\)-isotropic subspace of \(V = G/Z\));
- \(D_8 \le G\) is any rank-2 dihedral section, i.e. the preimage of a 2-dimensional \(Q\)-isotropic subspace of \(V\);
- \(Q_8 \le G\) is any rank-2 quaternion section, i.e. the preimage of a 2-dimensional \(Q\)-anisotropic subspace of \(V\).

Such \(D_8\) and \(Q_8\) sections both exist for \(m \ge 2\) by [AM04 §IV.2 Remark 2.13].

No single source states this in the form above. The closest precedents are [Quillen1971 Thm 5.10] (mod-2 detection by elementary abelians only) and [HaradaKono1987 Thm 1.1] (integral structure including the cyclic \(A(k)\) summand). The structural reason \(Q_8\) must appear is from Adem–Karagueuzian / Pham (\(Q_8\) is the unique 2-group with non-zero essential cohomology). The same \(\{E, D_8, Q_8\}\)-pattern, restricted to rank-2 elementary abelians plus (almost) extraspecial rank-2 sections, also detects the torsion endo-trivial modules of [CarlsonThevenaz2005], suggesting it is canonical in 2-group homological algebra.

### 3.2 Proof sketch (Quillen + Harada–Kono + UCT)

Apply the universal-coefficient theorem to \(0 \to \mathbb Z \to \mathbb R \to U(1) \to 0\): since \(H^k(BG; \mathbb R) = 0\) for finite \(G\) and \(k \ge 1\), the connecting homomorphism gives a natural isomorphism \(\delta \colon H^3(G; U(1)) \xrightarrow{\sim} H^4(G; \mathbb Z)\), compatible with restriction. So the claim reduces to injectivity of \(\mathrm{res} \colon H^4(G; \mathbb Z) \to H^4(E; \mathbb Z) \oplus H^4(D_8; \mathbb Z) \oplus H^4(Q_8; \mathbb Z)\).

By [HaradaKono1987 Thm 1.1], \(H^4(G; \mathbb Z) \cong A(4) \oplus V\) where \(A(4)\) is cyclic (\(\mathbb Z/8\) at \(m = 2\), \(\mathbb Z/4\) at \(m \ge 3\)) and \(V\) is elementary abelian 2-torsion.

*The \(V\) summand is detected on \(E\).* The mod-2 cohomology \(H^*(G; \mathbb F_2)\) injects into the product of \(H^*(\tilde W; \mathbb F_2)\) over maximal elementary abelians \(\tilde W = \pi^{-1}(W^\perp) \subset G\) by [Quillen1971 Thm 5.10], where \(W\) ranges over maximal \(Q\)-isotropic subspaces of \(V\). The summand \(V \subset H^4(G; \mathbb Z)\) is detected by the integral-to-mod-2 reduction inside \(H^4(G; \mathbb F_2)\); restriction to any one maximal elementary abelian \(E\) (rank \(m + 1\)) is then injective on \(V\), since for \(E_+(m)\) the action of \(\mathrm{Aut}(G)\) is transitive on maximal elementary abelians of given rank (a structural consequence of the orthogonal-group action on \(V\)).

*The \(A(4)\) summand is detected on \(Q_8\) (and partially on \(D_8\)).* The cyclic \(A(4)\) is not visible in \(H^4(E; \mathbb Z)\), which is a direct sum of \(\mathbb Z/2\) summands. To catch it we must restrict to a section with a *cyclic* \(\mathbb Z/8\) or \(\mathbb Z/4\) summand in degree 4. Both \(D_8\) and \(Q_8\) have such summands, but with crucial structural asymmetry:

- \(H^4(Q_8; \mathbb Z) \cong \mathbb Z/8\) is a single cyclic group of order 8, with no elementary-abelian 2-summand. This comes from \(Q_8\)'s 4-periodicity: \(H^4(Q_8; \mathbb Z) \cong \widehat H^0(Q_8; \mathbb Z) \cong \mathbb Z/|Q_8| = \mathbb Z/8\) [AM04 §IV.2 Thm 2.9, Lemma 2.10].
- \(H^4(D_8; \mathbb Z) \cong \mathbb Z/2 \times \mathbb Z/2 \times \mathbb Z/4\): a \(\mathbb Z/4\) summand from the order-4 normal-but-not-central cyclic subgroup \(\langle r \rangle\), plus two \(\mathbb Z/2\) factors from the elementary-abelian piece. Crucially, \(D_8\) has no cyclic \(\mathbb Z/8\) in degree 4: its centre is only \(\mathbb Z/2\), so the LHS spectral sequence cannot produce one.

The restriction \(\mathrm{res}\colon A(4)(G) \to H^4(Q_8; \mathbb Z)\) lands non-trivially on an *odd* element of \(\mathbb Z/8\) (e.g. 6 mod 8 in our pinned \(Q_8\) section at \(m = 3\), per the empirical analysis below), giving an injection \(\mathbb Z/4 \hookrightarrow \mathbb Z/8\). By contrast, the restriction \(\mathrm{res}\colon A(4)(G) \to H^4(D_8; \mathbb Z)\) lands in the \(\mathbb Z/4\) summand by *multiplication by an even integer* (i.e. by an element of the form \(2k\) in \(\mathbb Z/4\)), giving an image that is at most the unique \(\mathbb Z/2\) subgroup of \(\mathbb Z/4\). The order-2 sub-element of \(A(4)\) is therefore killed by \(D_8\) restriction but caught by \(Q_8\) restriction. *This is the Harada–Kono transfer-restriction "\(t \circ r = 2^h\)" formula in action* (HK Lemma 3.2): a \(Q\)-isotropic preimage in \(V^-\) — which is exactly what a \(D_8\) section is — satisfies the transfer-restriction multiplicativity-by-2 constraint; the \(Q\)-anisotropic preimage (the \(Q_8\) section) does not, because the transfer-restriction formula does not apply.

Steps for \(V\) and \(A(4)\) combine to give the injectivity claim.

### 3.3 Why \(Q_8\) is genuinely required (R-1 follow-up)

R-1's initial literature note (PR #205) raised the possibility — labelled a "surprise finding" — that the \(\{E, D_8\}\)-only family might suffice, with \(Q_8\)'s addition being implementation-specific. R-1's follow-up investigation (issue #215, PR #219, file `docs/superpowers/research/2026-05-17-d8-vs-q8-detection.md`) refuted this hypothesis empirically and rigorously.

The empirical experiment ran the \(\{E, D_8\}\)-only restriction on a basis vector \(e_g \in H^3(E_+(3); U(1))\) generating the cyclic \(A(4) \cong \mathbb Z/4\) summand, for each multiple \(c \cdot e_g\), \(c \in \{0, 1, 2, 3\}\). The \(\{E, D_8\}\)-only verdict correctly identified \(c = 0\) as trivial and \(c \in \{1, 3\}\) as non-trivial, but reported \(c = 2 \cdot e_g\) as *trivial* — a false positive. The full \(\{E, D_8, Q_8\}\) family correctly identified \(c = 2\) as non-trivial via the \(Q_8\) restriction.

To rule out a section-choice artefact, the investigation enumerated *all 280 conjugacy classes* of \(D_8\)-subgroups of \(E_+(3)\) (filtered by `IdGroup = [8, 3]`) and computed the restriction of \(e_g\) on each. The third coordinate of \(\mathrm{res}_{D_8}(e_g)\), in the \(\mathbb Z/4\) summand of \(H^4(D_8; \mathbb Z) \cong \mathbb Z/2 \times \mathbb Z/2 \times \mathbb Z/4\), took values in \(\{0, 2\} \subset \mathbb Z/4\) — never odd. So no choice of \(D_8\) section detects \(2 \cdot A(4)_{\mathrm{gen}}\) at \(m = 3\). Doubling any of the 280 rows gives \([0, 0, 0]\). This is uniform, not an implementation choice.

The same failure mode appears at \(m = 2\) on the order-2 element of \(A(4) \cong \mathbb Z/8\): the multiple \(4 \cdot e_g\) is non-zero in \(H^3\) but invisible to \(\{E, D_8\}\) (the \(D_8\) restriction returns \(2 \cdot [0, 0, 1] = [0, 0, 2] = [0, 0, 2]\), wait — \(2 \cdot [0, 0, 1]\) in torsion \([2, 2, 4]\) is \([0, 0, 2]\), so doubling once is fine; the failure shows on \(4 \cdot e_g\) which gives \([0, 0, 4] = [0, 0, 0]\) in torsion \([2, 2, 4]\) — see PR #219 §3.5 for the full table). The \(Q_8\) restriction returns \(4 \cdot [1] = [4]\) in torsion \([8]\), which is non-zero and detects the class.

**Verdict (PR #219):** Keep \(Q_8\) in the detecting family. The \(\{E, D_8\}\)-only failure is a genuine cohomological gap, not an implementation bug. The structural reason — \(D_8\)'s maximal cyclic factor in \(H^4(\cdot; \mathbb Z)\) is \(\mathbb Z/4\) (not \(\mathbb Z/8\)), so its image of \(A(4)\) cannot reach the order-2 sub-element — is consistent with Adem–Milgram's \(D_8\) cohomology computation and with Pham's / Adem–Karagueuzian's essential-cohomology theorem (\(Q_8\) is uniquely able to *not* lose information under restriction from a larger 2-group).

A subtler question — whether \(\{E, Q_8\}\) alone might suffice (i.e. whether \(D_8\) is the redundant member, opposite to R-1's original hypothesis) — is left open by PR #219 and out of scope here; the K-4a / D-VAN pipelines keep all three members for cross-validation reliability.

### 3.4 The detecting family in higher degrees

The injectivity argument extends to \(H^k(G; U(1))\) for any \(k\) with \(k + 1 \equiv 0 \pmod 4\) (i.e. \(k = 3, 7, 11, \dots\)): Quillen 1971 holds at all degrees mod-2, and Harada–Kono 1987 Thm 1.1 gives a cyclic \(A(k)\) summand whenever \(k \equiv 0 \pmod 4\) and zero otherwise. For our application only \(k = 3\) is relevant (twisted Drinfeld doubles are classified by \(H^3\)), but the general structure is worth noting for any future generalisation to module-category twists (higher \(k\)) or to higher-form symmetries.

---

## 4. D-VAN: the algebraic restriction pipeline

D-VAN's design specification is `docs/superpowers/specs/2026-05-15-detecting-family-vanishing-test-design.md`; the implementation lives in `extraspecial_orbifolds/scripts/detecting_family_restriction.g` and `extraspecial_orbifolds/scripts/detecting_family_vanish.g`, with the \(Q_8\) extension added in PR #156.

### 4.1 Public API

The public API is
\[
  \texttt{ResIsTrivialOnDetectingFamily}(m, \omega_{\mathrm{vec}}) \;\to\;
  \texttt{rec}(\texttt{trivial}, \texttt{res\_E\_vec}, \texttt{res\_D8\_vec}, \texttt{res\_Q8\_vec},
              \texttt{f\_E}, \texttt{f\_D8}, \texttt{f\_Q8}, \texttt{source})
\]
where `trivial : bool` is the verdict; `res_H_vec` are the explicit coordinate vectors in \(H^3(H; U(1))\) for each \(H \in \{E, D_8, Q_8\}\); the `f_H` are callable bar 3-cocycles realising the restricted classes; and `source` is \(\texttt{"hap"}\) or \(\texttt{"quillen"}\) depending on which phase produced the restriction matrices. The cocycle input \(\omega_{\mathrm{vec}}\) accepts either a hom-basis coordinate vector (length \(=\) `Length(UCT.hombasis)`, e.g. 10 for \(m = 2\), 35 for \(m = 3\)) or a raw \(R\)-basis cocycle vector (length \(=\) `R!.dimension(3)`); the wrapper dispatches by length.

The Keller-namespace wrappers `KellerTwistIsTrivial(m, omega_vec)` (just the boolean) and `KellerSEntry(m, omega_vec, i, j)` (dispatching to the closed-form \(S^0\) entry when the twist is trivial, else the K-2 S-Keller adapter) are thin layers on top.

### 4.2 Phase 1 — HAP-based restriction matrices, \(m \in \{2, 3, 5\}\)

The precomputed object is the *restriction matrix* \(M_H\) for each \(H \in \{E, D_8, Q_8\}\), expressed in terms of a hom-basis on \(H^3(G; U(1))\) and a hom-basis on \(H^3(H; U(1))\):
\[
  M_H \colon H^3(G; U(1)) \;\to\; H^3(H; U(1)),
  \qquad [\omega] \mapsto [\omega|_H].
\]

The matrix is built in four steps (file `detecting_family_restriction.g`, function `BuildRestrictionMatrices`):

1. Compute HAP resolutions of \(G\) and \(H\) to degree 4.
2. Lift the inclusion \(H \hookrightarrow G\) to a chain map via `EquivariantChainMap`.
3. Pull back a basis of degree-3 cocycle classes on \(G\) to \(H\) along the chain map.
4. Reduce each pullback into the hom-basis on \(H\), with appropriate rescaling when the exponents of \(H^3(G; U(1))\) and \(H^3(H; U(1))\) differ. This is the "Lcm-of-exponents rescale" fix: setting \(L = \mathrm{lcm}(\exp_G, \exp_H)\), \(\texttt{rescale\_G} = L / \exp_G\), \(\texttt{rescale\_H} = L / \exp_H\), then chain entries are rescaled to a common modulus. This handles both \(\exp_H \mid \exp_G\) (\(D_8\) case at \(m = 2\): \(L = 8\), `rescale_G = 1`, `rescale_H = 4`) and \(\exp_G \mid \exp_H\) (\(Q_8\) case at \(m = 3\): \(L = 8\), `rescale_G = 2`, `rescale_H = 1`). The rescale-fix patches are commits `c1d7390` (D_8) and `913c73e` (Q_8 generalisation).

Once \(M_H\) is built — a one-time cost dominated by the HAP resolutions — every subsequent test on a candidate \(\omega_{\mathrm{vec}}\) is a single matrix–vector product followed by a zero-check:
\[
  \texttt{trivial} \;:=\; M_E\, \omega_{\mathrm{vec}} \equiv 0 \pmod{\exp_E}
  \;\wedge\;
  M_{D_8}\, \omega_{\mathrm{vec}} \equiv 0 \pmod{\exp_{D_8}}
  \;\wedge\;
  M_{Q_8}\, \omega_{\mathrm{vec}} \equiv 0 \pmod{\exp_{Q_8}}.
\]
Each check is sub-millisecond.

**Empirical anchors.** The Gate 1A test ladder (specified in the D-VAN design doc, implemented in `tests/test_detecting_family_vanish.g`) runs on each generator of the hom-basis at \(m = 2\) and \(m = 3\) and confirms the D-VAN verdict against the independently computed restriction. At \(m = 2\) this is 10/10 agreement on the basis; at \(m = 3\) it is 35/35 agreement. Gate 1B specifically exercises the \(\mathbb Z/8\) summand of \(A(4)\) at \(m = 2\): the order-8 generator must restrict non-trivially to \(D_8\) or \(Q_8\), and we verify it lands on the order-8 image of \(H^4(Q_8; \mathbb Z)\). The \(m = 5\) anchor (Gate 1E) is gated on the kernel-of-\(\mathrm{Tr}\) ground truth at \(m = 5\) (issue #47, A-5b workstream) and is currently pending.

### 4.3 Phase 2 — Quillen-based restriction matrices, \(m = 7\)

At \(m = 7\) the HAP resolution of \(E_+(7)\) is not currently within reach: the resolution at \(m = 5\) took 9 minutes wall and 1.2 GB RSS, and at \(m = 7\) the projected memory cost is TB-scale without algorithmic redesign. Phase 2 avoids the HAP resolution by computing \(M_H\) analytically from the canonical Quillen presentation of \(H^*(E_+(m); \mathbb F_2)\) (Q-2a / `scripts/quillen_canonical_presentation.g`), pulled back along the inclusions of generating sets, then lifted to \(H^4(\cdot; \mathbb Z)\) via the Bockstein spectral sequence (Q-int A1 / `scripts/quillen_bockstein.g`). Phase 2 cross-validates against Phase 1 byte-for-byte at \(m = 2, 3, 5\) before going live at \(m = 7\) (Gate 2A of the D-VAN spec).

### 4.4 Strengths and weaknesses

**Strengths.**

- *Fast.* After the one-time restriction-matrix build, every \(\omega\)-test is a sub-millisecond matrix–vector product. The HAP resolution build is the dominant one-off cost; Phase 2 amortises this away at \(m = 7\) by replacing HAP with a closed-form Quillen presentation.

- *Algebraic.* No modular-data machinery is required: the test operates entirely on cocycle coordinate vectors. The output is "yes/no/here is the explicit non-zero restriction", with the non-zero restriction coming as an explicit coordinate vector in the relevant subgroup's \(H^3\).

- *Faithful to the kernel question.* D-VAN tests injectivity of \(\mathrm{res}\), which is the cohomology-level question. The "non-trivial" verdict is accompanied by a coordinate vector identifying the specific class — structural information beyond a boolean.

**Weaknesses.**

- *Requires \(\omega\) as a cocycle vector.* D-VAN's input is \(\omega \in H^3(E_+(m); U(1))\) in some basis. KRR do not give us \(\omega\) as a cocycle vector; they give us a lattice orbifold. Extracting \(\omega\) from KRR's data would amount to running the inverse cohomology problem on \(E_+(m)\) (the "D-INV" workstream, issue #140), which is currently blocked on Q-int Phase 2 and the full D-VAN restriction infrastructure. So D-VAN's primary use for the Keller question is *not* on KRR's \(\omega\) directly. It is on (i) specific candidate \(\omega\)'s nominated by external means (e.g. an explicit candidate derived from the level-matching constraint of [vEMS17]) and (ii) the kernel question itself, by sweeping a basis of \(H^3(E_+(m); U(1))\) and mapping out the relevant subspace.

- *Doesn't see the lattice.* D-VAN operates on \(H^3(E_+(m); U(1))\) as an abstract finite abelian group. Two different VOA orbifolds with the same \(E_+(m)\)-cocycle look identical to D-VAN.

For the Keller question proper, D-VAN provides the cross-validation witness; K-4a provides the *direct* lattice witness. Both must agree.

---

## 5. K-4a: the modular-data witness from CGR §5.2

K-4a's design specification is `docs/superpowers/specs/2026-05-17-k4a-phase2-implementation-spec.md`. Phase 1 (T1, T3, T4a) shipped the joint-permutation matcher, the closed-form abelian-cohomology checker, and the math derivation of \(\varepsilon_a\) (§6 below). Phase 2 wires these into an end-to-end pipeline: T2 (\(D_8\) classifier, PR #213), T4b (the \(\varepsilon\) callable, closed as superseded by T4c after the T4a finding moved the substantive content into `trace_on_W`), T4c (spectral `trace_on_W`, PR #218; m=5 variant in flight as #220), T5a (restriction to detecting subgroup, PR #217), T5b (CT modular data, PR #216), T6 (orchestrator, PR #224, with test fix in PR #228), and T7 (the \(m = 3\) anchor regression, closed by PR #224). The public API after Phase 2 is
\[
  \texttt{K4aClassify}(m) \;\to\;
  \texttt{rec}(m, \texttt{group}, \texttt{epsilon\_data}, \texttt{E\_class}, \texttt{D8\_class}, \texttt{Q8\_class}, \texttt{trivial}, \texttt{verdict}),
\]
with `verdict ∈ {"trivial", "non-trivial", "incomplete"}`.

### 5.1 KRR's lattice intertwiners and the CT case

KRR's construction provides, for every conjugacy class representative \(g \in E_+(m)\), a projective representation \(\phi_g \colon C_G(g) \to \mathrm{PGL}(W_g)\) on the \(g\)-twisted module \(W_g\) of the lattice VOA \(V_{\mathrm{BW}(m)}\). Lattice intertwiners \(T_h \in \mathrm{GL}(W_g)\) for \(h \in C_G(g)\) are produced explicitly. For the central sector \(g = z = -I\), \(L_g^\perp = L\) and \(N := L_g^\perp / L(1 - g) = L / 2L\) is an \(\mathbb F_2\)-vector space of rank \(2^m\). The Bakalov–Kac defect representation \((\rho, \Omega_0)\) of the finite Heisenberg group \(N\) is irreducible projective; choosing a symplectic basis \(\{\alpha_i, \beta_i \colon 1 \le i \le d\}\) of \(N\) with \(d = 2^{m-1}\), \(\Omega_0\) is the \(2^d\)-dimensional space with basis \(\{e_{\check c} \colon \check c \in \mathbb F_2^d\}\), and
\[
  \rho(\alpha)(e_{\check c}) = (-1)^{a \cdot \check c} \cdot e_{\check c + \check a}
\]
for \(\alpha = (a, \check a) \in \mathbb F_2^d \times \mathbb F_2^d\). Concretely \(\dim \Omega_0 = 16\) at \(m = 3\), \(65\,536\) at \(m = 5\), \(\sim 1.8 \times 10^{19}\) at \(m = 7\) — the latter being why \(T_h\) entries are computed in closed form rather than enumerated. The closed-form Schur-sum machinery is the `HardCodeShortComputeInterTwineref` family in `defect_rep_minus_id_optim.g`.

For each \(h \in C_G(g)\), \(\rho_h := \rho \circ h\) is again a projective rep of \(N\) (with cocycle \(P_h\)). The intertwiners \(T_h \colon \Omega_0 \to \Omega_0\) are constructed via Schur averaging (KRR eq. 4.1.5):
\[
  T_h \;:=\; \frac{1}{\sqrt{|N|}} \sum_{\alpha \in N} B_h(\alpha)^{-1} \cdot \rho(\alpha)^{-1} \cdot t \cdot \rho_h(\alpha),
\]
where \(t\) is a chosen linear map and \(B_h(\alpha)\) is a particular coboundary of \(P_h / P\) (KRR eq. 4.2.8). The \(T_h\) compose projectively (KRR eq. 4.1.4):
\[
  T_{h_1} T_{h_2} \;=\; \lambda(h_1, h_2) \cdot T_{h_1 h_2}.
\]
The scalar \(\lambda \colon C_G(g) \times C_G(g) \to \mathbb C^\times\) is the **cochain-level** version of the lattice 2-cocycle \(c_g\) on \(C_G(g)\).

For \(m \in \{3, 5, 7\}\) (KRR §4.4), the authors construct explicit lifts so that the \(T_h\)'s satisfy the *identity-on-the-nose* relations of \(E_+(m)/\langle z \rangle\):
\[
  T_h^2 = I, \qquad T_h T_{h'} = T_{h'} T_h \quad \forall h, h' \in \{\sigma\text{-generators}\}.
\]
Equivalently, \(\lambda \equiv 1\) on the generators (and hence on all of \(E_+(m)/\langle z \rangle\) by multiplicativity). So \(c_g \equiv 1\) *as a cochain*, not merely up to coboundary. This is the **CT case** (cohomologically trivial) of [CGR2000 §5.2].

Verification of the cochain-level identity has been ported from Magma to GAP (the optim pipeline in `defect_rep_minus_id_optim.g`) and runs through `test_defect_rep_optim.g` Test 3 (\(m = 5\)) and Test 4 (\(m = 7\)), modulo the choice of symplectic basis (our `SymplecticBasisF2` differs from KRR's Magma `WittDecomposition` but the substantive claims survive — see §6.4 of the T4a derivation note).

For the non-central conjugacy classes (\(g = \sigma_2\)-type and \(g = \sigma_1\sigma_2\)-type), KRR p.13 observe that the centraliser acts trivially on \(N\), so the intertwiner representation is itself trivial and \(c_g \equiv 1\) trivially. Only the central sector \(g = -I\) carries substantive content.

### 5.2 The CGR §5.2 closed-form

When \(\beta_g \equiv 1\) as a cochain (the CT case), [CGR2000 eq. 5.18] states that the 1-cochain trivialisation
\[
  \varepsilon_g \colon C_G(g) \to U(1), \qquad \delta \varepsilon_g = \beta_g = 1,
\]
is itself a 1-cocycle, i.e. a *character* of \(C_G(g)\). The modular matrices are (CGR eq. 5.20, 5.21; writing simple objects as \((a, \chi)\) with \(a\) a class representative and \(\chi\) a genuine character of \(C_G(a)\)):
\[
  T^\alpha_{(a, \chi),\, (a, \chi)}
  \;=\;
  \frac{\chi(a)}{\chi(e)} \cdot \varepsilon_a(a),
\]
\[
  S^\alpha_{(a, \chi),\, (b, \rho)}
  \;=\;
  \frac{1}{|G|}
  \sum_{\substack{x \in [a],\; y \in [b] \\ x y = y x}}
  \overline{\sigma(x \mid y)} \cdot \overline{\chi(t_x^{-1} y\, t_x)} \cdot \overline{\rho(s_y^{-1} x\, s_y)},
\]
with phase \(\sigma(x \mid y) := \varepsilon_x(y) \cdot \varepsilon_y(x)\) (CGR eq. 5.22). For \(\varepsilon \equiv 1\) the \(\sigma\) factor disappears and the formula reduces to the Bantay–Coste–Gannon–Ruelle expression for the untwisted \(S^0\).

The **critical observation**, stated in CGR immediately after eq. 5.22, is that
> "(5.20), (5.21) are (essentially, i.e. up to a relabelling of the characters \(\chi\)) independent of the choice of 1-cochains \(\varepsilon_a\) in (5.18), (5.19)."

So the modular data is gauge-invariant under the choice of \(\varepsilon_a\): different choices permute which projective character is paired with which group element, but the joint modular data is unchanged. The T4a finding (§6) is that under this gauge freedom, \(\varepsilon \equiv 1\) is the canonical choice.

### 5.3 Restriction to a detecting subgroup

Given \(\varepsilon\) on \(G = E_+(m)\), we restrict to a detecting subgroup \(H \in \{E, D_8, Q_8\}\) via `RestrictEpsilonToSubgroup` (T5a, `restrict_epsilon_to_subgroup.g`):

1. Build \(H\)'s simple-object index `BuildSimpleIndex(H)`.
2. For each \(H\)-class representative \(r \in H\), find its \(G\)-class \([a_G]\) and a conjugating element \(\tau\) with \(\tau r \tau^{-1} = a_G\).
3. Define \(\varepsilon^H_r(h) := \varepsilon^G_{a_G}(\tau h \tau^{-1})\) for \(h \in C_H(r)\).

The CT property is preserved by restriction (a coboundary cocycle trivial-as-cochain on \(G\) restricts to one trivial-as-cochain on \(H\)), so we can feed the restricted \(\varepsilon^H\) into CGR eq. 5.20+5.21 on \(H\) to compute \((S^\alpha|_H, T^\alpha|_H)\) via `ComputeCTModularData` (T5b, `ct_modular_data.g`).

Three edge cases are worth flagging. (i) An \(H\)-conjugacy class is in general a *subset* of a \(G\)-conjugacy class — an element may have larger centraliser in \(G\) than in \(H\) — so the map \(\texttt{class\_idx}_H \mapsto (\texttt{class\_idx}_G, \tau)\) is many-to-one on the \(G\) side. (ii) The conjugating element \(\tau\) need not lie in \(H\); we take it in \(G\). (iii) There are typically multiple non-conjugate \(D_8\) and \(Q_8\) subgroups; \(\texttt{D8Section\_E\_plus}(m)\) and \(\texttt{Q8Section\_E\_plus}(m)\) (in `quillen_detecting_subgroup.g`) pick canonical representatives. Under the detecting-family injectivity of §3, any single representative gives the same triviality verdict.

### 5.4 Classification on each \(H\)

The modular data \((S^\alpha|_H, T^\alpha|_H)\) is compared against the precomputed library of modular data for \(D^\omega(H)\), \(\omega \in H^3(H; U(1))/\mathrm{Aut}(H)\). The library lives under `modular_data/8/3/` for \(D_8\) and `modular_data/8/4/` for \(Q_8\) (Gruen–Morrison pipeline, `src/modular_data.g`). For the elementary abelian \(E\), we bypass the modular-data comparison and use the closed-form Eilenberg–Mac Lane structure of \(H^3((\mathbb Z/2)^{m+1}; U(1))\): for the abelian case the modular data is degenerate (every simple is one-dimensional), and \(\varepsilon\) alone is the discriminating invariant.

For \(D_8\) and \(Q_8\) the comparison is via the joint \((S, T)\)-permutation matcher of §7. The result on each \(H\) is one of:

- *trivial:* \((S^\alpha|_H, T^\alpha|_H)\) is permutation-equivalent to \((S^0|_H, T^0|_H)\), corresponding to \([\alpha|_H] = 0\) in \(H^3(H; U(1))\).
- *non-trivial with explicit class:* \((S^\alpha|_H, T^\alpha|_H)\) is permutation-equivalent to \((S^{\omega_k}|_H, T^{\omega_k}|_H)\) for some specific Aut(\(H\))-orbit class \(\omega_k\).
- *incomplete:* the matcher returns no match — either an implementation bug (most likely a sector-ordering inconsistency) or \(\alpha|_H\) lies outside the precomputed library (strong upstream-bug signal).

The triviality verdict at \(E_+(m)\) is the conjunction over \(H\): \([\alpha] = 0 \iff [\alpha|_E] = 0 \wedge [\alpha|_{D_8}] = 0 \wedge [\alpha|_{Q_8}] = 0\), bidirectional by §3's detection theorem.

The aggregator `K4aClassify(m)` (T6, `extraspecial_orbifolds/scripts/k4a_classify.g`) orchestrates the three classifications and returns the joint verdict. The \(m = 3\) anchor (T7, `extraspecial_orbifolds/scripts/tests/test_k4a_classify.g`) runs the full pipeline on the \(m = 3\) case where the orbifold is independently understood to be untwisted (BW(3) = E_8; see [GK19, GK21] for the orbifold theory) and confirms `verdict = "trivial"`; this is the gating test before applying to \(m = 5, 7\). It now passes 39/39 assertions in 3.4 s wall (well under the 300 s budget) per PR #224; the same test file additionally verifies the \(m = 2\) case (also `verdict = "trivial"`) as a bonus.

### 5.5 Strengths and weaknesses

**Strengths.**

- *Works directly from KRR's lattice data.* No need to materialise \(\alpha\) as a cocycle vector. The pipeline ingests KRR's \(T_h\) (equivalently, the lattice 2-cocycle on \(L_g^\perp / L(1 - g)\)) and produces modular data downstream.

- *Identifies the specific class on each \(H\).* When \([\alpha|_H] \ne 0\), the K-4a output names the Aut(\(H\))-orbit, not just "non-zero".

- *Closer to the physics.* The modular data \((S^\alpha, T^\alpha)\) is the actual object the VOA orbifold construction produces; K-4a's verdict at \(H\) is about the literal modular tensor category \(\mathrm{Mod}(D^\alpha(H))\).

**Weaknesses.**

- *Requires the CT case.* K-4a is not applicable to a generic \(\omega \in H^3(E_+(m); U(1))\); it requires \(\beta_g \equiv 1\) as a cochain, which is special to lattice orbifolds. KRR verify this explicitly for \(m \in \{3, 5, 7\}\). For non-CT \(\beta_g\) (only trivial up to coboundary), the more general CGR formula using a non-character 1-cochain \(\varepsilon\) would apply; K-4a does not currently handle that.

- *Permutation matching is non-trivial.* Even at rank 22 (\(D_8\), \(Q_8\)), matching \((S^\alpha|_H, T^\alpha|_H)\) against a stored \((S^{\omega_k}|_H, T^{\omega_k}|_H)\) is a backtracking search over permutations fixing the vacuum (§7).

- *Bypass at \(E\).* The classifier on \(E\) is cohomological, not modular-data-matching; the "modular-data approach" naming is precise only on the non-abelian sections.

---

## 6. The \(\varepsilon \equiv 1\) gauge (T4a)

The K-4a pipeline of §5 requires a choice of 1-cochain \(\varepsilon_a\) for each conjugacy class \(a \in G\). The K-4a-T4a derivation note (issue #196, PR #206, file `docs/superpowers/research/2026-05-17-epsilon-extraction-from-krr.md`) establishes that the *trivial* character \(\varepsilon \equiv 1\) is the canonical, mathematically correct choice for KRR's CT case, and that the natural alternative — extracting \(\varepsilon\) from \(T_h\) matrix entries on a putative "vacuum vector" of \(\Omega_0\) — is structurally impossible.

### 6.1 The CGR gauge-freedom argument

For \(\beta_a \equiv 1\) as a cochain (KRR's CT condition), CGR eq. 5.18 collapses to \(\delta \varepsilon_a \equiv 1\), making \(\varepsilon_a\) a 1-cocycle — i.e. a homomorphism \(C_G(a) \to U(1)\), or equivalently a *character* of \(C_G(a)\). Any character is a valid 1-cocycle satisfying eq. 5.18. By CGR's remark immediately after eq. 5.22, the modular data \((S^\alpha, T^\alpha)\) computed from CGR eqs. 5.20–5.21 is independent of the choice of \(\varepsilon_a\) up to relabelling of the projective characters \(\chi\) (which run over \(\mathrm{Irr}(C_G(a))\) for the genuine-rep case). So different choices of \(\varepsilon_a\) just permute the labels of the simples \((a, \chi)\); the modular data itself is invariant.

The simplest gauge-fixing choice is \(\varepsilon_a := \) trivial character of \(C_G(a)\). Under this choice:

- \(\sigma(h \mid g) = \varepsilon_h(g) \cdot \varepsilon_g(h) = 1 \cdot 1 = 1\) always.
- CGR eq. 5.20 simplifies to the untwisted-form \(S\) (no \(\sigma\) phase).
- CGR eq. 5.21 gives \(T^\alpha_{(a, \chi)} = \chi(a)/\chi(e)\).

All the non-trivial content of the modular data lives in the projective characters \(\chi\), not in \(\varepsilon\). For KRR's CT case at \(m \in \{3, 5, 7\}\), \(\chi\) is the *linear-character decomposition of \(\Omega_0\) under the commuting family \(\{T_h : h \in C_G(a)\}\)* in the central sector \(a = -I\); on the non-central sectors the centraliser acts trivially on \(N\) and \(\chi\) is just the regular character.

### 6.2 No canonical vacuum vector

The natural alternative — defining \(\varepsilon_a(h) := \langle v_a, T_h v_a \rangle\) for some canonical vacuum vector \(v_a \in \Omega_0\) — does not work. The T4a derivation establishes this by direct computation at \(m = 3\): the basis vector \(e_0 = e_{\check c = 0}\) of \(\Omega_0\) is *not* a simultaneous eigenvector of all \(T_h\). Concretely (T4a §2.1, using the basis from `defect_rep_minus_id_optim.g`):

|             \(h\)             |              \(T_h(e_0)\)                  |
|------------------------------|---------------------------------------------|
|         \(T_{1,1}\)          |               \(e_0\)                       |
|         \(T_{1,2}\)          |               \(e_0\)                       |
|         \(T_{2,1}\)          |               \(e_0\)                       |
|         \(T_{2,2}\)          |               \(e_0\)                       |
|         \(T_{3,1}\)          | \(\tfrac{1}{2}(e_0 + e_{(0,0,0,1)}) + \tfrac{1}{2}(e_{(0,1,1,0)} - e_{(0,1,1,1)})\) |
|         \(T_{3,2}\)          |               \(e_0\)                       |

So \((T_{3,1})_{0,0} = 1/2\), and \((T_h)_{0,0}\) is not multiplicative — incompatible with being a character. The "vacuum" of \(W_{-I}\) is not a single vector but the entire defect representation \(\Omega_0\), which is a non-trivial rep of \(C_G(-I) = E_+(m)\). The character that appears in CGR eq. 5.21 is one specific irreducible component of \(\Omega_0\) under the commuting family of \(T_h\), and CGR's gauge freedom says the choice of which component is arbitrary up to labelling.

### 6.3 Implementation consequence

For K-4a-T4b (issue #197), the deliverable was the trivial \(\varepsilon\) callable:
\[
  \texttt{epsilon}(g_1, g_2, a, b) \;:=\; 1 \qquad \forall (g_1, g_2, a, b).
\]
Under the T4a finding (\(\varepsilon \equiv 1\) is the canonical gauge), T4b reduces to a one-line literal and T4b was closed as superseded by T4c (issue #208, PR #218): the substantive lattice content moves into the spectral `trace_on_W`, which is the function that picks out which character \(\chi\) corresponds to each twisted-module piece. No \(T_h\) matrix entries are read for \(\varepsilon\). The substantive lattice-orbifold information needed by K-1's `ProjectorFormula` lives entirely in `trace_on_W`, not in \(\varepsilon\). `trace_on_W(class_idx, irrep_idx, h)` returns the character value \(\chi_{\texttt{class\_idx}, \texttt{irrep\_idx}}(h)\) where \(\chi\) ranges over the linear characters appearing in the decomposition of \(\Omega_0\) under \(\{T_h \colon h \in C_G(a)\}\), with the labelling fixed to match GAP's `Irr(C_G(a))` ordering. At \(m = 3\), T4c (PR #218) implements this via full joint eigendecomposition; at \(m = 5, 7\) the full-matrix approach is infeasible (a single \(T_h\) at \(m = 5\) is \(\sim 3.7\) years to build per PR #218's scalability finding), and the sparse-trace replacement `BuildKRRSpectralCharactersSparse` is the in-flight follow-up (#220).

The acceptance test for the \(\varepsilon \equiv 1\) gauge has two layers. The original K-3 anchor (issue #40, task #45) confirms the gauge choice on \(295\,360 / 295\,360\) central-row entries — three-way agreement between `SKeller` (the K-2 adapter), the closed-form `CentralSEntryClosedForm`, and the untwisted `ComputeSBlock` (see `tests/test_krr_vs_central_closed_form.g`). The K-3 extension (issue #211, PR #222) densifies this baseline to **all 5 161 984 \(S\)-entries and all 2 272 \(T\)-diagonal entries** at \(m = 3\), with 0 mismatches, giving a much stronger ground truth for diagnosing any character-misidentification bug in T4c-style spectral characters (see `tests/test_krr_full_s_t.g`). The orchestrator K-4a-T6 lifts these to the full three-subgroup verdict: `K4aClassify(3)` returns `verdict = "trivial"` with 39/39 assertions in 3.4 s wall (PR #224).

A note on what \(\varepsilon \neq 1\) would buy us: it is useful as a sanity check (if a canonical vacuum existed and gave a non-trivial \(\varepsilon\), this would let us double-check \(\sigma(a \mid b)\) against the K-3 anchor) and is necessary for the general non-CT case (e.g. a hypothetical non-zero \(\omega\), where \(\beta_a\) is only trivial up to coboundary). For the present application both are vacuous: KRR's CT case at \(m \in \{3, 5, 7\}\) is verified cochain-level, and the K-3 anchor passes with \(\varepsilon \equiv 1\).

---

## 7. The joint \((S, T)\)-permutation matcher

Both K-4a and the underlying modular-data library face the same technical question: given two modular-data pairs \((S, T)\) and \((S', T')\) of rank \(N\), decide whether there is a permutation \(\pi\) of \(\{1, \dots, N\}\) fixing the vacuum (\(\pi(1) = 1\)) such that
\[
  T'_{\pi(i)} = T_i \;\;\forall i, \qquad S'_{\pi(i), \pi(j)} = S_{i, j} \;\;\forall i, j.
\]
By [MignardSchauenburg18 Thm 5.4, MignardSchauenburg21], for \(|H| < 32\) this is a *complete* invariant of \(\mathrm{Mod}(D^\omega(H))\) — modular data determines the MTC up to braided fusion equivalence. So at \(D_8\) and \(Q_8\) (order 8) the matcher's verdict directly identifies the MTC isomorphism class.

### 7.1 Algorithmic structure

Naive search is infeasible at rank 22 (\(22! \approx 10^{21}\)). The matcher (file `extraspecial_orbifolds/scripts/joint_permutation_matcher.g`, K-4a-T1, issue #192, PR #203) uses signature-pruned backtracking, lifted from the one-shot \(Q_8\) extension-type case study (`q8_extension_type/scripts/find_permutation.g` and `q8_extension_type/writeup.md`) into a reusable callable `JointPermutationMatcher(S1, T1, S2, T2)`.

**Per-row signatures.** For each row \(i\) compute a signature
\[
  \mathrm{sig}(i) \;:=\; \bigl(T_i,\; \mathrm{SortedList}(S_{i,\cdot})\bigr).
\]
The candidate set for \(\pi(i)\) is the set of rows \(j\) of \(S_1\) with \(\mathrm{sig}_1(j) = \mathrm{sig}_2(i)\). Any valid \(\pi\) maps each row to one of its candidates. The signature is strictly stronger than a \((d_i, T_i)\) joint-invariant partition, since \(\mathrm{SortedList}(S_{i,\cdot})\) sees every row entry, not just the vacuum column \(S_{i,1}\); in practice it cuts the candidate sets to single-digit sizes at \(D_8\) and \(Q_8\). A cheap necessary precheck (\(\mathrm{SortedList}(T_1) = \mathrm{SortedList}(T_2)\)) and a per-row precheck (\(\mathrm{candidates}(i) \neq \varnothing\)) bail out before any search.

**Fail-fast row ordering.** The search order over rows of \(S_2\) is by ascending \(|\mathrm{candidates}(i)|\), so the most constrained rows are placed first. This is a heuristic, not a prune.

**Backtracking with online consistency.** Walk the rows of \(S_2\) in the chosen order; at each row \(i\), branch over the unused candidates \(j\) and, before recursing, verify \(S_2[i][k] = S_1[j][\pi(k)]\) for every already-assigned \(k\). This eliminates whole subtrees as soon as a partial assignment violates the \(S\) equation. At the leaf, verify the full \(S\) equation as a belt-and-braces check. The \(Q_8\) extension-type case study reports milliseconds-range runtime at rank 22 under this scheme.

### 7.2 Abelian case

For the elementary abelian \(E\), the simples of \(D^\omega(E)\) are pairs \((a, \chi)\) with \(a \in E\), \(\chi \in \widehat E\), and the modular data is degenerate (all simples one-dimensional; \(T\)-eigenvalues from the explicit Eilenberg–Mac Lane formula). The classification reduces to identifying \(\omega\) as an element of \(H^3(E; U(1)) \cong H^4(E; \mathbb Z)\) directly via [DPR91]'s explicit isomorphism to the set of pointed MTCs. No backtracking is needed; T-3 of the K-4a Phase 2 spec handles this in closed form (`abelian_e_form_check.g`).

### 7.3 Galois action

The matcher tests \((S, T)\)-equivalence as raw cyclotomic data, not up to Galois conjugation of the cyclotomic field. This is the *stronger* test: different Galois conjugates of the same nominal MTC are genuinely different MTCs (different \(S\)-matrices), and the orbifold-VOA construction produces a specific Galois conjugate. Testing up to Galois would be too coarse for our application; see [MignardSchauenburg18 §6] for discussion.

The \(Q_8\) extension-type investigation (`q8_extension_type/writeup.md`) reports an explicit case where the raw-cyclotomic test separates two classes and Galois conjugation does not bridge them: the modular data at the order-2 cocycle of \(Q_8\) is genuinely distinct from the untwisted, but the *fusion-ring* data (i.e. \((|S|, T)\) up to permutations) coincides. So at the \((S, T)\)-level Mignard–Schauenburg completeness is preserved, but fusion-ring data alone is *not* a complete invariant. This is a foundational sanity check for our use of \((S, T)\) as the discriminating invariant in K-4a.

---

## 8. Acceptance protocol

The two pipelines D-VAN and K-4a admit a clean cross-validation protocol at fixed \(m\). The protocol below is deliberately conservative: at \(m = 5, 7\) we do *not* declare Keller's conjecture proven on the strength of either pipeline alone.

### 8.1 Step 0 — Anchor at \(m = 3\)

Both `K4aClassify(3)` and `ResIsTrivialOnDetectingFamily(3, omega_KRR_3_vec)` must return verdicts of `trivial`. This is the bidirectional sanity check: K-4a's full pipeline correctly identifies a known-untwisted orbifold; D-VAN's restriction infrastructure correctly handles a known-zero class.

**Current status: anchor is GREEN end-to-end.**

- *D-VAN \(m = 3\) anchor* (Gate 1A) passes: 35/35 agreement of the D-VAN verdict with the per-basis-vector restriction at \(m = 3\), and the order-8 generator of the \(\mathbb Z/8\) summand at \(m = 2\) is detected by \(Q_8\) (Gate 1B). See `tests/test_detecting_family_vanish.g`.

- *K-3 anchor — central rows* (issue #40, original): 295 360 / 295 360 central-row entries of \(S^{\mathrm{Keller}}\) match the closed-form `CentralSEntryClosedForm` and the dense untwisted `ComputeSBlock` byte-for-byte, with \(\varepsilon \equiv 1\). See `tests/test_krr_vs_central_closed_form.g`.

- *K-3 anchor — full S + T* (issue #211, PR #222): the dense extension of K-3 covers all **5 161 984** \(S\)-entries (\(=\) rank\(^2\), with rank \(= 2272\)) and all **2 272** \(T\)-diagonal entries at \(m = 3\), with 0 mismatches against the untwisted ground truth \((S^0, T^0)\). See `tests/test_krr_full_s_t.g`. This gives a substantially denser baseline than the central-row check for diagnosing character-misidentification bugs.

- *K-4a full \(m = 3\) anchor* (T7, issue #201, closed by PR #224): `K4aClassify(3)` returns `verdict = "trivial"` end-to-end. The orchestrator (T6, issue #200, PR #224 with float-vs-int test fix in PR #228) wires together `BuildIntertwinerDataUntwisted` (the \(m \le 3\) pragmatic-choice path; observationally identical to the KRR-spectral path at \(\alpha = 0\) per K-3 extension, and avoids both the multiplicity-scaling reconciliation in PR #218 and the m=5 infeasibility in #220), the abelian \(E\) classifier (T3, PR #207), the \(D_8\) classifier (T2, PR #213), and the \(Q_8\) classifier (T1, PR #203), with restriction via T5a (PR #217) and CT modular data via T5b (PR #216). The test file `tests/test_k4a_classify.g` records **39/39 assertions PASS**, run time **3.4 s wall** (budget 300 s), with per-branch breakdown matching the §5.4 detection logic: \(E\) branch coboundary in 1.4 s, \(D_8\) classified to `class_idx = 1` (the trivial cocycle slot in `modular_data/8/3/`) in 1.0 s, \(Q_8\) classified to `class_idx = 1` (trivial slot in `modular_data/8/4/`) in 1.0 s. Note that T4b (issue #197, the \(\varepsilon\)-callable implementation) was closed as superseded by T4c (#208, PR #218) — under the T4a finding that \(\varepsilon \equiv 1\) is the correct gauge, the substantive content moves into the spectral `trace_on_W`; the orchestrator currently uses the untwisted-character path at \(m \le 3\), with the spectral path gated on the sparse-trace replacement (#220) for \(m = 5\).

- *K-4a \(m = 2\) bonus anchor.* The same `K4aClassify` orchestrator also passes at \(m = 2\) (verified in `tests/test_k4a_classify.g` test T4): `verdict = "trivial"`, \(E\) and \(D_8\) and \(Q_8\) all classified to their trivial slots, \(E\) CT modular-data block of rank \(64 = |E|^2\) (the maximal elementary abelian at \(m = 2\) has rank \(m + 1 = 3\), so \(|E| = 8\)).

### 8.2 Step 1 — Compute on the target \(m\)

Run `K4aClassify(m)` and `ResIsTrivialOnDetectingFamily(m, omega_candidates)`, where `omega_candidates` is whatever set of candidate 3-cocycles is most useful — typically the zero vector (for the sanity check that KRR's lattice maps to \([\alpha] = 0\)), plus a basis of \(H^3(E_+(m); U(1))\) at \(m \le 5\) (to map out the relevant subspace), or the specific class identified by K-4a if non-trivial. At \(m = 7\) the basis sweep depends on the Phase 2 Quillen restriction matrices.

**Current status at \(m = 5\):** K-4b's production driver scaffold landed in PR #227 (`extraspecial_orbifolds/scripts/run_k4b_m5.sh`, `k4b_xcheck_d_van.g`, `tests/test_k4b_scaffold_smoke.g`). The driver wraps a single call to `K4aClassify(5)` and gates explicitly on two upstream merges: (i) the sparse-trace replacement `BuildKRRSpectralCharactersSparse` (issue #220, in flight) for the \(\Omega_0\) representation, and (ii) lifting the \(m \le 3\) cap currently hard-coded in `k4a_classify.g` (the `n_max_supported := 3` deferral, errors out at \(m \ge 4\) with a pointer to #220). The dense \(\Omega_0\) at \(m = 5\) has dimension \(2^{16} = 65\,536\), making the literal entry-wise \(T_h\) computation infeasible (the m=3 dense path in PR #218 takes 2.4 s; the same approach at \(m = 5\) is projected at \(\sim\)3.7 years per matrix per PR #218's scalability note, motivating #220). The sparse-trace approach reduces this to \(\mathrm{Tr}(T_h^j)\) (touches only \(2^k\) diagonal entries per trace) and inverts via character orthogonality. Once #220 merges and `k4a_classify.g` lifts its cap, the \(m = 5\) driver should produce a verdict in a single shell invocation (`./run_k4b_m5.sh`).

**Current status at \(m = 7\):** future work. The Phase 2 Quillen restriction matrices and the analytical \(T_h\) computation (`compute_e_plus_7_T_analytical.g`) are the prerequisites; the latter is in place modulo verification.

### 8.3 Step 2 — Read verdicts

Three possible outcomes per \(m\), with the appropriate response to each:

1. **Jointly trivial.** Both K-4a and D-VAN report \([\alpha] = 0\). Strong evidence Keller's orbifold is untwisted at this \(m\), since the two pipelines share no critical path. The remaining doubt is the load-bearing detecting-family injectivity (§3); R-1's literature survey + R-1 follow-up empirical verification make this small.

2. **Jointly non-trivial, agreeing on the class.** Strong evidence of a non-zero \(\alpha\), and a research surprise: KRR's local conditions (\(c_g\) trivial, level matching) would no longer suffice. Inspection of *which* class would yield a precise counterexample to "local data determines \([\omega]\)".

3. **Jointly non-trivial, disagreeing on the class.** Contradiction — one of the two pipelines has a bug. The disagreement should be triaged according to §8.4.

4. **Disagreement (one trivial, one non-trivial).** Informative failure case (§8.4).

5. **Incomplete (K-4a).** The K-4a matcher returned no match; clear bug signal. Investigation should not block on K-4a; D-VAN's verdict is the primary input until K-4a is fixed.

### 8.4 Step 3 — Triage on disagreement

A K-4a / D-VAN disagreement points to one of three causes:

- *A bug in one or both pipelines.* The most likely source. K-4a has more moving parts (\(\varepsilon\) extraction, restriction, modular-data computation, permutation matcher); D-VAN has fewer (restriction matrix build, matrix–vector product, zero check). But D-VAN depends on a non-trivial mathematical claim (detection injectivity) and on the HAP-based restriction matrix construction being correct; K-4a depends on the CT case being correctly identified and CGR closed-form being implemented faithfully.

- *A subtle assumption violation.* E.g. KRR's setup is *not* the CT case (some \(\beta_g\) is non-trivial as a cochain, even though the cohomology class is trivial). K-4a would need to extend beyond [CGR2000 §5.2]; D-VAN continues to work as specified.

- *A detection-family failure.* \(\mathrm{res}_{\{E, D_8, Q_8\}}\) is not injective at this specific \(m\) for this specific class. This would contradict §3 and would be a substantial mathematical surprise. The fail-safe is to add more subgroups to the family until injectivity is restored.

In all three subcases, the resolution path is the same: investigate the smaller of the two pipelines first (D-VAN), confirm its verdict against `computed/transgression/m/kernel.g` on a basis (the kernel-of-\(\mathrm{Tr}\) ground truth at \(m \le 5\)), then either fix the K-4a bug or escalate to a math review.

The two pipelines also let us identify *which* specific cohomology class is responsible for any non-trivial verdict, in two slightly different ways: D-VAN names the class by its coordinate vector in \(H^3(H; U(1))\); K-4a names it by its Aut(\(H\))-orbit index in the precomputed library. Agreement of these two namings (via a one-time table lookup) is itself a cross-validation gate.

### 8.5 Step 4 — Document

Whatever the verdict, record:

- The exact GAP, HAP, and `modular_data/` library versions used.
- The full output of both pipelines (`epsilon_data`, `E_class`, `D8_class`, `Q8_class` from K-4a; `res_E_vec`, `res_D8_vec`, `res_Q8_vec`, `f_E`, `f_D8`, `f_Q8` from D-VAN).
- The exact subgroup choices (which Aut-orbit of \(D_8\) and \(Q_8\); which maximal \(E\)).
- The agreement (or disagreement) cross-table, for archival.

---

## 9. Status, open questions, and limitations

### 9.1 Current status

| Item | Status | Reference |
| --- | --- | --- |
| \(\ker(\mathrm{Tr})\) for \(E_+(2)\) (brute-force) | Verified, \(|\ker| = 2048\) | `run_e_plus_2_kernel.g`, `writeup/section_3_infrastructure.md` §3.7 |
| \(\ker(\mathrm{Tr})\) for \(E_+(2)\) (Path Z, structured) | Verified, agrees with brute force | T-1d, `solver/bockstein_iterated.g`, ~74 s wall |
| \(\ker(\mathrm{Tr})\) for \(E_+(3)\) | In progress via BRW-folded per-generator sweep | `transgression_per_generator_brw.g`, T-3 series |
| K-3 anchor — central rows (\(S\) at \(m = 3\)) | Passes, 295 360 / 295 360 entries | `tests/test_krr_vs_central_closed_form.g`, issue #40 |
| K-3 extension — full \(S\) + \(T\) at \(m = 3\) | Passes, 5 161 984 \(S\) + 2 272 \(T\), 0 mismatches | `tests/test_krr_full_s_t.g`, issue #211, PR #222 |
| D-VAN \(m = 3\) anchor (Gate 1A, 35 basis vectors) | Passes, 35/35 | `tests/test_detecting_family_vanish.g`, PR #205 |
| D-VAN \(m = 2\) \(\mathbb Z/8\) summand (Gate 1B) | Passes | same |
| D-VAN \(m = 5\) anchor (Gate 1E) | Pending, gated on A-5b kernel (issue #47, current sweep on PID 22335) | D-VAN spec |
| K-4a T4a (\(\varepsilon\) derivation, \(\varepsilon \equiv 1\)) | Complete | PR #206, issue #196 |
| K-4a T4b (\(\varepsilon\) callable implementation) | Superseded by T4c (#208) | issue #197, closed |
| K-4a T4c (spectral `trace_on_W`, \(m = 3\)) | Complete | PR #218, issue #208 |
| K-4a T6 (orchestrator) | Complete | PR #224 (+ test fix PR #228), issue #200 |
| K-4a Phase 2 \(m = 3\) anchor (T7) | Passes, 39/39 assertions, 3.4 s wall | `tests/test_k4a_classify.g`, issue #201, PR #224 |
| K-4a \(m = 2\) anchor (bonus) | Passes (same test file, T4) | `tests/test_k4a_classify.g`, PR #224 |
| K-4b \(m = 5\) production driver | Scaffolded, gated on #220 + lifting `n_max_supported` cap | `scripts/run_k4b_m5.sh`, PR #227 |
| Sparse `trace_on_W` for \(m = 5, 7\) | In flight | issue #220 |
| K-4c \(m = 7\) production | Future work, blocked on Q-int B2-6 / m=7 unblock path | depends on K-4b + D-VAN Phase 2 |
| BRW-folded \(S\) for \(E_+(2)\) | Byte-for-byte matches `modular_data/32/49/1.txt` | `compute_canonical_blocks.g`, untwisted modular data |
| BRW-folded \(S\) for \(E_+(7)\) | Canonical blocks persist in \(\sim 9\,\mathrm{GB}\) | `compute_canonical_blocks.g` |

### 9.2 Open questions

**Detecting-family injectivity beyond \(H^3\).** §3.4 sketches the extension to \(H^k(G; U(1))\) for \(k + 1 \equiv 0 \pmod 4\). For module-category twists (which involve \(H^4\) or higher) or higher-form symmetries the detection argument would need to be revisited.

**\(\{E, Q_8\}\)-only detection.** R-1 follow-up (§3.3) raised the possibility that \(D_8\) is the *redundant* member of the family, with \(\{E, Q_8\}\) sufficing. The empirical evidence is suggestive: \(D_8\) only adds detection power on the \(\mathbb F_2\) components, which Quillen 1971 + maximal elementary abelians already cover. This is out of scope for K-4a/D-VAN as currently implemented and would be a future cleanup.

**Non-CT generalisation of K-4a.** K-4a assumes KRR's CT condition (cochain-level \(\beta_g \equiv 1\)). For a generic twisted orbifold where \(\beta_g\) is only trivial up to coboundary, the general CGR formula uses a 1-cochain \(\varepsilon\) that is not a character. K-4a does not currently handle this. D-VAN is unaffected.

**Aut(\(G\))-equivariance of restriction.** The detecting-family injectivity is stated for individual cocycle vectors. Our application reduces cocycles modulo Aut(\(G\)) (in `src/modular_data.g` via `AutomorphismOrbits`), and both detection sources naturally factor through Aut(\(G\)), but a fully explicit statement of Aut(\(G\))-equivariance for restriction is folklore; if a referee asks, the relevant naturality citations are [Mac Lane Homology §IV.5, Brown CofG §III.10].

**Inverse cohomology problem (D-INV).** Going from KRR's lattice \(\varepsilon\) back to an explicit \(\omega\)-vector in \(H^3(E_+(m); U(1))\) — the "D-INV" workstream (issue #140) — is blocked on Q-int Phase 2 and the D-VAN restriction infrastructure. We do not need this for the verdict at Keller's question (both pipelines bypass it), but it would let us *name* the specific class \([\alpha]\) in \(H^3(E_+(m); U(1))\) if it turns out non-zero. Without D-INV, we identify \([\alpha]\) only by its restrictions to \(\{E, D_8, Q_8\}\).

**Galois action.** §7.3 notes that the matcher tests raw cyclotomic equality, not Galois-quotient equivalence. This is the correct choice for our application (the orbifold construction produces a specific Galois conjugate), but it would need relaxation for a hypothetical Galois-quotient MTC isomorphism class question.

**Cross-validation in the disagreement case.** The disagreement triage of §8.4 has not been exercised on a real disagreement. The \(m = 3\) anchor is the first place a genuine double-pipeline check has been completed: both K-4a (via `K4aClassify(3) = "trivial"`, PR #224) and D-VAN (via `ResIsTrivialOnDetectingFamily(3, \cdot) = true` on each of the 35 basis vectors, PR #205) agree at \(m = 3\) on the known-untwisted ground truth. The protocol therefore has its first joint anchor; refinement of the triage flow with real disagreement data must wait until either \(m = 5\) or a constructed false-positive \(\omega\) is fed through.

**Sparse `trace_on_W` performance at \(m = 5, 7\).** The trace-only / character-orthogonality reformulation of `BuildKRRSpectralCharacters` (issue #220, in flight) is the gating performance question for K-4a at \(m = 5\) and \(m = 7\). The math is standard (decompose a representation into irreps via traces in cyclotomic arithmetic), but the engineering — exposing \(\mathrm{Tr}(T_h^j)\) without materialising the full \(2^{2k}\)-entry \(T_h\) matrix — is non-trivial; the acceptance target is \(<30\) min total for all class reps at \(m = 5\) per the issue's spec.

**A-5b batched back-substitution (#177, R2-3 series).** The current bottleneck in the \(E_+(5)\) kernel sweep is concentrated in `IsCoboundary2Mod2WithLiftVec`'s back-substitution loop. A live perf sample on the production sweep shows \(\approx 99.7\%\) interpreter overhead in the inner loop; PRs #221 (`BocksteinH1ToH2`) and #225 (`IsCoboundary2Mod2WithLiftWitness`) replaced the nested for-loops with `KroneckerProduct`, and a batched back-substitution variant is being prepared as the next R2-3 follow-up. This is in the \(\ker(\mathrm{Tr})\) infrastructure, not the methodology pipelines themselves; it gates D-VAN \(m = 5\) (Gate 1E).

**`BoundaryMatrixGF2` vectorisation.** A separate optimisation, distinct from the `KroneckerProduct` route in #221/#225, targets `BoundaryMatrixGF2` in the structured solver. The expected speedup is modest but combinatorial in the chain of upstream calls; tracked as a follow-up to #221.

### 9.3 Limitations

- *KRR's conjecture is empirical evidence, not proof.* KRR's formal conjecture (Conjecture 5.2) is **m = 7 only**. They verify cochain-level \(c_g\) triviality at \(m \in \{3, 5, 7\}\) (one necessary condition) and the [vEMS17] level-matching at \(m = 7\) only. These are necessary but not sufficient in general; D-VAN + K-4a upgrade KRR's necessary conditions to a sufficient verdict at \(m = 5, 7\).

- *D-VAN does not see the lattice.* If two different VOA orbifolds at \(E_+(m)\) happened to share the same \(\omega\) (which is the case if and only if their modular data agrees up to MTC iso), D-VAN cannot distinguish them; only the K-4a path through the lattice intertwiners is sensitive to the lattice itself.

- *K-4a depends on cochain-level triviality.* Even within KRR's framework, a small loosening of "\(\beta_g \equiv 1\)" to "\(\beta_g\) is a coboundary" would break K-4a's specialisation to CGR §5.2 closed-forms. We use KRR's stronger property of cochain-level triviality and would have to fall back to a general (non-CT) CGR formula otherwise.

- *No cross-platform reproducibility.* GAP and HAP versions are not pinned. When citing results, record the GAP version (`Version()`) and HAP version (loadable via `IsBound(GAPInfo.PackagesInfo!.hap)`).

- *Repository scope.* All persisted modular data referenced lives under `modular_data/` (a 77 GB tree, not under version control) and `extraspecial_orbifolds/computed/`. GAP source is not reproduced in the paper.

---

## References

```bibtex
@book{AdemMilgram2004,
  author    = {Adem, Alejandro and Milgram, R. James},
  title     = {Cohomology of Finite Groups},
  series    = {Grundlehren der mathematischen Wissenschaften},
  volume    = {309},
  edition   = {2},
  publisher = {Springer-Verlag Berlin Heidelberg},
  year      = {2004},
  isbn      = {978-3-642-05785-4},
  doi       = {10.1007/978-3-662-06280-7},
}

@article{AdemKaragueuzian1997,
  author  = {Adem, Alejandro and Karagueuzian, Dikran},
  title   = {Essential Cohomology of Finite Groups},
  journal = {Commentarii Mathematici Helvetici},
  volume  = {72},
  year    = {1997},
  pages   = {101--109},
  note    = {Available at \url{https://personal.math.ubc.ca/~adem/essential.pdf}.},
}

@article{Bantay1997,
  author  = {Bantay, P.},
  title   = {The kernel of the modular representation and the Galois action in {RCFT}},
  journal = {Communications in Mathematical Physics},
  year    = {1997},
  note    = {Cited as [Ban97] in the body.},
}

@article{Bantay1998,
  author = {Bantay, P.},
  title  = {Characters and modular properties of permutation orbifolds},
  journal = {Physics Letters B},
  year   = {1998},
  note   = {Cited as [Ban98] in the body.},
}

@book{BakalovKac2004,
  author  = {Bakalov, Bojko and Kac, Victor},
  title   = {Twisted modules over lattice vertex algebras},
  series  = {Lie theory and its applications in physics V},
  year    = {2004},
  note    = {Cited as [BK04] in the body.},
}

@book{BakalovKirillov2001,
  author    = {Bakalov, Bojko and Kirillov, Alexander Jr.},
  title     = {Lectures on Tensor Categories and Modular Functors},
  series    = {University Lecture Series},
  publisher = {American Mathematical Society},
  year      = {2001},
}

@article{BoltRoomWall1961,
  author  = {Bolt, B. and Room, T. G. and Wall, G. E.},
  title   = {On the {C}lifford collineation, transform, and similarity groups},
  journal = {Journal of the Australian Mathematical Society},
  year    = {1961},
  note    = {Cited as [BRW61] in the body.},
}

@book{Brown1982,
  author    = {Brown, Kenneth S.},
  title     = {Cohomology of Groups},
  series    = {Graduate Texts in Mathematics},
  volume    = {87},
  publisher = {Springer-Verlag},
  year      = {1982},
}

@article{BruillardNgRowellWang2016,
  author  = {Bruillard, Paul and Ng, Siu-Hung and Rowell, Eric C. and Wang, Zhenghan},
  title   = {Rank-finiteness for modular categories},
  journal = {Journal of the American Mathematical Society},
  year    = {2016},
  note    = {Cited as [BNRW16] in the body.},
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

@article{CosteGannonRuelle2000,
  author  = {Coste, A. and Gannon, T. and Ruelle, P.},
  title   = {Finite group modular data},
  journal = {Nuclear Physics B},
  volume  = {581},
  year    = {2000},
  pages   = {679--717},
  doi     = {10.1016/S0550-3213(00)00285-6},
  note    = {Preprint hep-th/0001158. Cited as [CGR2000] in the body.},
}

@article{DijkgraafPasquierRoche1991,
  author  = {Dijkgraaf, R. and Pasquier, V. and Roche, P.},
  title   = {Quasi-{H}opf algebras, group cohomology and orbifold models},
  journal = {Nuclear Physics B (Proc. Suppl.)},
  year    = {1991},
  note    = {Cited as [DPR91] in the body.},
}

@article{DijkgraafVerlindeVerlindeVafa1989,
  author  = {Dijkgraaf, R. and Verlinde, C. and Verlinde, E. and Vafa, C.},
  title   = {The operator algebra of orbifold models},
  journal = {Communications in Mathematical Physics},
  year    = {1989},
  note    = {Cited as [DVVV89] in the body.},
}

@article{DongLinNg2015,
  author  = {Dong, Chongying and Lin, Xingjun and Ng, Siu-Hung},
  title   = {Congruence property in conformal field theory},
  journal = {Algebra \& Number Theory},
  year    = {2015},
  note    = {Cited as [DLN15] in the body.},
}

@article{EvansGannon2018,
  author  = {Evans, David E. and Gannon, Terry},
  title   = {Reconstruction and local extensions for twisted group doubles, and permutation orbifolds},
  year    = {2018},
  note    = {arXiv:1804.11145. Cited as [EvG18] or [EG18] in the body.},
}

@article{HaradaKono1987,
  author  = {Harada, Masana and Kono, Akira},
  title   = {On the integral cohomology of extraspecial 2-groups},
  journal = {Journal of Pure and Applied Algebra},
  volume  = {44},
  year    = {1987},
  pages   = {215--219},
  doi     = {10.1016/0022-4049(87)90025-9},
}

@phdthesis{Hoehn1996,
  author = {H{\"o}hn, Gerald},
  title  = {Selbstduale {V}ertexoperatorsuperalgebren und das {B}abymonster},
  school = {Universit{\"a}t Bonn},
  year   = {1996},
}

@article{Hoehn2019,
  author = {H{\"o}hn, Gerald},
  title  = {On the genus of the {M}oonshine module},
  year   = {2019},
  note   = {Cited as [Höh19] in the body.},
}

@article{KellerRobertsRoberts2024,
  author  = {Keller, Christoph A. and Roberts, Ashley Winter and Roberts, Jeremy},
  title   = {{CFTs} with large gap from {B}arnes--{W}all lattice orbifolds},
  year    = {2024},
  note    = {arXiv:2411.13646. Cited as [KRR24] in the body. v2 dated 17 Mar 2026.},
}

@article{Kirillov2002,
  author = {Kirillov, Alexander Jr.},
  title  = {Modular categories and orbifold models},
  year   = {2002},
  note   = {Cited as [Kir02] in the body.},
}

@book{MacLane1975,
  author    = {Mac Lane, Saunders},
  title     = {Homology},
  series    = {Grundlehren der mathematischen Wissenschaften},
  edition   = {3},
  publisher = {Springer-Verlag},
  year      = {1975},
}

@article{MasonNg2005,
  author  = {Mason, Geoffrey and Ng, Siu-Hung},
  title   = {Group cohomology and gauge equivalence of some twisted quantum doubles},
  journal = {Transactions of the American Mathematical Society},
  year    = {2005},
  note    = {Cited as [MN05] in the body.},
}

@article{MignardSchauenburg18,
  author  = {Mignard, Michael and Schauenburg, Peter},
  title   = {Morita equivalence of pointed fusion categories of small rank},
  year    = {2017},
  note    = {arXiv:1708.06538. Cited as [MignardSchauenburg18] in the body.},
}

@article{MignardSchauenburg21,
  author  = {Mignard, Michael and Schauenburg, Peter},
  title   = {Modular categories are not determined by their modular data},
  journal = {Letters in Mathematical Physics},
  year    = {2021},
  volume  = {111},
  number  = {3},
  doi     = {10.1007/s11005-021-01410-4},
  note    = {Cited as [MignardSchauenburg21] in the body.},
}

@article{NaiduNikshych2008,
  author  = {Naidu, Deepak and Nikshych, Dmitri},
  title   = {Lagrangian subcategories and braided tensor categories},
  year    = {2008},
  note    = {Cited as [NN08] in the body.},
}

@article{NebeRainsSloane2001,
  author  = {Nebe, Gabriele and Rains, Eric M. and Sloane, Neil J. A.},
  title   = {The invariants of the {C}lifford groups},
  journal = {Designs, Codes and Cryptography},
  year    = {2001},
  note    = {Cited as [NRS01] in the body.},
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

@article{vanEkerenMollerScheithauer2017,
  author  = {van Ekeren, Jethro and M{\"o}ller, Sven and Scheithauer, Nils R.},
  title   = {Construction and classification of holomorphic vertex operator algebras},
  year    = {2017},
  note    = {Cited as [vEMS17] in the body.},
}

@article{Witten2007,
  author = {Witten, Edward},
  title  = {Three-dimensional gravity revisited},
  year   = {2007},
  note   = {arXiv:0706.3359. Cited as [Wit07] in the body.},
}
```

### Internal cross-references

These documents in the repository are cited inline for the reader following along; they are not part of the formal bibliography.

- `writeup/section_3_infrastructure.md` — the cross-cutting Tier-4 infrastructure: torsion-split solver, BRW-symmetry reduction, centraliser cache, resumable state.
- `extraspecial_orbifolds/writeup.md` — long-form mathematical writeup, including the Magma → GAP port of [KRR24]'s evidence pipeline.
- `q8_extension_type/writeup.md` — \(Q_8\) extension-type case study, demonstrating that fusion-ring data alone is insufficient but full \((S, T)\) is.
- `docs/superpowers/specs/2026-05-15-detecting-family-vanishing-test-design.md` — D-VAN design (Phase 1 HAP, Phase 2 Quillen).
- `docs/superpowers/specs/2026-05-17-k4a-phase2-implementation-spec.md` — K-4a Phase 2 implementation specification.
- `docs/superpowers/specs/2026-05-17-k4b-m5-production-spec.md` — K-4b \(m = 5\) production driver.
- `docs/superpowers/research/2026-05-17-detecting-family-literature.md` — R-1 literature survey (Quillen 1971 + Harada–Kono 1987 + Pham 2000 / Adem–Karagueuzian 1997 + AM04 §IV.4–§IV.5 synthesis).
- `docs/superpowers/research/2026-05-17-d8-vs-q8-detection.md` — R-1 follow-up: keep \(Q_8\) in the detecting family, with the 280-class \(D_8\) scan and the structural argument.
- `docs/superpowers/research/2026-05-17-epsilon-extraction-from-krr.md` — T4a derivation: \(\varepsilon \equiv 1\) is the correct gauge.
