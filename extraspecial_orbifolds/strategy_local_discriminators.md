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

If we want a *theoretical* answer rather than a *computational* one: compute the kernel of the transgression
$$
\mathrm{Tr}: H^3(E_+(m); U(1)) \;\longrightarrow\; \bigoplus_{[g]} H^2(C_{E_+(m)}(g); U(1)).
$$

If this kernel is trivial as an abelian group, then $c_g = 0$ for all $g$ implies $\omega = 0$ — *the Keller conjecture follows automatically* from their published evidence, no further computation needed.

If the kernel is non-trivial, the residual classes are classified, and additional conditions (e.g., level matching plus specific extra checks) decide $\omega$.

**Calculation route.** HAP's `GroupCohomology(G, n)` returns $H^n(G; \mathbb Z)$ as an abelian group. UCT then gives $H^n(G; U(1))$. The transgression is computed via `EquivariantChainMap` plus standard Eilenberg-Maclane / restriction maps. For $E_+(m)$ at $m = 3$ this is cheap; $m = 5, 7$ may need clever decomposition (using extraspecial structure).

For $E_+(m)$, the cohomology rings are known: $H^*(E_+(m); \mathbb F_2)$ has polynomial + exterior structure described in Quillen [1971] and Adem-Milgram. The mod-2 transgression is computable from these explicit formulas. Lifting to $\mathbb Z$ / $U(1)$ adds bookkeeping but no new ideas.

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
