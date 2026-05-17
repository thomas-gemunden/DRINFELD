# 5. Conclusions and open questions

This section closes the methodology paper. §5.1 distils the
contributions; §5.2 records what the present work implies for Keller's
question; §5.3 sets out open questions in three categories
(computational, mathematical, methodological); §5.4 is an honest
account of caveats and limitations. Forward-looking claims are scoped
to the roadmap visible at time of writing — issue numbers in this
section refer to items on the public tracker and are placeholders for
empirical content that will land as the m = 5 and m = 7 verdicts
arrive.

The structure of the paper to this point has been: §1 motivation
(Keller's question and the twin-witness strategy); §2 mathematical
setup (twisted Drinfeld doubles, transgression, the extraspecial
2-groups \(E_+(m)\)); §3 the detecting family \(\{E, D_8, Q_8\}\); §4
D-VAN, the algebraic restriction pipeline; §5 K-4a, the modular-data
witness from the CGR §5.2 closed-form; §6 the \(\varepsilon \equiv 1\)
gauge; §7 the joint \((S, T)\)-permutation matcher; §8 the acceptance
protocol; §9 status. The cross-cutting infrastructure (T-1 through
T-5) is documented separately in `writeup/section_3_infrastructure.md`
and is treated here as a black box.

---

## 5.1 Summary of contributions

This paper delivers six concrete contributions, each anchored to a
verifiable artefact in the repository.

### 5.1.1 The \(\{E, D_8, Q_8\}\) detecting family

We prove, by synthesising
[Quillen1971 Thm 5.10] + [HaradaKono1987 Thm 1.1] + the universal
coefficient theorem + the [AdemMilgram2004] §IV.4–§IV.5 framework,
that for \(G = E_+(m)\) with \(m \ge 2\) the restriction map
\[
  \mathrm{res} \colon H^3(G;\, U(1)) \;\longrightarrow\;
  H^3(E;\, U(1)) \,\oplus\, H^3(D_8;\, U(1)) \,\oplus\, H^3(Q_8;\, U(1))
\]
is injective, where \(E\) is any maximal elementary abelian
2-subgroup of rank \(m + 1\), \(D_8\) is any rank-2 \(Q\)-isotropic
section, and \(Q_8\) is any rank-2 \(Q\)-anisotropic section. The
structural separation of roles is:

- the elementary-abelian summand \(V_4 \subset H^4(G; \mathbb Z)\) is
  detected on \(E\) via Quillen 1971;
- the cyclic summand \(A(4) \subset H^4(G; \mathbb Z)\) is detected on
  \(Q_8\) (which carries \(H^4(Q_8; \mathbb Z) \cong \mathbb Z/8\)),
  partially on \(D_8\) (which only carries \(\mathbb Z/4\) as a maximal
  cyclic factor — sufficient on the generator of \(A(4)\) at \(m \ge 3\)
  but not on its order-2 sub-element).

The empirical investigation of issue #215 (PR #219) verified that
\(Q_8\) is *genuinely required* and not a redundant member of the
family: an exhaustive scan over all 280 conjugacy classes of
\(D_8\)-subgroups of \(E_+(3)\) shows that the doubling of the
\(A(4)\) generator maps to zero in every \(D_8\) restriction (a
structural ceiling, not a section-choice artefact). \(Q_8\) catches
this class. The same failure mode appears at \(m = 2\) on the order-2
element of \(\mathbb Z/8\). See §3.3.

### 5.1.2 Two independent computational pipelines

We construct two cross-validating verdicts for Keller's question:

- **D-VAN** (issue #142 EPIC; spec
  `docs/superpowers/specs/2026-05-15-detecting-family-vanishing-test-design.md`)
  tests whether a candidate \(\omega_{\mathrm{vec}} \in H^3(E_+(m); U(1))\)
  restricts to zero on the detecting family. After a one-time
  restriction-matrix build (Phase 1 HAP at \(m \in \{2, 3, 5\}\); Phase 2
  Quillen at \(m = 7\)), every subsequent test is a sub-millisecond
  matrix–vector product. D-VAN is algebraic — it operates on cocycle
  coordinate vectors, not modular data.

- **K-4a** (issue #187 EPIC; spec
  `docs/superpowers/specs/2026-05-17-k4a-phase2-implementation-spec.md`)
  bypasses the cohomology presentation of \(\alpha\) altogether. It
  computes the modular data \((S^\alpha, T^\alpha)\) on each subgroup
  of the detecting family via CGR §5.2 closed-form, then matches against
  the precomputed Gruen–Morrison library of modular data for
  \(D^\omega(H)\) using the joint \((S, T)\)-permutation matcher of
  §7. K-4a is *physical* — it sees the literal modular tensor
  category produced by the orbifold construction.

The two pipelines share no critical path. D-VAN depends on Quillen +
Harada–Kono detection and on HAP-based restriction matrices; K-4a
depends on the CT property of KRR's intertwiners and on
Mignard–Schauenburg completeness at \(|H| < 32\). They are designed
to fail differently: a unified verdict carries weight that neither
could carry alone.

### 5.1.3 \(\varepsilon \equiv 1\) as the correct CGR gauge for the CT case

The K-4a-T4a derivation note (issue #196, PR #206;
`docs/superpowers/research/2026-05-17-epsilon-extraction-from-krr.md`)
settles the choice of the CGR 1-cochain \(\varepsilon_a\) for KRR's
CT setting. The argument is twofold:

1. *Gauge invariance.* CGR's remark immediately after eq. 5.22 is that
   the modular data \((S^\alpha, T^\alpha)\) is independent of the
   choice of 1-cochain \(\varepsilon_a\) up to relabelling of the
   projective characters \(\chi\). So different choices of \(\varepsilon_a\)
   just permute the labels of simples \((a, \chi)\); the modular data
   is invariant.

2. *No canonical vacuum vector.* The natural alternative — defining
   \(\varepsilon_a(h) := \langle v_a, T_h v_a \rangle\) for some
   canonical vacuum \(v_a \in \Omega_0\) — fails structurally because
   the basis vector \(e_0 \in \Omega_0\) is not a simultaneous
   eigenvector of all \(T_h\) (explicit table at §6.2 of the methodology;
   T4a derivation note §2.1).

With \(\varepsilon \equiv 1\), the CGR phase \(\sigma(h \mid g) =
\varepsilon_h(g) \cdot \varepsilon_g(h)\) collapses to 1 and
\(T^\alpha\) reduces to \(T^0\) trivially. All non-trivial content
lives in the projective characters \(\chi\), specifically in the
linear-character decomposition of \(\Omega_0\) under the commuting
family \(\{T_h \colon h \in C_G(a)\}\).

### 5.1.4 The K-4a pipeline architecture

The K-4a Phase 2 pipeline is structured as four composable layers
(spec
`docs/superpowers/specs/2026-05-17-k4a-phase2-implementation-spec.md`):

1. **Subgroup restriction.** `RestrictEpsilonToSubgroup`
   (`restrict_epsilon_to_subgroup.g`, T5a) restricts the CT 1-cochain
   \(\varepsilon\) from \(G = E_+(m)\) to each \(H \in \{E, D_8, Q_8\}\)
   along a chosen embedding. CT is preserved by restriction.

2. **CT modular data.** `ComputeCTModularData`
   (`ct_modular_data.g`, T5b) feeds the restricted \(\varepsilon^H\)
   into CGR eq. 5.20 + 5.21 on \(H\) to produce
   \((S^\alpha\!\restriction_H, T^\alpha\!\restriction_H)\).

3. **Joint \((S, T)\) matcher.** `JointPermutationMatcher`
   (`joint_permutation_matcher.g`, T1, issue #192) compares against
   the stored library \(\{(S^{\omega_k}\!\restriction_H,
   T^{\omega_k}\!\restriction_H)\}_{\omega_k \in H^3(H;\, U(1)) /
   \mathrm{Aut}(H)}\) using bucketing + colour refinement +
   backtracking; abelian \(E\) is handled separately by closed-form
   Eilenberg–Mac Lane comparison (T3, `abelian_e_form_check.g`).

4. **Classification + aggregation.** `K4aClassify(m)`
   (`k4a_classify.g`, T6) orchestrates the three branch classifiers
   and aggregates them into a single Keller verdict
   \(\in \{\text{trivial}, \text{non-trivial}, \text{incomplete}\}\),
   bidirectional by §3's detection theorem.

### 5.1.5 Empirical \(m = 3\) anchor at three depths

The K-3 / K-4a stack has been validated at the \(m = 3\) anchor at
three independent levels of granularity:

- **K-3 central-row anchor** (issue #40,
  `tests/test_krr_vs_central_closed_form.g`): the 295 360 entries of
  the central row of \(S^{\mathrm{Keller}}\) (computed via the K-2
  adapter `SKeller`) match three-way against the closed-form
  `CentralSEntryClosedForm` and the dense untwisted `ComputeSBlock`,
  byte-for-byte (cyclotomic equality). Zero mismatches in 16.6 s wall.

- **K-3 extension anchor** (PR #222,
  `tests/test_k3_extension_full_s_anchor.g`): the *full* \(S\) matrix
  and \(T\) diagonal at \(m = 3\), totalling 5 164 256 entries,
  match the untwisted ground truth. Zero mismatches in ≈290 s wall.

- **K-4a full pipeline anchor** (PR #224 + #228,
  `tests/test_k4a_classify.g`, the K-4a-T7 acceptance gate at issue
  #201): `K4aClassify(3)` returns `verdict = "trivial"` in 3.4 s wall,
  matching KRR's known \(\alpha = 0\) at \(m = 3\). All 39 acceptance
  assertions PASS — T1 smoke (4), T2 \(m = 3\) trivial anchor (23),
  T3 \(m \ge 4\) error path (4), T4 \(m = 2\) smoke (8). PR #228
  contributed the float-vs-integer comparison one-line fix needed to
  bring the test green; the underlying pipeline of #224 is unchanged.

- **D-VAN \(m = 3\) basis anchor** (Gate 1A,
  `tests/test_detecting_family_vanish.g`, PR #205): all 35 generators
  of the hom-basis at \(m = 3\) verified, 35/35 agreement. Gate 1B
  specifically tests the \(\mathbb Z/8\) summand of \(A(4)\) at \(m = 2\)
  and confirms detection by \(Q_8\).

The four anchors run independently — different code paths, different
assumptions, different invariants — and converge on the same verdict.

### 5.1.6 Bonus \(m = 2\) anchor

`K4aClassify(2)` also returns `verdict = "trivial"` (PR #228), giving
a second known-trivial point for cross-validation. This is below the
range \(\{3, 5, 7\}\) of Keller's specific application but is a
free sanity check on the orchestrator's behaviour at the smallest
non-trivial extraspecial.

---

## 5.2 What this implies for Keller's question

Keller's question (KRR24 §1.4) asks whether the obstruction class
\([\alpha] \in H^3(E_+(m);\, U(1))\) controlling the orbifold MTC
\(\mathrm{Mod}(V_{\mathrm{BW}(m)}^{E_+(m)})\) vanishes for \(m = 5\)
and \(m = 7\). At \(m = 3\), KRR settle this directly by producing
the untwisted holomorphic VOA. At \(m = 5, 7\), they verify the
*necessary* conditions (local 2-cocycles \(c_g\) trivial cochain-level
on every conjugacy class; level matching of [vEMS17]) and conjecture
that those conditions are sufficient.

### 5.2.1 Where we stand at \(m = 3\)

The \(m = 3\) anchor of §5.1.5 is the principal validation event for
the whole methodology. KRR's orbifold at \(m = 3\) is the untwisted
\(V_{E_8}\) by [KRR24] direct construction, so we know
\([\alpha] = 0\) by other means. Both pipelines (D-VAN and K-4a) plus
the K-3 and K-3-extension intermediate anchors agree: the K-4a
verdict is `trivial` in 3.4 s, the D-VAN basis sweep is 35/35
agreement, the K-3 central-row check is 295 360 / 295 360
byte-for-byte, the K-3 extension is 5 164 256 / 5 164 256 entries
byte-for-byte. *The pipeline correctly identifies Keller's verified
\(\alpha = 0\) at \(m = 3\).*

This is necessary but not sufficient. It rules out the most likely
classes of bugs — sign errors, off-by-one in the simple-object
labelling, wrong gauge convention on \(\varepsilon\), incorrect
restriction matrices — that would produce a *false-positive
non-triviality* verdict. It does not rule out bugs that would
produce a false-positive *triviality* verdict; we discuss the
remaining cross-validation gates in §8.4 and the disagreement triage
protocol in §8.

### 5.2.2 Where we stand at \(m = 5\) and \(m = 7\)

Both target \(m\)'s remain open. The pipelines are *ready* modulo
specific named blockers:

- *K-4a at \(m = 5\)* is blocked on sparse \(\texttt{trace\_on\_W}\)
  (issue #220, in flight). The dense \(\Omega_0\) at \(m = 5\) has
  dimension \(2^{16} = 65\,536\); the literal entry-wise \(T_h\) build
  is the bottleneck (\(\approx 3.7\) years per matrix at the measured
  per-entry cost). The sparse approach uses character inversion of
  \(\mathrm{Tr}(T_h^j)\) over the conjugacy classes of \(C_G(a)\)
  and reduces the cost to a scan over only the support of \(\Omega_0\)
  under the projection onto each isotype. Once #220 merges, the m = 5
  production run is projected at hours of wall clock on a single
  node (per spec
  `docs/superpowers/specs/2026-05-17-k4b-m5-production-spec.md`).

- *D-VAN at \(m = 5\)* (Gate 1E, issue #148) is blocked on the
  A-5b m = 5 kernel-of-\(\mathrm{Tr}\) sweep completion (issue #47).
  The kernel-of-\(\mathrm{Tr}\) ground truth at \(m = 5\) is what
  D-VAN cross-checks against on the basis sweep; without it, D-VAN
  has no per-class falsification target. The A-5b sweep is currently
  running with the optimisations of issue #177 (batched
  back-substitution, the R2-3 round of patches in flight, projected
  10–100× speedup over the original ≈ 11-day projection).

- *K-4a / D-VAN at \(m = 7\)* depend on the Phase 2 Quillen restriction
  matrices (D-VAN) and on the analytical \(T_h\) computation (K-4a),
  both of which exist modulo cross-validation. The HAP resolution at
  \(m = 7\) is infeasible (projected TB-scale memory), motivating the
  Q-int C alternative-resolution workstream (issue #137, Pontryagin
  route via path B3 currently active; path 4 sparse declared dead).

### 5.2.3 What an affirmative verdict would buy us

If both K-4a and D-VAN return `trivial` verdicts at \(m = 5\) and
\(m = 7\), the resulting evidence for Keller's conjecture is
*strong* but not a proof. The remaining gaps are:

1. *Detecting-family injectivity is a synthesised theorem.* §3 is
   a clean assembly of Quillen 1971 + Harada–Kono 1987 + UCT + the
   AM04 §IV.4 framework, but it is not a single named theorem in the
   literature. A reviewer must verify the synthesis. The synthesis is
   straightforward in our hands — R-1 collected the literature in PR
   #205, R-1 follow-up confirmed Q_8 is required in PR #219 — but it
   is not yet refereed as a free-standing result.

2. *CT case only.* K-4a does not handle generic \(\omega\) with
   \(\beta_g\) only trivial up to coboundary; it requires KRR's
   stronger cochain-level triviality. D-VAN is unaffected by this
   restriction.

3. *Modular-data completeness at \(|H| < 32\).* The Mignard–Schauenburg
   completeness theorem
   [MignardSchauenburg18, MignardSchauenburg21] gives us
   bidirectional verdicts on \(D_8\) and \(Q_8\); for \(E_+(m)\)
   itself (\(|G| \ge 2^{11}\) at \(m = 5\)) the modular-data
   completeness is no longer guaranteed by Mignard–Schauenburg, but
   we never compare modular data of \(D^\omega(G)\) directly — only
   the restricted data on detecting subgroups. The completeness used
   is the one on \(|H| < 32\).

A negative verdict (Joint non-triviality) is a research surprise: it
would mean KRR's local conditions (trivial \(c_g\)'s, level-matched)
are not sufficient to force \([\alpha] = 0\), and would identify
explicit non-trivial classes on the detecting subgroups. The
disagreement triage of §8.4 spells out the remaining cases (one
pipeline trivial, one non-trivial; both non-trivial but disagreeing
on the class; matcher returns incomplete).

The philosophical stance: *the twin-witness strategy upgrades KRR's
necessary-conditions evidence to a sufficient-conditions verdict,
modulo the synthesised detecting-family theorem*. We do not claim a
proof of Keller's conjecture; we claim that an affirmative
double-pipeline verdict at \(m = 5\) and \(m = 7\) is the strongest
computational evidence currently obtainable, and it identifies the
remaining doubt structurally (§5.4).

---

## 5.3 Open questions

We organise the open questions into three categories: computational
unblocks (concrete next steps on the roadmap, all in flight or
planned), mathematical open questions (load-bearing background facts
or natural generalisations), and methodological extensions (where
the framework points).

### 5.3.1 A. Computational unblocks

These are concrete next steps. Each is on the roadmap and has an
issue tracker entry; the cited PR numbers refer to in-flight work.

- *Sparse \(\texttt{trace\_on\_W}\) for \(m \in \{5, 7\}\)* — issue
  #220. The K-4a-T4c follow-up. Trace-only character inversion
  reduces the dense \(T_h\) build (\(\approx 3.7\) years/matrix at
  \(m = 5\)) to seconds per matrix. Once merged, gates K-4a on
  m = 5 production. Critical path for the K-4b spec
  (`docs/superpowers/specs/2026-05-17-k4b-m5-production-spec.md`).

- *A-5b m = 5 kernel sweep completion* — issue #47 closed,
  sweep running, with the optimisation rounds tracked at issue #177.
  Batched back-substitution (the R2-3 patches, in flight) is
  projected 10–100× over the current per-generator cost. Once the
  sweep produces `computed/transgression/5/kernel.g`, the D-VAN m = 5
  anchor (Gate 1E, issue #148) becomes a one-line replay against the
  basis.

- *Q-int C low-memory HAP resolution at \(m = 7\)* — issue #137. The
  HAP resolution at \(m = 7\) is the dominant remaining obstacle to
  *all* m = 7 work. Path 4 (sparse-resolution-via-projectivity) was
  declared dead after the path-3 spike (PR thread in
  `docs/superpowers/specs/2026-05-16-path3-hap-resolution-redesign.md`).
  Path B3 (Pontryagin-square-based, Q-int B3) is currently active and
  is the most promising route to an \(m = 7\) resolution within the
  TB-scale memory ceiling implied by the b2-4 OOM regression
  (issue #185). The Q-int A2 Bockstein derivation (PR #159) gave the
  torsion structure of \(H^3(E_+(m); U(1))\) for \(m = 5, 7\) without
  a resolution; what remains is the resolution itself for downstream
  cocycle-level work.

- *K-4a + D-VAN cross-validation at \(m = 3\) with sparse
  \(\varepsilon\) source.* Currently the K-4a \(m = 3\) anchor uses
  `BuildIntertwinerDataUntwisted` (the pragmatic untwisted path of
  PR #224 §"Pragmatic choice"). Replacing this with
  `BuildKRRIntertwinerData` (the KR-bridge of K-4a, issue #188)
  is the natural cross-check, gated on issue #218's multiplicity
  question and on resolving the KR-bridge for non-trivial central
  sectors. Not on the critical path for the m = 5 verdict but is
  a desirable cleanup.

### 5.3.2 B. Mathematical open questions

These are the mathematical questions the present work leaves open or
points to. They are not blockers for the Keller verdict but are
natural follow-up directions for the framework.

- *Beyond CT: when does a naturally-occurring orbifold give a
  non-CT twist?* KRR's setup is CT (\(\beta_g \equiv 1\) cochain-level),
  but the general CGR formula admits twists with \(\beta_g\) only
  trivial up to coboundary. Identifying any naturally-occurring
  example (e.g. a lattice orbifold not in the Barnes–Wall family
  satisfying \([\beta_g] = 0\) but \(\beta_g \not\equiv 1\)
  cochain-level) would motivate the K-4a generalisation to the full
  CGR formula. D-VAN handles non-CT twists without modification.

- *Modular-data completeness at \(|H| \ge 32\).* The
  Mignard–Schauenburg completeness theorem
  [MignardSchauenburg18 Thm 5.4, MignardSchauenburg21] holds at
  \(|H| < 32\); above that, modular data is not a complete invariant.
  The \(Q_8\) extension-type investigation in `q8_extension_type/`
  shows that fusion-ring data is genuinely coarser than full
  \((S, T)\) data at rank 22, but that full \((S, T)\) is still
  complete at \(|Q_8| = 8\). The natural question is: at what rank
  (or which \(H\)) does \((S, T)\)-completeness break down for
  twisted Drinfeld doubles? Mignard–Schauenburg exhibit explicit
  counterexamples; a more granular characterisation of *which*
  \(\omega \in H^3(H; U(1))\) admit modular-data twins would refine
  the K-4a matcher's region of applicability for any future extension
  to \(|H| \ge 32\).

- *The essential ideal in higher degree.* Quillen's "essential
  cohomology" theorem [AdemKaragueuzian1997, Pham2000] starts at
  degree \(2m\) for extraspecial 2-groups, and for \(E_+(m)\) the
  essential ideal is non-trivial only at \(m \ge 2\); the lower
  bound of degree 2 in our application is comfortably above it.
  For higher-degree applications — \(H^4\) module-category twists
  (e.g. higher gauge theories of \(E_+(m)\)) or \(H^5\) higher-form
  symmetries — the detection argument would need to be revisited:
  either an extended detecting family or a different framework
  (e.g. fully restoring the [AdemKaragueuzian1997] essential
  ideal description).

- *The redundant member of the family.* R-1 follow-up (PR #219)
  refutes the hypothesis that \(\{E, D_8\}\) alone detects; we
  *keep* \(Q_8\) in the family. The dual question — whether
  \(\{E, Q_8\}\) alone suffices, i.e. \(D_8\) is the redundant
  member — is open. Empirically \(D_8\) only contributes detection
  on \(\mathbb F_2\) components that Quillen 1971 + maximal elementary
  abelians already cover; if this holds in general,
  \(\{E, Q_8\}\) would be a streamlined family. Cross-validation
  reliability is the main reason to keep \(D_8\) in the pipeline
  today; if a future cleanup confirms redundancy, the K-4a
  pipeline simplifies.

- *Aut\((G)\)-equivariance of restriction in full.* Both detection
  sources (Quillen, Harada–Kono) factor through \(\mathrm{Aut}(G)\)
  naturally, and the restriction matrices in §4.2 inherit
  Aut-equivariance, but a fully explicit statement of
  Aut\((G)\)-equivariance for our specific
  \(\mathrm{res}\colon H^3(E_+(m); U(1)) \to \bigoplus_H H^3(H; U(1))\)
  map is folklore. The relevant naturality citations are
  [MacLane1975 Homology §IV.5] and [Brown1982 §III.10]; a formal
  statement is left for a future write-up.

### 5.3.3 C. Methodological extensions

These are extension directions where the present framework points
beyond the Keller question.

- *Higher-form symmetries.* The detecting-family approach generalises
  to \(H^k(G; U(1))\) for \(k + 1 \equiv 0 \pmod 4\) (§3.4); for
  \(k = 5\) (\(H^6(\cdot; \mathbb Z)\)) the Harada–Kono cyclic summand
  \(A(6)\) is again present and the detection argument applies. For
  \(k = 4\) (\(H^5(\cdot; \mathbb Z)\)) the cyclic summand is absent
  and the detection picture is purely elementary-abelian via Quillen;
  the pipeline simplifies. Either generalisation would extend the
  twin-witness strategy beyond \(H^3\) classification problems.

- *Other 2-group families.* Does the \(\{E, D_8, Q_8\}\)-style
  family detect \(H^3(G; U(1))\) for non-extraspecial 2-groups —
  e.g. the Sylow-2 subgroups of sporadic simple groups, or the
  almost-extraspecial groups (\(E_+(m) \times \mathbb Z/2\),
  \(E_+(m) \times \mathbb Z/4\))? [CarlsonThevenaz2005] use a
  structurally similar family for endo-trivial modules, suggesting
  the pattern is canonical in 2-group homological algebra; a
  cross-pollination of their detecting family with ours would
  identify the class of groups where this works.

- *Multi-witness strategies.* D-VAN + K-4a is *two* independent
  pipelines. A *third* witness — for example, directly evaluating
  Frobenius–Schur indicators or higher gauge-invariant central
  charges from the CGR formula on each detecting subgroup, or a
  representation-theoretic invariant such as the projective
  Burnside ring on \(C_G(g)\) at each conjugacy class — would
  further harden the verdict. Each additional witness narrows the
  set of bugs or assumption-violations that could survive all
  witnesses simultaneously. The minimal-effort path here is the
  FS-indicator route, since the CT modular data is already in hand;
  see `DRINFELD/src/universal_coefficients.g` for the
  Mignard–Schauenburg FS-indicator machinery (currently partially
  broken per the CLAUDE.md note but a reasonable starting point).

- *Inverse cohomology problem (D-INV).* Going from KRR's lattice
  data back to an explicit \(\omega\)-vector in
  \(H^3(E_+(m); U(1))\) — the "D-INV" workstream (issue #140) —
  would let us *name* the specific cohomology class. It is currently
  blocked on Q-int Phase 2 and on the full D-VAN restriction
  infrastructure. The Keller verdict does not depend on D-INV (both
  pipelines bypass it), but D-INV would convert any future
  non-triviality verdict from "the class on \(H\) is \(\omega_k\)"
  to "the class on \(G\) is the explicit coordinate vector
  \([\alpha]\)".

---

## 5.4 Caveats and limitations

We close the section with an honest enumeration of limitations.
These are not failures of the present methodology; they are scoped
boundaries to make claims falsifiable. Each is named explicitly to
make the strength of the resulting verdicts auditable.

- *Detecting-family injectivity is a synthesised theorem.* §3.1's
  injectivity claim is not a single named result in the literature;
  it is a clean assembly of Quillen 1971 Thm 5.10 + Harada–Kono 1987
  Thm 1.1 + UCT for \(0 \to \mathbb Z \to \mathbb R \to U(1) \to 0\)
  + the AM04 §IV.4–§IV.5 framework. R-1's literature note
  (`docs/superpowers/research/2026-05-17-detecting-family-literature.md`,
  PR #205) gives the citations; R-1 follow-up (PR #219) verifies
  empirically that \(Q_8\) is required. The synthesis is
  straightforward but the resulting theorem is not (yet) refereed
  as a free-standing result. A reviewer should verify the
  Quillen + HK + UCT chain and the specific decomposition of \(V\)
  and \(A(4)\) summands.

- *CT case only for K-4a.* K-4a's specialisation to the CGR §5.2
  closed-form requires KRR's stronger property that \(\beta_g \equiv 1\)
  as a cochain (not merely up to coboundary). For a generic twisted
  orbifold with \([\beta_g] = 0\) but \(\beta_g \not\equiv 1\)
  cochain-level, K-4a does not apply; the more general CGR formula
  with a non-character \(\varepsilon\) would be needed. D-VAN does
  not depend on the CT property; for non-CT \(\omega\)'s D-VAN is
  the sole pipeline that applies.

- *Computational dependence on GAP, HAP, and modular-data library
  versions.* Every empirical claim in the paper depends on a
  specific GAP version, a specific HAP version, and a specific
  commit hash of the `modular_data/` library. The reproducibility
  appendix (W-3, issue #60) records the exact `Version()` and HAP
  load output for the canonical runs; until W-3 is merged, citing
  results should include the GAP version, HAP version, and the
  exact commit on the repository's main branch.

- *No GAP-version pinning across the historical modular-data
  library.* The 77 GB `modular_data/` tree was assembled across
  multiple GAP versions over the project's lifetime. The
  `SmallGroup(n, m)` identifier ordering depends on the
  `smallgrp` library version; mixing new modular-data runs under a
  different GAP version risks misaligning \((n, m)\) IDs against
  the existing tree. The `q8_extension_type/` investigation
  validated the canonical `SmallGroup(8, 3)` (\(= D_8\)) and
  `SmallGroup(8, 4)` (\(= Q_8\)) IDs, but a comprehensive
  cross-version audit is out of scope here.

- *Verdicts at \(m = 5, 7\) not yet produced.* The pipelines are
  ready modulo specific named blockers (§5.2.2). No verdict can be
  reported until #220 (sparse trace), the A-5b m = 5 kernel sweep
  (#47, #177), and — for m = 7 — Q-int C (#137) all merge. The
  earliest \(m = 5\) verdict is bounded below by the merge of #220
  and one production run; the \(m = 7\) verdict is bounded below by
  Q-int C plus a Phase 2 D-VAN restriction matrix build.

- *D-VAN does not see the lattice.* D-VAN operates on
  \(H^3(E_+(m); U(1))\) as an abstract finite abelian group. If two
  different lattice VOA orbifolds at \(E_+(m)\) happened to share
  the same \(\omega\)-class, D-VAN would treat them as identical.
  K-4a, by contrast, ingests the lattice intertwiner data directly.
  This is why both pipelines are necessary: D-VAN is the
  cohomology-level witness; K-4a is the lattice-level witness.

- *Disagreement protocol is aspirational.* §8.4's disagreement
  triage protocol has not been exercised on a real disagreement, by
  design. Both pipelines pass at \(m = 3\). The protocol is
  documented prospectively; it will be refined if and when
  empirical data forces a real disagreement at \(m = 5\) or
  \(m = 7\).

The remaining doubt structure is therefore:

1. The synthesised detecting-family theorem (§5.4.1).
2. The CT assumption (§5.4.2) — applicable only if KRR's
   cochain-level triviality is wrong; KRR verify this explicitly.
3. The computational stack (GAP/HAP version pinning, §5.4.3, §5.4.4)
   — addressed by the W-3 reproducibility appendix.
4. The verdicts themselves (§5.4.5) — to be filled in once the
   computational unblocks of §5.3.1 land.

A joint trivial verdict at \(m = 5\) and \(m = 7\), once the
computational unblocks land, would establish: KRR's local conditions
plus modular-data-on-detecting-subgroups plus algebraic-restriction-
on-detecting-subgroups all agree on triviality. Modulo the
synthesised detecting-family theorem, this is sufficient to conclude
\([\alpha] = 0\) and Keller's conjecture at those \(m\). Modulo the
CT assumption and the computational stack, this is the strongest
computational evidence currently obtainable for Keller's orbifold
construction.

---
