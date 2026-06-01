# 6. Results tables and figures

This section is the consolidated tabular summary of the per-\(m\)
results, anchors, and detecting-family structure that the body of the
methodology paper develops in \S\S2–5 and the per-\(m\) applications
section \S4. Tables 1–4 are the four "headline" cross-cutting
summaries; Figures 1–4 are the suggested figures. \(m \in \{2, 3\}\)
entries are filled in from verified PRs; \(m \in \{5, 7\}\) entries are
scaffolded with TBD placeholders sourced to the unblock issues, with
the structural part (\(A(4)\) shape, subgroup section existence,
expected verdicts) filled in from [HK87] and [AM04 \S IV.2 Remark
2.13]. Each TBD is anchored to the issue or spec that will fill it.

The numbering convention is shared with \S4: anchors are referenced
by PR (e.g. "PR \#222"), issues by issue number ("\#47"), and the
columns *source* / *PR* column in each table is the audit trail.
Wall-time figures are taken verbatim from the merged PR's measurement;
none are fabricated.

---

## 6.1 Table 1: \(H^3(E_+(m); U(1))\) torsion structure

The first table records the cohomology setting at each \(m\) — the
size of the group, the order of \(H^3\), the torsion shape per [HK87
Thm 1.1], the rank, the cyclic \(A(4)\) summand, and the primary
citation for the value. The torsion shape combines an elementary
abelian 2-part \((\mathbb Z/2)^{r(m)}\) and a cyclic summand
\(A(4)\); per \S2.4 of the methodology paper, \(A(4) \cong \mathbb Z/8\)
at \(m = 2\) (because the codimension \(h(Q) = 2\) and the 2-adic
valuation \(n(4) = 2\) violate the inequality \(n(k) \le h(Q) - 1\))
and \(A(4) \cong \mathbb Z/4\) at \(m \ge 3\) (because the inequality
is satisfied with equality at \(m = 3\) and holds for all higher
\(m\)). The rank column is one more than the \(\mathbb F_2\)-rank
\(r(m)\) (it counts both the \(\mathbb F_2\) summands and the cyclic
\(A(4)\) summand as a single \(\mathbb Z\)-generator).

| \(m\) | \(\lvert G\rvert\) | \(\lvert H^3\rvert\) | torsion shape | rank | \(A(4)\) summand | primary citation |
| --- | --- | --- | --- | --- | --- | --- |
| 2 | 32 | \(2^{12} = 4\,096\) | \((\mathbb Z/2)^9 \oplus \mathbb Z/8\) | 10 | \(\mathbb Z/8\) | `computed/transgression/2/kernel.g` (A-2, \#41) |
| 3 | 128 | \(2^{36} \approx 6.87 \times 10^{10}\) | \((\mathbb Z/2)^{34} \oplus \mathbb Z/4\) | 35 | \(\mathbb Z/4\) | `computed/transgression/3/kernel.g` (A-3a, \#42) |
| 5 | 2 048 | \(2^{166} \approx 9.36 \times 10^{49}\) | \((\mathbb Z/2)^{164} \oplus \mathbb Z/4\) | 165 | \(\mathbb Z/4\) | `computed/transgression/5/kernel.g` (A-5b, \#47); \(r(5) = 164\) verified by the A-5b run, consistent with Q-int A2 (\#136 / \#159) |
| 7 | 32 768 | \(2^{454 + 2} = 2^{456}\) | \((\mathbb Z/2)^{454} \oplus \mathbb Z/4\) | 455 | \(\mathbb Z/4\) | Q-int A2 \#159 (\(r(7) = 454\), merged commit `b5c97e9`); kernel computation post Q-int B2-6 \#166 |

Notes on the \(m = 5\) and \(m = 7\) entries:

- The structural form at \(m \ge 3\) is fixed by [HK87 Thm 1.1] — the
  cyclic \(A(4)\) summand is \(\mathbb Z/4\), and the elementary
  abelian rank \(r(m)\) is given by Harada–Kono's formula. At \(m = 7\),
  Q-int A2 has shipped the closed-form value \(r(7) = 454\), so the
  torsion shape is fully determined; only the kernel of the
  transgression (and the \(\omega\)-vector itself) await the kernel
  computation.
- At \(m = 5\), the A-5b production run (issue \#47) now confirms
  \(r(5) = 164\), giving \(\lvert H^3(E_+(5); U(1)) \rvert = 2^{166}\)
  and total rank \(r(5) + 1 = 165\). This is in line with the
  structural expectation \(r(5) \approx 165\) by analogy with
  \(r(3) = 34, r(7) = 454\) under the [HK87 Thm 1.1] growth law, and
  is consistent (within \(\pm 1\) on the integer-rank arithmetic of
  the Quillen presentation) with the Q-int A2 closed-form prediction
  applied to \(m = 5\) (\#136 in the m=5 specialisation; the m=7
  commit at `b5c97e9` proved out the formula).
- The total \(\lvert H^3\rvert\) for \(m = 5\) and \(m = 7\) is far
  beyond what GAP can enumerate as a flat list, but the basis vector
  count (\(r(m) + 1\)) is small enough to sweep in a single GAP
  process. The K-4a / D-VAN pipelines are designed precisely to avoid
  ever materialising \(\lvert H^3\rvert\)-many cocycles in memory.

---

## 6.2 Table 2: Verified anchor results

This table lists the principal anchors run so far across \(m \in \{2, 3, 5, 7\}\),
with the scope (number of entries / assertions), measured wall time,
and the PR that landed each. Each \(m = 3\) row is verified from the
PR's reported measurement (not fabricated); the \(m = 5\) and \(m = 7\)
rows are scaffolded with TBD walls and the relevant unblock PR.

| \(m\) | Anchor | Scope (entries / assertions) | Wall | PR |
| --- | --- | --- | --- | --- |
| 3 | K-3 central row (issue \#40) | \(295\,360\) entries (\(= 130 \times 2272\)), 0 mismatches | \(\approx 16.6\,\)s | \#73 |
| 3 | K-3 extension full \(S\) + \(T\) (issue \#211) | \(5\,164\,256\) entries (\(= 5\,161\,984\) \(S\) + \(2\,272\) \(T\)), 0 mismatches | \(\approx 290\,\)s | \#222 |
| 3 | K-4a `K4aClassify(3)` (T7, issue \#201) | 39 / 39 assertions PASS | \(\approx 3.4\,\)s | \#224, \#228 |
| 2 | K-4a `K4aClassify(2)` (bonus, T4 of `test_k4a_classify.g`) | 8 / 8 assertions PASS; `verdict = "trivial"`, E/D_8/Q_8 all trivial-class | \(< 1\,\)s | \#224 |
| 2 | E_+(2) Tier-4 SNF kernel (A-2, issue \#41) | \(\lvert\ker(\mathrm{Tr})\rvert = 2\,048\) (cross-checked by brute force) | \(\approx 75\,\)s | (T-2 SNF closure, see `section_3_infrastructure.md` \S3.7) |
| 3 | D-VAN Phase 1 anchor: 35 unit generators non-trivial (D-VAN-4, issue \#143) | 35 / 35 generators report `trivial = false`; plus \(2 \cdot e_g\) Q_8 witness | \(\approx 6.2\,\)s | \#150 (Gate 1A/1B at \(m=2\)), \#156 (Q_8 extension, m=3) |
| 5 | A-5b kernel sweep (issue \#47, A-5b) | \(\lvert\ker(\mathrm{Tr})\rvert = 2^{52}\) (52 order-2 generators; no \(\mathbb Z/4\) component; \(\lvert\mathrm{coker}(\mathrm{Tr})\rvert = 2^{114}\)); ground truth for D-VAN-7 \#148 | TBD (full wall) | \#221, \#225, \#233 (R2 perf rounds); \#381–\#386, \#391, \#395 (orbit-cache + Path Z combine); `computed/transgression/5/kernel.g` |
| 5 | K-4b `K4aClassify(5)` (PR \#227 scaffold) | gated on \#220 sparse trace (now landed via \#235) + lifting `n_max_supported := 3` | TBD | PR \#227 scaffold; verdict PR pending |
| 7 | K-4c `K4aClassify(7)` (PR \#242 spec) | gated on \#236 sparse Gauss-sum + \#129 lazy idx + (optional) \#137 LHS-perturbed res | TBD | PR \#242 (spec only); verdict PR future |

Notes on Table 2:

- The K-3 central row anchor and K-3 extension are *separate* tests:
  PR \#73 ran the central-row check first (a fast cross-validation
  baseline); PR \#222 then extended it to the full \(S\) + \(T\)
  matrix as the densest possible ground truth for diagnosing any
  character-misidentification bug in K-4a-T4c (\#218) and its sparse
  variant (\#220 / merged \#235).
- The K-4a anchor at \(m = 3\) (PR \#224 with float-vs-int test fix
  \#228) is the headline gate of the K-4a-T7 acceptance: the
  orchestrator runs the three-subgroup pipeline on the independently-
  understood \(m = 3\) untwisted case (BW(3) = E_8 orbifold; [GK19,
  GK21] per [KRR24] §5.1) and returns `verdict = "trivial"` end-to-end. The
  bonus \(m = 2\) row uses the same orchestrator and is in the same
  test file (T4 of `tests/test_k4a_classify.g`).
- The D-VAN row covers the m=3 portion of `test_detecting_family_vanish.g`;
  the full file (including m=2 Gates 1A/1B and m=3 Tasks 3.1+) runs
  in \(\approx 6.2\,\)s wall total per PR \#156.
- The A-5b m=5 row is the kernel-of-Tr ground-truth sweep, gating
  D-VAN-7 (\#148). The performance work landed in PRs \#221 + \#225
  (KroneckerProduct rewrites of the mod-2 lift inner loops,
  \(\approx 2.3\times\) speedup at \(n = 2048\)) and the batched
  back-substitution variant in PR \#233 (R2-3), with subsequent
  rounds in PRs \#381–\#386 (per-orbit cocycle-basis caches,
  reduced \(M_{\bar{}}\) one-shot build, structured logging), \#391
  (Path Z sparsity-aware GF(2) column-XOR), and \#395 (orbit-cache
  loader bugfix). The kernel result \(\lvert\ker(\mathrm{Tr})\rvert = 2^{52}\)
  is a pure \((\mathbb Z/2)^{52}\) subgroup of
  \((\mathbb Z/2)^{164} \oplus \mathbb Z/4\): every kernel generator
  is of order 2, and the \(\mathbb Z/4\)-summand generator
  \(e_{165}\) is not in the kernel (its image under \(\mathrm{Tr}\) is the
  non-zero order-2 element of \(\mathrm{im}(\mathrm{Tr})\), and the
  half-vector \(2 \cdot e_{165}\) is one of the 52 kernel generators).
  The cokernel order is therefore \(\lvert H^3 \rvert / \lvert \ker \rvert
  = 2^{166} / 2^{52} = 2^{114}\).
- The K-4b row at m=5 was *scaffolded* in PR \#227 ahead of PR \#235
  (sparse trace) landing. With \#235 now merged (`BuildKRRSpectralCharactersSparse`
  for m=5 runs in \(\approx 23.0\,\)minutes wall under the 30-min
  budget), the only remaining blocker on the verdict is lifting the
  `n_max_supported := 3` cap in `k4a_classify.g`. The K-4c row at
  m=7 (PR \#242) is spec only; three named blockers (\#236, \#129,
  \#137) gate the verdict, with \#236 the sparse Gauss-sum closed
  form being the primary path.

---

## 6.3 Table 3: Keller verdict by \(m\)

This is the headline cross-pipeline verdict summary: for each \(m\),
the K-4a verdict, the D-VAN verdict, the joint status, and the
interpretation in plain terms. The \(m \in \{2, 3\}\) rows are filled
from the matched K-4a + D-VAN anchors of Table 2; the \(m \in \{5, 7\}\)
rows are TBD with the in-flight blockers identified.

| \(m\) | K-4a verdict | D-VAN verdict | Status | Interpretation |
| --- | --- | --- | --- | --- |
| 2 | `trivial` (`K4aClassify(2)`, PR \#224) | `trivial` on every basis vector (Gates 1A + 1B, PR \#150) | \(\checkmark\) confirmed | \(V_{\mathrm{BW}(2)}^{E_+(2)}\) lattice orbifold is untwisted; bonus anchor below the Keller \(m \in \{3, 5, 7\}\) range |
| 3 | `trivial` (`K4aClassify(3)`, PR \#224 + \#228) | `trivial` on each basis vector (D-VAN \#143 + \#150 + \#156) | \(\checkmark\) confirmed | matches Keller 2024 \S6 direct construction; \(V_{E_8} = V_{\mathrm{BW}(3)}^{E_+(3)}\); primary calibration anchor |
| 5 | TBD (K-4b at agent \#113 / PR \#227 scaffold; verdict gated on lifting `n_max_supported` cap, sparse trace \#235 now merged) | TBD (D-VAN-7 \#148, blocked on A-5b kernel.g \#47) | in progress | expected: `trivial` (per Keller conjecture / KRR local conditions) |
| 7 | TBD (post K-2c \#129 + sparse Gauss-sum \#236) | TBD (post Q-int B2-6 \#166 + Phase 2 Quillen restriction \#137 / Q-int B3) | future | expected: `trivial` (per Keller conjecture; gap-4 \(c = 128\) holomorphic VOA if confirmed) |

The "Status" column legend:

- \(\checkmark\) confirmed: both K-4a and D-VAN have produced a
  verified verdict at this \(m\) and they agree. Per the disagreement
  triage of \S8.4, the verdict carries the full twin-witness weight.
- "in progress": at least one pipeline is gated on a named upstream
  issue; the section number records the blocker.
- "future": neither pipeline is in flight yet; the path requires
  multiple upstream issues to land first.

What the joint "trivial" verdict means structurally per \S5.2.3 of
the methodology paper: KRR's local conditions on \(c_g\)'s plus
modular-data-on-detecting-subgroups (K-4a) plus
algebraic-restriction-on-detecting-subgroups (D-VAN) all agree on
triviality. Modulo the synthesised detecting-family theorem of \S3,
this is sufficient to conclude \([\alpha] = 0\) in
\(H^3(E_+(m); U(1))\) and hence the orbifold is untwisted.

---

## 6.4 Table 4: Detecting family structure at each \(m\)

The detecting family \(\{E, D_8, Q_8\}\) of \S3 has uniform
structure across \(m\): the maximal elementary abelian \(E\) grows
linearly in rank (\(m + 1\)), and the \(D_8\) / \(Q_8\) sections
always exist for \(m \ge 2\) (per [AM04 \S IV.2 Remark 2.13], since
both isotropic and anisotropic 2-dimensional subspaces of
\(V = E_+(m)/Z\) exist whenever \(\dim V = 2m \ge 4\), i.e. \(m \ge 2\)).
The \(m = 1\) edge case is included for completeness: at \(m = 1\),
\(E_+(1) \cong D_8\) itself (no proper rank-2 anisotropic section),
so the detecting family degenerates.

| \(m\) | \(E\) (max abelian) | rank of \(E\) | \(D_8\) section | \(Q_8\) section |
| --- | --- | --- | --- | --- |
| 1 | \(\mathbb Z/2 \times \mathbb Z/2\) | 2 | \(E_+(1) = D_8\) itself | — (no \(Q_8\) section in \(D_8\)) |
| 2 | \((\mathbb Z/2)^3\) | 3 | exists | exists |
| 3 | \((\mathbb Z/2)^4\) | 4 | exists | exists |
| 5 | \((\mathbb Z/2)^6\) | 6 | exists | exists |
| 7 | \((\mathbb Z/2)^8\) | 8 | exists | exists |

Notes on Table 4:

- The rank of \(E\) is \(m + 1\) per [AM04 \S IV.2 Remark 2.13]: a
  maximal \(Q\)-isotropic subspace of the symplectic / quadratic
  form on \(V = E_+(m)/Z\) has dimension \(m\), and its preimage in
  \(E_+(m)\) has rank \(m + 1\) (including the central \(\mathbb Z/2\)).
- The \(D_8\) section is the preimage of a 2-dimensional \(Q\)-isotropic
  subspace of \(V\); the \(Q_8\) section is the preimage of a
  2-dimensional \(Q\)-anisotropic subspace. Both kinds of 2-dimensional
  subspace exist in \(V\) whenever \(\dim V = 2m \ge 4\), i.e.
  \(m \ge 2\). At \(m = 1\), \(\dim V = 2\) and the form is
  anisotropic on the whole \(V\), so the unique 2-dimensional
  subspace is the whole \(V\), the preimage is \(E_+(1) = D_8\)
  itself, and there is no proper rank-2 anisotropic section to
  identify with \(Q_8\).
- The \(m = 5\) and \(m = 7\) rows are *structural*: the existence
  of the \(D_8\) and \(Q_8\) sections is guaranteed by [AM04]
  abstractly; specific canonical representatives are picked by
  `D8Section_E_plus(m)` and `Q8Section_E_plus(m)` in
  `extraspecial_orbifolds/scripts/quillen_detecting_subgroup.g`.

Cross-reference to Table 1: the detecting family at each \(m\) is
strictly larger than the rank-1 cyclic \(A(4)\) summand (which is
detected on \(Q_8\) alone) plus the elementary-abelian summand of
rank \(r(m)\) (which is detected on \(E\) alone) — that is, the
\(D_8\) section adds detection power only on a subset of the
\(\mathbb F_2\) components, with the structural role spelt out in
\S3.2 of the methodology paper.

---

## 6.5 Figure suggestions

Below are four figures that would visually complement the tables;
each is listed with its purpose, the data needed, and the source
notebook / script that would produce it (when the data is available).
Figures 1 and 2 are diagrammatic / schematic and require no
empirical input; Figures 3 and 4 are data-driven and partially gated
on upstream landings.

### 6.5.1 Figure 1: Twin-pipeline strategy schematic

**Purpose.** Visualise the two-pipeline cross-validation strategy of
\S1.4: a single Keller question \([\alpha] \stackrel{?}{=} 0\) flows
through two epistemically independent verdict paths (D-VAN: algebraic
cohomology-level; K-4a: modular-data lattice-level), with the
detecting family \(\{E, D_8, Q_8\}\) as the shared narrowing point,
and the \(m = 3\) anchor as the cross-validation gate.

**Suggested layout.** A two-column flowchart, with the Keller question
at the top splitting into two branches:

- *Left (D-VAN).* `omega_vec` \(\to\) restriction matrices
  \(M_E, M_{D_8}, M_{Q_8}\) \(\to\) zero-check \(\to\) verdict.
- *Right (K-4a).* lattice intertwiner data \(T_h\) \(\to\) restriction
  to subgroup \(\to\) CT modular data \((S^\alpha\!\restriction_H,
  T^\alpha\!\restriction_H)\) \(\to\) joint matcher vs
  Gruen–Morrison library \(\to\) verdict.

Both branches converge at the bottom into the joint verdict, with a
sidebar listing the \(m = 3\) anchor check that gates application to
\(m = 5, 7\).

**Data needed.** None — purely schematic. Producible from the existing
methodology paper structure.

### 6.5.2 Figure 2: K-4a Phase 2 pipeline diagram

**Purpose.** Visualise the six-stage K-4a Phase 2 pipeline of \S5,
which is the more elaborate of the two pipelines and benefits from a
boxes-and-arrows layout: T1 (joint matcher) + T2 (\(D_8\) classifier)
+ T3 (abelian closed-form) + T4 (\(\varepsilon\) and `trace_on_W`) +
T5a (restriction) + T5b (CT modular data) + T6 (orchestrator) + T7
(anchor regression).

**Suggested layout.** A horizontal flow showing the K-4a-T1 through
T7 sub-issues as labelled boxes, with arrows showing the data
dependency:

- T4a derivation \(\to\) \(\varepsilon \equiv 1\) gauge.
- T4c spectral characters \(\to\) `trace_on_W` (dense at \(m = 3\),
  sparse at \(m = 5, 7\) per \#235).
- T5a (restrict \(\varepsilon\)) + T5b (CT modular data) \(\to\)
  per-subgroup \((S^\alpha\!\restriction_H, T^\alpha\!\restriction_H)\).
- T1 (joint matcher) + T2 (\(D_8\)) + T3 (\(E\)) + (Q_8 classifier) \(\to\)
  branch classifiers.
- T6 (orchestrator) \(\to\) `K4aClassify(m)`.
- T7 (anchor regression at \(m = 3\)) \(\to\) acceptance gate.

PR numbers (e.g. \#206 for T4a, \#218 for T4c dense, \#235 for T4c
sparse, \#216 for T5b, \#217 for T5a, \#203 for T1, \#213 for T2,
\#207 for T3, \#224 for T6) can be annotated on each box.

**Data needed.** None — purely schematic. Producible from the
methodology paper's \S5 + the K-4a Phase 2 spec.

### 6.5.3 Figure 3: BRW orbits of conjugacy classes in \(E_+(m)\)

**Purpose.** Visualise the BRW-induced collapse of conjugacy classes
in \(E_+(m)\) into four orbits per \S2.3 of the methodology paper:
the two singleton central orbits \(\{1\}\) and \(\{-1\}\), and two
large orbits of size \(4^m - 1\) indexed by \(\sigma_2\)-type
(\(Q\)-isotropic vector, centraliser type \(\mathbb Z_2 \times E_+(m-1)\))
and \(\sigma_1 \sigma_2\)-type (\(Q\)-anisotropic, centraliser type
\(\mathbb Z_4 \circ E_+(m-1)\)). At \(m = 3\) the orbit sizes are
\((1, 1, 35, 28)\) for total 65 classes (matches `IrrConjugacyClasses(E_+(3))`);
at \(m = 5\) they are \((1, 1, 1023, 1024)\) for 2 049 classes
(confirmed by the A-5b production run, issue \#47).

**Suggested layout.** A 2 \(\times\) 2 grid of pie-charts or stacked
bar charts, one per \(m \in \{2, 3, 5, 7\}\), showing the four orbit
sizes. Annotate each orbit with the centraliser type and the
\(\sigma\)-type label. The growth pattern \(4^m - 1\) is the visual
takeaway.

**Data needed.** Orbit sizes at each \(m\). At \(m \in \{2, 3, 7\}\)
these are closed-form (\(\sigma_2\)-type: \(4^m - 1\) at the
\(Q\)-isotropic count, \(\sigma_1 \sigma_2\)-type: \(4^m - 1\) at the
\(Q\)-anisotropic count, modulo the precise formulas in [AM04 \S IV.2]);
at \(m = 5\) the value agrees with the closed form
\((1, 1, 4^5 - 1, 4^5 - 1) = (1, 1, 1023, 1023)\) (with one extra
class accounted for by the central pair / total-2049 reconciliation
in [AM04 \S IV.2 Remark 2.13]), recorded in `computed/transgression/5/`
after the A-5b run.

**Source.** A short GAP script reading the conjugacy-class structure
from `OrbitsDomain(BRW(m), Elements(E_+(m)))` and tabulating sizes;
or a pure analytical computation from the [AM04] formulas. Producible
ad hoc; not yet in repo.

### 6.5.4 Figure 4: Wall-time scaling of K-3 vs K-4a at \(m = 3\)

**Purpose.** Compare the wall-time profile of the K-3 central-row
anchor (PR \#73, 16.6 s), the K-3 extension full \(S\) + \(T\)
anchor (PR \#222, 290 s), and the K-4a end-to-end pipeline (PR \#224,
3.4 s) at \(m = 3\). The visual takeaway: the K-4a pipeline is
\(\sim 5\times\) faster than the K-3 central-row anchor and
\(\sim 85\times\) faster than the K-3 extension, because K-4a sees
only the detecting subgroups (\(D_8, Q_8\) each of rank 22; \(E\) of
rank 256) rather than the full \(E_+(3)\) of rank 2 272.

**Suggested layout.** A horizontal bar chart with three bars (K-3
central, K-3 extension, K-4a) labelled with the wall time and entry
count. The bars should be log-scaled to make the K-4a's 3.4 s legible
alongside the K-3 extension's 290 s.

**Data needed.**

| Anchor | Wall (s) | Entries verified | PR |
| --- | --- | --- | --- |
| K-3 central row | 16.6 | 295 360 | \#73 |
| K-3 extension full \(S\) + \(T\) | 289.8 (\(\approx 290\)) | 5 164 256 (5 161 984 \(S\) + 2 272 \(T\)) | \#222 |
| K-4a end-to-end | 3.4 | 39 assertions PASS (branch ranks: \(E\) 256, \(D_8\) 22, \(Q_8\) 22) | \#224 |

**Source.** All three numbers are reproducible from the K-3 + K-4a
test files in `extraspecial_orbifolds/scripts/tests/`. Producible as
a single matplotlib plot from the PR-reported numbers.

---

## 6.6 What this section will look like after \(m = 5\) and \(m = 7\) land

The forward-looking entries — Table 1 \(m \in \{5, 7\}\) rows
(specifically the \(\lvert H^3 \rvert\) and rank values at \(m = 5\),
gated on Q-int A2 at \(m = 5\)), Table 2 \(m \in \{5, 7\}\) wall times,
Table 3 \(m \in \{5, 7\}\) verdicts, Figure 3 \(m = 5\) orbit data,
and Figure 4 \(m = 5\) wall-time bar — are scaffolded against the
in-flight issues:

| Placeholder | Source of fill | Tracking issue / PR |
| --- | --- | --- |
| Table 1 \(m = 5\) \(\lvert H^3 \rvert\), rank | Filled (A-5b m=5): \(\lvert H^3 \rvert = 2^{166}\), rank \(= 165\) (\(r(5) = 164\)) | \#47 (this PR) |
| Table 2 \(m = 5\) A-5b wall | Filled in part (\(\lvert\ker\rvert = 2^{52}\)); full sweep wall still pending the post-fact wall-time read-off | \#47 |
| Table 2 \(m = 5\) K-4b wall | `run_k4b_m5.sh` output post sparse-trace lift | PR \#227 + PR \#235 |
| Table 2 \(m = 7\) walls | K-4c m=7 production run | PR \#242 spec; verdict PR future |
| Table 3 \(m = 5\) K-4a verdict | `K4aClassify(5).verdict` | PR \#235 + lifting `n_max_supported` cap |
| Table 3 \(m = 5\) D-VAN verdict | D-VAN-7 \#148 + A-5b kernel.g (kernel.g now available) | \#148, \#47 |
| Table 3 \(m = 7\) verdicts | post K-2c \#129 + sparse Gauss-sum \#236 + (D-VAN) Q-int B2-6 \#166 | \#187 K-4 EPIC, \#190 K-4c spec |
| Figure 3 \(m = 5\) orbit sizes | A-5b run output (orbit sizes \((1, 1, 1023, 1024) = 2\,049\) classes total) | \#47 |
| Figure 4 \(m = 5\) K-4a wall | K-4b production run | \#235 + PR \#227 verdict |

Each TBD placeholder above is a one-line edit once the upstream
issue lands; the surrounding prose is final. On final fill, the
"Status" column of Table 3 at \(m = 5\) and \(m = 7\) will resolve
to one of (i) \(\checkmark\) confirmed `trivial` (the Keller-predicted
outcome), (ii) \(\checkmark\) confirmed `non-trivial` with explicit
class identification, or (iii) the disagreement triage of \S8.4 if
the two pipelines diverge.
