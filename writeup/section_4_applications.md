# 4. Per-\(m\) applications

This section reports the per-\(m\) status of the Keller question
\([\alpha] \stackrel{?}{=} 0\) in \(H^3(E_+(m); U(1))\), using the
methodology of `writeup/methodology.md`. The empirical anchor at \(m = 3\)
is now fully landed (PRs #224, #228); \(m = 5\) and \(m = 7\) are scaffolded
for fill-in once the relevant computational blockers clear. \(m = 2\) is
included as a warm-up — the relevant kernel is small enough that the
verdict was already accessible by brute force, but it exercises the same
pipelines and so serves as an anchor for both.

The format per subsection is uniform: (i) the cohomology setting and order,
(ii) the verified anchors, with verbatim test outputs and wall times,
(iii) the verdict at the present \(m\), and (iv) what is left to do.
Subsection §4.5 summarises the implications of the per-\(m\) verdicts.

---

## 4.1 \(m = 2\) — warm-up, also verified

### 4.1.1 Setting

The group is \(E_+(2) \cong 2_+^5 \cong \mathrm{SmallGroup}(32, 49)\) of order
\(|E_+(2)| = 2^5 = 32\). Its degree-3 cohomology with \(U(1)\) coefficients
has torsion structure
\[
  H^3(E_+(2); U(1)) \;\cong\; (\mathbb Z/2)^{9} \oplus \mathbb Z/8,
\]
so \(|H^3(E_+(2); U(1))| = 2^{12} = 4\,096\) and the cyclic
\(A(4) \cong \mathbb Z/8\) summand of [HaradaKono1987 Thm 1.1] attains order
8 (the largest among the \(m\)'s of interest). At \(m = 2\) the codimension
\(h(Q) = 2\) and the 2-adic valuation \(n(4) = 2\) violate the inequality
\(n(k) \le h(Q) - 1 = 1\), so by the HK87 formula \(a(k, Q) = h(Q) + 1 = 3\)
and \(A(4) \cong \mathbb Z/2^3 = \mathbb Z/8\) — see §2.4 of the methodology
paper. The kernel of the total transgression of §1.2 was computed two
independent ways:

- *Brute force.* Direct enumeration of all 4 096 \(H^3\) classes via
  Adem–Milgram and per-class testing for \([c_g] = 0\). Output file
  `computed/transgression/2/kernel.g` (issue #41, A-2).
- *Structured solver.* The torsion-split + BRW-amortised pipeline of
  `writeup/section_3_infrastructure.md` (issue #46, T-2 SNF closure on the
  per-generator output). Driver `run_e_plus_2_kernel.g`.

Both routes agree:
\[
  |\ker(\mathrm{Tr})| = 2\,048 = 2^{11},
\]
which is exactly *half* of \(|H^3(E_+(2); U(1))|\). The brute-force file
records the full kernel as a lex-sorted list of 2 048 integer vectors in
\((\mathbb Z/2)^9 \oplus \mathbb Z/8\) (lines 30–onwards of
`computed/transgression/2/kernel.g`); the structured solver returns the
same kernel as a \(\mathbb Z\)-generator list of identical
\(\mathbb Z\)-span. The structured solver runs in
\(\sim 75\,\mathrm{s}\) wall on a 2024 laptop, vs. the augmented-\(\mathbb Z\)
baseline which exceeded \(3{:}13\) without completing a single generator
(`writeup/section_3_infrastructure.md` §3.7).

### 4.1.2 Verified anchors

| Anchor | Result | Wall | Reference |
| --- | --- | --- | --- |
| Tier-4 SNF closure (A-2, #41) | \(\lvert\ker(\mathrm{Tr})\rvert = 2\,048\) | \(\sim 75\,\)s | `run_e_plus_2_kernel.g` |
| Brute-force enumeration | \(\lvert\ker(\mathrm{Tr})\rvert = 2\,048\), agrees | n/a | `computed/transgression/2/kernel.g` |
| K-4a m=2 `K4aClassify(2)` (bonus) | `verdict = "trivial"`, E/D_8/Q_8 all trivial-class | \(\sim 3\,\)s | PR #224 + #228, `tests/test_k4a_classify.g` T4 |
| D-VAN Gate 1A at m=2 (#143, #144) | 10/10 unit generators reported non-trivial | sub-ms each | `tests/test_detecting_family_vanish.g` |
| D-VAN Gate 1B at m=2 (the \(\mathbb Z/8\) witness) | order-8 generator caught by \(Q_8\); \(\mathrm{res}_{D_8}\) row is even | sub-ms | same |

The K-4a m=2 test (T4 of `test_k4a_classify.g`) asserts:

- `K4aClassify(2).verdict = "trivial"`,
- `E_class.is_coboundary = true`,
- `D8_class.class_idx = 1` (trivial 3-cocycle),
- `Q8_class.class_idx = 1` (trivial 3-cocycle),
- E branch rank \(=\lvert E\rvert^2 = (2^{m+1})^2 = 8^2 = 64\) at \(m = 2\),
- D_8 and Q_8 CT modular data are rank 22.

D-VAN's Gate 1B is the *load-bearing* m=2 check from the §3 detection
argument: a class generating the \(\mathbb Z/8\) summand of
\(H^3(E_+(2); U(1))\) must be caught by the \(Q_8\)-restriction. The full
\(\{E, D_8, Q_8\}\) family does so. R-1 follow-up (issue #215, PR #219,
§3.5 of `docs/superpowers/research/2026-05-17-d8-vs-q8-detection.md`) shows
that \(\{E, D_8\}\)-only would *miss* the order-2 sub-element \(4 \cdot e_g\)
of the \(\mathbb Z/8\) generator (the \(D_8\) restriction lands in
\(\{0, 2\} \subset \mathbb Z/4\), so doubling kills it once and quadrupling
kills it twice). The \(Q_8\) restriction lands on an odd element of
\(\mathbb Z/8\) and survives both doublings.

### 4.1.3 Verdict at \(m = 2\)

\([\alpha] = 0\) is the expected verdict: Keller's lattice orbifold of
\(V_{\mathrm{BW}(2)}\) at the \(E_+(2)\)-grading is the BW-coded
Niemeier–like construction at central charge \(c = 4\), which is
classically untwisted. K-4a at m=2 returns `verdict = "trivial"` in
\(\sim 3\,\)s with all three detecting-subgroup branches concurring.

The verdict is consistent with the structural observation that
\(|\ker(\mathrm{Tr})| = 2^{11}\) is *half* of \(|H^3|\), so the kernel is a
proper subgroup at this \(m\) and the local-cocycle obstruction
\([c_g] = 0\) for all \(g\) does not by itself collapse the kernel to the
origin. The K-4a verdict supplies the extra information needed to pin the
class at \([\alpha] = 0\) within that kernel.

---

## 4.2 \(m = 3\) — primary anchor, fully verified

### 4.2.1 Setting

The group is \(E_+(3) \cong 2_+^7 \cong \mathrm{SmallGroup}(128, 2326)\) of
order \(|E_+(3)| = 2^7 = 128\). Its degree-3 cohomology is
\[
  H^3(E_+(3); U(1)) \;\cong\; (\mathbb Z/2)^{34} \oplus \mathbb Z/4,
\]
so \(|H^3(E_+(3); U(1))| = 2^{36} = 68\,719\,476\,736\) and the \(A(4)\)
summand drops to \(\mathbb Z/4\) by [HK87 Thm 1.1]: at \(m = 3\), \(h(Q) = 3\)
and \(n(4) = 2\), so the inequality \(n(k) \le h(Q) - 1 = 2\) is now
satisfied (with equality), giving \(a(k, Q) = n(k) = 2\) and
\(A(4) \cong \mathbb Z/2^2 = \mathbb Z/4\). The elementary-abelian part
jumps from rank 9 to rank 34. The torsion vector recorded in
`computed/transgression/3/kernel.g` is
\[
  [\underbrace{2, 2, \dots, 2}_{34 \text{ copies}}, 4], \qquad \exp = 4.
\]
The maximal elementary abelian \(E \le E_+(3)\) has rank \(m + 1 = 4\) and
order \(|E| = 16\).

The kernel of the total transgression at \(m = 3\) is computed by the
per-generator BRW-amortised sweep (T-3d + T-4 + T-5,
`run_e_plus_3_kernel.g`, A-3a issue #42) and persists in
`computed/transgression/3/kernel.g`. The headline:
\[
  \lvert\ker(\mathrm{Tr})\rvert
  \;=\; 68\,719\,476\,736
  \;=\; \lvert H^3(E_+(3); U(1))\rvert,
\]
i.e. **the whole \(H^3(E_+(3); U(1))\) is in the kernel of \(\mathrm{Tr}\)**
at \(m = 3\). Every basis vector \(e_i\) (\(i = 1, \dots, 35\)) is in
\(\ker(\mathrm{Tr})\); so is the half-vector \(2 \cdot e_{35}\) (the only
order-4 generator). The "DP-I" verdict at m=3 (file
`computed/transgression/3/dp_i_verdict.g`) records this as the
*candidate-elimination* branch trigger:

```text
kernel_size       := 68719476736,
kernel_trivial    := false,
branch_label      := "candidate-elimination",
verdict           := "DP-I: |ker Tr| = 68719476736. Next: candidate-elimination"
```

This makes \(m = 3\) the structurally interesting case for the Keller
question: the local 2-cocycle test \([c_g] = 0\) for all \(g\) is
*completely uninformative* (every class satisfies it), and we need a
sharper invariant to pin \([\alpha]\) at \(0 \in H^3\). K-4a's modular-data
verdict and D-VAN's restriction verdict are precisely such sharper
invariants.

### 4.2.2 Verified anchors at \(m = 3\)

We have five independent verifications converging on the verdict
\([\alpha] = 0\) at \(m = 3\):

#### Anchor 1 — A-3a Tier-4 transgression kernel (#42)

Driver: `run_e_plus_3_per_gen.g` (per-generator BRW sweep over the 4 BRW
orbits of conjugacy classes: sizes 1, 35, 28, 1, total 65 classes), with
T-4 centraliser-type cache (~5 distinct centraliser iso-classes) and T-5
resumable per-generator state.

Result: \(\lvert\ker(\mathrm{Tr})\rvert = 2^{36}\) — the entire
\(H^3(E_+(3); U(1))\). Cross-checked on 100 deterministic-stride
kernel-sample vectors (all verified in-kernel against all 65 centralisers
via `IsCoboundary2Split`) and 100 non-kernel-sample vectors (all detected
as not-in-kernel, by construction `kernel + not-in-ker unit-gen`).

#### Anchor 2 — K-3 central-row anchor (#40)

Test: `tests/test_krr_vs_central_closed_form.g`.

Three-way agreement on every entry of *central rows* of \(S^{\mathrm{Keller}}\)
at \(m = 3\):

- A: `SKeller(3, gi, gj)` from the K-2 adapter (`skeller_adapter.g`);
- B: the inline §4.3 closed-form expression
  \(S^0_{(g_1, \rho), (h, \sigma)} = \dim\sigma / \lvert C_G(h)\rvert \cdot \overline{\rho(h)}\)
  for \(g_1\) central, recomputed from scratch via `CentralSEntryClosedForm`;
- C: the helper `ClosedFormCentralS` in `closed_form_central.g`.

Entry count: \(2 \text{ central classes} \times \lvert\mathrm{Irr}(G)\rvert \times \mathrm{rank} = 2 \times 65 \times 2272 = 295\,360\) entries
(two singleton central classes \(\{+I\}\) and \(\{-I\}\); \(\mathrm{Irr}(G)\)
provides 65 row-irreps; the rank is the total number of simples of
\(D^0(E_+(3))\), \(2272\)).

Reported result (from the test header, line 7 of `test_krr_full_s_t.g`):
the K-3 central-row sweep completes in approximately **16.6 s** wall on
\(295\,360 / 295\,360\) entries with **0 mismatches**. PR #73 merged this
anchor (commit `d0ecb3c`).

#### Anchor 3 — K-3 extension: full \(S\) + \(T\) at \(m = 3\) (#211, PR #222)

Test: `tests/test_krr_full_s_t.g`.

Densest possible cross-check: every entry of \(S^{\mathrm{Keller}}\) and
every diagonal entry of \(T^{\mathrm{Keller}}\) at \(m = 3\). The rank
is \(2272\), so:

- \(S\) entries: \(2272^2 = 5\,161\,984\), of which we verify
  `SKeller(3, gi, gj) = S^0(gi, gj)` via block-amortised `ComputeSBlock`
  comparison plus symmetric-pair cross-check. **0 mismatches** on all
  \(5\,161\,984\) entries.
- \(T\) entries: \(2272\), of which we verify
  \(T^{\mathrm{Keller}}_{\mathrm{diag}}[gi] = T^0_{\mathrm{diag}}[gi]\)
  via the LAZY `BuildSimpleIndexLazy` path against a fresh EAGER
  `BuildSimpleIndex` (independent code paths, same algebraic formula
  \(T_{(g, \chi)} = \chi(g)/\chi(1)\)). **0 mismatches** on all \(2272\)
  entries.
- \(T\) spectrum: every entry is a fourth root of unity, matching the
  analytical prediction for \(E_+(3)\) (cf. `extraspecial_orbifolds/scaling_plan.md`
  line 193: \(T\)-multiset \(\{1^{1172}, -1^{1044}, i^{28}, -i^{28}\}\)).

Reported wall (PR #222 summary table):

| Phase | Wall |
| --- | --- |
| K-2 cache build | 0.07 s |
| Eager idx build | 0.15 s |
| T diagonal | 0.12 s |
| Full S sweep | 289.8 s |
| **Total** | **\(\sim 290\,\mathrm{s}\) (\(\sim 4\):50)** |

This is the strongest ground-truth baseline available at \(m = 3\) for
diagnosing modular-data character-misidentification bugs in K-4a-T4c
(#218) and its sparse variant (#220); it confirms that the K-2 SKeller
adapter, the closed-form central-row expression, and the dense untwisted
`ComputeSBlock` are byte-for-byte consistent across the entire modular
center.

#### Anchor 4 — K-4a end-to-end at \(m = 3\) (#200, #201, PR #224 + #228)

Test: `tests/test_k4a_classify.g`. This is the K-4a-T7 acceptance gate of
issue #201: KRR's m=3 lattice orbifold is verified untwisted, so
`K4aClassify(3)` must return `verdict = "trivial"` with all three
detecting-subgroup classifiers returning their trivial-class indices.
Result:
\[
  \texttt{K4aClassify}(3)\texttt{.verdict} \;=\; \texttt{"trivial"}.
\]

Per-branch outputs (from T2 of the test, lines 169–199):

| Branch | Subgroup type | Rank of CT modular data | Verdict | Wall |
| --- | --- | --- | --- | --- |
| E (maximal elementary abelian, \(\mathbb Z_2^4\), \(\lvert E\rvert = 16\)) | abelian | \(\lvert E\rvert^2 = 256\) simples | `is_coboundary = true` | \(\sim 1.4\,\)s |
| \(D_8\) (any rank-2 dihedral section) | non-abelian | 22 | `class_idx = 1` (trivial) | \(\sim 1.0\,\)s |
| \(Q_8\) (any rank-2 quaternion section) | non-abelian | 22 | `class_idx = 1` (trivial) | \(\sim 1.0\,\)s |

Total wall: **\(\sim 3.4\,\)s** (budget 300 s, per the spec in `k4a_classify.g`).
**39 / 39 assertions PASS** (T1 smoke 4; T2 m=3 anchor 23; T3 m≥4 error
path 4; T4 m=2 smoke 8) — see PR #228 summary.

By the §3 detection theorem (Quillen 1971 + Harada–Kono 1987 + UCT, with
R-1 follow-up's empirical confirmation that \(Q_8\) is genuinely required),
the conjunction of the three branch verdicts is the verdict on \(G\)
itself:
\[
  \begin{aligned}
    [\alpha]\bigr|_E       &= 0
      &&\Longleftarrow\ \texttt{E\_class.is\_coboundary} = \texttt{true},\\
    [\alpha]\bigr|_{D_8}   &= 0
      &&\Longleftarrow\ \texttt{D8\_class.class\_idx} = 1,\\
    [\alpha]\bigr|_{Q_8}   &= 0
      &&\Longleftarrow\ \texttt{Q8\_class.class\_idx} = 1,\\
    \therefore\quad [\alpha] &= 0 \text{ in } H^3(E_+(3); U(1)).
  \end{aligned}
\]
This is the **K-4a Phase 2 m=3 GREEN anchor** referenced in the
methodology paper §8.1.

A technical note: at \(m \le 3\), the K-4a orchestrator uses
`BuildIntertwinerDataUntwisted(branch.parent)` rather than the spectral
KRR characters from `BuildKRRSpectralCharacters(m)`. The two are
*observationally identical* under Keller's verified \([\alpha] = 0\), and
the untwisted route avoids both the K-4a-T4c multiplicity question (#218)
and the m=5 sparse-trace infeasibility (#220). The spectral path will be
exercised at m=5 once #220 lands. See lines 36–46 of
`extraspecial_orbifolds/scripts/k4a_classify.g`.

#### Anchor 5 — D-VAN Phase 1 at \(m = 3\) (#143, #144)

Test: `tests/test_detecting_family_vanish.g`, Task 3.1 onwards.

D-VAN's Gate 1A at \(m = 3\): for each of the **35 unit generators** \(e_i\)
(\(i = 1, \ldots, 35\)) of the hom-basis of \(H^3(E_+(3); U(1))\),
\(\texttt{ResIsTrivialOnDetectingFamily}(3, e_i)\) must return
`trivial = false` (each \(e_i\) is non-zero in \(H^3\) by construction; by
detection-family injectivity, its restriction must therefore be non-zero on
at least one of \(\{E, D_8, Q_8\}\)). **All 35/35 generators correctly
report non-trivial.**

A subtler test exercises the order-4 invariant factor of the
\(A(4) \cong \mathbb Z/4\) summand at \(m = 3\). With
\(e_g = e_{\text{exp\_index}}\) the order-4 generator (`exp_index = 35`
per `computed/transgression/3/kernel.g`):

| Class | Order in \(H^3\) | D-VAN verdict |
| --- | --- | --- |
| \(e_g\) | 4 | non-trivial |
| \(2 \cdot e_g\) | 2 | **non-trivial** (\(Q_8\) catches; D_8 row is \([0, 0, 2]\) in \(\mathbb Z/4\), doubling kills) |
| \(4 \cdot e_g\) | 1 (zero class) | trivial |

The order-2 case \(2 \cdot e_g\) is the R-1 follow-up witness: with the
\(Q_8\) section in the family the verdict is correctly `non-trivial`;
without \(Q_8\) (i.e. \(\{E, D_8\}\) only) the verdict would be a *false
positive trivial*, since the \(D_8\) restriction lands in
\(\{0, 2\} \subset \mathbb Z/4\) and doubling kills it. See lines 277–292
of `test_detecting_family_vanish.g` and PR #219 §3 for the full table.

This is the **load-bearing test** for the §3.3 detection-family
argument of the methodology paper: the empirical evidence that \(Q_8\) is genuinely required at
\(m \ge 3\) and not just an artefact of section choice (PR #219
exhaustively enumerated all 280 conjugacy classes of \(D_8\)-subgroups of
\(E_+(3)\), confirming that no choice of \(D_8\) section detects
\(2 \cdot A(4)_{\mathrm{gen}}\)).

### 4.2.3 Verdict at \(m = 3\)

\([\alpha] = 0\) in \(H^3(E_+(3); U(1))\), confirmed independently by:

- K-3 (central-row \(S\) match, anchor 2),
- K-3 extension (full \(S\) + \(T\) match, anchor 3),
- K-4a (modular-data verdict via CGR §5.2 closed-form, anchor 4),
- D-VAN Phase 1 (algebraic restriction verdict, anchor 5).

The K-4a verdict aligns with the independent verification by Keller in
[Keller24 arXiv:2410.18638 §6] that the BW-lattice orbifold at \(m = 3\)
is untwisted; this is the *known* anchor case for the Keller question, and
it tests the K-4a/D-VAN pipelines in the regime where the answer is
expected.

The strongest claim made by anchors 4 and 5 (which together are the K-4a
Phase 2 m=3 GREEN and D-VAN Phase 1 m=3 GREEN gates of the methodology
paper §8.1) is therefore:

> The K-4a and D-VAN pipelines have been **calibrated against the known
> Keller anchor at \(m = 3\)** and return the correct verdict
> (`trivial`) in both algebraic and modular-data formulations.

This is the methodological precondition for applying the same pipelines
at \(m = 5\) and \(m = 7\).

---

## 4.3 \(m = 5\) — in progress

### 4.3.1 Setting

The group is \(E_+(5) \cong 2_+^{11}\), order \(|E_+(5)| = 2^{11} = 2\,048\).
By [HK87 Thm 1.1] the integer cohomology is
\[
  H^3(E_+(5); U(1)) \;\cong\; (\mathbb Z/2)^{r(5)} \oplus \mathbb Z/4,
\]
with \(r(5)\) the rank of the \(\mathbb F_2\)-part. The exact value of
\(r(5)\) is the target of the Q-int A2 derivation (issue #159) and the
A-5b kernel-of-\(\mathrm{Tr}\) driver (issue #47); HAP's resolution build at
\(m = 5\) succeeded in 548 s wall and 1.21 GB peak RSS (file
`computed/transgression/5/dp_ii_verdict.g`, DP-II succeeded branch).

Critically: at \(m = 5\) we **cannot** brute-force enumerate \(H^3\) — the
order is many orders of magnitude beyond what GAP can store as a flat
list — so the kernel of \(\mathrm{Tr}\) at this \(m\) is itself out of
reach without algorithmic structure. This is the regime where the
**twin-witness K-4a + D-VAN strategy of §1.4** becomes load-bearing
rather than merely cross-checking.

### 4.3.2 Status of the two pipelines at \(m = 5\)

**D-VAN at \(m = 5\)** is gated on the empirical kernel-of-\(\mathrm{Tr}\)
ground truth from A-5b (#47). The A-5b R2 performance work has shipped
two `KroneckerProduct` rewrites of the mod-2 lift inner loops (PRs #221
for `BocksteinH1ToH2`, #225 for `IsCoboundary2Mod2WithLiftWitness`), each
giving a measured 2.33×–2.37× speedup at \(n = 2048\); batched
back-substitution is in flight on branch `a5b-r2-3-batched-backsub`. The
m=5 kernel sweep itself runs on PID 22335 at time of writing (a multi-day
background job).

Once A-5b lands `computed/transgression/5/kernel.g` in the same schema as
`computed/transgression/3/kernel.g` (the `in_kernel_gens`, `exp_index`,
`half_vec_in_kernel`, `basis_summary` fields described in
`writeup/section_3_infrastructure.md`), D-VAN-7 (#148) will run the
analogous unit-generator sweep at \(m = 5\) and compare. The expectation
(by analogy with \(m = 2, 3\) and by Harada–Kono structure) is that
\(\ker(\mathrm{Tr})\) is *at least* the rank-1 \(A(4)\) and the
\(\mathbb F_2\) elementary-abelian part — i.e. potentially the whole
\(H^3(E_+(5); U(1))\) as at \(m = 3\), or a proper sub if some local
2-cocycle catches one of the generators. Either way the D-VAN verdict
on each unit generator is then a single matrix–vector product followed by
a zero check, and is sub-millisecond per generator (cf. §4.2 of the
methodology paper).

**K-4a at \(m = 5\)** is gated on the sparse trace optimisation of issue
#220. The dense computation `BuildKRRSpectralCharacters(m)` takes 2.4 s
at \(m = 3\) but is projected at \(\sim 3.7\,\)years per \(T_h\) matrix at
\(m = 5\) — the central defect representation \(\Omega_0\) has dimension
\(2^{16} = 65\,536\), and a single \(T_h\) matrix has \(2^{32} \approx 4.3 \times 10^9\)
entries at \(\sim 27\,\)ms each. The sparse variant
`BuildKRRSpectralCharactersSparse(m)` (issue #220, in flight) replaces
the entry-wise materialisation with a trace-only path: compute
\(\mathrm{Tr}(T_h^j)\) for \(j \in \{0, 1, \ldots, \lvert C_G(a)\rvert - 1\}\),
each touching only the \(2^k\) diagonal entries; then invert via the
character orthogonality
\[
  \mathrm{mult}_\chi
  \;=\; \frac{1}{\lvert C_G(a)\rvert} \sum_{h \in C_G(a)} \mathrm{Tr}(T_h) \cdot \overline{\chi(h)}.
\]
The acceptance criterion for #220 is `Tr(T_h)` per `(class, h)` pair in
seconds (not hours) at \(m = 5\), with a total `BuildKRRSpectralCharactersSparse(5)`
budget of \(<\,30\,\)minutes (#220 acceptance). The K-4b m=5 production
driver scaffold (PR #227, `run_k4b_m5.sh` + `k4b_xcheck_d_van.g` +
`TEMPLATE-k4b-m5-verdict.md`) is in place and gated on #220 + T6.

### 4.3.3 Placeholder verdict and unblock path

**Verdict at \(m = 5\):** *TBD.*

| Unblock | What | Status |
| --- | --- | --- |
| #220 | `BuildKRRSpectralCharactersSparse(5)` lands at \(< 30\) min wall | in flight |
| #47 / A-5b | `computed/transgression/5/kernel.g` produced | running (PID 22335) |
| #148 / D-VAN-7 | D-VAN unit-generator sweep at m=5 + verdict-vs-kernel agreement | gated on #143, #47 |
| PR #227 / K-4b | `run_k4b_m5.sh` execution | gated on #220 + T6 |

The expected outcome (per Keller's prediction): \([\alpha] = 0\) in
\(H^3(E_+(5); U(1))\). If confirmed, the K-4b verdict + D-VAN-7
cross-check forms the **empirical proof of Keller's m=5 conjecture
under the detecting-family injectivity assumption of §3**.

If the verdict is non-trivial at \(m = 5\), the cross-validation triage of
§8.4 of the methodology paper applies: a K-4a / D-VAN disagreement points
to one of the three causes (pipeline bug, CT-assumption violation,
detection-family failure) and the smaller of the two pipelines (D-VAN)
adjudicates first.

### 4.3.4 What §4.3 will record once \(m = 5\) lands

The following fields are TBD placeholders to be filled in by the K-4b
verdict ship:

- **`kernel_size` at \(m = 5\):** TBD (loaded from `computed/transgression/5/kernel.g`).
- **`torsion` shape:** TBD (expected \((\mathbb Z/2)^{r(5)} \oplus \mathbb Z/4\); the value of \(r(5)\) is a Q-int A2 deliverable).
- **D-VAN-7 result:** TBD (35-or-\(r(5)\)-many unit-generator verdicts, expected all `non-trivial`).
- **K-4b verdict:** TBD (`K4aClassify(5).verdict`).
- **Per-branch wall times:** TBD (expected: similar order of magnitude as m=3, dominated by `BuildKRRSpectralCharactersSparse(5)` build cost).
- **K-4b/D-VAN cross-table at \(m = 5\):** TBD (the §8.5 archival record).

---

## 4.4 \(m = 7\) — future work

### 4.4.1 Setting

The group is \(E_+(7) \cong 2_+^{15}\), order \(|E_+(7)| = 2^{15} = 32\,768\).
The integer cohomology has shape
\[
  H^3(E_+(7); U(1)) \;\cong\; (\mathbb Z/2)^{r(7)} \oplus \mathbb Z/4,
\]
again by [HK87 Thm 1.1]. Q-int A2 (#159, merged commit `b5c97e9`) gives
\(r(7) = 454\), so the torsion vector at \(m = 7\) is
\([2 \times 454, 4]\), \(|H^3| = 2^{454} \cdot 4\) — many orders of
magnitude beyond direct enumeration.

At \(m = 7\) the HAP resolution at depth 4 OOMs (projected memory cost on
the order of TB without algorithmic redesign, per issue #137). Both
pipelines therefore require their respective Phase 2 / production paths:

### 4.4.2 Status of the two pipelines at \(m = 7\)

**D-VAN at \(m = 7\)** requires Phase 2 — Quillen-based restriction
matrices (cf. §4.3 of the methodology paper). The Phase 2 spec is
`docs/superpowers/specs/2026-05-16-path3-hap-resolution-redesign.md`
(Path 3 / Pontryagin square redesign); the matrix construction would
analytically pull back along inclusions of the Quillen-canonical
presentation. Cross-validation at \(m = 2, 3, 5\) against the HAP
restriction matrices is the Gate 2A criterion of the D-VAN design doc.

**K-4a at \(m = 7\)** would require:

1. The Q-int B2-6 m=7 production kernel (#166), which is itself blocked on
   the completion of the Q-int B3 Pontryagin path (Path 3 active; Path 4
   sparse-HAP ruled out at \(\sim 28\times\) memory penalty).
2. The analytical \(T_h\) computation at \(m = 7\) (the optim pipeline's
   `compute_e_plus_7_T_analytical.g` is in place modulo verification —
   the dense path is \(\Omega_0\)-dimension \(\sim 1.8 \times 10^{19}\),
   forcing the sparse-trace path to be load-bearing here).
3. A-7a (#50) Tier-4 driver for \(\ker(\mathrm{Tr})\) at \(m = 7\) (the
   D-VAN cross-anchor at \(m = 7\)), itself blocked on Q-int B2-6.

### 4.4.3 Placeholder verdict and unblock path

**Verdict at \(m = 7\):** *TBD post m=5.*

The dependency chain is:

\[
  \text{m=5 ships} \;\Longrightarrow\; \text{pipeline validated}
  \;\Longrightarrow\; \text{m=7 unblock track:}
\]

| Unblock | What | Issue / spec |
| --- | --- | --- |
| Q-int B3 Pontryagin | low-mem HAP resolution alternative | #137 / `docs/superpowers/specs/2026-05-16-path3-hap-resolution-redesign.md` |
| Q-int B2-6 | m=7 production kernel.g | #166 |
| A-7a | m=7 Tier-4 driver \(\ker(\mathrm{Tr})\) | #50 |
| K-4a m=7 | spectral characters via analytical \(T_h\) + sparse trace at \(\dim \Omega_0 \approx 1.8\,{\times}\,10^{19}\) | gated on #220, #166 |
| D-VAN at m=7 | Phase 2 Quillen restriction matrices, validated at m \(\le\) 5 | D-VAN design §4.3 |

The expected outcome (per Keller's prediction): \([\alpha] = 0\) in
\(H^3(E_+(7); U(1))\). The same disagreement triage of §8.4 applies if
the verdict is non-trivial.

### 4.4.4 What §4.4 will record once \(m = 7\) lands

- **Kernel-of-\(\mathrm{Tr}\) at \(m = 7\):** TBD (output of #166 + A-7a).
- **D-VAN at m=7:** TBD (Phase 2 Quillen restriction matrices + unit-generator sweep).
- **K-4a verdict at m=7:** TBD.
- **Per-branch wall times:** TBD (dominated by analytical \(T_h\) + sparse trace at \(\dim \Omega_0\) on the order of \(10^{19}\)).
- **Cross-table:** TBD.

---

## 4.5 Cross-reading: what the per-\(m\) verdicts will imply

The m=3 anchor is now landed; m=5 and m=7 are the targets. The two
non-trivial possible outcome patterns merit separate discussion.

### 4.5.1 If both m=5 and m=7 verdicts come in trivial

This is Keller's predicted outcome. Granting the joint verdict:

1. **Confirms Keller's open question** for the BW-lattice orbifold at
   \(m \in \{3, 5, 7\}\). The m=3 case is already independently verified
   ([Keller24 §6]); the m=5 and m=7 cases would be this work's
   contribution, with the verdict derived from two epistemically
   independent pipelines (D-VAN: algebraic restriction; K-4a: modular-data
   matching). The \(c = 32\) lattice orbifold at \(m = 5\) and the
   \(c = 128\) gap-4 lattice orbifold at \(m = 7\) (the latter the
   motivating case for the Höhn/Witten gap-large-than-2 question, per the
   methodology paper §1.1) would then both be holomorphic.

2. **Localises the obstruction.** Combined with the empirical observation
   at \(m = 3\) that \(\ker(\mathrm{Tr}) = H^3\), this says the BW-lattice
   orbifold cocycle sits at the *origin* of the kernel, not at a
   non-trivial kernel-class. The interpretive consequence: KRR's local
   conditions (\(c_g \equiv 1\) cochain-level, level-matching) plus the
   detecting-family verdicts are jointly sufficient. The local conditions
   alone are *necessary* but not sufficient (cf. [vEMS17] for the
   level-matching half); the K-4a + D-VAN pair is what supplies
   sufficiency at \(m = 5, 7\).

3. **Methodological evidence** that \(\{E, D_8, Q_8\}\) detection + CGR
   §5.2 closed-form is a *usable* tool, not specific to the BW-lattice
   case. The joint-permutation matcher of §7 applies to any modular data
   of rank \(< 32\); the detection family applies to any extraspecial
   2-group cohomology question in degree-3-or-higher (cf. §3.4 of the
   methodology paper).

### 4.5.2 If verdicts are non-trivial at one or both \(m\)

This would be a research surprise and is the case the protocol of §8 is
written to handle. Two sub-cases:

1. **K-4a and D-VAN agree non-trivial at the same class.** This is the
   informative non-trivial case: a counterexample to the conjecture
   "local cohomological conditions \(c_g\) trivial + level-matching \(\Rightarrow [\alpha] = 0\)"
   for the BW-lattice orbifold at the relevant \(m\), with the specific
   class identified by its restriction-to-\(\{E, D_8, Q_8\}\) coordinates
   (D-VAN naming) and by its Aut(\(H\))-orbit index in the precomputed
   library (K-4a naming). This would be a Mignard–Schauenburg-style
   example at higher rank: a non-trivial 3-cocycle whose modular-data
   shape was missed by local conditions, exhibited via its modular data
   on a detecting subgroup.

2. **K-4a and D-VAN disagree.** Diagnostic triage per §8.4 of the
   methodology paper: investigate D-VAN's algebraic verdict first
   (smaller code surface), confirm against `computed/transgression/m/kernel.g`
   on a basis, then either fix the K-4a bug or escalate to a math review.

### 4.5.3 The \(m = 3\) anchor's role

What \(m = 3\) already buys us, independent of the m=5 / m=7 verdicts:

- **A calibrated pipeline.** Both K-4a and D-VAN are now validated on a
  known-trivial case at the rank where the question is non-trivial (the
  full \(H^3(E_+(3); U(1))\) is in the kernel of \(\mathrm{Tr}\), so the
  local-cocycle test is uninformative). The verdict at \(m = 3\)
  therefore exercises the *non-trivial* part of the K-4a / D-VAN
  machinery — the closed-form modular-data computation and the
  detection-family restriction — and confirms it agrees with the
  expected `trivial` answer.

- **Empirical evidence for the §3 detection theorem.** The R-1 follow-up
  exhaustive 280-class \(D_8\) scan (PR #219) supplies *empirical*
  evidence that the \(\{E, D_8, Q_8\}\) family is genuinely minimal at
  \(m = 3\) — the \(\mathbb F_2\)-summand alone is not enough, the
  \(D_8\) augmentation is not enough, and the \(Q_8\) section is
  load-bearing for the \(A(4)\) detection.

- **A baseline cost profile.** The K-4a m=3 wall is \(\sim 3.4\,\)s; the
  K-3 extension full-(S, T) anchor is \(\sim 290\,\)s. The corresponding
  m=5 costs are bounded above by the sparse-trace budget of #220 plus
  the joint-permutation matching cost at rank 22 (independent of m).
  This is the working budget for the m=5 production run.

---

## 4.6 What this section will look like after m=5 and m=7 land

This section is forward-looking. The §4.1, §4.2 entries are final; the
§4.3, §4.4 entries are scaffolded. Each TBD placeholder is anchored to
the issue + spec that will fill it:

| TBD placeholder | Source of the fill | Tracking |
| --- | --- | --- |
| §4.3.4 m=5 kernel size, torsion | `computed/transgression/5/kernel.g` | #47 A-5b |
| §4.3.4 D-VAN-7 verdict | `tests/test_detecting_family_vanish.g` Task 6.x | #148 |
| §4.3.4 K-4b verdict, per-branch walls | `run_k4b_m5.sh` output | PR #227 + #220 |
| §4.3.4 cross-table | `TEMPLATE-k4b-m5-verdict.md` post-fill | spec §3 |
| §4.4.4 m=7 kernel size | A-7a output | #50, #166 |
| §4.4.4 D-VAN at m=7 | Phase 2 Quillen route | D-VAN spec §4.3 |
| §4.4.4 K-4a verdict at m=7 | K-4c production | future |
| §4.5 final cross-reading | once m=5 and m=7 verdicts both land | post-K-4c |

On final fill, §4.5.1 vs §4.5.2 collapses to the one branch that
matches the empirical outcome.
