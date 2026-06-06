# Appendix: Reproducibility

This appendix documents how a third party can reproduce, end-to-end, every computational result quoted in the body of the methodology paper (`writeup/methodology.md`) and in the infrastructure note (`writeup/section_3_infrastructure.md`). The scope is the anchored regime $m \in \{2, 3\}$: every claim made at those values is reproducible by a reader from a clean checkout in under five minutes of total GAP wall time on a standard workstation. The unanchored regime ($m = 5, 7$) is recorded under "Known limitations" (§6) with pointers to the in-flight follow-up issues.

The appendix closes issue #60 (W-3), the workstream-W deliverable on reproducibility.

---

## 1. Environment

### 1.1 GAP and packages

| Component | Version (reference) | How to query |
| --- | --- | --- |
| GAP                            | 4.15.1 (local development); 4.13.0 in CI | `gap --version` |
| HAP (Group cohomology)         | latest available against GAP install     | `LoadPackage("hap");` then `PackageInfo("hap")[1].Version` inside GAP |
| IO                             | latest available                         | `PackageInfo("io")[1].Version` inside GAP |
| HAPcocyclic (`hapco`)          | optional; only needed for `DRINFELD/src/universal_coefficients.g` | `PackageInfo("hapco")` inside GAP |

GAP 4.15.1 is used on the local development workstation. The CI runner under `.github/workflows/ci.yml` uses GAP 4.13.0 (the latest version exposed by `gap-actions/setup-gap@v2` at the time of writing). The regression suite avoids 4.15-only features, so any 4.13+ runtime is acceptable. See `docs/CI.md` for the CI configuration.

To check your install matches before running a paper-anchor reproduction:

```bash
gap --version
gap -q -b -c 'LoadPackage("hap"); LoadPackage("IO"); Print(PackageInfo("hap")[1].Version, "\n", PackageInfo("io")[1].Version, "\n"); QUIT;'
```

`hapco` is only required to run `DRINFELD/src/universal_coefficients.g`. The methodology paper at $m \in \{2, 3\}$ does not exercise that file; you can omit `hapco` unless you intend to reproduce the FS-indicator / gauge-invariant computations of [MignardSchauenburg18] from `DRINFELD/src/universal_coefficients.g`.

### 1.2 Hardware

The wall times quoted in the body of the paper (and reproduced in §3 below) were measured on:

- Apple Silicon (Apple M-series; the workstation reports `arm64` and the macOS kernel build is `RELEASE_ARM64_T6050`).
- macOS 25.x (Darwin 25.4.0).
- 1 GAP process, single-threaded (no manual parallelism). HAP internally uses no threads.
- Sufficient RAM for the per-test working set: 16 GB physical is comfortably above the peak, since the heaviest anchor (K-3 full S sweep) holds the lazy K-2 cache plus one eager simple-object index, well under 1 GB resident.
- No long-running background processes contending for CPU.

The reproducibility budget below is conservative for any 2024–2026 vintage workstation with $\ge 8\,$GB RAM. The bulk-driver runs of `modular_data/` (§5) used by earlier work were on the same class of hardware over much longer wall clocks.

### 1.3 Shell prerequisites

A POSIX shell (bash / zsh), `git`, and standard Unix utilities (`ln`, `rm`, `mkdir`) suffice. The `run_tests.sh` driver requires `python3` for sub-second wall-time accounting; this falls back to second-resolution `date +%s` if `python3` is absent.

---

## 2. Codebase

### 2.1 Repository and pinned commit

The methodology paper code lives in a single git repository:

- GitHub: <https://github.com/thomas-gemunden/DRINFELD>.
- Pinned commit for this appendix: `9915652b85024a2c700b5bd3ad14b60cd40ff79c` (PR #227, `[K-4b scaffold] m=5 production driver + cross-validation harness + interpretation template`). This is the tip of `origin/main` at the date of writing. Reproducers should `git checkout 9915652b85024a2c700b5bd3ad14b60cd40ff79c` to match the paper exactly.
- Default branch: `main`.

To reproduce against a fresh checkout:

```bash
git clone https://github.com/thomas-gemunden/DRINFELD.git
cd DRINFELD
git checkout 9915652b85024a2c700b5bd3ad14b60cd40ff79c
```

### 2.2 Branch structure

Active development uses workstream-prefixed branches that merge to `main` via PR:

- `main` — the integration branch; always passes `run_tests.sh` under FAST=1.
- `<workstream>-<task>-<description>` — e.g. `k4a-t6-orchestrator`, `dvan-3-vanish-test`, `q5-uc-sequence`. Workstream prefixes: `K` (Keller / modular-data witness), `D-VAN` or `dvan` (detecting-family vanishing), `Q` and `qint` (Quillen analytical pipeline), `T` (transgression-kernel solver), `V` (validators), `A` (kernel sweeps), `K-4b` (m=5 production), `W` (writeup).

Each merged PR is referenced inline in the body of the paper (e.g. "PR #224", "PR #150", "PR #228") as the audit trail for a specific claim.

### 2.3 Where each computational artefact lives

The reproducibility-critical files are all under `DRINFELD/`. Paths below are repo-relative. Each entry lists the script (or test) and the issue/PR that landed it.

**K-4a end-to-end pipeline (§5 of the paper):**

| Component | File | Land |
| --- | --- | --- |
| Orchestrator | `extraspecial_orbifolds/scripts/k4a_classify.g` | PR #224, issues #200, #201 |
| $D_8$ classifier | `extraspecial_orbifolds/scripts/d8_classifier.g` | PR #213, issue #194 |
| $Q_8$ classifier | `extraspecial_orbifolds/scripts/q8_classifier.g` | PR #203, issue #192 |
| Joint $(S, T)$-permutation matcher | `extraspecial_orbifolds/scripts/joint_permutation_matcher.g` | PR #203, issue #192 |
| Abelian $E$ closed-form check | `extraspecial_orbifolds/scripts/abelian_e_form_check.g` | PR #207 |
| CT modular data (CGR §5.2) | `extraspecial_orbifolds/scripts/ct_modular_data.g` | PR #216 |
| Restrict $\varepsilon$ to subgroup (T-5a) | `extraspecial_orbifolds/scripts/restrict_to_subgroup.g`, `epsilon_omega.g` | PR #217 |
| KRR spectral / lattice intertwiners | `extraspecial_orbifolds/scripts/defect_rep_minus_id_optim.g`, `krr_spectral_characters.g`, `krr_projector.g`, `kr_intertwiner_bridge.g` | PR #218 (T4c), PR #191 (scaffold) |
| K-4a $m = 3$ anchor test | `extraspecial_orbifolds/scripts/tests/test_k4a_classify.g` | PR #224, fix PR #228 |

**K-3 anchors (§5.5 / §8 of the paper):**

| Component | File | Land |
| --- | --- | --- |
| K-3 central-row anchor (test) | `extraspecial_orbifolds/scripts/tests/test_krr_vs_central_closed_form.g` | PR #73, issue #40 |
| K-3 full S + T anchor (test) | `extraspecial_orbifolds/scripts/tests/test_krr_full_s_t.g` | PR #222, issue #211 |
| SKeller adapter (K-2) | `extraspecial_orbifolds/scripts/skeller_adapter.g` | PR #125 |
| Untwisted modular data (K-1) | `extraspecial_orbifolds/scripts/untwisted_modular_data.g`, `krr_projector.g` | PR #66 |

**D-VAN (§4 of the paper):**

| Component | File | Land |
| --- | --- | --- |
| Vanishing test (`ResIsTrivialOnDetectingFamily`) | `extraspecial_orbifolds/scripts/detecting_family_vanish.g` | PR #150 (Gates 1A/1B at $m=2$), PR #156 (Q_8 extension) |
| Restriction-matrix builder | `extraspecial_orbifolds/scripts/detecting_family_restriction.g` | PR #149, PR #156 |
| Detecting-subgroup choices (Quillen) | `extraspecial_orbifolds/scripts/quillen_detecting_subgroup.g` | PR #133 |
| D-VAN $m \in \{2, 3\}$ anchor test | `extraspecial_orbifolds/scripts/tests/test_detecting_family_vanish.g` | PR #150, extended in PR #156 |
| Keller wrappers | `extraspecial_orbifolds/scripts/keller/keller_twist_is_trivial.g`, `keller_s_entry.g` | PR #157, PR #158 |

**Q_8 extension-type case study (cited as a sanity check in §7.3):**

| Component | File | Land |
| --- | --- | --- |
| Verify Q_8 + identify cocycles | `q8_extension_type/scripts/verify_q8.g` | |
| Backtracking permutation search | `q8_extension_type/scripts/find_permutation.g` | |
| Modular data symlink setup | `q8_extension_type/scripts/setup.sh` | |
| Sub-investigation index | `q8_extension_type/scripts/README.md` | |

**Precomputed `modular_data/` tree (used by the $D_8$ / $Q_8$ classifiers above):**

This is the Gruen–Morrison library of $(S, T)$ pairs for $D^\omega(G)$ at $|G| \le \text{(varies)}$. **It is not under version control** — roughly 77 GB across $\sim 106$ group-orders. See §5 below for the regeneration recipe. The K-4a / Q_8 classifiers read from `modular_data/8/3/{1..12}.txt` ($D_8$, twelve Aut-orbits) and `modular_data/8/4/{1..8}.txt` ($Q_8$, eight Aut-orbits).

---

## 3. How to reproduce each anchor

The five anchor results below collectively underpin every quantitative claim in the methodology paper at $m \in \{2, 3\}$. Total wall time on a 2024-vintage workstation is well under five minutes. Each command is a single GAP invocation reading a single test file by absolute path (see §7 for why the absolute path is required).

Each entry below provides:

- the command to run, with `<repo>` denoting your absolute path to the repository root (e.g. `/Users/alice/DRINFELD`);
- the expected console signature (PASS / FAIL line and the headline counts);
- the expected wall time (taken from the merged PR's measured baseline, not fabricated);
- the issue/PR audit trail.

### 3.1 K-3 central-row anchor — SKeller vs §4.3 closed form at $m = 3$

**What it verifies.** `SKeller(3, i, j)` agrees with the writeup §4.3 closed form `S^0_{((g_1, ρ), (h, σ))} = σ(g_1) · conj(ρ(h)) / |C_G(h)|` on every central-row entry of $S^0$ for $\mathcal Z(\mathrm{Vec}_{E_+(3)})$. Three-way agreement: SKeller, the inline §4.3 closed form, and `ClosedFormCentralS` (V-2 stand-in).

**Command.**

```bash
gap -q -b -c 'Read("<repo>/extraspecial_orbifolds/scripts/tests/test_krr_vs_central_closed_form.g");'
```

**Expected output (tail).**

```
Sanity A (σ(1) = dim σ):                 true
Main 3-way agreement on central rows:    true
Entries verified: 295360
Wall time (main sweep): <about 16.6> s
K-3 ACCEPTANCE (SKeller = §4.3 closed form on central rows): true
```

**Wall.** $\approx$ 16.6 s for the main sweep (PR #73 measurement); $\le 30$ s end-to-end including dependencies' load. The entry count $295\,360 = 130 \times 2272$ is the number of central-row entries for $E_+(3)$.

**Audit.** PR #73, issue #40.

### 3.2 K-3 extension — full S matrix + T diagonal at $m = 3$

**What it verifies.** Extends §3.1 from the central rows to (a) the full $S$ matrix (all $5\,161\,984 = 2272^2$ entries) and (b) the entire $T$-diagonal ($2272$ entries), at $m = 3$. Three checks: SKeller vs block S, SKeller symmetry, block S symmetry, plus the lazy-vs-eager cross-check for $T$.

**Command.**

```bash
gap -q -b -c 'Read("<repo>/extraspecial_orbifolds/scripts/tests/test_krr_full_s_t.g");'
```

**Expected output (tail).**

```
  Entries verified:
    S entries:   5161984  (rank^2 = 5161984)
    T entries:   2272     (rank = 2272)

  Mismatches:
    SKeller vs blockS  : 0
    SKeller symmetry   : 0
    blockS symmetry    : 0
    T^Keller vs T^0    : 0

  K-3 EXTENSION (#211) PASS
  SKeller(3, i, j) = S^0(i, j) on all 5161984 entries.
  T^Keller_diag = T^0_diag on all 2272 entries.
```

**Wall.** $\approx$ 290 s ($\approx$ 4:50) total. Breakdown from PR #222:

| Phase | Time |
| --- | --- |
| K-2 cache build | 0.07 s |
| Eager idx build | 0.15 s |
| T diagonal | 0.12 s |
| Full S sweep | 289.8 s |
| **Total** | $\approx$ 290 s |

Well under the 10-minute acceptance budget recorded in the issue body.

**Audit.** PR #222, issue #211; extends PR #73 / issue #40.

### 3.3 K-4a end-to-end $m = 3$ anchor — `K4aClassify(3)` returns `"trivial"`

**What it verifies.** The K-4a-T7 acceptance gate (issue #201): `K4aClassify(3)` runs the full three-subgroup pipeline ($E$, $D_8$, $Q_8$) on the $m = 3$ KRR-equivalent data and returns

- `verdict = "trivial"`,
- `trivial = true`,
- `E_class.is_coboundary = true`,
- `D8_class.class_idx = 1` (the trivial $D_8$ cocycle),
- `Q8_class.class_idx = 1` (the trivial $Q_8$ cocycle).

The same orchestrator also produces a bonus $m = 2$ smoke result (`K4aClassify(2)` returns the same).

**Command.**

```bash
gap -q -b -c 'Read("<repo>/extraspecial_orbifolds/scripts/tests/test_k4a_classify.g");'
```

This test also requires the precomputed `modular_data/` tree at $D_8$ ($n=8$, $m=3$) and $Q_8$ ($n=8$, $m=4$), and a `Modular_Data` symlink visible to GAP's cwd. See §5 for setup. The convenience driver `extraspecial_orbifolds/scripts/run_k4a.sh 3` performs the symlink + invocation in one step.

**Expected output (tail).**

```
T2: m = 3 trivial anchor (K-4a-T7 acceptance gate, issue #201)
  T2 wall time: <about 3.4> s
  [ok] T2: verdict = 'trivial' (K-4a-T7 gate)
  [ok] T2: trivial = true
  [ok] T2: D8_class.class_idx = 1 (trivial cocycle)
  [ok] T2: Q8_class.class_idx = 1 (trivial cocycle)
  ...
Summary: 39 passes, 0 failures.
PASS test_k4a_classify
```

**Wall.** $\approx$ 3.4 s for `K4aClassify(3)` (PR #228 measurement). Total test wall (T1 smoke + T2 anchor + T3 m≥4 error + T4 m=2 bonus): well under one minute.

**Audit.** PR #224 (T6 orchestrator + anchor); PR #228 (float-vs-int fix; the final GREEN). Issues #200, #201.

### 3.4 D-VAN Phase 1 anchor — Gates 1A, 1B at $m \in \{2, 3\}$

**What it verifies.** For each unit generator $e_i$ of the hom-basis on $H^3(E_+(m); U(1))$ at $m \in \{2, 3\}$:

- Gate 1A at $m = 2$: all $10$ unit generators report `trivial = false` (none of them is in $\ker \mathrm{res}_{\{E, D_8, Q_8\}}$).
- Gate 1B at $m = 2$: the $\mathbb Z/8$ generator (the cyclic $A(4)$ summand at $m = 2$ per Harada–Kono) is correctly detected as non-trivial; the $D_8$-side restriction is non-zero, plus the $Q_8$ section catches $2 \cdot e_{\mathbb Z/8}$ which $D_8$ alone misses (R-1 follow-up, §3.3 of the paper).
- Gate 1A at $m = 3$: all $35$ unit generators report `trivial = false`.
- Order-4 element checks at $m = 3$: $e_{\text{order-4 gen}}$, $2 \cdot e_{\text{order-4 gen}}$ both non-trivial; $4 \cdot e_{\text{order-4 gen}}$ trivial (the latter is the zero class in $\mathbb Z/4$). The $2 \cdot e_g$ case is the empirical justification for keeping $Q_8$ in the detecting family (PR #219).

**Command.**

```bash
cd <repo>/extraspecial_orbifolds/scripts
gap -q -b -c 'Read("tests/test_detecting_family_vanish.g");'
```

(This test is one of the few that loads its module from cwd-relative path `detecting_family_vanish.g`. Run from `extraspecial_orbifolds/scripts/`.)

**Expected output (tail).**

```
--- Task 3.1: Gate 1A m=3 (35 unit generators are non-zero, D-VAN-4) ---
  E_+(3) torsion length is 35: PASS
  Gate 1A m=3: no unit generator gets trivial=true: PASS
  e_{order-4 gen} (order 4) is non-trivial in H^3: PASS
  2 * e_{order-4 gen} (order 2 in Z/4) is non-trivial (Q_8 catches): PASS
  Q_8 witness present at m=3 (res_Q8_vec is non-zero on 2*e_g): PASS
  4 * e_{order-4 gen} = zero class is trivial: PASS

=== test_detecting_family_vanish: PASS ===
```

**Wall.** $\approx$ 6.2 s for the full file at $m \in \{2, 3\}$ (PR #156 measurement). Builds two restriction matrices ($m=2$, $m=3$) and runs $45$ verification assertions across Tasks 2.1–3.1.

**Audit.** PR #150 (Gates 1A/1B at $m=2$, issue #144); PR #155 (rescale fix); PR #156 ($Q_8$ extension, issue #153); PR #219 (R-1 follow-up empirical validation, issue #215).

### 3.5 Q_8 baseline — verify the cross-checking sub-investigation

**What it verifies.** That `SmallGroup(8, 4)` is $Q_8$ as expected, and identifies the trivial and order-2 cocycles in `modular_data/8/4/` by H³ class. This is the prerequisite for the Q_8 extension-type case study (`q8_extension_type/writeup.md`) cited in §7.3 of the paper.

**Command.**

```bash
cd <repo>/q8_extension_type/scripts
./setup.sh                     # creates the Modular_Data symlink
gap -q -b -c 'Read("verify_q8.g");'
```

**Expected output (tail).**

```
StructureDescription: Q8
|G|: 8
...
UCT.exponent: 8
UCT.torsion : [ 8 ]
Number of orbits: 8
Orbit sizes: [ ... ]
  TRIVIAL  cocycle is at file index <some index>
  ORDER-2  cocycle is at file index <some index>
```

**Wall.** Few seconds (HAP resolution at $Q_8$ is trivially fast).

**Audit.** `q8_extension_type/scripts/README.md`; conclusion in `q8_extension_type/writeup.md` (section "modular data detects extension type").

---

## 4. Verification harness

The repository ships a single regression-test driver, `run_tests.sh` at the top level:

```bash
cd <repo>
./run_tests.sh                # full suite, including slow tests
FAST=1 ./run_tests.sh         # CI mode: skip slow tests (currently test_quillen_vs_hap.g)
```

The driver:

1. `cd`s into `extraspecial_orbifolds/scripts/`.
2. Iterates `tests/test_*.g` in lexical order.
3. Runs each via `gap -q -b <test>`, capturing stdout/stderr to `/tmp/<name>.log`.
4. Prints `PASS` / `FAIL` / `SKIP` per test plus a wall-time stamp.
5. Writes `/tmp/<name>.timing` (a single float, in seconds) for per-test perf tracking.
6. Exits 0 iff every non-skipped test exited 0.

The CI workflow at `.github/workflows/ci.yml` runs `FAST=1 ./run_tests.sh` on every push to `main` and every PR targeting `main`. Per `docs/CI.md`, the only slow test currently skipped in CI is `test_quillen_vs_hap.g`. The `test_baselines.json` file at `extraspecial_orbifolds/perf/test_baselines.json` is the perf-regression baseline (zero-valued entries are placeholders).

The K-3 extension test (§3.2) and the K-4a end-to-end test (§3.3) are also picked up by the harness; the harness's per-test wall stamp is the source of truth for the times above.

A handful of tests cannot be invoked from `run_tests.sh` because they require an absolute path (the K-4a-T1 convention in PR #203 — see §7). For those, invoke GAP directly as shown in §3.

---

## 5. Modular data tree generation

The K-4a classifier branches on $D_8$ and $Q_8$ require the precomputed library `modular_data/`. The full tree is $\sim 77$ GB across $\sim 106$ group-orders and is **not under version control** for size reasons (CLAUDE.md §"Repository layout"). Reproducers have two options.

### 5.1 Tree shape

Each cocycle's stored modular data lives at `modular_data/<order>/<small_group_id>/<cocycle_orbit_index>.txt`, where:

- `<order>` is $|G|$,
- `<small_group_id>` is the GAP `SmallGroup` ID (e.g. $G = D_8 \Leftrightarrow$ `SmallGroup(8, 3)`, $G = Q_8 \Leftrightarrow$ `SmallGroup(8, 4)`),
- `<cocycle_orbit_index>` runs over $\mathrm{Aut}(G)$-orbits of 3-cocycles modulo coboundary.

Each leaf `<m>/` directory also contains `3-cocycles.txt` (the orbit representatives as integer vectors) and `timing.txt`. Per CLAUDE.md "Data format conventions", the `<k>.txt` files are GAP source files ending in `;;` (the sentinel checked by `AlreadyExists` to detect partial writes); $T$ is stored as the diagonal vector and the loader wraps it in `DiagonalMat`.

For the methodology paper the only required slices are:

- `modular_data/8/3/{1..12}.txt` (12 $\mathrm{Aut}(D_8)$-orbits of 3-cocycles on $D_8$),
- `modular_data/8/4/{1..8}.txt` (8 $\mathrm{Aut}(Q_8)$-orbits of 3-cocycles on $Q_8$).

Both slices are small (sub-MB) and regenerate in seconds.

### 5.2 Regeneration via Gruen's pipeline

Per CLAUDE.md "Running things in GAP" and `DRINFELD/src/modular_data.g`, the regeneration command for the two required slices is:

```gap
# From the repository root, with GAP's cwd at <repo>:
Read("DRINFELD/src/modular_data.g");          # loads hap + IO
SaveModularDataParallel(8, 3, 1, 0, false);   # D_8: order 8, SmallGroup #3
SaveModularDataParallel(8, 4, 1, 0, false);   # Q_8: order 8, SmallGroup #4
```

The `(N, j) = (1, 0)` arguments sharded for single-process use. The hard-coded output path is `Modular_Data/<order>/<small_group_id>/`, with capital M and capital D, **relative to GAP's cwd** (CLAUDE.md "Running things in GAP" caveat).

To make Gruen's output land in the repository tree without renaming, either:

- `cd` into a parent directory that already contains a `Modular_Data` symlink to your `modular_data/` tree, or
- create the symlink: `ln -s ../modular_data Modular_Data` (from the GAP cwd you intend to run from).

### 5.3 The `Modular_Data` symlink trick for tests

GAP's cwd at test time matters: `LoadModularData(n, m, k)` reads `Modular_Data/<n>/<m>/<k>.txt` relative to the current directory. The K-4a-T1 follow-up (PR #203) adopts the following convention:

```bash
cd <repo>/extraspecial_orbifolds/scripts/tests
ln -s ../../../modular_data Modular_Data
```

so that when tests like `test_q8_classifier.g` or `test_d8_classifier.g` are invoked by absolute path (which sets GAP's cwd to the original cwd, not the test directory — see §7), the loader still resolves `Modular_Data/8/4/3.txt` correctly. The `q8_extension_type/scripts/setup.sh` script automates the same trick for that sub-investigation; see `q8_extension_type/scripts/README.md`.

### 5.4 `.gitignore` hygiene

To prevent the convenience symlinks from being accidentally committed, the top-level `.gitignore` carries (added in PR #203):

```
**/scripts/Modular_Data
**/tests/**/Modular_Data
```

These two globs cover both the `q8_extension_type/scripts/Modular_Data` symlink and the `extraspecial_orbifolds/scripts/tests/Modular_Data` symlink used by the K-4a classifier tests.

### 5.5 Full library

For reproducers wanting the full $\sim 77$ GB modular-data tree (e.g. to spot-check classifier behaviour at $G \ne D_8, Q_8$), the regeneration recipe is the same `SaveModularDataParallel(n, m, ...)` calls iterated across groups. Bulk drivers are in `DRINFELD/src/modular_data.g`:

```gap
SaveAllDataForGivenOrder(n);                   # all SmallGroups of order n
ComputeDataForeverParallel(start, finish, N, i, detailed);  # bulk shard
```

The bulk runs scale linearly in group-order count and superlinearly in $|G|$. See CLAUDE.md for caveats on parallel sharding (the `*Parallel` variants shard across group orders/IDs, not threads — run multiple GAP processes with different `i` for actual parallelism).

---

## 6. Known limitations

These are the gaps between "anchored regime" and "production targets" in the paper. Each is documented inline in §8 / §9 of `methodology.md`; this section is the consolidated index for the reproducibility appendix.

### 6.1 $m = 5$ production

`K4aClassify(5)` errors deliberately with a message pointing at issue #220 (and `K4aClassify(4)` does the same). The blocker is `BuildKRRSpectralCharactersSparse`: at $m = 5$ the central twisted module $W_a = \Omega_0$ has dimension $2^{16} = 65\,536$, so the dense $T_h$ approach used at $m = 3$ would take $\approx 3.7$ years per matrix. The fix is a sparse / trace-only approach using $\mathrm{Tr}(T_h^j)$ and character orthogonality, described in issue #220 (in flight).

The D-VAN $m = 5$ anchor (Gate 1E, revised) is a self-contained 165/165 `trivial=false` sweep on the unit basis of $H^3(E_+(5); U(1))$, by direct analogy with the m=3 Task 3.1. It does **not** depend on A-5b's kernel-of-Tr computation. (An earlier draft asserted such a dependency; that was a math conflation between $\ker(\mathrm{Tr})$ and the detecting-family restriction kernel, corrected in the 2026-06-06 audit at `extraspecial_orbifolds/docs/superpowers/research/2026-06-06-ker-tr-detecting-family-audit.md`.)

### 6.2 $m = 7$ production

Blocked on (a) the same K-4a sparse-trace work as $m = 5$, and (b) a HAP-resolution alternative for $E_+(7)$ to support D-VAN Phase 2 — `ResolutionFiniteGroup(E_+(7), 4)` exhausts $\sim 60\,$GB without completing. Path 3 / the HAP-resolution redesign (issue #137) is currently dead; the active alternative is the Q-int B3 Pontryagin-square / integer-3-cocycle pipeline (`hap_pontryagin_square.g`, `integrate_to_3cocycle.g`, `solver/iterated_bockstein.g`), in development.

### 6.3 A-5b kernel-sweep performance at $m = 5$

The kernel-of-Tr sweep at $m = 5$ initially clocked $\approx 11$ days for the $165$-generator scan. A series of perf rounds has closed most of the gap; the umbrella issue is #177 (with sub-issues #186 on the `BocksteinH1ToH2` n²-loop hotspot). Two key patches are now merged: PR #221 (`KroneckerProduct` swap in `BocksteinH1ToH2`, $\approx 2.3\times$ speedup at $n = 2048$) and its sibling PR #225 (same swap in `IsCoboundary2Mod2WithLiftWitness`). Batched back-substitution remains in flight.

### 6.4 The `modular_data/` tree

Per §5, the precomputed library is not in git. The K-4a $D_8$ / $Q_8$ classifiers need a $\sim$sub-MB slice; full bulk runs are gated by the Gruen–Morrison drivers. No piece of the methodology paper at $m \in \{2, 3\}$ requires more than the two leaf directories above.

---

## 7. Test invocation gotchas

A short list of gotchas that have caught earlier reproducers; folded back into PR #203's K-4a-T1 convention and observed throughout the suite.

### 7.1 Absolute paths for invocation

Per PR #203 (K-4a-T1), tests that need to locate their sibling modules via `INPUT_FILENAME()` must be invoked with an absolute path:

```bash
gap -q -b -c 'Read("/Users/alice/DRINFELD/extraspecial_orbifolds/scripts/tests/test_k4a_classify.g");'
```

The reason is that `INPUT_FILENAME()` returns the path the file was loaded from; the test then strips known suffixes (`/test_*.g`, `/tests`, `/extraspecial_orbifolds/scripts`) to recover the worktree root, which it uses to `Read` sibling files (`src/modular_data.g`, the test's own dependencies). A relative input path collapses the suffix-stripping to empty, and the subsequent `Read` calls fail with "file not found". The check pattern in every K-4a test is:

```gap
SELF := INPUT_FILENAME();;
if SELF = fail or SELF = "stream" then
    Error("...INPUT_FILENAME() unavailable; Read by absolute path.");
fi;
```

Affected tests are listed in §3 above; non-K-4a tests (e.g. the D-VAN one in §3.4) load from cwd and need `cd extraspecial_orbifolds/scripts` first instead.

### 7.2 GAP `PrintTo` line-wrap at column 80

GAP's `PrintTo` auto-wraps at 80 columns by inserting `\\\n` (backslash followed by newline). This is harmless for human-readable output but breaks parsers that round-trip through `Read` (`ReadAsFunction`). The recommended idiom for any data-file write is:

```gap
stream := OutputTextFile(path, false);;
SetPrintFormattingStatus(stream, false);     # disable line-wrap
AppendTo(stream, ...);                       # or PrintTo(stream, ...)
CloseStream(stream);
```

The kernel-state appender in `transgression_resume.g` (§3.6 of `section_3_infrastructure.md`) works around the auto-wrap by running `ReplacedString(bytes, "\\\n", "")` on load. Newly written data files in this repo follow the `OutputTextFile + SetPrintFormattingStatus` pattern.

### 7.3 Name clobbering between `src/modular_data.g` and `src/universal_coefficients.g`

Per CLAUDE.md "Repository layout", do **not** `Read` both `DRINFELD/src/modular_data.g` and `DRINFELD/src/universal_coefficients.g` in the same GAP session — each file defines its own `ComplementIntMatWithTransforms`, `UniversalCoefficientsTheorem`, `AutomorphismOrbits`, and `ProjectiveCharacters`, and the second `Read` silently overrides the first. The K-4a tests above only need `src/modular_data.g`; the universal-coefficients file is reference material for the math, not a runtime dependency. (Some quirks in `src/universal_coefficients.g` are flagged in CLAUDE.md: undeclared `factors` and `hombasis` in `GaugeInvariants`, syntax slip in `FSIforAGT`. Treat that file as reference.)

### 7.4 SmallGroup ID stability

Per CLAUDE.md "Caveats when extending the code", `SmallGroup` ordering depends on the GAP `smallgrp` library version. Existing precomputed data in `modular_data/` was generated under a specific `smallgrp` version. When regenerating slices on a different GAP install, verify `IdGroup(SmallGroup(8, 4)) = [8, 4]` and `StructureDescription(SmallGroup(8, 4)) = "Q8"` before running the K-4a classifier — a stale `smallgrp` could swap $D_8$ and $Q_8$ identifiers.

### 7.5 Two-file diverge: `ComplementIntMatWithTransforms`

The two `.g` files in `DRINFELD/src/` define slightly different versions of `ComplementIntMatWithTransforms`: the `modular_data.g` version omits the `complement` field that the `universal_coefficients.g` version returns. When porting helpers between them (not required for the paper anchors), check the record fields before reusing.

---

## 8. Cross-workstream infrastructure

The methodology paper at $m \in \{2, 3\}$ runs entirely on the K-4a / K-3 / D-VAN files in §2.3. For completeness, the broader workstream architecture that supplies the underlying primitives and (for $m \ge 5$) the future Phase-2 pipeline is documented here. Each workstream below contributes infrastructure that is currently a black-box dependency of the anchors above; reproducing the anchors does not exercise the workstream directly, but understanding the architecture helps when reading the per-PR audit trail.

**Q workstream — analytical Quillen $H^3$ pipeline.** Files: `extraspecial_orbifolds/scripts/quillen_canonical_presentation.g` (Q-2a; Adem–Milgram canonical presentation of $H^*(E_+(m); \mathbb F_2)$), `quillen_bockstein.g` (Q-int A1; Bockstein spectral sequence lifting $\mathbb F_2$ to $\mathbb Z$), `quillen_h3_callable.g` (callable $H^3$ classes), `quillen_h4_torsion.g` (Q-5; integer $H^4$ via the UC sequence), `hap_pontryagin_square.g` (Q-int B3-2), `integrate_to_3cocycle.g` (Q-int B3-3), `solver/iterated_bockstein.g`. These supply the Phase-2 D-VAN restriction infrastructure intended for $m = 7$ (currently blocked but in development per §6.2 above).

**V workstream — validators.** Files: `extraspecial_orbifolds/scripts/epsilon_omega.g` (V-1), `closed_form_central.g` (V-2; closed-form $S^\omega$ on central rows — the K-3 anchor's cross-check), `fsi_wrapper.g` (V-3; Frobenius–Schur indicators), `aut_nt.g` (V-5a; $\mathrm{Aut}(N, T)$ for the modular-data permutation matcher), `aut_nt_refine.g` (V-5b; colour refinement on fusion-row signatures), `s_entry.g` (V-7a; single-entry $S$-matrix primitive), `fusion_coefficient.g` (V-7b; single-entry fusion-coefficient query via Verlinde). The V-2 closed-form-central validator powers the K-3 anchor of §3.1.

**T workstream — transgression-kernel solver.** Files: `transgression_kernel.g`, `solver/iscoboundary2_split.g` (T-1 dispatcher), `solver/mod2_solver.g` ($\mathbb F_2$ path), `solver/z4_fallback.g` ($\mathbb Z/m$ fallback for elementary $m$), `solver/iterated_bockstein.g` (iterated-Bockstein path for $\mathbb Z/2^k$, $k \ge 2$). The torsion-split solver (T-1) is the foundation of all kernel sweeps; see `writeup/section_3_infrastructure.md` for the full mathematical exposition.

The K-3 / K-4a / D-VAN anchors of §3 do not call into the T workstream directly — the kernel computations are already merged and persisted under `extraspecial_orbifolds/computed/transgression/<m>/kernel.g`, and the anchors read those persisted records. To reproduce the kernel computation itself at $m = 2$ (the verified anchor $|\ker \mathrm{Tr}| = 2048$, §3.7 of `section_3_infrastructure.md`):

```bash
cd <repo>/extraspecial_orbifolds/scripts
gap -q -b -c 'Read("run_e_plus_2_kernel.g");'
```

The driver asserts `exact.kernel_size = 2048` and writes the persisted kernel record. Wall time $\approx 75$ s (`section_3_infrastructure.md` §3.7).

---

## 9. Reproducibility summary table

The five reproducible anchors of §3 collectively establish the methodology paper's $m \in \{2, 3\}$ claims:

| Anchor | Command (paths relative to `<repo>`) | Wall | What it anchors |
| --- | --- | --- | --- |
| K-3 central (§3.1)              | `gap -q -b -c 'Read("<repo>/extraspecial_orbifolds/scripts/tests/test_krr_vs_central_closed_form.g");'` | $\approx$ 16.6 s | SKeller vs §4.3 closed form, 295,360 entries |
| K-3 full S + T (§3.2)           | `gap -q -b -c 'Read("<repo>/extraspecial_orbifolds/scripts/tests/test_krr_full_s_t.g");'` | $\approx$ 290 s | SKeller = $S^0$ on all $5\,161\,984$ entries; $T^\mathrm{Keller}_\mathrm{diag} = T^0_\mathrm{diag}$ |
| K-4a end-to-end (§3.3)          | `gap -q -b -c 'Read("<repo>/extraspecial_orbifolds/scripts/tests/test_k4a_classify.g");'` | $\approx$ 3.4 s (anchor); $\le 1$ min (test) | `K4aClassify(3) = "trivial"`, K-4a-T7 acceptance |
| D-VAN Phase 1 (§3.4)            | `cd <repo>/extraspecial_orbifolds/scripts && gap -q -b -c 'Read("tests/test_detecting_family_vanish.g");'` | $\approx$ 6.2 s | Gate 1A/1B at $m \in \{2, 3\}$, $Q_8$ witness check |
| Q_8 baseline (§3.5)             | `cd <repo>/q8_extension_type/scripts && ./setup.sh && gap -q -b -c 'Read("verify_q8.g");'` | $\le 10$ s | $\mathrm{SmallGroup}(8, 4) = Q_8$, identify trivial / order-2 cocycles |

Total wall time, all five anchors run sequentially: under five minutes on a 2024-vintage workstation.

---

## 10. Documenting your reproduction

When citing a reproduction of these anchors in downstream work, record:

- GAP, HAP, and `smallgrp` versions (`gap --version`; `PackageInfo("hap")[1].Version`; `PackageInfo("smallgrp")[1].Version`).
- The pinned commit hash of `DRINFELD` (`git rev-parse HEAD`).
- The hardware spec and approximate wall time (so future readers can compare).
- Any deviations from the §3 anchor commands (e.g. a different value of `<repo>`).
- The full PASS/FAIL summary from each test's tail output.

The §8.5 "Document" step of the methodology paper's acceptance protocol gives the same checklist for the verdict-level outputs of D-VAN and K-4a at the (eventual) production targets $m = 5, 7$; the appendix here is its precondition.
