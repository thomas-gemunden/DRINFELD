# Scaling Mod(D¹(E₊(m))) computation to m = 3, 5, 7

## Problem statement

Compute the modular data $(S, T)$ of the untwisted Drinfeld center
$\mathrm{Mod}(D^1(E_+(m)))$ for $m = 3, 5, 7$, in support of the
Keller-Roberts-Roberts conjecture (arXiv:2411.13646) that the orbifold
of the Barnes-Wall lattice VOA in dim $2^m$ by $E_+(m)$ has trivial
't Hooft anomaly $\omega \in H^3(E_+(m); U(1))$ — i.e. produces
exactly this category up to permutation. Their pipeline does not
produce $(S, T)$ directly; we want to provide the comparison target.

## Cost model

| $m$ | $\lvert G\rvert$ | rank | $\lvert C\rvert$ typical | per-S-row work | per-S-entry work |
|---|---:|---:|---:|---:|---:|
| 3 | 128 | 2 272 | 128 / 64 | $\le$ 2272 · 4 ops | $\le$ 4 ops |
| 5 | 2 048 | 527 872 | 2048 / 1024 | $\le$ 527 872 · 4 ops | $\le$ 4 ops |
| 7 | 32 768 | 134 275 072 | 32768 / 16384 | $\le$ 1.34$\cdot$10$^8$ · 4 ops | $\le$ 4 ops |

The "$\le$ 4 ops" estimate uses the fact that for non-central
$g, h \in E_+(m)$ both conjugacy classes have size 2, so the
commuting-pair sum $\sum_{(g',h') \in [g]\times[h]: g'h' = h'g'}\dots$
has at most 4 terms (and is 0 about half the time).

Storage:

| $m$ | $T$ size | one $S$-row | full $S$ (dense) | full $S$ (sparse, ~50% non-zero) |
|---|---:|---:|---:|---:|
| 3 | 36 KB | 36 KB | $\sim$80 MB | $\sim$40 MB |
| 5 | 8 MB | 8 MB | $\sim$5 TB | $\sim$2.5 TB |
| 7 | 2 GB | 2 GB | $\sim$3 · 10$^{17}$ B | $\sim$1.5 · 10$^{17}$ B |

So:
- $m = 3$: full $(S, T)$ trivial.
- $m = 5$: $T$ trivial; full $S$ borderline-feasible if chunked
  to disk; selected rows are easy.
- $m = 7$: $T$ feasible (a couple of GB); full $S$ impossible
  even on disk; selected rows or analytic blocks only.

## Underlying formulas

### T (closed form, valid for any $m$)

For the simple object $(g, \rho)$ with $g$ a conjugacy class
representative and $\rho \in \mathrm{Irr}(C_G(g))$:
$$T_{(g,\rho)} \;=\; \frac{\rho(g)}{\dim \rho}.$$
Since $g \in Z(C_G(g))$, by Schur's lemma $\rho(g)$ is a scalar
multiple of $\dim \rho$; the ratio is a root of unity.

### S (general formula)

Bantay-style:
$$S_{(g,\rho),(h,\sigma)}
\;=\; \frac{1}{|G|}
\sum_{\substack{(g',h') \in [g]\times[h] \\ g'h' = h'g'}}
\overline{\rho\bigl(\tau_g(g')\,h'\,\tau_g(g')^{-1}\bigr)}\,
\overline{\sigma\bigl(\tau_h(h')\,g'\,\tau_h(h')^{-1}\bigr)}$$
where $\tau_g(g')$ is any choice of $x \in G$ with $xgx^{-1} = g'$
(and similarly $\tau_h(h')$).

For $E_+(m)$, $|[g]| \le 2$ for all $g$, so the outer sum has $\le 4$
terms. Each term is a character-table lookup. So per-entry work is
trivial; the cost is in the SHEER NUMBER of entries.

### Closed forms for central rows

Specialise to $g = 1$. Then $[g] = \{1\}$, $C(g) = G$, $\rho \in \mathrm{Irr}(G)$,
and $\tau_g$ can be taken as identity. The sum collapses:
$$\boxed{\;S_{((1,\rho),(h,\sigma))}
\;=\; \frac{\dim \sigma}{|C_G(h)|}\,\overline{\rho(h)}\;}$$
which is **O(1)** per entry, looking up the character table of $G$ once.

The same calculation for $g = -1$ (also central) gives
$$\boxed{\;S_{((-1,\rho),(h,\sigma))}
\;=\; \frac{\sigma(-1)}{|C_G(h)|}\,\overline{\rho(h)}\;}$$
where $\sigma(-1) = \pm \dim \sigma$ since $-1$ is central in
$C_G(h)$ and so acts as a scalar on $\sigma$.

Together these give analytical closed forms for $2(4^m + 1)$ rows of $S$
(and by $S = S^T$, the same number of columns). For $m = 7$ that is
$32\,770$ rows out of $1.34 \cdot 10^8$ — about 0.024 %, but covers
every "physically meaningful" row (the central-sector quantum dimensions
and S-row interpretations).

### Block structure and sparsity

$S$ has a natural block decomposition by pair of conjugacy classes
$([g_1], [g_2])$. For $E_+(m)$ there are only **three types** of
class:

1. **Central** ($\{1\}$ or $\{-1\}$): centraliser $E_+(m)$,
   $|\mathrm{Irr}| = 4^m + 1$.
2. **Non-central order 2** (image of $\sigma_2$ flavour): centraliser
   $\mathbb Z_2 \times E_+(m-1)$, $|\mathrm{Irr}| = 2 \cdot 4^{m-1} + 2$.
3. **Non-central order 4** (image of $\sigma_1\sigma_2$ flavour):
   centraliser $\mathbb Z_4 \circ E_+(m-1)$,
   $|\mathrm{Irr}| = 2 \cdot 4^{m-1} + 2$.

For two non-central classes $[g], [h]$ with images
$\bar g, \bar h \in E_+(m)/Z = (\mathbb F_2)^{2m}$:
$$\text{commuting pair exists} \;\iff\; \omega(\bar g, \bar h) = 0$$
where $\omega$ is the standard symplectic form on $(\mathbb F_2)^{2m}$.
About half of the non-central × non-central blocks are therefore
**identically zero** by orthogonality. This is real sparsity, not
floating-point noise.

For $m = 7$ that halves the non-zero block count from
$\sim$ 16 000² to $\sim$ 1.3 · 10⁸. Still huge, but useful.

## Output / storage format

Each chunk is a self-contained GAP source file that returns a record.
Format conventions:

```gap
# T-chunk (per-sector):
return rec(
  group   := [128, 2326],          # SmallGroup id
  cocycle := "trivial",
  sector  := <conjugacy class index in ConjugacyClasses(G)>,
  rep     := <class representative as a GAP element>,
  centraliser_order := <int>,
  T_values := [<root of unity>, ...],   # one entry per Irr(C_g)
  irrep_dims := [<int>, ...],
  schema_version := 1
);
```

```gap
# S-chunk (per-row, for row index i):
return rec(
  group   := [128, 2326],
  cocycle := "trivial",
  row_index := <int>,                   # global simple index
  source := rec(g_class := <int>, irrep_index := <int>),
  entries := [[<col_index>, <value>], ...],   # SPARSE: only non-zero
  schema_version := 1
);
```

Disk layout under `extraspecial_orbifolds/computed/E_plus_<m>/`:
```
T/sector_<class_index>.g
S/row_<row_index>.g
manifest.g                # which rows/sectors are done; signature of inputs
```

### Resume protocol

A driver script computes `(g, ρ)` indices on the fly, checks
`S/row_<i>.g` existence, skips if present.

A `manifest.g` records:
- the GAP version used,
- the SmallGroup id and structure description,
- the conjugacy-class numbering convention (sometimes GAP gives different
  orderings under different versions),
- a hash of the irrep-dimension vector (cheap fingerprint).

A new run aborts if the manifest disagrees, to prevent silent inconsistency.

## Parallelism

Three levels:

1. **Sector-level for T**: spawn $N$ GAP processes, each handling
   a disjoint range of conjugacy classes. Since the per-sector
   work is trivial, $N$ can be small (= number of CPUs). Trivially
   embarrassingly parallel; no shared state.

2. **Row-level for S**: spawn $N$ GAP processes, each handling a
   disjoint range of `row_index`. Each process knows the full G,
   conjugacy classes, character tables, then enumerates only its
   row range. Each process writes its own `row_<i>.g` files. No
   coordination needed beyond initial char-table replication.

3. **Block-level**: for very-non-uniform work patterns (rare here,
   since per-entry work is uniform), schedule blocks of the
   $S$ matrix as work units to a worker pool.

For $m = 7$ specifically, on this machine (8-core M-series), 8
parallel GAP processes can chew through one $S$-row in maybe an
hour, so $\sim 200$ rows per day. That's enough to cover the
analytic (1, ·) and (-1, ·) rows in a reasonable time, plus a few
selected non-central rows of physical interest.

## Verification strategy at each phase

| Phase | Checks |
|---|---|
| Direct D(G) library | Compute $T$ for $E_+(2)$ and check against `modular_data/32/49/1.txt`. Compute $S$ for $E_+(2)$ and check against the precomputed S in the same file. Both rank and per-sector T-multiset should match the `predict_e_plus_m.g` analytical output. |
| Full $E_+(3)$ S, T | Rank = 2272 (analytical). T-multiset = $\{1^{1172}, -1^{1044}, i^{28}, -i^{28}\}$ (analytical). $\sum_a S_{ia}\overline{S_{ja}} = \delta_{ij}$ within numerical tolerance (unitarity). $S^2 = (ST)^3$ (modularity). |
| Closed-form $(1,\cdot)$ row | Compare for $E_+(2)$ against the corresponding row of the precomputed $S$. Spot check three random columns for $E_+(3)$ against the freshly-computed full $S$. |
| $E_+(5)$ full S | Per-row unitarity: $\sum_a |S_{ia}|^2 = 1$ for every computed row $i$. (Cheap once a row is on disk.) |
| $E_+(7)$ partial | T spectrum matches the analytical multiset $\{1^{67145792}, (-1)^{67113024}, i^{8128}, (-i)^{8128}\}$. Closed-form rows satisfy unitarity in expectation (the squared-norm is computable analytically too). |

## Phased deliverables

| Phase | Code artefact | Wall-clock (this machine) | Output |
|---|---|---|---|
| **A. Direct D(G) library** | `untwisted_modular_data.g` | ~30 min to write | A library with `ComputeUntwistedT(G)` and `ComputeUntwistedS(G)`. |
| **B. Full $E_+(3)$** | `compute_e_plus_3.g` | minutes | `computed/E_plus_3/{T,S}/...` |
| **C. Chunked $E_+(5)$ T** | `compute_e_plus_5_T.g` | minutes | `computed/E_plus_5/T/sector_*.g` |
| **D. Closed-form central rows for $E_+(5), E_+(7)$** | `closed_form_central_rows.g` | seconds for $m{=}5$, hours for $m{=}7$ | `computed/E_plus_<m>/S/row_<i>.g` for $i$ in central sectors |
| **E. Chunked $E_+(5)$ full S** | `compute_e_plus_5_S.g` (parallelisable) | $\sim$ 1-2 days on 8 cores | `computed/E_plus_5/S/row_*.g` |
| **F. $E_+(7)$ T full** | `compute_e_plus_7_T.g` (parallelisable) | hours | `computed/E_plus_7/T/sector_*.g` |
| **G. $E_+(7)$ on-demand S rows** | `compute_e_plus_7_S_row.g <i>` | hours per row | `computed/E_plus_7/S/row_<i>.g` |

Phases A, B, C, D are *this-session* work. E, F, G are setup-and-let-run.

## Analytic shortcuts to investigate

Already identified:
- (1, ·) and (-1, ·) rows: closed form (above).

Worth investigating further:
- The (1, ·) row by itself determines all **quantum dimensions**:
  $d_{(g, \rho)} = S_{(1, \mathrm{triv}), (g, \rho)} / S_{(1, \mathrm{triv}), (1, \mathrm{triv})} = \dim \rho \cdot |[g]|$,
  so $d_{(g,\rho)} = \dim\rho$ if $g$ central, else $2 \dim\rho$.
  Total quantum dimension squared:
  $\mathcal D^2 = \sum (d_{(g,\rho)})^2 = |G|$ (general fact for $D(G)$).
  For $E_+(m)$: $\mathcal D = \sqrt{2^{2m+1}} = 2^{m+1/2}$.

- The (g, ρ) row when $g$ has order 2 non-central: $C_G(g) = \mathbb Z_2 \times E_+(m-1)$,
  and the conjugating sum collapses to a sum over $E_+(m-1)$ characters.
  Likely a closed form exists row-wise.

- The (g, ρ) row when $g$ has order 4 non-central: more complex
  centraliser ($\mathbb Z_4 \circ E_+(m-1)$), but still tractable.

- **Symplectic-orthogonality block-diagonality**: pre-compute the
  commuting matrix of conjugacy classes once, use as an index
  into which entries of $S$ to even attempt. For $m = 7$ this
  matrix is $16385 \times 16385$ (storable as $\sim$32 MB packed
  bits) and tells us in O(1) whether a block is zero.

## Dependencies, concerns, open questions

- **Conjugacy class numbering**: GAP can re-order conjugacy classes
  between sessions / versions, especially when `ConjugacyClasses` is
  invoked on a freshly-constructed group. Need to pin numbering by a
  fingerprint (e.g. order/representative-in-canonical-form) and
  check on resume.

- **Parallelism with shared GAP state**: each parallel GAP process
  must reload the group, character tables, etc. independently. For
  $m = 7$ the character table of $E_+(7)$ has $4^7 + 1 = 16\,385$
  irreps; computing it once takes time, then it's serialisable to
  disk and re-loadable. Pre-compute once, replicate to all workers.

- **Validity of unitarity check**: in exact arithmetic GAP returns
  cyclotomic numbers, so unitarity is an *exact* identity, not
  approximate. This is a strong structural check.

- **Storage tier**: at $m = 5$ full $S$ is 5 TB. Beyond local SSD
  capacity. May want to compress per-row (e.g. RLE on the sparse
  non-zero pattern) before writing. Or, more pragmatically: don't
  compute the full $S$ for $m = 5$ as a baseline; compute only
  selected rows of physical interest, plus the analytical closed
  forms.

- **Validation against an existing implementation**: Gruen's pipeline
  for trivial cocycle works for $m = 1, 2$ (we have the precomputed
  data). Cross-check our direct library on those cases first; only
  trust the new code once it agrees byte-for-byte (after permutation).

## Recommended order of attack

1. **Write the direct D(G) library** (Phase A). Verify on $E_+(2)$
   against precomputed $32/49/1.txt$. Mandatory before anything else.
2. **Run for $m = 3$** (Phase B). Confirm rank = 2272 and T-multiset
   matches `predict_e_plus_m.g`. Save full $S, T$ to disk.
3. **Implement the closed-form central rows** (Phase D) and run
   for $E_+(7)$ in parallel with chunked $E_+(5)$ T (Phase C).
4. **Decide based on phase-1-3 results**: do we need the full
   $E_+(5)$ S (Phase E), or are central rows + spot checks enough?
   This depends on what comparison Keller et al.'s pipeline will
   provide. Hold this question until the section-6 optimisation
   port lands and we can see what they expose.

End of plan.
