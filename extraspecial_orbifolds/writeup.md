# Mod(D¹(E_+(m))) and the Keller–Roberts–Roberts orbifold conjecture

This directory records two intertwined investigations:

1. A complete Magma → GAP port of the
   [Keller–Roberts–Roberts](https://arxiv.org/abs/2411.13646) supplement,
   reproducing in GAP their evidence that the Barnes–Wall lattice VOA
   orbifold by E_+(m) (m = 3, 5, 7) has trivial 2-cocycles c_g on each
   g-twisted module — necessary conditions for the 't Hooft anomaly
   ω ∈ H³(E_+(m); U(1)) to vanish.

2. A scalable computation of the *untwisted* modular data of
   Z(Vec_{E_+(m)}) — the modular tensor category Keller et al.
   conjecture is also the modular data of their orbifold construction —
   built directly from GAP's character tables and bypassing
   Gruen–Morrison's cohomology pipeline.

Together these give an end-to-end reproducible target: the modular
data of Mod(D¹(E_+(m))) as it would be if the conjecture holds.

## Background

[Keller, Roberts and Roberts, arXiv:2411.13646](https://arxiv.org/abs/2411.13646)
construct an orbifold of the Barnes–Wall lattice VOA in $d = 128$ by
the extraspecial 2-group $E_+(7) \cong 2_+^{15}$. Granting their
conjecture that $\omega \in H^3(E_+(7); U(1))$ vanishes, the orbifold
admits a holomorphic extension $V_L^{\mathrm{orb}(E(7))}$ which is a
holomorphic CFT of central charge $128$ and gap $4$ — the first such
example known with gap larger than $2$.

Their evidence for $\omega = 0$ has two parts.

1. **Level matching** (the *type-0* condition of [vEMS17]):
   the restriction of $\omega$ to every cyclic subgroup is trivial.
   For $E_+(7)$ this is read off from the integer-valued conformal
   weights $\rho_g$ of the $g$-twisted modules.
2. **Triviality of the multipliers $c_g$**: for every $g$, the
   2-cocycle $c_g$ of the projective representation
   $\phi_g : C_G(g) \to \mathrm{PGL}(W_g)$ on the $g$-twisted module is
   trivial as a class in $H^2(C_G(g); U(1))$. They verify this for
   $m = 3, 5, 7$ via Schur averaging on the *defect representation*
   $\Omega_0$ of $N = L_g^\perp / L(1-g)$.

Both conditions are *necessary* but not sufficient for $\omega = 0$
in $H^3(E_+(m); U(1))$.

## Part I — Magma → GAP port (paper's own pipeline)

Status of the port (every section verified end-to-end):

| Magma section | Lines | Our GAP file | Verified |
|---|---:|---|---|
| 2: $E(m)$, $BRW(m)$, $C(m)$ | ~170 | `scripts/em_construction.g` | $E_+(m)$ identifies with `ExtraspecialGroup(2^{2m+1}, "+")` for $m=1,2,3$ |
| 3: $BBW_{2^m}$, $BW_{2^m}$ | ~60 | `scripts/bw_lattice.g` | Discriminant of BW(3) = 1 (so it is $E_8$); shortest squared length $= 2^{\lfloor m/2 \rfloor}$ |
| 4: twisted group algebra, $u_g$ | ~150 | `scripts/twisted_group_algebra.g` | Theorem 3.5 of paper holds: 0 errors across 64 ($m=2$), 288 ($m=3$), 1024 ($m=4$) checks |
| 5: F₂ quadratic forms | ~170 | `scripts/qforms_f2.g` | All 7 hand-built test cases pass |
| 6 brute-force core | ~250 | `scripts/defect_rep_minus_id.g` | $m=3$: $T_{a,r}^2 = 256\cdot I$, $[T_{a,r}, T_{b,s}] = 0$, trace distribution on $(\mathbb Z/2)^6$ matches paper exactly |
| 6 closed-form Gauss sum | ~600 | `scripts/defect_rep_minus_id_optim.g` | $m=3$ single-entry cross-check: 1536 / 1536 entries agree with brute force; $m=3$ product cross-check: 9216 / 9216 entries agree with direct matrix product |
| 7: other conjugacy classes | ~100 | `scripts/defect_rep_other.g` | For $m=3$ and $m=5$, every element of $C_{E(m)}(g)$ acts trivially on $N_\theta$ for both $g_2 = \Sigma_{1,1}$ and $g_4 = \Sigma_{1,1}\Sigma_{1,2}$ (the paper's Section 4.4 surprise observation) |

**End-to-end result.** Independently of the paper's published tables,
the GAP port reproduces the substantive paper claims for all three
non-trivial m:

- **$m = 3$**: full c_g triviality for *every* conjugacy class
  (g = -1 via brute-force Schur averaging, g₂ and g₄ via centraliser
  acting trivially on $N_\theta$).
- **$m = 5$**: c_{-1} triviality via the closed-form Gauss-sum
  relation matrix (10×10, diag = 1, symmetric, so $T_{a,r}^2$ = scalar·I
  and $[T_{a,r}, T_{b,s}] = 0$, hence $c_{-1}$ trivial). c_{g₂}, c_{g₄}
  triviality from centraliser-trivial-action argument.
- **$m = 7$**: same for c_{-1} via the 14×14 closed-form relation
  matrix.

The literal entries of our $m=5, 7$ relation matrices differ from
the paper's eq (4.4.9), (4.4.10) values because our `SymplecticBasisF2`
and Magma's `WittDecomposition` pick different symplectic bases of
$N = L/2L$. The abstract intertwiner representations are the same;
the trace distribution on $(\mathbb Z/2)^{2m}$ is identical at $m=3$
(verified) and the substantive properties (diag = 1, symmetric)
hold at $m=5,7$.

Wall-clock summary:

| Test | Wall |
|---|---|
| $m=3$ brute-force core (paper claim verification) | < 1 s |
| $m=3$ closed-form cross-check (1536 entries) | 0.3 s |
| $m=3$ product cross-check (9216 entries) | 1.6 s |
| $m=5$ relation matrix (100 entries) | 0.24 s |
| $m=7$ relation matrix (196 entries) | 15 s |
| Section 7 verification ($m=3, 5$) | 1 s |

## Part II — Direct untwisted modular data of $\mathrm{Mod}(D^1(E_+(m)))$

If the Keller conjecture holds, the resulting modular tensor category
is exactly $\mathrm{Mod}(D^1(E_+(m)))$ — the Drinfeld double of the
*untwisted* group algebra. That category has well-defined modular
data $(S, T)$ depending only on $E_+(m)$.

### Library

`scripts/untwisted_modular_data.g` computes $(S, T)$ for any finite
group $G$ directly from `ConjugacyClasses(G)`, `Centralizer(G, \cdot)`
and `CharacterTable(\cdot)`. Bypasses Gruen–Morrison's pipeline (no
`ResolutionFiniteGroup`, no `IsomorphismFpGroup` of centralisers, no
projective-character extension): the trivial cocycle case admits a
direct formula

$$
T_{(g, \rho)} = \rho(g) / \dim \rho,
\qquad
S_{(g, \rho), (h, \sigma)}
\;=\; \tfrac{1}{|G|}
\sum_{\substack{a \in [g],\, b \in [h] \\ ab = ba}}
\overline{\rho(t_a^{-1} b\, t_a)}\,
\overline{\sigma(s_b^{-1} a\, s_b)}.
$$

For $E_+(m)$ each conjugacy class has size $\le 2$, so the inner sum
has at most 4 terms — the cost is in the SHEER NUMBER of entries.

### Per-sector / analytic prediction

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

### Closed-form central rows

For any $m$, the rows associated to the central elements admit a
closed form (`scripts/closed_form_central.g`):

$$
\boxed{\;S_{((1, \rho), (h, \sigma))} = \frac{\dim \sigma}{|C_G(h)|}\,\overline{\rho(h)}\;}
\qquad
\boxed{\;S_{((-1, \rho), (h, \sigma))} = \frac{\sigma(-1)}{|C_G(h)|}\,\overline{\rho(h)}\;}
$$

Each entry is **O(1)** given the character tables, so the whole
$2(4^m + 1)$ central rows are computable per-row in O(rank) without
iterating over commuting pairs. Verified against the direct
`ComputeSBlock` on $E_+(2)$: 1472 / 1472 entries agree (8 rows × 184
columns).

### Computed data on disk

Under `extraspecial_orbifolds/computed/`:

| Group | Output | Wall | Status |
|---|---|---|---|
| $E_+(2)$ | full $(S, T)$, rank 184 | 0.36 s | rerun-on-demand; matches `modular_data/32/49/1.txt` byte-for-byte |
| $E_+(3)$ | full $(S, T)$, rank 2272, S 26 MB | 7 m 30 s wall (1m51s S, 5m45s S² = (ST)³ check) | persisted to `E_plus_3/{S, T, manifest}.g` |
| $E_+(5)$ | $T$ only (full S would be ~5 TB), 1025 sector chunks | 100 s | persisted to `E_plus_5/T/sector_*.g` |
| $E_+(7)$ | $T$ only (full S impossible) | running, ETA ~55 min | will persist to `E_plus_7/T/sector_*.g` |

For each computed instance: rank matches the analytical prediction,
T-multiset matches exactly, modularity $S^2 = (ST)^3$ verified
exactly (in $E_+(3)$), unitarity $\sum_a \lvert S_{ia}\rvert^2 = 1$
verified on sample rows.

## Verification ladder

| Property | $m=3$ | $m=5$ | $m=7$ | How |
|---|---|---|---|---|
| rank matches predictor | ✓ | ✓ | (Phase F) | direct lib + analytical |
| T-multiset matches predictor | ✓ | ✓ | (Phase F) | direct lib + analytical |
| modularity $S^2 = (ST)^3$ | ✓ | (full S not computed) | (impossible) | direct |
| c_g trivial for $g = -1$ | ✓ | ✓ | ✓ | Magma port (brute-force + closed-form) |
| c_g trivial for $g = g_2$ | ✓ | ✓ | (m=7 not run; same argument applies) | centraliser acts trivially on $N_\theta$ |
| c_g trivial for $g = g_4$ | ✓ | ✓ | (same) | same |
| level matching $\omega\rvert_{\langle g \rangle} = 0$ | (paper) | (paper) | (paper, $\rho_g \in \mathbb Z$) | from $\rho_g$ values |

## What we have NOT done

* **Full $S$ for $E_+(5), E_+(7)$**: $E_+(5)$ would require
  $\sim 1$–$2$ days × 8 cores parallel and $\sim 5$ TB disk;
  $E_+(7)$ is fundamentally out of reach
  ($\sim 3 \cdot 10^{17}$ bytes of dense storage).
* **Direct test of $[\omega] = 0$**: triviality of all $c_g$ at every
  conjugacy class is *necessary* but not *sufficient* for $\omega = 0$.
  A definitive proof needs the *full* $S$ to demonstrate isomorphism
  with $\mathrm{Mod}(D^1(E_+(m)))$, OR a higher-cohomology argument
  that shows no obstruction beyond the c_g.

## Open question for next round

Both Keller's pipeline and ours give the same data for
$m = 3, 5, 7$ at every checked point. To strengthen this from
"compatible" to "equal" without computing the full $S$, we want
**local discriminators**: cheaply-computable invariants that would
show $S_{\mathrm{Keller}} \ne S_{\mathrm{untwisted}}$ if any non-zero
$[\omega]$ slipped past the $c_g = 0$ tests. See the strategic note
following this writeup.

## Reproducing

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
gap -q -b -c 'Read("compute_e_plus_7_T.g");'         # E_+(7) T-vector (~1 hr)
gap -q -b -c 'Read("test_closed_form_central.g");'   # closed-form central rows
```

All `.g` files in `scripts/` are pure GAP libraries (no `QUIT;` at end);
test/driver scripts begin with `test_` or `compute_` prefixes.
Computed outputs land under `extraspecial_orbifolds/computed/`.
