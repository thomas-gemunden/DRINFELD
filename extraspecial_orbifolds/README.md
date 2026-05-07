# Extraspecial 2-group orbifolds

Investigation of Keller–Roberts–Roberts ([arXiv:2411.13646](https://arxiv.org/abs/2411.13646)),
who construct an orbifold of the Barnes–Wall lattice VOA in $d = 128$ by
the extraspecial $2$-group $E(7) = 2_+^{15}$ and conjecture that the
resulting modular tensor category $D^\omega(E(7))\text{-mod}$ has trivial
$\omega \in H^3(E(7);U(1))$, yielding a holomorphic CFT of central
charge $128$ with gap $4$. Their evidence is two-fold:

1. **Level matching** (the *type 0 condition* of [vEMS17]): the
   restriction of $\omega$ to every cyclic subgroup is trivial. This is
   read off from the conformal weights $\rho_g$ of the $g$-twisted
   modules.
2. **Triviality of the multipliers $c_g$**: for every $g \in E(m)$,
   the $2$-cocycle $c_g$ of the projective representation
   $\phi_g: C_G(g) \to \mathrm{PGL}(W_g)$ on the $g$-twisted module of
   the lattice VOA is trivial as a class in $H^2(C_G(g); U(1))$. They
   verify this for $m = 3, 5, 7$ via Schur averaging on the *defect
   representation* $\Omega_0$ of $N = L_g^\perp / L(1-g)$.

Both are *necessary but not sufficient* for $\omega = 0$ in
$H^3(E(m); U(1))$. The user's question:
*can we compute the untwisted modular data $\mathrm{Mod}\bigl(D^1(E(m))\bigr)$ in
GAP and check that what Keller et al.\ found for $E(7)$ is consistent
with that picture?*

## Setup

Underlying group construction (`scripts/em_construction.g`):

$$
E(m) \;=\; \langle z=-I_{2^m},\; \Sigma_{a,r} = I_2 \otimes \cdots \otimes I_2 \otimes \sigma_r \otimes I_2 \otimes \cdots \otimes I_2 \rangle \;\le\; O(2^m, \mathbb{R})
$$

where $\sigma_1 = \begin{pmatrix}0&1\\1&0\end{pmatrix}$,
$\sigma_2 = \begin{pmatrix}1&0\\0&-1\end{pmatrix}$, and $\sigma_r$ sits
in slot $a$. We verified for $m = 1, 2, 3$ that this realises GAP's
`ExtraspecialGroup(2^{2m+1}, "+")` exactly:

| $m$ | $\lvert E_+(m) \rvert$ | `IdSmallGroup` |
|---|---|---|
| 1 | 8   | `[8, 3]`      |
| 2 | 32  | `[32, 49]`    |
| 3 | 128 | `[128, 2326]` |

## Status of the Magma → GAP port

Sections of [`/tmp/keller/BWOrbifoldsMagma.txt`](BWOrbifoldsMagma.txt is
not in this repo — it ships with arXiv:2411.13646 as
`anc/BWOrbifoldsMagma.txt`):

| Magma section | Lines | GAP port status |
|---|---:|---|
| 1: Misc matrix utilities | ~150 | n/a (subsumed into the helpers used below) |
| 2: $E(m)$, $BRW(m)$, $C(m)$ | ~170 | **$E(m)$ ported**; `scripts/em_construction.g` |
| 3: $BBW_{2^m}$, $BW_{2^m}$ | ~60 | **Gram + half-Gram ported via Lemma A.1.2 directly**; `scripts/bw_lattice.g` |
| 4: Twisted group algebra, lift, $u_g$ | ~150 | **ported**; `scripts/twisted_group_algebra.g`. Theorem 3.5 of paper verified for $m = 2, 3, 4$ (zero failures across 64, 288, 1024 checks of relations (A) and (B) of the lifting proof). |
| 5: Quadratic forms ($\mathbb F_2$ standardisation) | ~170 | **ported**; `scripts/qforms_f2.g`. All 7 hand-built test cases pass (radical splits, hyperbolic-pair finding, anisotropic / totally-singular separation, canonical-form output). |
| 6: Defect representation for $g = -1$, Schur averaging | ~600 | **brute-force core ported**; `scripts/defect_rep_minus_id.g`. For $m = 3$, runs in ~1 s and reproduces the substantive paper claim: $T_{a,r}^2 = 256\cdot I$ (so $T_{a,r}^2 = I$ after dividing by 16), $T_{a,r}T_{b,s} = T_{b,s}T_{a,r}$, and the trace distribution on $(\mathbb Z/2)^6$ matches the paper exactly. The intertwiners are not literally bit-for-bit equal to the paper's because Magma's `WittDecomposition` and our `SymplecticBasisF2` pick different symplectic bases of $N = L/2L$ — but the abstract rep is the same. The optimisation pipeline (`Finder` / `HardCodeFinder` / `efCoeff*`) needed for tractable $m \in \{5, 7\}$ via single-entry computations is **not** ported. |
| 7: Defect representation, other classes | ~100 | **ported**; `scripts/defect_rep_other.g`. For $m \in \{3, 5\}$ and the two non-$(-1)$ conjugacy class representatives $g_2 = \Sigma_{1,1}$ and $g_4 = \Sigma_{1,1}\Sigma_{1,2}$, exhaustively verified that *every* element of $C_{E(m)}(g)$ acts trivially on $N_\theta$ (the paper's Section 4.4 surprise observation). The intertwiner representation is therefore trivial and $c_g = 0$ automatically. |

In addition to the brute-force port for $m = 3$, we also independently
checked the paper's published outputs:

- **$m = 3$**: the paper's explicit intertwiner formulas (4.4.3)–(4.4.8)
  are implemented in `scripts/m3_intertwiners_explicit.g`.
  We verified $T_{a,r}^2 = I$ and $T_{a,r} T_{b,s} = T_{b,s} T_{a,r}$
  for all $6$ generators (15 pair-commutators), so $c_{-1}$ is trivial
  on the nose, not just up to coboundary.
- **$m = 5$**: `scripts/m5_relation_matrix.g` transcribes the
  $10 \times 10$ relation matrix of equation (4.4.9) and verifies it
  has $1$'s on the diagonal and is symmetric.

The relation matrix entries record values of a single matrix entry of
the products $T_{a,r}\,T_{b,s}$, by a Schur's-lemma argument: equality
of those entries plus symmetry of the index pair certifies
$T_{a,r}T_{b,s} = T_{b,s}T_{a,r}$ as matrices.

## Cross-check against $\mathrm{Mod}\bigl(D^1(E_+(m))\bigr)$

Predicted rank from the conjugacy-class / centraliser-irrep count
$2(4^m + 1) + (4^m - 1)\cdot 2(4^{m-1} + 1)$:

| $m$ | $\lvert G \rvert$ | rank |
|---|---:|---:|
| 1 | 8     | 22 |
| 2 | 32    | 184 |
| 3 | 128   | 2272 |
| 4 | 512   | 33664 |
| 5 | 2048  | 527872 |
| 7 | 32768 | $1.34\times 10^8$ |

The precomputed `modular_data` tree contains $E_+(m)$ untwisted modular
data for $m = 1$ (`modular_data/8/3/1.txt`) and $m = 2$
(`modular_data/32/49/1.txt`). For $m = 2$ we confirmed:

- rank $= 184$,
- $T$-multiset $= \{1^{102}, (-1)^{70}, i^6, (-i)^6\}$,

which matches exactly the analytical prediction from the centraliser
character tables ($Z_2 \times D_8$ for order-$2$ classes,
$Z_4 \circ D_8$ for order-$4$ classes).

For $m = 3$ no precomputed data exists; the rank is $2272$ and a fresh
GAP run is required.

## Remaining work, by usefulness

1. **Continue the Magma port** through sections 4–6, so the Schur
   averaging is reproducible end-to-end in GAP and the $m = 5, 7$
   computations can be driven entirely from this repository (today
   they piggy-back on the paper's published intermediate outputs).
2. **Compute $\mathrm{Mod}(D^1(E_+(3)))$** with Gruen's pipeline (rank
   $2272$, expected to take minutes–hours on a single CPU). The result
   is a non-trivial baseline for any future twisted comparison.
3. **Per-sector $T$-multiset prediction for any $m$** (no full $S$
   matrix needed). Tractable even at $m = 7$ via the centraliser
   character tables; gives a target the authors' machinery can be
   pointed at when they compute the full twisted MTC.

## Reproducing

```sh
cd scripts
ln -sfn ../../../modular_data Modular_Data           # for inspect_e_plus_2_data.g
gap -q -b -c 'Read("identify_extraspecial.g");'      # SmallGroup IDs of E_±(m)
gap -q -b -c 'Read("test_em_and_bw.g");'             # E(m) + BW lattice sanity checks
gap -q -b -c 'Read("twisted_group_algebra.g");'      # lifting Thm 3.5 for m=2,3,4
gap -q -b -c 'Read("test_qforms_f2.g");'             # F_2 quadratic-form utilities
gap -q -b -c 'Read("test_defect_rep_m3.g");'         # brute-force Schur averaging, m=3
gap -q -b -c 'Read("test_defect_rep_other.g");'      # other conjugacy classes, m=3, 5
gap -q -b -c 'Read("m3_intertwiners_explicit.g");'   # m=3 intertwiners via paper's formulas
gap -q -b -c 'Read("m5_relation_matrix.g");'         # m=5 relation matrix transcription
gap -q -b -c 'Read("inspect_e_plus_2_data.g");'      # untwisted Z(Vec_{E_+(2)}) shape
```

The headline check is `test_defect_rep_m3.g` plus `test_defect_rep_other.g`:
together they reproduce, **end-to-end from scratch in GAP**, the paper's
$c_g = 0$ result for $m = 3$ (all three conjugacy class types) and the
non-$(-1)$ conjugacy classes for $m = 5$.
