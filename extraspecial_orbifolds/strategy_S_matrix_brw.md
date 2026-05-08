# Same trick for S: BRW-orbit-folded block representation

**The user's insight, applied to S.** The conjugacy classes of
$E_+(m)$ under the LARGER group $\mathrm{BRW}(m)$ are just **four**
(KRR Prop 3.1): $\{1\}$, $\{-1\}$, $\{\sigma_2 \otimes I^{\otimes (m-1)}\}^{\mathrm{BRW}}$,
$\{\sigma_1\sigma_2 \otimes I^{\otimes (m-1)}\}^{\mathrm{BRW}}$. Two
$E_+(m)$-conjugacy classes within the same BRW-orbit have:

- isomorphic centralisers,
- identical character tables (up to relabelling by the BRW
  conjugation),
- the same number of irreps,
- the same T-values per irrep.

That is exactly what we used for the analytical Phase F' T-vector.

The same observation extends to **S**, but with one twist. The
formula

$$
S_{(g_1, \chi_1), (g_2, \chi_2)}
\;=\; \tfrac{1}{|G|}
\sum_{\substack{a \in [g_1],\; b \in [g_2] \\ ab = ba}}
\overline{\chi_1(t_a^{-1} b\, t_a)}\,
\overline{\chi_2(s_b^{-1} a\, s_b)}
$$

has TWO sources of structural dependence:

1. **Centraliser types** of $g_1$, $g_2$ — fixed by the BRW orbit.
2. **The commuting structure** between $g_1$ and $g_2$ — determined
   by the symplectic form on $E_+(m) / Z \cong \mathbb F_2^{2m}$:
   $g_1, g_2$ commute iff $\omega(\bar g_1, \bar g_2) = 0$, where
   $\omega$ is the standard symplectic form on $\mathbb F_2^{2m}$.

Within a fixed (type, type) pair, two CHOICES of $(g_1, g_2)$ are
equivalent under BRW conjugation iff they give the same commuting
structure. So the S-block is determined by the
**(type, type, commute-structure)** triple.

## Block taxonomy for S

For E_+(m), the distinct block types are:

| (type$_1$, type$_2$) | block size | commuting structure | block category |
|---|---|---|---|
| $(\{1\}, \{1\})$         | $(4^m+1)^2$       | always commute | one block |
| $(\{1\}, \{-1\})$        | $(4^m+1)^2$       | always commute | one block |
| $(\{1\}, \sigma_2)$       | $(4^m+1)(2{\cdot}4^{m-1}+2)$ | always commute | one block per σ_2-class |
| $(\{1\}, \sigma_1\sigma_2)$ | similar         | always commute | one block per σ_1σ_2-class |
| $(\{-1\}, \{-1\})$        | same               | always commute | one block |
| $(\{-1\}, \sigma_2)$      |                    | always commute | one block |
| $(\{-1\}, \sigma_1\sigma_2)$ |                  | always commute | one block |
| $(\sigma_2, \sigma_2)$    | $(2{\cdot}4^{m-1}+2)^2$ | commute or not | two blocks (one zero) |
| $(\sigma_2, \sigma_1\sigma_2)$ | mixed         | commute or not | two blocks (one zero) |
| $(\sigma_1\sigma_2, \sigma_1\sigma_2)$ | similar | commute or not | two blocks |

Plus the (g, h) ↔ (h, g) symmetry from $S = S^T$, halving the
distinct-block count again.

**Net distinct S-blocks: ≤ 10** (well, ≤ 14 if we count the
"non-commuting → all zero" trivial blocks).

## Storage scaling

For E_+(7):

| Block | Size | Storage |
|---|---|---|
| $(\{1\}, \{1\})$         | $16385 \times 16385$ | ~4 GB |
| $(\{1\}, \{-1\})$        | $16385 \times 16385$ | ~4 GB |
| $(\{1\}, \sigma_2)$       | $16385 \times 8194$  | ~2 GB |
| $(\{1\}, \sigma_1\sigma_2)$ | similar           | ~2 GB |
| ... (about 10 blocks) | ... | ~10–20 GB total |

Compared to the full S which would be **3·10¹⁷ bytes** dense, we get
a **5×10⁶× compression** purely from the BRW orbit structure of
$E_+(m)$. **The "intractable" full-S story is wrong** — it's only
intractable in dense form. Structurally, E_+(7) S is comparable in
storage to E_+(3) S (26 MB).

## Per-entry query cost

Given a query $S_{(i,j)}$ where $i, j$ are global simple indices:

1. Decode $i \to (\mathrm{class}_1, \mathrm{irrep}_1)$,
   $j \to (\mathrm{class}_2, \mathrm{irrep}_2)$.
2. Look up types $(t_1, t_2)$ of $\mathrm{class}_1, \mathrm{class}_2$.
3. Look up commute-flag $\omega(\bar{g}_{\mathrm{class}_1}, \bar{g}_{\mathrm{class}_2})$.
4. If commute-flag is "non-commuting", return 0.
5. Otherwise look up the canonical block $S^{(t_1, t_2, \mathrm{commute})}$
   at coordinates given by $(\mathrm{irrep}_1, \mathrm{irrep}_2)$ via
   the canonical relabelling.

Total cost: O(1) given the structural rep is in memory or on disk.

## Implementation outline

1. **Construct E_+(m-1)** as a PC group via
   `ExtraspecialGroup(2^{2m-1}, "+")`. For m=7, that's |G|=8192,
   memory-friendly.
2. **Compute character tables** of E_+(m-1), $\mathbb Z_2 \times E_+(m-1)$,
   and $\mathbb Z_4 \circ E_+(m-1)$. The first is the bulk of the work.
3. **Pick canonical representatives** $g^*$ for each of the 4 BRW types
   (these are explicit: $1, -1, \sigma_2 \otimes I^{m-1}, \sigma_1\sigma_2 \otimes I^{m-1}$).
4. **For each (type, type, commute-flag) triple**, compute the
   canonical S-block by direct evaluation of the Bantay/CGR formula at
   $(g_1^*, g_2^*)$. Store as a 2-D array.
5. **Persist** to disk as 10 separate `.g` files (~20 GB total for
   E_+(7); much smaller for E_+(5), E_+(3)).
6. **Provide a query function** `S_lookup(i, j, structural_S)` that
   returns the entry in O(1).

## Caveats

- **Symplectic-form computation for the commute-flag**: requires
  iterating through pairs of class representatives in
  $E_+(m) / Z \cong \mathbb F_2^{2m}$. For E_+(7) that is
  $16384 \times 16384 \approx 2.7 \cdot 10^8$ pairs. Storable as a
  packed-bit matrix in ~32 MB. One-time cost.
- **Block-level character tables** still need to be computed in GAP.
  For E_+(6) (the bottleneck for non-central centralisers), that's
  on a group of order 8192 — should be tractable, but may need a
  workaround if `CharacterTable(E_+(6))` itself hits memory limits
  (worst case fall back to the analytical structure of E_+(m)
  irreps: 4^m of dim 1 + 1 of dim 2^m).
- **Canonical relabelling within a BRW orbit**: needs careful
  bookkeeping. The relabelling is by the BRW automorphism that takes
  $g_1$ to a chosen representative; this acts on $\mathrm{Irr}(C_{g_1})$
  via composition.

## Recommended next phases

| Phase | Description | Cost |
|---|---|---|
| **F'** ✓ | Structural T for any m via BRW orbits | done; see `compute_e_plus_7_T_analytical.g` |
| **E_BRW** | Structural S for E_+(3) via BRW orbits | minutes; cross-check against the full S we already have on disk |
| **E_BRW (m=5)** | Structural S for E_+(5) | hours; first time we get usable S data for m=5 |
| **E_BRW (m=7)** | Structural S for E_+(7) | days at most; ~20 GB on disk |

The cross-check at E_+(3) is mandatory: we verify that the BRW-folded
block representation, when expanded, equals the dense S we already
have at `computed/E_plus_3/S.g` (rank 2272, 26 MB). If not, the
folding logic has a bug.
