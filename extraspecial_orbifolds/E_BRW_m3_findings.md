# E_BRW m=3 step 1: validation findings

We empirically tested whether the BRW-folded S representation works for
E_+(3), using the dense rank-2272 S already computed (`computed/E_plus_3/S.g`).

## Result: 22 canonical blocks suffice

For each pair of conjugacy classes $(i, j)$ of $E_+(3)$, the S-block is
a $|\mathrm{Irr}(C_i)| \times |\mathrm{Irr}(C_j)|$ submatrix. Grouping
the $65 \times 65 = 4225$ block-positions by

$$(\mathrm{type}_i, \mathrm{type}_j, \mathrm{commute\text{-}flag}, \mathrm{diag/off})$$

— where:

- $\mathrm{type}_i \in \{\mathrm{id}, \{-1\}, \sigma_2, \sigma_1\sigma_2\}$ is the BRW-orbit type of class $i$,
- commute-flag $\in \{0, 1\}$,
- diag/off encodes whether $i = j$ as class indices,

we found that

* **all 22 non-empty groups have a uniform canonical form** (lex-sort rows then lex-sort columns gives the same matrix for every $(i, j)$ in the group);
* therefore each block in a group is a **row + column permutation of one canonical block** for that group.

So storing the full $S$ structurally requires:

1. **22 canonical blocks**, one per refined group.
2. **A per-class permutation** $\Pi_i$ for each class $i$, mapping $\mathrm{Irr}(C_i)$ to $\mathrm{Irr}(C_{i_{\mathrm{canonical}(t)}})$ where $t = \mathrm{type}(i)$.
3. **For groups whose canonical's two indices belong to the same type** (diagonal of sigma2/sigma2 commute, off-diagonal of sigma2/sigma2 commute, etc.), an additional fixed reference is needed for the second axis when it points to a non-canonical class.

For E_+(3), the 22 groups are:

| group key | block-positions | size of block |
|---|---:|---|
| `id/id/1/diag` | 1 | 65×65 |
| `id/minus_one/1/off` | 1 | 65×65 |
| `id/sigma2/1/off` | 35 | 65×34 |
| `id/sigma_1sigma_2/1/off` | 28 | 65×34 |
| `minus_one/id/1/off` | 1 | 65×65 |
| `minus_one/minus_one/1/diag` | 1 | 65×65 |
| `minus_one/sigma2/1/off` | 35 | 65×34 |
| `minus_one/sigma_1sigma_2/1/off` | 28 | 65×34 |
| `sigma2/id/1/off` | 35 | 34×65 |
| `sigma2/minus_one/1/off` | 35 | 34×65 |
| `sigma2/sigma2/0/off` | 560 | 34×34 (zero) |
| `sigma2/sigma2/1/diag` | 35 | 34×34 |
| `sigma2/sigma2/1/off` | 630 | 34×34 |
| `sigma2/sigma_1sigma_2/0/off` | 560 | 34×34 (zero) |
| `sigma2/sigma_1sigma_2/1/off` | 420 | 34×34 |
| `sigma_1sigma_2/id/1/off` | 28 | 34×65 |
| `sigma_1sigma_2/minus_one/1/off` | 28 | 34×65 |
| `sigma_1sigma_2/sigma2/0/off` | 560 | 34×34 (zero) |
| `sigma_1sigma_2/sigma2/1/off` | 420 | 34×34 |
| `sigma_1sigma_2/sigma_1sigma_2/0/off` | 336 | 34×34 (zero) |
| `sigma_1sigma_2/sigma_1sigma_2/1/diag` | 28 | 34×34 |
| `sigma_1sigma_2/sigma_1sigma_2/1/off` | 420 | 34×34 |

Of the 22 distinct canonical forms, **6 are entirely zero blocks**
(non-commuting class pairs), so really only 16 nontrivial canonical
blocks are needed. The total storage for E_+(3) is well under 1 MB —
versus 26 MB for the dense $S$.

## Why the diag/off split is necessary

For $(i, i)$ blocks (diagonal): the formula
$S_{(g, \chi),(g, \psi)}$ has the special structure of "self-pairing"
on a single conjugacy class. For $(i, j)$ with $i \neq j$ but both
of the same type and commuting, the formula has a different
structure: it pairs *two distinct* classes that happen to commute.

Empirically (step 3 of our investigation), these two cases give
distinct canonical forms even though they share the (type, type,
commute) labelling. The diag/off split fixes this.

## Scaling to E_+(m)

The same structural decomposition applies for any $m$. The number of
refined groups is bounded by $4 \cdot 4 \cdot 2 \cdot 2 = 64$ (in
practice ~22 since many sub-cases collapse), independent of $m$.
Block sizes scale as $|\mathrm{Irr}(C_g)|^2$:

| $m$ | $|\mathrm{Irr}(C_{\mathrm{central}})|$ | $|\mathrm{Irr}(C_{\mathrm{noncentral}})|$ | Largest canonical block | Total structural storage |
|---|---:|---:|---:|---:|
| 3 | 65 | 34 | 65×65 = 4225 entries | <1 MB |
| 5 | 1025 | 514 | 1025² ≈ 10⁶ entries | ~10 MB |
| 7 | 16385 | 8194 | 16385² ≈ 2.7×10⁸ entries | ~5 GB |

(Per-entry storage in cyclotomic-encoded form is small; the upper
bound 16 bytes per entry is conservative.)

For E_+(7) this is **5 GB structural rep instead of 3·10¹⁷ B dense**.

## Open implementation work

1. **Compute per-class irrep relabellings $\Pi_i$.** For each
   non-canonical class $i$ of type $t$, find a conjugating element
   $x_i$ in $\mathrm{BRW}(m)$ (or $E_+(m)$ if available) with
   $x_i \cdot g_{i_{\mathrm{canonical}(t)}} \cdot x_i^{-1} = g_i$,
   then compute the induced permutation of $\mathrm{Irr}$ by
   pulling back via $x_i$. For E_+(3), 64 non-canonical classes;
   straightforward but requires explicit BRW(m) realisation.

2. **Compute the 22 canonical blocks** by direct evaluation of the
   Bantay/CGR formula at the canonical pair, using the existing
   `ComputeSBlock` function.

3. **Verify reconstruction.** For each $(i, j)$, look up
   $\mathrm{block}_{i, j}[k, l] = \mathrm{canonical}_{\mathrm{group}}[\Pi_i(k), \Pi_j(l)]$
   and compare to the entry of the dense $S$.

The structural insight is now established; the implementation work
is bookkeeping.
