# Per-class irrep relabellings: subtler than expected

We attempted to compute, for each non-canonical class $i$ in
$E_+(3)$, a single irrep permutation
$\sigma_i \colon \mathrm{Irr}(C_{i_{\mathrm{canonical}(t)}}) \to \mathrm{Irr}(C_i)$
that would let us reconstruct any $S$-block $(i, j)$ from the
canonical block of its refined group.

## What works

The 22 **canonical S-blocks** are computed and saved for $m = 3, 5, 7$.
Each contains the full structural information for one
$(\mathrm{type}_i, \mathrm{type}_j, \mathrm{commute}, \mathrm{diag/off})$
group; every $(i, j)$ block is permutation-equivalent to its group's
canonical block (canonical-form check verified).

For per-entry queries — comparing single S-entries against
Keller's pipeline — the canonical blocks plus on-demand
recomputation via `ComputeSBlock` is sufficient:
1. Decode global indices $(i, j)$ to $(\mathrm{class}_i, \mathrm{irrep}_i),
   (\mathrm{class}_j, \mathrm{irrep}_j)$.
2. Identify the refined group; check commute-flag (return 0 if not commuting).
3. Compute centralisers $C_{\mathrm{class}_i}, C_{\mathrm{class}_j}$ and call `ComputeSBlock`.

## Why the simple per-class permutation idea fails

I'd hoped: "for each non-canonical class $i$ of type $t$, a single
intrinsic permutation $\sigma_i$ of $|\mathrm{Irr}(C_{i_{\mathrm{canonical}(t)}})|$
suffices, recoverable by row-matching block$(i_{\mathrm{canonical}}, 1)$
against block$(i, 1)$."

This **doesn't work** because the BRW element $x_i$ conjugating
$g_{i_{\mathrm{canonical}}}$ to $g_i$ also acts on $\mathrm{Irr}(E_+(m)) =
\mathrm{Irr}(G)$ via outer automorphism of $G$ (BRW is the normaliser
of $E_+(m)$ in $O(2^m, \mathbb R)$, so it acts on $E_+(m)$ by
conjugation, *outer* — non-trivial on $E_+(m)$-conjugacy classes,
hence on $\mathrm{Irr}(E_+(m))$). So when we look at
block$(i, 1)$ vs block$(i_{\mathrm{canonical}}, 1)$, the columns
*also* permute (specifically, by the BRW action on $\mathrm{Irr}(G)$);
they are not row-permutations alone.

Empirically: for $E_+(3)$, all 61 non-canonical classes failed the
row-only `FindRowPerm` test against the dense $S$. This is consistent
with the col axis genuinely permuting.

## What WOULD let us fully reconstruct from canonical blocks alone

To make canonical blocks + per-class data sufficient, we need to track
the BRW action $\mathrm{Ad}(x_i)$ on **both** axes:

- $\sigma_i$: the row permutation on $\mathrm{Irr}(C_i)$ relative to
  $\mathrm{Irr}(C_{i_{\mathrm{canonical}(t)}})$.
- $\tau_i$: the corresponding permutation on $\mathrm{Irr}(G)$ (acting
  via the same $x_i$).

Plus, for non-central centralisers, the per-class perm on
$\mathrm{Irr}(C_j)$ for any second axis $j$.

The cleanest way to compute these is to **build $\mathrm{BRW}(m)$
explicitly** as a matrix subgroup of $O(2^m, \mathbb R)$ (KRR Section 3
gives the generators) and use `RepresentativeAction(\mathrm{BRW}(m), g_{\mathrm{canonical}}, g_i)`
to find $x_i$. Then conjugation by $x_i$ acts on character tables
canonically.

This is left as future work.

## Practical conclusion

For the **Keller comparison** that motivated this whole effort (single
S-entry queries to compare against Keller's pipeline output), we DO
NOT need per-class permutations. The canonical blocks plus on-demand
`ComputeSBlock` evaluation at the actual $(i, j)$ pair gives the
answer in seconds, using the existing `untwisted_modular_data.g`
infrastructure.

For E_+(3), E_+(5): the per-class centralisers are already in our
`BuildSimpleIndex` records.

For E_+(7): we computed centralisers of *canonical* classes (orders
16384, GAP handles fine). For non-canonical classes, computing the
centraliser on demand is also fast — just `Centralizer(G, class_rep)`
followed by `CharacterTable`. The full BRW orbit structure isn't
needed for individual entry queries.

## Summary table of structural rep status

| $m$ | $|G|$ | rank | canonical blocks | dense S size | on disk |
|---|---:|---:|---:|---:|---:|
| 3 | 128 | 2272 | 22 | 26 MB | 337 KB structural |
| 5 | 2048 | 527,872 | 22 | ~5 TB | 94 MB structural |
| 7 | 32,768 | 1.34×10⁸ | 9 (of 22) | ~3×10¹⁷ B | 8.7 GB structural |

For $m = 7$, the 13 missing groups are either zero blocks
(non-commuting pairs) or fully-central blocks (closed-form O(1) per
entry, no need to materialise).
