# `q8_extension_type/scripts/`

GAP scripts used to compare the modular data of `Z(Vec_{Q_8})` (trivial
3-cocycle) and `Z(Vec_{Q_8}^{ω_4})` (the unique order-2 3-cocycle on
Q_8). The findings these produce are summarised in
[`../writeup.md`](../writeup.md) (and the LaTeX version
[`../writeup.tex`](../writeup.tex)).

## Prerequisites

- GAP ≥ 4.14 (Sage's bundled GAP works; standalone GAP via Homebrew tap
  `gap-system/gap` works too).
- HAP and IO packages installed in your GAP.
- The `modular_data/` data tree present alongside this repository (i.e.
  at `../../../modular_data/` from this directory). This data is *not*
  in version control; it is too large (~77 GB if exhaustive). You can
  use the existing precomputed tree or regenerate the relevant slice
  yourself with Gruen's `SaveModularDataParallel(8, 4, 1, 0, false)`
  from `../../src/modular_data.g`.

## Setup

Run once:

```sh
./setup.sh
```

This creates a symlink `Modular_Data -> ../../../modular_data` because
Gruen's `LoadModularData` expects the data directory under the name
`Modular_Data` (capital M, D) relative to the current working directory.

## Running

From this directory:

```sh
gap -q -b -c 'Read("verify_q8.g");'
gap -q -b -c 'Read("recompute_perm.g");'
gap -q -b -c 'Read("find_permutation.g");'
# ...
```

## Script index

| Script | Purpose |
|---|---|
| `verify_q8.g` | Confirm `SmallGroup(8,4) = Q_8` and identify the trivial / order-2 cocycles by H³ class. |
| `recompute_check.g` | Recompute `(S, T)` from scratch for cocycles 1, 2 and naively compare to stored. |
| `recompute_perm.g` | Same, but tolerate the random row-ordering and check up-to-permutation equivalence. |
| `find_permutation.g` | Exhaustive backtracking search for a permutation aligning `(S₁, T₁)` and `(S₂, T₂)`. Returns `fail`. |
| `sanity_check.g` | Sanity-check the search by running it on `(S₁, T₁)` vs itself and vs a known random permutation. |
| `galois_and_fusion.g` | Galois-twisted (i ↔ −i) version of the search, plus Verlinde-derived fusion ring computation and its permutation search. |
| `fusion_plus_T.g` | Backtracking search for permutations aligning fusion ring **and** T-vector jointly. Returns count 0. |
| `sanity_count.g` | Counts |Aut(N, T)| for each cocycle individually (6 vs 24, the discriminating invariant). |
| `label_simples.g` | Recovers `(g_class, dim)` labels for every row of stored `1.txt`/`2.txt` and prints the fusion-ring iso π_F in label form. |
| `test_q8_equiv.g` | Quick coarse multiset-level checks (the first round of investigation). |

## Provenance

These scripts were written during the investigation of whether the Q_8
twisted Drinfeld doubles yield a counterexample to "modular data
detects extension type" (Evans–Gannon, [arXiv:1804.11145](https://arxiv.org/abs/1804.11145)). The conclusion is in `../writeup.md`: at the
level of full `(S, T)` they do not (modular tensor categories are
genuinely inequivalent, consistent with Mignard–Schauenburg
[arXiv:1708.06538](https://arxiv.org/abs/1708.06538)), but the
fusion rings *do* coincide.
