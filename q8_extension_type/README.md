# Q_8 extension-type investigation

## Question

Evans and Gannon ([arXiv:1804.11145](https://arxiv.org/abs/1804.11145))
show that twisted Drinfeld doubles `D^ω(G)` admit "trivialising" type-1
module categories (in their language: are *of extension type* with
respect to all of `G`) when the 3-cocycle `ω` is trivial. The folklore
expectation is that this property — equivalently `[ω] = 0 ∈ H³(G)` — is
detectable from the modular data `(S, T)` alone.

This directory records an investigation of whether `Q_8` is a
counterexample: do the trivial cocycle and the unique order-2 cocycle
on `Q_8` give modular data identifiable under some natural equivalence?

## Files

- [`writeup.md`](writeup.md) — full markdown writeup with the equivalence
  ladder, sector-by-sector decomposition, and verdict.
- [`writeup.tex`](writeup.tex) — same content as a self-contained
  `amsart` LaTeX article, with proper bibliography.
- [`scripts/`](scripts/) — the GAP scripts driving the investigation,
  with their own README explaining how to run them.

## TL;DR

The trivial cocycle and order-2 cocycle on `Q_8` give modular data with:

- **same** T-spectrum,
- **same** Grothendieck (fusion) ring (we exhibit an explicit iso `π_F`
  of order 6),
- but **different** modular tensor category structure: an exact
  backtracking search rules out any permutation aligning `(S₁, T₁)` with
  `(S₂, T₂)`, even with a Galois twist `i ↔ −i`. The full `(N, T)`
  pairs even have different automorphism counts (6 vs 24).

By Mignard–Schauenburg's completeness theorem for `|G| < 32`, this
means `Vec_{Q_8}` and `Vec_{Q_8}^{ω_4}` are not Morita equivalent. So
`Q_8` is **not** a counterexample under the standard reading of
"modular data" as `(S, T)` up to permutation.

The interesting weak observation: the fusion ring alone, or the
T-spectrum alone, *cannot* distinguish them. The entire numerical
difference is concentrated in **one** order-4 conjugacy class, where two
T-eigenvalues swap.
