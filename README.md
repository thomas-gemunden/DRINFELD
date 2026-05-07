# DRINFELD

Code and notes for computing modular data of twisted Drinfeld doubles
`D^ω(G) = Z(Vec_G^ω)` of finite groups, and for investigating when this
modular data detects categorical / VOA-theoretic invariants such as
"extension type" in the sense of Evans–Gannon
([arXiv:1804.11145](https://arxiv.org/abs/1804.11145)).

The original goal: *work out how to detect whether the module category
of an orbifold VOA is untwisted.*

## Contents

| Path | What |
|---|---|
| [`src/modular_data.g`](src/modular_data.g) | Gruen / Gruen–Morrison GAP code computing `(S, T)` for `Z(Vec_G^ω)`. The main pipeline. ([Gruen thesis](https://tqft.net/web/research/students/AngusGruen/thesis.pdf), [Gruen–Morrison arXiv:1808.05060](https://arxiv.org/abs/1808.05060)) |
| [`src/universal_coefficients.g`](src/universal_coefficients.g) | Mignard–Schauenburg helper code for cohomology + projective characters + FS-indicators. ([arXiv:1708.06538](https://arxiv.org/abs/1708.06538)). Note: `GaugeInvariants` and `FSIforAGT` have lingering bugs (undeclared variables, typos); treat them as a reference for the math, not as runnable code. |
| [`q8_extension_type/`](q8_extension_type/) | An investigation of whether `Q_8`'s order-2 cocycle gives a counterexample to "modular data detects extension type". Includes a markdown and LaTeX writeup, plus 10 GAP scripts. The verdict: not at the level of full `(S, T)` (Mignard–Schauenburg's completeness is preserved), but the fusion rings do coincide. |

## The data

The modular-data database (precomputed `(S, T)` for groups up to order
~168, indexed by the GAP `SmallGroup(n, m)` library) lives **outside**
this repository, as a sibling directory `../modular_data/`. It is
roughly 77 GB and is not a good candidate for git. Each leaf
`../modular_data/n/m/k.txt` is a self-contained GAP source file:

```gap
data := ReadAsFunction("Modular_Data/n/m/k.txt")();;
# data.S is the S-matrix; data.T is the diagonal of the T-matrix.
```

The naming convention (capital `Modular_Data` from the current working
directory) is hard-coded into Gruen's `LoadModularData(n, m, k)`. Most
scripts in this repo therefore expect a symlink or a same-named tree
visible from CWD; the investigation directories include a `setup.sh`
that creates this symlink.

## Quick start

```sh
# any GAP >= 4.14 with the hap and IO packages
gap -q -b
gap> Read("src/modular_data.g");
gap> data := ComputeALittleData(8, 4, 1);;   # Q_8, trivial cocycle
gap> Display(data.T);
```

For the `Q_8` investigation specifically:

```sh
cd q8_extension_type/scripts
./setup.sh
gap -q -b -c 'Read("verify_q8.g");'
```

## References

- Evans, Gannon. *Reconstruction and local extensions for twisted group doubles, and permutation orbifolds.* [arXiv:1804.11145](https://arxiv.org/abs/1804.11145).
- Gruen, Morrison. *Computing modular data for pointed fusion categories.* [arXiv:1808.05060](https://arxiv.org/abs/1808.05060).
- Gruen. *Computing modular data for Drinfeld centres of pointed fusion categories.* B.Phil. thesis, ANU 2017. [PDF](https://tqft.net/web/research/students/AngusGruen/thesis.pdf).
- Mignard, Schauenburg. *Morita equivalence of pointed fusion categories of small rank.* [arXiv:1708.06538](https://arxiv.org/abs/1708.06538). Establishes that modular data is a complete invariant of `Z(C(G, ω))` for `|G| < 32`.
