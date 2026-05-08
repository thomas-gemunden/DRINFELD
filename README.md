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

## Workstream issue dispatch

Active research is structured as parallel workstreams (see
[`extraspecial_orbifolds/parallel_workstreams_design.md`](extraspecial_orbifolds/parallel_workstreams_design.md)
and the execution plan
[`extraspecial_orbifolds/trajectory_c_execution_plan.md`](extraspecial_orbifolds/trajectory_c_execution_plan.md)).
GitHub issues are pre-populated; agents pick up an issue labelled
`ready` and follow the TDD template at
[`docs/superpowers/plans/2026-05-08-issue-T-1-tdd.md`](docs/superpowers/plans/2026-05-08-issue-T-1-tdd.md).

When an agent closes their issue, run

```sh
./scripts/dispatch/relabel_on_close.sh <issue-id>
```

(e.g. `./scripts/dispatch/relabel_on_close.sh Q-1`) to advance any
downstream issues from `blocked` to `ready` once all of *their*
upstream dependencies are closed. The dependency graph is recorded
in [`scripts/dispatch/dependency_graph.json`](scripts/dispatch/dependency_graph.json).

The full set of dispatch scripts lives under
[`scripts/dispatch/`](scripts/dispatch/):

- `_helpers.sh` — shared body-extraction and issue-creation
  functions sourced by the bulk creators.
- `create_epics.sh` — one-shot creator for the 7 workstream
  meta-issues.
- `create_wave_0.sh` — one-shot creator for the 14 ready-from-day-1
  issues.
- `create_remaining.sh` — one-shot creator for the 39 downstream
  issues that begin in the `blocked` state.
- `relabel_on_close.sh` — the auto-promotion hook described above.
- `epic_numbers.txt` — a snapshot of the GitHub epic issue numbers
  for cross-reference.

## References

- Evans, Gannon. *Reconstruction and local extensions for twisted group doubles, and permutation orbifolds.* [arXiv:1804.11145](https://arxiv.org/abs/1804.11145).
- Gruen, Morrison. *Computing modular data for pointed fusion categories.* [arXiv:1808.05060](https://arxiv.org/abs/1808.05060).
- Gruen. *Computing modular data for Drinfeld centres of pointed fusion categories.* B.Phil. thesis, ANU 2017. [PDF](https://tqft.net/web/research/students/AngusGruen/thesis.pdf).
- Mignard, Schauenburg. *Morita equivalence of pointed fusion categories of small rank.* [arXiv:1708.06538](https://arxiv.org/abs/1708.06538). Establishes that modular data is a complete invariant of `Z(C(G, ω))` for `|G| < 32`.
