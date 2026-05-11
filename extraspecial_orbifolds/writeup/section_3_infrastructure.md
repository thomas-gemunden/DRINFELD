# Section 3. Cross-cutting infrastructure (the upgraded Tier-4 pipeline)

**Status.** Draft skeleton — to be expanded subsection by subsection.

This section documents the cross-cutting computational infrastructure
that the kernel and modular-data computations of $\S 4$ and $\S 5$ all
share. The infrastructure has gone through several rebuilds; what is
described here is the version that succeeded in producing
$\ker(\mathrm{Tr})$ for $E_+(2)$ in $\sim 75\,$ seconds and that is the
basis for the $E_+(3)$ kernel run.

---

## 3.1 Setup: the augmented-$\mathbb{Z}$ bottleneck

*The motivation for the rework — why the baseline `IsCoboundary2`
pipeline failed at $E_+(3)$ scale.*

## 3.2 Torsion-split solver (T-1)

*`IsCoboundary2Split` dispatches per centraliser based on the
$H^2$ torsion structure: $\mathbb F_2$-linear algebra on the
order-$2$ piece, Bockstein imaging on the mod-$4$ piece, iterated
Bockstein on higher $2$-torsion.*

## 3.3 SNF wrapper (T-2)

*Smith Normal Form on per-class cocycle-basis matrices to extract
the kernel exactly as a free $\mathbb Z$-module of rank
${\rm rank} - r$.*

## 3.4 BRW symmetry reduction (T-3a/b/c/d)

*The outer Brauer–Reynolds–Witt normaliser $\mathrm{BRW}(m)$ acts
compatibly on conjugacy classes and on $H^3$; transgression
evaluation reduces to one representative per BRW orbit (4 orbits
for $E_+(3)$ from 65 classes).*

## 3.5 Centraliser-type cache (T-4)

*A single `ResolutionFiniteGroup` per `IdGroup`-isomorphism class,
shared across the orbit representatives that have the same
centraliser type.*

## 3.6 Resumable per-generator state (T-5)

*Each completed generator is appended to a state file; on restart
the state is parsed and the solver skips already-finished
generators.*

## 3.7 Verified anchor

*End-to-end driver `run_e_plus_2_kernel.g` produces
$|\ker \mathrm{Tr}| = 2048$ on the new pipeline in $\sim 1\,$ min
$15\,$ s. `run_e_plus_3_kernel.g` is the analogous driver for
$E_+(3)$.*

---
