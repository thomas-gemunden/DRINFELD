# Q_8 modular data: trivial vs order-2 3-cocycle

## Question

Evans–Gannon ([arXiv:1804.11145](https://arxiv.org/abs/1804.11145)) show that
twisted group doubles `D^ω(G)` admit a *trivialising* type-1 module category
(in their language, are "of extension type" with respect to all of `G`)
when `ω = 1`; their Corollary 2 phrases this as: a trivialising type-1 module
category of `D^ω(G)` corresponds to `K ≤ G` and `ψ' ∈ Z²(K)` with `ω|_K` a
coboundary, and `K = G` is automatic for trivial `ω`. The folklore expectation
in the physics community is that this property — equivalently `[ω] = 0 ∈ H³(G)`
— is detectable from the modular data `(S, T)` of `D^ω(G)` alone.

Suspected counterexample: the trivial cocycle and the unique order-2
cocycle on `Q_8 = SmallGroup(8, 4)` produce modular data that look identical
under "a suitable equivalence relation", yet only one of them is
extension-type with `K = G`.

## Verified setup

- `SmallGroup(8, 4) = Q_8` (StructureDescription "Q8"; element-order
  distribution `{1: 1, 2: 1, 4: 6}`; non-abelian; all subgroups normal).
- `H³(Q_8; U(1)) ≅ Z/8` (UCT.exponent = 8, UCT.torsion = `[8]`).
- `Aut(Q_8)` acts trivially on `H³(Q_8)`: 8 orbits, all singletons.
- **File index 1** in `modular_data/8/4/` has cocycle vector `[0,0,0]` whose
  H³-class is `[0,0]` → the **trivial cocycle**.
- **File index 2** has cocycle vector `[0,4,0]` whose H³-class is `[0,4]`,
  the unique class of order 2 → the **order-2 cocycle**.
- Both modular data sets have rank 22 (= 5+5+4+4+4 from the conjugacy-class
  / centralizer-irrep count).
- Cross-checked: fresh-from-scratch GAP runs of `ComputeModularData` for
  cocycles 1 and 2 reproduce the stored `1.txt`, `2.txt` up to permutation
  (the random-row selection in `GenerateModularData` makes ordering
  session-dependent, but the data is content-equivalent).

## Equivalence ladder

| Equivalence relation | Cocycles 1 vs 2 |
|---|---|
| T-spectrum (multiset) | **MATCH**:  `{1×12, −1×4, i×3, −i×3}` |
| S-row multisets | **MATCH** |
| Fusion ring (Grothendieck ring) | **MATCH** — explicit iso `π_F = (6,8)(7,9)(10,12)(11,13)(15,16,17)(19,21)(20,22)`, order 6 |
| Joint (Fusion ring, T-vector) up to permutation | **NO MATCH** — exhaustive search returns 0; \|Aut(N₁,T₁)\| = 6 vs \|Aut(N₂,T₂)\| = 24 (unequal, so non-isomorphic as labelled fusion algebras) |
| Full (S, T) up to permutation | **NO MATCH** — exhaustive backtracking search rules it out |
| (S, T) up to permutation **+** Galois twist `i ↔ −i` on T | **NO MATCH** |

`BasicEquivalentModularDataTests` in `DRINFELD/modular_data.g` returns
`true` here. That heuristic only checks per-T-block sorted S-diagonal
multisets; it does not verify cross-row consistency of S, so it is
genuinely fooled. The exact backtracking search confirms it is wrong on
this pair. (Sanity-checked: the search recovers identity on `(S, T)` vs
itself and recovers the correct shuffle on `(S, T)` vs a known random
permutation of itself.)

## Interpretation: where exactly do the two diverge?

Each row (= simple object) of the modular data has a `(g_class, ρ_dim)`
label, recovered by re-running `GenerateSimpleObjects` and aligning the
deterministic fresh ordering to the stored one with the same backtracking
search.

The simples partition by `g_class`:

| `g_class` | rows in stored data 1 (and data 2) | dim | T-values (data 1) | T-values (data 2) |
|---|---|---|---|---|
| `{1}` (identity) | 1, 2, 3, 4, 5 | 1, 1, 1, 1, 2 | 1, 1, 1, 1, 1 | 1, 1, 1, 1, 1 |
| `{−1}` (centre) | 14, 15, 16, 17, 18 | 1, 1, 1, 1, 2 | 1, 1, 1, 1, −1 | 1, 1, 1, 1, −1 |
| order-4 class A (`cls2`) | 6, 7, 8, 9 | 1, 1, 1, 1 | 1, −1, i, −i | 1, −1, i, −i |
| order-4 class B (`cls3`) | 10, 11, 12, 13 | 1, 1, 1, 1 | 1, −1, i, −i | 1, −1, i, −i |
| order-4 class C (`cls5`) | 19, 20, 21, 22 | 1, 1, 1, 1 | **1, −1**, i, −i | **−1, 1**, i, −i |

So **the entire difference between the two modular data is a swap of two
T-eigenvalues in exactly one g-twisted sector** — the third order-4
conjugacy class. The other two order-4 sectors are completely unaffected
by the twist. Visible at the level of file diff too: `1.txt` vs `2.txt`
differ in T only at positions 19, 20.

This is exactly what one would expect: `Q_8` has `H²(Z/4) = 0`, so the
2-cocycle `β(h,k) = ω(g,h,k) + ω(h,k,g) − ω(h,g,k)` on a cyclic centralizer
is necessarily a coboundary, but the *explicit* coboundary depends on `g`,
and rotates the T-eigenvalues in that sector by a phase. Under `ω = ω_4`,
two of the three order-4 classes get a phase of 0 (mod 1) and one gets a
nontrivial phase.

The fusion ring is unaffected by these phases (fusion coefficients are
non-negative integers — phase-blind), which is why `π_F` exists. The S-matrix
and T-matrix individually carry the phase information, which is why no
joint permutation works.

## Verdict on the original suspicion

**Q_8 is not a counterexample under the standard reading of "modular data".**
If "modular data" means the pair `(S, T)` up to permutation of simples,
Mignard–Schauenburg ([arXiv:1708.06538](https://arxiv.org/abs/1708.06538)) prove that for `|G| < 32` modular
data is a *complete invariant* of `Z(C(G, ω))`. Combined with our explicit
non-existence of a permutation aligning `(S₁, T₁)` and `(S₂, T₂)`, this means
`Z(Vec_{Q_8})` and `Z(Vec_{Q_8}^{ω_4})` are genuinely inequivalent as braided
fusion categories, so `Vec_{Q_8}` and `Vec_{Q_8}^{ω_4}` are not Morita
equivalent. The full `(S, T)` therefore does see the difference.

**Q_8 _is_ a counterexample at strictly weaker invariants.** The fusion
ring (Grothendieck ring) alone identifies the two; even augmenting it with
the T-vector taken as an unordered multiset does not separate them. Anyone
trying to read "extension-type" off the fusion ring by itself, or off the
T-spectrum by itself, would conflate `D^1(Q_8)` and `D^{ω_4}(Q_8)`.

The actual obstruction lives entirely in the third order-4 conjugacy
class, in the relative phase between two simples, and is detectable only
when S and T are read together (or when the T-vector is read jointly with
its index in the fusion algebra).

## Reproducing

The GAP scripts driving this investigation live alongside this file in
[`scripts/`](scripts/) and are individually documented in
[`scripts/README.md`](scripts/README.md). The high-level flow:

```sh
cd scripts/
./setup.sh                                # creates Modular_Data symlink
gap -q -b -c 'Read("verify_q8.g");'       # confirm SmallGroup(8,4) = Q_8
gap -q -b -c 'Read("find_permutation.g");'# exact (S, T) search
gap -q -b -c 'Read("fusion_plus_T.g");'   # joint (N, T) search
gap -q -b -c 'Read("label_simples.g");'   # recover (g, ρ) labels
# ...
```

Any GAP ≥ 4.14 with `hap` and `IO` packages works (Sage's bundled GAP is
fine; standalone GAP via the `gap-system/gap` Homebrew tap is fine).

The actual modular data files live at
`../../modular_data/8/4/{1,2}.txt` from this directory; that data tree
is not under version control because of its size (≈77 GB if exhaustive).
