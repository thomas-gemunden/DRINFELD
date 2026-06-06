# K-4b m=7 Deep Performance Audit — Closed-Form Bypasses

**Date:** 2026-06-06
**Branch:** `k4b-m7-deep-perf-audit-447`
**Scope:** the full K-4b m=7 call chain from `run_k4b_m7.sh` down through `BuildKRRSpectralCharactersSparse(7)`, `BuildSimpleIndexLazy(EmUnimodGroup(7))`, the per-class trace machinery, and the post-spectral E/D_8/Q_8 branches.
**Trigger:** K-4b m=7 production has OOM'd twice during `BuildSimpleIndexLazy(EmUnimodGroup(7))` while GAP's generic `ConjugacyClasses(G)` for a degree-128 unimodular matrix group consumed >48 GB. Issue #447 spec dispatched two perf agents (Change A = closed-form CC; Change B = BRW-orbit Tr collapse). The user wants a broader audit identifying every other place in the call chain where generic GAP/HAP is doing computation we could short-circuit with closed-form / structural knowledge of `E_+(m)`.

## TL;DR

The K-4b m=7 pipeline has **one strict blocker** (Tier-A) and a stack of large opportunistic wins below it. Issue #447 Change A (the closed-form CC enumerator) IS the Tier-A blocker — m=7 is infeasible until `ConjugacyClasses(EmUnimodGroup(7))` is replaced by a direct enumeration based on `predict_e_plus_m.g` / `compute_e_plus_7_T_analytical.g`'s sector structure. Issue #447 Change B (BRW-orbit Tr collapse, already in flight on this branch) drops Step 3/4 from 16385 trace evals to 4. After both land the call chain has another **eight 5×–500× wins** sitting in the `BuildSimpleIndexLazy` / `_BuildTraceCtx` / restriction / matcher layers that compound to make m=7 production not just feasible but quick.

### Top 5 findings

1. **A1 — `ConjugacyClasses(EmUnimodGroup(7))` OOM** (the #447 Change A target) — must be replaced by a closed-form sector enumerator based on `compute_e_plus_7_T_analytical.g`. Without this, m=7 is impossible at any budget.
2. **A2 — `BuildSimpleIndexLazy` calls `Centralizer(G, x)` per class rep** (~16385 calls at m=7). Closed-form: centralisers of `E_+(m)` elements are determined by the BRW orbit type and m alone (`id/-id` → G itself; `sigma2` → `Z_2 × E_+(m-1)`; `sigma_1 sigma_2` → `Z_4 ∘ E_+(m-1)`). Three groups total, computed once.
3. **A3 — `_BuildTraceCtx`'s `BPi^T` row reduction is a P5/P3 hot mess.** The augmented-matrix RREF at line 134-153 uses `List([1..2*n], i -> ...)` per pivot row over 2n=256 columns at m=7, in interpreted bytecode. Should use compiled `TriangulizeMat` on a GF(2)-tagged matrix. Already flagged as **A-K4-2** in the 2026-06-02 audit but NOT shipped.
4. **B1 — `_RTS_FindGClassOf` does `RepresentativeAction(G, a_H, idx_G.reps[k_G])` per H-class.** For the D_8/Q_8/EA detecting subgroups this calls into GAP's pc-group orbit-stabiliser machinery on degree-128 matrices once per H-class. Closed-form: for `E_+(m)`, every conjugator either is `1` (central class) or has order 2 in `BRW(m)/E_+(m)` and can be found by a single explicit BRW generator lookup.
5. **B2 — `TranslateSpectralDataToEPlus` rebuilds another `BuildSimpleIndexLazy(EPlusGroup(7))`** on the EP-side and a `BuildSimpleIndexLazy` for each detecting subgroup H. The EP-side is the SAME conjugacy class structure as the EU-side (psi-equivariant); a class-permutation map suffices. Net: 3 additional copies of the 16385-class enumeration get built on the K-4b m=7 path after the EU-side bypass lands.

### Other Tier-A blockers found (beyond closed-form CC)?

**Yes — one.** Finding **A3** (the manual `BPi^T` row-reduction in `_BuildTraceCtx`) is on the m=7 hot path: at 4 trace evaluations per `BuildKRRSpectralCharactersSparse(7)` (after #447 Change B), each calls `_BuildTraceCtx` once, each row-reduction is a 128×256 augmented matrix in interpreted GAP. This is not OOM-level but is the new dominant cost after Changes A+B; the audit found this is a 5–10× slowdown vs `TriangulizeMat`-with-GF(2)-tagging. Already a Tier-A finding in the 2026-06-02 audit (A-K4-2) but NOT shipped — I am marking it as a Tier-A here too because the cost surfaces visibly at m=7.

The OTHER post-spectral Tier-A surfaces in the **detecting-subgroup E branch** at m=7: `_K4A_ClassifyEBranchMulti` iterates the 8 EAs from `LoadDVANEAFamily(7)` and calls `ComputeModularData(H_EA, omega_H_fn, val, expon)` per EA, which under default opts is the |H|^4 = 65536 S-matrix build PER EA. PR #437's `_K4A_USE_FAST_ABELIAN_BRANCH = true` switches this to `ClassifyAbelianBranchFast` (the q_ω + b_ω closed form, O(|H|^2) = 16384) but is OPT-IN and the K-4b m=7 driver does NOT set it. That's a missing one-line config that unblocks ~256× speedup on the E branch.

---

# 1. Call chain skeleton

```
run_k4b_m7.sh                                            (shell driver)
  └─ gap -q -b -o 48g -c '...'                           (one-shot session)
      ├─ Read("src/modular_data.g")
      ├─ Read("k4a_classify.g")
      └─ K4aClassify(7)                                  (k4a_classify.g:726)
          ├─ KellerTwistIsTrivial(7, ω=fail)             (skipped: ω = 0)
          ├─ BuildKRRSpectralCharactersSparse(7)         (krr_spectral_characters_sparse.g:1142)
          │   ├─ EmUnimodGroup(7)                        (krr_spectral_characters.g:100)
          │   ├─ BuildSimpleIndexLazy(G)                 ★ OOM HERE ★
          │   │   ├─ ConjugacyClasses(G)                 — A1 (Change A) #447
          │   │   ├─ List(reps, x -> Centralizer(G, x))  — A2
          │   │   ├─ List(centralisers, NrConjugacyClasses) — A2 (transitively cheap)
          │   │   └─ build offset / lookup tables        — fine
          │   ├─ for i in [1..16385] do
          │   │     if reps[i] = z then
          │   │         CentraliserClassData(idx, i)     — calls ConjugacyClasses(G) AGAIN
          │   │         _SparseClassifyEmBRWTypes(...)   — Change B (shipped on branch)
          │   │         for each of 4 orbit-types:
          │   │             TraceOnOmega0(h_rep, 7)
          │   │                 ├─ _BuildGaussCtx(h, 7)
          │   │                 │   ├─ _BuildTraceCtx(h, 7)
          │   │                 │   │   ├─ BasisForN(7), TwoCocycleForN(7)
          │   │                 │   │   ├─ MhHalfefMat(h, 7), Kernef(h, 7)
          │   │                 │   │   ├─ _efPerHData(h, 7), _efShAndTarget(h, 7)
          │   │                 │   │   └─ ★ manual BPi^T RREF over GF(2)  — A3
          │   │                 │   └─ build Q via F2_Mul chains           — fine
          │   │                 └─ TraceOnOmega0Gauss(h, 7)
          │   │                     ├─ _F2_AffineSolveCols(F + BT, ...)    — interp RREF, B0
          │   │                     └─ _F2_FastSymplecticBasis(B_psi)      — already O(d^3) closed form
          │   │         CharacterMultiplicities(idx, i, cls_data, traces)  — Step 4
          │   │     fi
          │   │   od
          │   └─ build trace_on_W closure
          ├─ MaximalElementaryAbelian_E_plus(7)
          │   └─ BuildElementaryAbelianDirect_E_plus(G, 7) — Comm() + greedy
          ├─ TranslateSpectralDataToEPlus(sparse, ea_rec.parent)
          │   ├─ EmEPlusTranslate(7) / EmEPlusTranslateAgainst(7, EP) — GroupHomomorphismByImages
          │   ├─ BuildSimpleIndexLazy(ep_group)           ★ ANOTHER 16385-class enum ★ — B2
          │   ├─ for each EP-class: Image(psi_inv, rep_ep); membership in eu_classes
          │   └─ BuildTransportsLazy(idx_EP)              — fine until materialised
          ├─ RestrictTraceOnWToSubgroupHonourParent(data_E, H_EA)
          │   ├─ BuildIntertwinerDataUntwisted(H_EA)
          │   │   └─ BuildSimpleIndex(H_EA)               — small (~16) OK at H=2^8
          │   ├─ for each H_EA-class:
          │   │     _RTS_FindGClassOf(idx_G, a_H, G)      — B1: linear scan + RepresentativeAction
          │   ├─ RestrictedIrrepDecomposition per class   — char inner product
          │   └─ (multiplicity_lookup setup)
          ├─ ComputeCTModularData(restricted_E, H_EA)
          │   ├─ _CTComputeSBlock(intertwiner_data, i, j) — Ni × #commuting × Nj evaluations
          │   └─ T-diag via trace_on_W per simple
          ├─ JointPermutationMatcher / ClassifyAbelianBranchFast
          ├─ D8Section_E_plus(7)                          — gens_G[1], gens_G[2]; fast
          ├─ <repeat translate + restrict for D8 > — three copies
          ├─ Q8Section_E_plus(7)
          └─ <repeat translate + restrict for Q8 >
```

The asterisked ★ rows are where m=7 cannot finish under the current implementation.

The "fine" markers represent calls whose cost is dominated by other work in the chain and are not in the audit's critical path.

---

# 2. Tier-A findings: must-fix bypasses

## A1 — `ConjugacyClasses(EmUnimodGroup(7))` enumeration OOM ⟶ closed-form sector enumerator

**Already specced as Change A of issue #447. Including here for completeness; this is the strict blocker.**

**Location:**
- `extraspecial_orbifolds/scripts/untwisted_modular_data.g:119` (`BuildSimpleIndexLazy`)
- via `extraspecial_orbifolds/scripts/krr_spectral_characters_sparse.g:1164` (`BuildSimpleIndexLazy(G)` at `m=7`)

**Current shape:**
```gap
classes := ConjugacyClasses(G);
reps := List(classes, Representative);
class_sizes := List(classes, Size);
```

For `G = EmUnimodGroup(7)`, this calls into GAP's generic conjugacy-class enumeration. GAP routes pc-group / permutation-group conjugacy enumeration through `claspcgs.gi:33` (per the OOM stack trace in `extraspecial_orbifolds/perf/raw/k4b/k4b_m7_20260605_213744Z.log`), which iterates the whole group with `ExponentsOfPcElement` per element. For `|G| = 2^15 = 32768` over a degree-128 matrix realisation, this consumes >48 GB.

**Closed-form replacement that already exists:**

`extraspecial_orbifolds/scripts/compute_e_plus_7_T_analytical.g` documents the FULL E_+(m)-conjugacy class structure:
- 1 singleton class `{1}` (identity)
- 1 singleton class `{-1}` (central involution)
- `2^{2m-1} + 2^{m-1} - 1` size-2 order-2 non-central classes
- `2^{2m-1} - 2^{m-1}` size-2 order-4 non-central classes

So `num_classes(E_+(m)) = 2 + (4^m - 1) = 4^m + 1`. At m=7: `16385`.

`predict_e_plus_m.g:5-22` documents the centralisers:
- For `{1}` and `{-1}`: centraliser is G itself (`|Irr| = 4^m + 1`)
- For order-2 non-central g: centraliser is `Z_2 × E_+(m-1)` (`|Irr| = 2 · 4^{m-1} + 2`)
- For order-4 non-central g: centraliser is `Z_4 ∘ E_+(m-1)` (`|Irr| = 2 · 4^{m-1} + 2`)

Both of these are exactly what `BuildSimpleIndexLazy` needs.

**Effort:** ~250 LOC in a new file `e_plus_conjugacy_classes_closed_form.g` providing:
- `EPlusConjugacyClassReps(G, m)` — return the `4^m + 1` class reps via direct construction (z and identity from the centre; non-central reps via two enumerated families of bit-encoded normaliser cosets per the symplectic-form classification of `BWGram`'s `F2Mod`).
- `EPlusCentraliserOf(G, m, class_type)` — return one of three pre-cached groups (G itself, `Z_2 × E_+(m-1)`, `Z_4 ∘ E_+(m-1)`).
- `EPlusClassSize(class_type)` — 1 or 2.
- An `EPlusBuildSimpleIndexLazy(G, m)` wrapping the three above into the existing schema.

**Estimated win at m=7:**
- OOM → ~5 seconds for the index build (the entire 16385-class structure pre-computed in O(n) time using the closed form, plus ~3 cached centralisers).
- Memory: ~50 MB for 16385 class reps (vs >48 GB for the generic enumeration).
- Without this, the rest of the audit's wins are unrealised.

**Mathematical citation:**
- Keller-Roberts-Roberts (arXiv:2411.13646), Prop 3.1.
- `predict_e_plus_m.g` (head-of-file derivation, applies to all m).
- `compute_e_plus_7_T_analytical.g` (m=7-specific aggregation).

---

## A2 — `Centralizer(G, x)` called per class rep ⟶ orbit-type-keyed cache

**Location:**
- `extraspecial_orbifolds/scripts/untwisted_modular_data.g:122` (`BuildSimpleIndexLazy`):

```gap
centralisers := List(reps, x -> Centralizer(G, x));
```

**Why it's a perf hit even after A1:**

Even after A1 ships and `reps` is the closed-form list of 16385 class representatives, the next line calls `Centralizer(G, x)` for each one. `Centralizer` on a pc-group / matrix group of order 2^15 is internally driven by another orbit-stabiliser run; for 16385 separate calls, this could OOM AGAIN unless we bypass it.

**Closed-form replacement:**

There are only **three** distinct centralisers across the 16385 classes:
1. `id` and `minus_one` classes (2 classes): `Centralizer(G, x) = G`.
2. `sigma2`-type non-central classes (`2^{2m-1} + 2^{m-1} - 1` classes): `Centralizer(G, x) ≅ Z_2 × E_+(m-1)`. Construct ONCE.
3. `sigma_1 sigma_2`-type non-central classes (`2^{2m-1} - 2^{m-1}` classes): `Centralizer(G, x) ≅ Z_4 ∘ E_+(m-1)`. Construct ONCE.

But the BSi/lazy machinery only uses the centraliser for:
- `NrConjugacyClasses(centralisers[i])` — these are pre-determined: `4^m + 1` for cases 1, `2*4^{m-1} + 2` for cases 2-3.
- (Later) `CharacterTable(centralisers[i])` — only for the central class, lazy.
- (Later) `ConjugacyClasses(C)` for class-function evaluation (called by `CentraliserClassData` at krr_spectral_characters_sparse.g:1018).

So for the K-4b m=7 spectral path, the only centraliser that gets materialised is `G itself` (since only the central class -I is processed in the per-class loop). The other 16384 entries of `idx.centralisers` are NEVER touched — but `BuildSimpleIndexLazy` builds them all eagerly anyway.

**Effort:** Modify `BuildSimpleIndexLazy` (or provide a new variant `BuildSimpleIndexEPlusLazy`) such that `centralisers[i]` is itself a lazy thunk keyed by `class_types[i]`, materialising on access. ~30 LOC.

**Estimated win at m=7:**
- Pre-shipped Change B (orbit collapse): only 1 of 4 centraliser types is ever needed (the `id/minus_one` case = G itself, already known).
- Saves 16384 `Centralizer(G, x)` calls. At even ~10 ms each = ~3 minutes wall savings AND the memory cost (each non-trivial centraliser is ~10-100 MB at m=7) that contributes to the OOM cliff.
- Without this, even the closed-form CC enumerator might OOM on the centraliser build.

**Cross-ref:** This is closely related to but NOT redundant with A1 — A1 fixes the class enumeration; A2 fixes the centraliser build. Both must ship together for m=7 to finish.

---

## A3 — Manual GF(2) RREF in `_BuildTraceCtx` ⟶ compiled `TriangulizeMat`

**Already flagged as `A-K4-2` in `extraspecial_orbifolds/docs/superpowers/research/2026-06-02-orthogonal-perf-paths-audit-dvan-k4.md`.** Including here because at m=7 it becomes the dominant per-trace cost after #447 Changes A and B ship.

**Location:**
- `extraspecial_orbifolds/scripts/krr_spectral_characters_sparse.g:130-153` (`_BuildTraceCtx` row reduction loop).

**Current shape (line 134-153):**
```gap
BPiT := F2_Trans(BPi);  # n x n
A2 := List([1..n], i -> Concatenation(BPiT[i], IdentityMat(n)[i]));
r := 1;
pivCols := [];
pivRows := [];
for c in [1..n] do
    if r > n then break; fi;
    i := r;
    while i <= n and A2[i][c] = 0 do i := i + 1; od;
    if i > n then continue; fi;
    if i <> r then A2{[r, i]} := A2{[i, r]}; fi;
    for j in [1..n] do
        if j <> r and A2[j][c] = 1 then
            A2[j] := List([1..2 * n],
                          i -> (A2[j][i] + A2[r][i]) mod 2);   # ★ P3 ★
        fi;
    od;
    Add(pivCols, c);
    Add(pivRows, r);
    r := r + 1;
od;
```

At m=7: n=128, so this is a 128 × 256 augmented matrix being row-reduced via interpreted `List([1..2*n], i -> (A2[j][i] + A2[r][i]) mod 2)` — that's a P3 anti-pattern (CLAUDE.md anti-pattern catalogue):

> WRONG:
> ```gap
> A2[j] := List([1..2 * n], i -> (A2[j][i] + A2[r][i]) mod 2);
> ```
> RIGHT (per CLAUDE.md P3):
> ```gap
> A2[j] := (A2[j] + A2[r]) mod 2;
> ```

Even better, tag as GF(2) and use compiled `TriangulizeMat`:

```gap
A2 := List(A2, row -> row * Z(2)^0);  # GF(2) tag
ConvertToMatrixRep(A2, GF(2));
TriangulizeMat(A2);                    # compiled RREF
# Recover pivCols, solveMap, feasMat from the now-reduced A2.
```

**Effort:** ~50 LOC rewrite, plus careful conversion of `solveMap` / `feasMat` extraction. Test against existing m=3 / m=5 known-good outputs.

**Estimated win at m=7:**
- Per-trace cost of `_BuildTraceCtx` at m=7: currently dominated by this RREF.
- A clean compiled-RREF version is 5–15× faster than the interpreted version on a 128 × 256 GF(2) matrix (per the 2026-06-02 audit's measurements at smaller m).
- After #447 Changes A+B, `BuildKRRSpectralCharactersSparse(7)` only invokes `_BuildTraceCtx` 4 times (one per BRW orbit type). So absolute wall savings is small (~few seconds), but unblocks any future change that needs to invoke `_BuildTraceCtx` on more h values (e.g. ε ≠ 1 follow-up).

**Cross-ref:**
- The same anti-pattern is duplicated in `_F2_AffineSolveCols` (krr_spectral_characters_sparse.g:524-575) and `F2_SolveRowEq` (defect_rep_minus_id.g:60-98). Both are called by `TraceOnOmega0Gauss` per orbit-type trace eval. Same compiled-`TriangulizeMat` replacement applies.

---

# 3. Tier-B findings: 5-50× wins on top of #447

## B1 — `RepresentativeAction(G, a_H, idx_G.reps[k_G])` in `_RTS_FindGClassOf` ⟶ orbit-type lookup

**Location:**
- `extraspecial_orbifolds/scripts/restrict_to_subgroup.g:243-273` (`_RTS_FindGClassOf`).

**Current shape:**
```gap
_RTS_FindGClassOf := function(idx_G, a_H, G)
    local k, conj;
    for k in [1..Length(idx_G.classes)] do
        if a_H in idx_G.classes[k] then
            conj := RepresentativeAction(G, a_H, idx_G.reps[k]);   # ★
            ...
            return rec(k_G := k, conj := conj);
        fi;
    od;
    Error(...);
end;;
```

Called once per H-class by:
- `RestrictTraceOnWToSubgroup` (line 334) — H = EA, D_8, or Q_8.
- `RestrictTraceOnWToSubgroupHonourParent` (line 607).
- `RestrictTraceOnWToSubgroupProjective` (line 952).

At m=7 with the 8-EA family + D_8 + Q_8, this is `(8 × 256 + 8 + 8) = 2064` `RepresentativeAction` calls, each on degree-128 matrices over the parent G with 32K elements.

**Why it's wasteful given closed-form CC:**

After A1 (closed-form class structure), we know the class of `a_H` directly: it's determined by `Order(a_H)` and whether `a_H` is central in G:
- `a_H = 1` → class `{1}`, conj = 1.
- `a_H = -1` → class `{-1}`, conj = 1.
- `Order(a_H) = 2`, central in `E_+(m)` (i.e., `a_H = -1`) → handled above.
- `Order(a_H) = 2`, non-central → one of the `2^{2m-1} + 2^{m-1} - 1` size-2 classes. The class index is `BRW(m)`-determined via the symplectic-form action.
- `Order(a_H) = 4` → one of the size-2 order-4 classes.

The conjugator is one element of a BRW(m)/E_+(m) coset; for ANY two representatives in the same E_+(m)-class, the conjugator can be read directly from the BRW(m) generators (`brw_construction.g`).

Actually, the issue is more subtle: `RestrictTraceOnWToSubgroup` uses `conj` to evaluate `conj * x * conj^-1` for `x in C_H(a_H)` during the restriction's irrep-decomposition. So `conj` MUST be in `G` (not BRW), and must be a specific element conjugating `a_H` to `idx_G.reps[k_G]`. But under the closed-form CC enumeration, `idx_G.reps[k_G]` is THE element produced by our class enumerator — so picking `conj` is a problem in `E_+(m)/<a_H>`, which is solvable analytically.

**Effort:**
- ~150 LOC `_RTS_FindGClassOfEPlus(idx_G, a_H, m)` that does:
  - Match `a_H` against the closed-form representatives by orbit-type lookup.
  - Compute `conj` directly via the symplectic-form structure of `E_+(m)/Z(E_+(m))` (a search over `2^{2m}` cosets, but feasible at m=7 since `2^{14} = 16384`).
- Use it ONLY when `idx_G.is_closed_form` is set (the new flag from A1).
- Backward compat: when not set, fall back to the existing `_RTS_FindGClassOf` (m ≤ 5 keeps working).

**Estimated win at m=7:**
- Per call: ~1 ms (orbit-type lookup + symplectic conjugator search) vs ~50-500 ms (RepresentativeAction on |G|=32K).
- Per K-4a sweep: 2064 calls × ~100 ms = ~3.4 minutes saved per K-4b m=7 run, on the post-spectral E/D_8/Q_8 branches.

**Mathematical citation:** Implicit in `brw_conjugacy_action.g`'s BRW-as-O+(2m, F_2) classification.

---

## B2 — `TranslateSpectralDataToEPlus` rebuilds `BuildSimpleIndexLazy(EPlusGroup(7))` ⟶ class-index permutation

**Location:**
- `extraspecial_orbifolds/scripts/em_eplus_translate.g:433` (`idx_EP := BuildSimpleIndexLazy(ep_group)`).
- Called three times in `K4aClassify(7)`: once per detecting branch (E_EA, D_8, Q_8).

**Current shape:**
```gap
# em_eplus_translate.g
idx_EP := BuildSimpleIndexLazy(ep_group);                            # rebuild EP-side index
# Build the EP -> EU class index map.
idx_EU := spectral_data_eu.idx;
eu_classes := idx_EU.classes;
ep_to_eu_class := [];
for k_ep in [1..Length(idx_EP.reps)] do
    rep_ep := idx_EP.reps[k_ep];
    rep_eu := Image(tr_rec.psi_inv, rep_ep);
    k_eu := fail;
    for j in [1..Length(eu_classes)] do
        if rep_eu in eu_classes[j] then
            k_eu := j;
            break;
        fi;
    od;
    ...
    Add(ep_to_eu_class, k_eu);
od;
```

After A1 ships for `EmUnimodGroup`, calling `BuildSimpleIndexLazy(EPlusGroup(7))` would ALSO need to be funneled through the closed-form path (otherwise we hit the SAME OOM on the EP-side, since `EPlusGroup(m) = ExtraspecialGroup(2^(2m+1), "+")` has the same conjugacy class structure as `EmUnimodGroup(m)`).

**Closed-form replacement:**

The EU↔EP isomorphism `psi` is an explicit map between two GAP families of the same abstract group `E_+(m)`. The class structure on both sides is the same (`4^m + 1` classes, same orbit-types). The class-index permutation `ep_to_eu_class[k_EP]` can be computed as follows under the closed-form path:
1. For each EP-class rep `rep_ep`, classify its orbit type via `Order(rep_ep)` + central-or-not test (analytical lookup, O(1)).
2. The corresponding EU-class is determined by the SAME orbit-type label, with the within-orbit position determined by `psi` applied to the symplectic-basis representative.

Net: `ep_to_eu_class` can be built in O(num_classes × log(num_classes)) without ever calling `BuildSimpleIndexLazy` on the EP-side.

**Effort:** ~80 LOC: `_EET_ClassIndexMap_ClosedForm(m, psi, idx_EU, ep_group)` returning the permutation. Plumb a flag through `TranslateSpectralDataToEPlus` to use this path when `idx_EU.is_closed_form`.

**Estimated win at m=7:**
- Avoids one full `BuildSimpleIndexLazy(EPlusGroup(7))` per K-4b run (called 3 times in `K4aClassify` for E/D_8/Q_8) = 3 instances of the 16385-class build.
- Without this, the EP-side rebuild becomes the SECOND OOM cliff (or, with closed-form on EP-side too, ~5 sec × 3 = 15 sec saved).

---

## B3 — `RestrictedIrrepDecomposition`'s irrep inner products ⟶ Bantay closed form

**Location:**
- `extraspecial_orbifolds/scripts/restrict_to_subgroup.g:410-481` (`RestrictedIrrepDecomposition`).
- `extraspecial_orbifolds/scripts/restrict_to_subgroup.g:655-679` (the calling loop in `RestrictTraceOnWToSubgroupHonourParent`).

**Current shape:**
```gap
for j in [1..n_classes_H] do
    cls_H := cc_H[j];
    rep_h := Representative(cls_H);
    phi_rep := conj * rep_h * conj^-1;
    cls_idx_G := ClassIndexInCentraliser(idx_G, k_G, phi_rep);   # member-of-class search
    Add(chi_G_phi_values, cls_idx_G);
    Add(class_size_h, Size(cls_H));
od;
# Then per j_G:
chi_G_vals := List([1..n_classes_H], t -> idx_G.irreps[k_G][j_G_arg][chi_G_phi_values[t]]);
result := [];
for l_H in [1..num_irreps_H] do
    acc := 0;
    chi_l_H := irr_H[l_H];
    for t in [1..n_classes_H] do
        ...
        acc := acc + class_size_h[t] * val_chi_g * ComplexConjugate(val_chi_l);
    od;
    acc := acc / normaliser;
    ...
od;
```

**Why it's wasteful:**

For the K-4b m=7 path, the parent G is `EPlusGroup(7)`. The H-subgroup is either an EA (rank 8), D_8, or Q_8. The decomposition of `Res^G_H chi_G` is computed via the standard Frobenius reciprocity inner product over H-conjugacy classes. For the E_+(m) family this is closed-form: the irreps of E_+(m-1)-style centralisers have known restriction patterns to their subgroups (see KRR Section 3).

But more concretely: the current implementation calls `Representative(cls_H)`, `conj * rep_h * conj^-1` (a matrix conjugation at m=7), and `ClassIndexInCentraliser` (which materialises the centraliser's CT) per H-centraliser-class. At m=7 with H=EA (rank 8) we have 256 H-centraliser classes per EA × 8 EAs = ~2048 per-class operations.

**Closed-form replacement:**

For abelian H, every irrep is 1-dimensional, so the H-centraliser of any h in H is H itself, and every H-class is a singleton. The Frobenius reciprocity inner product collapses to:
- For chi_l_H a 1-dim character of H, the multiplicity is `<chi_G|_H, chi_l_H>_H = #{h in H : chi_G(conj * h * conj^-1) = chi_l_H(h)} / |H|`.
- This is the Pontryagin dual evaluation of `chi_G|_H` against H's character group, which is O(|H|) total work, not O(|Irr(C_G(a_G))| × |classes(C_H(a_H))|).

For H = D_8 / Q_8, the irrep theory is small enough (5 irreps each) that the full multiplicity table can be hardcoded.

**Effort:** ~80 LOC for the abelian-H closed-form; ~50 LOC for D_8/Q_8 hardcoding. Total ~130 LOC.

**Estimated win at m=7:** ~3-5× per restriction call. After A1+B1, this is the next bottleneck on the K-4b m=7 post-spectral path.

---

## B4 — `_CTComputeSBlock` per-irrep trace evaluations ⟶ batched chi_at_class lookup

**Already flagged as `A-K4-4` in `2026-06-02-orthogonal-perf-paths-audit-dvan-k4.md` (Tier B).** Surfacing here because at m=7 it interacts with the spectral data shape.

**Location:** `extraspecial_orbifolds/scripts/ct_modular_data.g:115-198` (`_CTComputeSBlock`).

**Current shape (inner loop):**
```gap
for k in [1..Ni] do
    for l in [1..Nj] do
        M[k][l] := M[k][l]
            + ComplexConjugate(intertwiner_data.trace_on_W(i, k, b_tilde))
            * ComplexConjugate(intertwiner_data.trace_on_W(j, l, a_tilde));
    od;
od;
```

Per (a, b) commuting pair, `Ni × Nj` `trace_on_W` calls. At m=7 with H=EA (|H| = 256, ~64 H-classes), and Ni = Nj = ~258 = `2*4^(7-1)+2`, this is ~258² = ~66500 trace evals per (a,b) pair × O(|H|²/|H|) commuting pairs = millions of evals per S-block.

**Closed-form replacement:**

`trace_on_W(i, k, b_tilde)` is just `EvalIrr(idx, i, k, b_tilde)` on non-central classes. The per-(i, b_tilde) value vector `(EvalIrr(idx, i, k, b_tilde) for k in [1..Ni])` is just `idx.irreps[i][*][ClassIndexInCentraliser(idx, i, b_tilde)]`. So:
- Pre-compute `b_tilde_class_idx = ClassIndexInCentraliser(idx, i, b_tilde)` ONCE per (i, b_tilde).
- Look up `chi_vec_b = idx.irreps[i][*][b_tilde_class_idx]` ONCE per (i, b_tilde).
- The inner loop becomes a vector outer product: `M += conj(chi_vec_b) * conj(chi_vec_a)^T`.

**Effort:** ~80 LOC refactor of `_CTComputeSBlock` to extract `chi_vec_at_class(i, b_tilde)`. ~30 LOC if we accept caching by `b_tilde` only (not (i, b_tilde)).

**Estimated win at m=7:** ~Ni × Nj / Ni = Nj ≈ 256× per S-block. Vector outer product also benefits from compiled GAP matmul.

---

## B5 — `ClassifyAbelianBranchFast` opt-in flag missing from K-4b m=7 driver

**Location:** `extraspecial_orbifolds/scripts/run_k4b_m7.sh:164-235` (GAP one-liner inside the driver).

**Current shape:**

The driver does NOT set `_K4A_USE_FAST_ABELIAN_BRANCH := true`, so `K4aClassify(7)` invokes the slow O(|H|^4) `ComputeModularData` per EA on the E branch.

PR #437 landed `ClassifyAbelianBranchFast` (~500× speedup at |EA|=8 measured at m=2). Per the active-job-graph (`2026-06-03-active-job-graph.md` Stage 3-F'), the fast path is intended to be enabled for m=7 production via a one-line opt-in.

**Effort:** Add to the GAP one-liner in `run_k4b_m7.sh`:
```gap
_K4A_USE_FAST_ABELIAN_BRANCH := true;;
```
3 lines including a Print() audit log.

**Estimated win at m=7:** At |EA| = 256 (m=7 EA rank 8), the slow path is O(|H|^4) = 4×10^9 entries on the S matrix. The fast path is O(|H|^2) = 65536. With 8 EAs in the K-4 detecting family, that's ~32× per EA × 8 EAs = ~256× total speedup of the E branch.

**Caveat:** Per the job-graph's Stage 2-F precondition, this requires that PR #437 has been cross-validated at m=5 first (B' in the graph). If that's done, enabling at m=7 is trivial; if not, this finding is gated on Stage 2.

---

## B6 — `_BuildGaussCtx`'s `feasMat` row-by-row column slice is a closure ⟶ compiled slice

**Location:** `extraspecial_orbifolds/scripts/krr_spectral_characters_sparse.g:622-628`.

**Current shape:**
```gap
X_mat := NullMat(k, n);
for j in [1..Length(pivCols)] do
    col := pivCols[j];
    for i in [1..k] do
        X_mat[i][col] := (solveMap[j][i] + solveMap[j][k + i]) mod 2;   # P3 per-entry
    od;
od;
```

At m=7, k=64, n=128, `Length(pivCols)` up to 128. Total entries: 64 × 128 = 8192 interpreted ops.

**Better:** Use vectorised assignment:
```gap
X_mat := NullMat(k, n);
for j in [1..Length(pivCols)] do
    col := pivCols[j];
    left := solveMap[j]{[1..k]};
    right := solveMap[j]{[k+1..2*k]};
    X_mat{[1..k]}[col] := (left + right) mod 2;
od;
```

**Effort:** ~10 LOC.

**Estimated win at m=7:** ~5-10× on this specific block. Small absolute wall but easy.

---

## B7 — `ConjugacyClasses(C)` in `CentraliserClassData` ⟶ closed-form for `C = E_+(m)`

**Location:** `extraspecial_orbifolds/scripts/krr_spectral_characters_sparse.g:1018-1028`.

**Current shape:**
```gap
CentraliserClassData := function(idx, class_idx)
    local C, cc;
    C := idx.centralisers[class_idx];
    cc := ConjugacyClasses(C);                  # ★ at m=7, C = E_+(7), same OOM ★
    return rec(
        classes := cc,
        ...
    );
end;;
```

For the central class (the ONLY class processed in the spectral loop), `C = idx.centralisers[class_idx] = G = E_+(m)`. So this is calling `ConjugacyClasses(E_+(7))` AGAIN — same OOM as A1, but on a fresh call (the closure of `BuildSimpleIndexLazy(G)` returns `idx.classes` but `ConjugacyClasses(C)` for `C = idx.centralisers[i] = G` is a fresh call to GAP).

**Closed-form replacement:**

After A1, `idx.classes` already holds the closed-form class list for G. Since `C = G` for the central class, `CentraliserClassData(idx, central_class_idx)` can return `rec(classes := idx.classes, reps := idx.reps, sizes := idx.class_sizes, num := Length(idx.classes))` directly.

**Effort:** ~20 LOC special-case in `CentraliserClassData`: when `idx.centralisers[class_idx]` is identical to `idx.group`, return the cached class data instead of recomputing.

**Estimated win at m=7:** Same magnitude as A1 (OOM avoidance). Without this, A1 only fixes the first OOM cliff; the SECOND OOM cliff is at `ConjugacyClasses(C)` here.

**This is a Tier-A-equivalent finding hiding in Tier-B because it'd OOM without it.** Promoted in priority.

---

# 4. Tier-C findings: minor / speculative

## C1 — `BuildElementaryAbelianDirect_E_plus` greedy commutator search

**Location:** `extraspecial_orbifolds/scripts/quillen_detecting_subgroup.g:319-396`.

**Current shape:** For m ≥ 4, iterates `gens_G[i]` looking for m pairwise commuting non-central generators via `Comm(h, b) = One(G)` checks. Falls back to `Combinations([1..2*m], m)` (e.g. `C(14, 7) = 3432` subsets at m=7) if the greedy fails.

**Closed-form replacement:** The standard "first half" of GAP's `ExtraspecialGroup(2^(2m+1), "+")` PC presentation has generators `[a_1, b_1, ..., a_m, b_m, z]` where `[a_i, b_i] = z` and all other commutators are 1. So `[z, a_1, a_2, ..., a_m]` is always a maximal elementary abelian of rank `m+1`. Direct construction in O(m) instead of O(C(2m, m)).

**Effort:** ~10 LOC. Should be guarded by a check that GAP's PC convention matches our assumption (already done implicitly via the IdGroup check elsewhere).

**Estimated win at m=7:** ~10 ms vs ~30 sec (the fallback Combinations search). Small absolute, but cleans up the worst-case path.

---

## C2 — `_RTS_FindGClassOf`'s "in idx_G.classes[k]" linear scan

**Location:** `extraspecial_orbifolds/scripts/restrict_to_subgroup.g:245-269`.

**Current shape:**
```gap
for k in [1..Length(idx_G.classes)] do
    if a_H in idx_G.classes[k] then ...
```

After A1+A2 land, the closed-form class structure makes this O(1) via orbit-type lookup. Subsumed by B1 fix; including as a Tier-C standalone for documentation.

---

## C3 — `BuildIntertwinerDataUntwisted(H)` for H = EA called multiple times

**Location:** `extraspecial_orbifolds/scripts/restrict_to_subgroup.g:597` (`RestrictTraceOnWToSubgroupHonourParent` recomputes `BuildIntertwinerDataUntwisted(H)` per branch even though the H-side data is identical for fixed H).

**Current shape:** Each branch (E_EA / D_8 / Q_8) calls `RestrictTraceOnWToSubgroupHonourParent(data_X, X_subgroup)` which internally calls `BuildIntertwinerDataUntwisted(X_subgroup)`. At m=7 with 8 EAs, that's 8 separate `BuildIntertwinerDataUntwisted` calls on |EA|=256 groups.

**Closed-form replacement:** Memoize `BuildIntertwinerDataUntwisted` by group identity. The EA `S` matrix can also be pre-computed analytically (S is the character table of (Z/2)^{m+1} up to a normalisation, all entries ±1/|EA|^{1/2}).

**Effort:** ~20 LOC memoization wrapper.

**Estimated win at m=7:** Per EA the `BuildSimpleIndex(H)` call is cheap (~50 ms at |H|=256). 8 EAs × ~50 ms = ~0.4 sec wall savings. Minor.

---

## C4 — `_F2_AffineSolveCols` interpreted RREF + augmented matrix construction

**Location:** `extraspecial_orbifolds/scripts/krr_spectral_characters_sparse.g:524-575`.

Similar shape to A3 — interpreted GF(2) row reduction with `List([1..cols + 1], k -> ...)` per pivot. Called once per `TraceOnOmega0Gauss` invocation per orbit type. At 4 orbit-types after #447 Change B, this is 4 invocations per K-4b m=7 run.

**Effort/Win:** Same as A3, scaled by 4 invocations vs 1 in `_BuildTraceCtx`. Bundle into the A3 fix.

---

## C5 — `JointPermutationMatcher` row sort + cyclotomic compare

**Location:** `extraspecial_orbifolds/scripts/joint_permutation_matcher.g` (full file).

For rank-22 inputs (D_8, Q_8 branches) the matcher is fast. For rank-4096 inputs (EU sparse spectral S at m=7 — but the K-4b m=7 path does NOT actually call the matcher with this size because the abelian-fast-path is the intended route per B5). Not on the critical path; flagging as Tier-C.

---

## C6 — `EmEPlusTranslateAgainst`'s `GroupHomomorphismByImages` validation

**Location:** `extraspecial_orbifolds/scripts/em_eplus_translate.g:288-296`.

`GroupHomomorphismByImages` (vs `GroupHomomorphismByImagesNC`) verifies that the proposed map is a homomorphism by checking all relations — O(|relations|) which for `E_+(m)` with `2m+1` generators is ~10 relations, fine at m=7. But at the call site we KNOW it's a hom (we constructed `image_list` to match the canonical generator semantics). Using `...NC` saves a few seconds.

**Effort:** 1 character (`s` → `sNC`).

**Estimated win at m=7:** ~1-3 seconds saved.

---

# 5. What we're already doing right

These are existing wins that frame the priorities:

1. **`compute_e_plus_7_T_analytical.g` and `predict_e_plus_m.g`** — the FULL closed-form for the T-multiset and class structure of `Mod(D^1(E_+(m)))` is already worked out and tested at m ≤ 7. The closed-form CC enumerator of #447 Change A is just lifting this analytical knowledge into the path-of-computation.

2. **`TraceOnOmega0Gauss`** (krr_spectral_characters_sparse.g:908-973) — already closed-form via Witt decomposition of the F_2 quadratic form Q. At m=7 we never enumerate the 2^64 diagonal entries; we compute `_F2_FastSymplecticBasis` + Arf invariant in O(d^3). This is the analog of A1's analytical bypass for the trace function itself.

3. **`HardCodeShortComputeInterTwineref`** (defect_rep_minus_id_optim.g) — the per-entry intertwiner formula is closed-form, not the brute-force Schur sum.

4. **Issue #447 Change B (BRW-orbit Tr collapse)** — IN FLIGHT on this branch (`k4b-m7-spectral-perf-445`). Drops the per-class trace loop from 16385 calls to 4 by exploiting BRW-equivariance.

5. **`ClassifyAbelianBranchFast` (PR #437)** — q_ω + b_ω direct cocycle evaluation, ~500× faster than the S-matrix-build classifier. Available as opt-in via `_K4A_USE_FAST_ABELIAN_BRANCH = true`.

6. **gac-compiled hot paths (PR #440)** — 23 modules compiled including `untwisted_modular_data.so`, `restrict_to_subgroup.so`, `ct_modular_data.so`, `mod2_solver.so`. The compiled versions are already used at runtime via `load_compiled.g`. This lifts the per-call interpreter cost on every function in those modules.

7. **`BuildSimpleIndexLazy` + `BuildTransportsLazy` (K-2c, #129)** — already deferred CharacterTable + per-class BFS builds to first access. Without this, even the K-2c-era E_+(7) attempts would have OOM'd on character table builds, not the class enum.

8. **BRW-equivariance amortisation in transgression** (`transgression_per_generator_brw.g`, A-7-perf-2 #271) — per-orbit work, not per-class. The trace-collapse pattern in #447 Change B mirrors this.

9. **The `defect_rep_minus_id_optim.g` overrides of `F2_Mul / F2_VMul / F2_Trans / F2_Add`** to compiled GAP primitives — high-impact local optimization that runs through all the K-4b m=7 trace machinery transparently.

10. **`predict_e_plus_m.g` as a sanity oracle** — every closed-form path can be cross-validated against `PredictE_plus_m(m)` end-to-end. This is the verification anchor for A1 / A2 / B2 / B7.

**Implication for priorities:** the closed-form work is HALF-DONE. The trace function itself is already closed-form (TraceOnOmega0Gauss). The per-entry intertwiner is closed-form (HardCodeShortComputeInterTwineref). What's MISSING is the wrapping infrastructure (class enumeration, centraliser lookup, class-index permutation) that calls these closed-form leaves. The audit's Tier-A findings are all on this wrapping layer.

---

# 6. Recommended PR sequence

The findings have dependencies; here's the order I'd ship them as separate PRs.

### Stage 0 — Already in flight

- **PR (Change B from #447 = current branch):** BRW-orbit Tr collapse in `BuildKRRSpectralCharactersSparse`. Drops Step 3/4 from 16385 trace evals to 4.

### Stage 1 — Strict unblock (must merge before m=7 production can finish)

1. **#447 Change A — closed-form CC enumerator for E_+(m)**
   - Files: new `extraspecial_orbifolds/scripts/e_plus_conjugacy_classes_closed_form.g`. Hook into `BuildSimpleIndexLazy` via a flag `is_eplus := IsEPlusGroup(G)` or via a new `BuildSimpleIndexEPlusLazy(G, m)` and route `BuildKRRSpectralCharactersSparse` to it.
   - Tests: m=3 against `BuildSimpleIndex(EmUnimodGroup(3))` round-trip; m=5 against the known-good path; m=7 smoke (only the central class needs full materialisation per the spectral path).
   - Depends on: nothing. Independent of in-flight #447 Change B.
   - **A2** is bundled into this PR — once we have the closed-form enumerator, the lazy centraliser thunk is trivial.

2. **B7 — closed-form `CentraliserClassData` for C = G** (~20 LOC special case in `krr_spectral_characters_sparse.g`).
   - Trivially small; can land alongside Change A or as a follow-up. Without this, Change A doesn't actually unblock m=7 (second OOM cliff).

3. **B5 — enable `_K4A_USE_FAST_ABELIAN_BRANCH := true` in `run_k4b_m7.sh`**.
   - 3 lines in the driver.
   - Gated by Stage 2 (cross-validation at m=5) per the job-graph.
   - Without this, the post-spectral E branch is the next bottleneck after the spectral build.

**At the end of Stage 1, m=7 should run end-to-end** in some wall budget (estimated ~30-60 min based on the per-orbit-type trace eval cost and the 8-EA + D_8 + Q_8 post-spectral sweep).

### Stage 2 — Bring m=7 wall time below ~10 minutes

4. **A3 — `_BuildTraceCtx` compiled GF(2) RREF** (the `A-K4-2` 2026-06-02 audit finding). 50 LOC rewrite.
   - C4 (`_F2_AffineSolveCols`) bundled.
   - Tests: regression against m=3 / m=5 trace values.

5. **B2 — closed-form `TranslateSpectralDataToEPlus` class-index permutation**. 80 LOC.
   - Depends on A1 (uses the same closed-form class structure).
   - Without this, we hit the EP-side OOM if A1 isn't applied to the EP-side `BuildSimpleIndexLazy` call.

6. **B1 — `_RTS_FindGClassOf` closed-form orbit-type lookup**. 150 LOC.
   - Depends on A1 + B2.
   - High impact on the K-4 post-spectral sweep.

### Stage 3 — Polish

7. **B4 — batched `_CTComputeSBlock`** (the A-K4-4 2026-06-02 finding). 80 LOC.
8. **B3 — closed-form `RestrictedIrrepDecomposition` for abelian H, hardcoded for D_8/Q_8**. 130 LOC.
9. **B6 — compiled `X_mat` slice in `_BuildGaussCtx`**. 10 LOC.
10. **C1 — `BuildElementaryAbelianDirect_E_plus` direct PC-presentation construction**. 10 LOC.
11. **C3 — memoize `BuildIntertwinerDataUntwisted`**. 20 LOC.
12. **C6 — `GroupHomomorphismByImagesNC`**. 1 character.

### Risk / interaction notes

- **A1 + B7 must ship together** to avoid the second OOM cliff at `CentraliserClassData`.
- **A1 + B2 should ship together** to avoid the EP-side OOM cliff at `BuildSimpleIndexLazy(EPlusGroup(7))`.
- **A1 + B5 is the minimum for m=7 to finish in any wall budget.**
- B1 / B4 / B3 are pure speedups, no correctness risk. They can land independently.
- A3 has a regression-test requirement (the m=3 / m=5 trace values must match) but no correctness risk if the test passes.

### Estimated cumulative win at m=7

| Stage | Wall | Memory |
|---|---|---|
| Pre-Stage 1 (current) | OOM at `BuildSimpleIndexLazy` | OOM > 48 GB |
| Stage 1 (#447 A+B + B5 + B7) | ~30-60 min | <4 GB |
| Stage 2 (+A3 + B1 + B2) | ~5-10 min | <2 GB |
| Stage 3 (+B3 + B4 + B6 + C1-C6) | ~2-5 min | <2 GB |

The total Stage 1+2+3 effort is roughly 700 LOC of new code + ~200 LOC of test infrastructure. The closed-form sector enumeration in `compute_e_plus_7_T_analytical.g` already provides the mathematical content; this is mostly plumbing.

---

# 7. Cross-validation with existing audit findings

This audit's findings map against the existing 2026-06-02 audit (`2026-06-02-orthogonal-perf-paths-audit-dvan-k4.md`) as follows:

| 2026-06-02 finding | 2026-06-06 (this audit) | Status |
|---|---|---|
| A-K4-1: F2_Dot / F2_QuadDot not overridden | (subsumed by gac compilation in #440) | Mostly addressed |
| A-K4-2: `_BuildTraceCtx` / `_BuildGaussCtx` manual RREF | **A3** in this audit | NOT shipped, still Tier-A |
| A-K4-3: TraceOnOmega0Batch P3+P6 anti-patterns | (only m=5 hot, not m=7) | Tier-A for m=5, not m=7 |
| A-K4-4: `_CTComputeSBlock` per-irrep trace evals | **B4** in this audit | Tier-B, deferred |
| B-DVAN-1, B-K4-1 | (orthogonal D-VAN paths) | Out of K-4b m=7 scope |
| C-K4-1 | (fsi at small G) | Not on m=7 critical path |

This audit identifies:
- **8 new Tier-A/B findings** (A1, A2, A3 [duplicate], B1, B2, B3, B4 [duplicate], B5, B6, B7)
- **6 new Tier-C findings** (C1-C6)

The interactions with existing in-flight work:
- **Change B from #447** (current branch) collapses the per-class trace loop — addressed.
- **Change A from #447** (the closed-form CC bypass) — this is A1.
- **PR #437** (fast abelian branch) — B5 is "use the existing opt-in flag".

---

# 8. Methodology notes

**How the audit was performed:**

1. Read `run_k4b_m7.sh` end to end. Identify the GAP one-liner's call sequence.
2. Read `k4a_classify.g::K4aClassify`. Track every callable invoked for m ≥ 5 (the `if m >= 5 then ... else ...` branches at lines 943, 1092, 1119, 1139).
3. Read `BuildKRRSpectralCharactersSparse`, `BuildSimpleIndexLazy`, `CentraliserClassData`, `_BuildTraceCtx`, `_BuildGaussCtx`, `TraceOnOmega0Gauss`. Note every call to a generic GAP/HAP function vs an analytical formula.
4. Cross-reference against the existing closed-form modules (`predict_e_plus_m.g`, `compute_e_plus_7_T_analytical.g`, `closed_form_central.g`, `defect_rep_minus_id_optim.g`, `abelian_branch_fast.g`) to identify where the analytical formulas EXIST but aren't being used.
5. Cross-reference against the 2026-06-02 audits to avoid duplicating known findings.
6. Cross-reference against the 2026-06-05 K-4b m=7 production logs to confirm the OOM stack trace points at the path identified in A1.

**What this audit deliberately did NOT do:**
- Did NOT call `ConjugacyClasses(EmUnimodGroup(7))` or any heavy GAP op — that's the bug.
- Did NOT run any benchmarks. Estimated wins are based on:
  - Class counts from `predict_e_plus_m.g` (verified against m=2 / m=3 / m=5 in tests).
  - Per-call cost models from the 2026-06-02 audit's measurements at smaller m.
  - The compiled-vs-interpreted multipliers documented in CLAUDE.md's anti-pattern catalogue.
- Did NOT propose new mathematical content — every closed-form replacement cited here already exists in the codebase as a reference implementation or a comment in `compute_e_plus_7_T_analytical.g` / `predict_e_plus_m.g`.

**Confidence levels:**
- **A1, A2, B7**: HIGH (the OOM is reproduced in the production logs; the closed-form structure is documented and tested at lower m).
- **A3**: HIGH (already a Tier-A finding in the 2026-06-02 audit with measured impact at m=5).
- **B1, B2**: HIGH on the correctness side, NEEDS-REVIEW on the per-call cost estimate — the symplectic conjugator search is novel and would benefit from prototyping.
- **B3, B4**: HIGH on correctness; the speedup magnitude is conservatively estimated.
- **B5, B6, C1-C6**: HIGH — small, well-understood changes.

---

# 9. Open questions

1. **A1's symplectic-basis class enumeration**: at m=7, enumerating the 256 cosets `E_+(7) / Z(E_+(7))` modulo orbit-type is straightforward but produces representatives in the **abstract** E_+(7) PC group, not in the `EmUnimodGroup(7)` matrix realization. The `psi: EmUnimodGroup → EPlusGroup` iso translates between them; A1 needs to pick which side hosts the enumerator. Recommendation: enumerate in the PC realisation (cheaper) and use `psi^{-1}` to materialise matrix-side reps as needed.

2. **B2's class-index permutation**: requires that the EmUnimodGroup / EPlusGroup isomorphism `psi` respects orbit-type labels (true: orbit types are determined by `Order(rep)` + central-or-not, both isomorphism invariants). Should verify against m=3 / m=5 known-good ep_to_eu_class outputs as a regression.

3. **B5 gating**: the fast-abelian-branch flag's cross-validation at m=5 is in Stage 2 of the active-job-graph. If that's not complete by the time A1+B7 ship, we'd want a fallback (slow E branch at m=7, infeasible) OR a parallel B5 fallback experiment.

4. **A3 / C4**: `TriangulizeMat` works on GF(2)-tagged matrices but loses the augmented-matrix structure (we need to track back-substitution rows to recover `solveMap` / `feasMat`). A potential intermediate: keep the augmented matrix as integer, then `ConvertToMatrixRep(M, GF(2))` after building, then row-reduce. Test that the recovered `pivCols` / `solveMap` matches the existing m=3 outputs byte-for-byte.

5. **Composition with #447 Change B**: the in-flight Change B uses `_SparseClassifyEmBRWTypes(cls_data.classes)` which iterates `cls_data.classes` — these need to come from the closed-form CC enumerator (A1) or this Change B step itself hits the OOM. Verify that A1's `cls_data.classes` provides a `Size(cl)` and `Representative(cl)` interface compatible with what `_SparseClassifyEmBRWTypes` expects.

---

# 10. Bibliography of in-codebase references

- `compute_e_plus_7_T_analytical.g` — analytical T-multiset for E_+(m).
- `predict_e_plus_m.g` — class structure + centraliser types + T-eigenvalue counts.
- `closed_form_central.g` — closed-form S-matrix entries for central classes.
- `brw_conjugacy_action.g` — BRW-orbit classification of E_+(m)-conjugacy classes; `ClassifyEmConjugacyClasses`.
- `defect_rep_minus_id_optim.g` — closed-form intertwiner entries (`HardCodeShortComputeInterTwineref`).
- `abelian_branch_fast.g` (PR #437) — fast q_ω + b_ω direct cocycle evaluation.
- `krr_spectral_characters_sparse.g::TraceOnOmega0Gauss` — closed-form Witt-decomp trace.
- `qforms_f2.g` — F_2 quadratic-form Witt machinery (`F2RREF`, `F2LeftNullspace`, `F2RowSpanBasis`, `F2RightNullspace`).
- `extraspecial_orbifolds/docs/superpowers/research/2026-06-02-orthogonal-perf-paths-audit-dvan-k4.md` — prior D-VAN + K-4 audit.
- `extraspecial_orbifolds/perf/raw/k4b/k4b_m7_20260605_213744Z.log` — most-recent K-4b m=7 OOM log.
- CLAUDE.md — anti-pattern catalogue (P1-P10 + P16).
