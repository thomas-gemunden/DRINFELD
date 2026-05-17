# K-4a Phase 2: Detecting-family modular-data pipeline

**Date:** 2026-05-17
**Workstream prefix:** K-4a
**Status:** Design (this doc); amended 2026-05-17 post-T4a (see Amendment below).
**Parent EPIC:** #187 (K-4)
**Phase 1 (shipped):** T1 #192 (Q_8 classifier), T3 #195 (Abelian E closed-form), T4a #196 (ε_a math derivation)
**Phase 2 (this doc):** T2 #194, ~~T4b #197~~ (downscoped), **T4c #208** (new), T5a #198, T5b #199, T6 #200, T7 #201

## Amendment 2026-05-17 (post-T4a)

K-4a-T4a (#196, PR #206) concluded that **ε ≡ 1 is the correct gauge choice** for KRR's CT case. CGR §5.2 (eqs 5.18-5.22) shows the modular data is independent of the ε_a choice up to relabelling of characters χ. The Rayleigh-quotient hypothesis from #196 was tested and falsified at m=3 (KRR's explicit formula 4.4.7 shows the vacuum vector is not a simultaneous eigenvector of all T_h).

**Phase 2 task restructure**:

| Original | Status post-T4a |
|----------|-----------------|
| T4b (#197) — Implementation: ε_a callable | Downscoped to a one-liner `epsilon := function(g1, g2, a, b) return 1; end`. Lives inline in T5b's epsilon wiring; no separate file. |
| **(new) T4c (#208)** — Spectral `trace_on_W` from KRR lattice intertwiners | Now the actual critical-path implementation. Replaces the substantive part of T4b. Implements `BuildKRRSpectralCharacters(m)` — joint eigendecomposition of {T_h} on each W_a, character matching to `Irr(C_G(a))`. |
| T5b (#199) — CT modular data | Largely unchanged. With ε ≡ 1, σ(h\|g) = ε_h(g) · ε_g(h) = 1; the existing `ProjectorFormula` works as-is. The lattice content moves into `trace_on_W` (T4c output). |
| T5a (#198), T6 (#200), T7 (#201) | Unchanged shape; consume T4c output instead of T4b output. |

**Where the lattice content actually lives**: T4c. K-4a's substantive math is in `BuildKRRSpectralCharacters` — identifying which character χ each twisted-module piece corresponds to via joint eigendecomposition of {T_h : h ∈ generators of C_G(a)}.

**Anchor**: K-3 (#40) confirms ε ≡ 1 + standard `Irr(C_G(a))` characters reproduce S^0 at m=3 (re-verified 2026-05-17, 295,360 entries, 0 mismatches). T4c's m=3 anchor (subsuming T7) will additionally confirm KRR's spectral characters match standard characters up to permutation (forced by α=0 at m=3 per Keller).

The spec body below predates this amendment; the design described there remains the reference architecture, with the substitutions in the table above applied.

## Goal

Given KRR's lattice orbifold at E_+(m), produce a verdict on `[α] ∈ H³(E_+(m); U(1))` by restricting to the detecting family `{E, D_8, Q_8}` (per AM04 + D-VAN-FIX #151) and computing modular data of `Z(Vec_H^{α|_H})` on each H via CGR §5.2 closed-forms.

The verdict at m = 5, 7 answers Keller's open question for the BW lattice orbifold at those m values.

## Motivation

K-4a's Phase 1 (T1, T3, T4a) produces three independent pieces:
- A reusable joint-permutation matcher (T1).
- A closed-form abelian-cohomology checker (T3).
- A math recipe for extracting ε_a from KRR lattice intertwiners (T4a).

Phase 2 wires these into an end-to-end pipeline:
1. Implement the ε_a recipe (T4b).
2. Restrict ε_a to detecting subgroups (T5a).
3. Compute (S^α, T^α) on each H via CGR §5.2 (T5b).
4. Classify on D_8 (T2, mirror of T1).
5. Orchestrate the three-branch verdict (T6).
6. Anchor against the known-trivial m = 3 case (T7).

## Pipeline

```
                      ε_a callable on E_+(m)
                          │       (T4b: implements T4a recipe)
                          │
                          ▼
              RestrictEpsilonToSubgroup(ε_data, H)
                          │       (T5a)
                          │
         ┌────────────────┼────────────────┐
         │                │                │
         ▼                ▼                ▼
       H = E           H = D_8          H = Q_8
       (abelian)       (rank ~22)       (rank ~22)
         │                │                │
         │                ▼                ▼
         │     ComputeCTModularData(ε_H, H)
         │                │       (T5b: CGR §5.20+5.21)
         │                │
         │     produces (S_H, T_H)
         │                │
         ▼                ▼                ▼
ClassifyOnAbelianE  ClassifyOnD8     ClassifyOnQ8
       (T3)          (T2)             (T1 = #192)
         │                │                │
         └────────────────┴────────────────┘
                          │
                          ▼
                    K4aClassify(m)
                          │       (T6: aggregator)
                          ▼
              rec(trivial: bool, per-subgroup classes)
                          │
                          ▼
              test_k4a_anchor_m3
                       (T7)
```

## Public API (after Phase 2)

```gap
# T5a:
RestrictEpsilonToSubgroup(epsilon_data_G, H) -> rec(
    group     : H,
    idx       : BuildSimpleIndex(H),
    epsilon   : function(class_idx_H, h) -> root of unity
);

# T5b:
ComputeCTModularData(epsilon_data_H, H) -> rec(
    S         : square cyclotomic matrix,
    T         : diagonal cyclotomic matrix,
    simples   : list of (class_idx, irrep_idx),
    group     : H
);

# T2:
ClassifyOnD8(S, T) -> rec(class_idx, pi, all_matches);

# T6:
K4aClassify(m) -> rec(
    m, group,
    epsilon_data,
    E_class   : rec from ClassifyOnAbelianE,
    D8_class  : rec from ClassifyOnD8,
    Q8_class  : rec from ClassifyOnQ8,
    trivial   : bool,
    verdict   : "trivial" | "non-trivial" | "incomplete"
);
```

## Module specs

### T5a — RestrictEpsilonToSubgroup

**File:** `extraspecial_orbifolds/scripts/restrict_epsilon_to_subgroup.g`
**Issue:** #198
**Depends on:** T4b (#197). Can be developed against a stub ε.

#### Function

```gap
RestrictEpsilonToSubgroup := function(epsilon_data_G, H)
    local idx_H, class_to_G_class, restricted_eps;

    # 1. Build H's own class structure.
    idx_H := BuildSimpleIndex(H);

    # 2. For each H-class, identify which G-class contains its rep.
    #    class_to_G_class[k_H] := (k_G, conj : G -> G such that conj * rep_H[k_H] * conj^{-1} = rep_G[k_G]).
    class_to_G_class := List([1..Length(idx_H.reps)], k_H ->
        _FindGClassOf(epsilon_data_G.idx, idx_H.reps[k_H])
    );

    # 3. Restricted ε callable.
    restricted_eps := function(class_idx_H, h)
        local map, k_G, conj, h_in_G;
        map := class_to_G_class[class_idx_H];
        k_G := map.k_G;
        conj := map.conj;
        # h ∈ C_H(rep_H[k_H]) ⊂ G. Conjugate so it lands in C_G(rep_G[k_G]).
        h_in_G := conj * h * conj^(-1);
        return epsilon_data_G.epsilon(k_G, h_in_G);
    end;

    return rec(
        group   := H,
        idx     := idx_H,
        epsilon := restricted_eps
    );
end;;
```

#### Edge cases

1. **Multiple H-classes inside one G-class**: an element of H may have a larger centraliser in G than in H, so a single G-class can split into multiple H-classes. The map class_idx_H → (k_G, conj) is many-to-one on the k_G side.
2. **Conjugation by elements of G \ H**: the "conj" element may not lie in H. That's fine — we just need it as an element of G.
3. **Q_8 vs D_8 with the same elements**: in E_+(m), there are multiple Q_8 and D_8 subgroups. `D8Section_E_plus(m)` and (proposed) `Q8Section_E_plus(m)` pick canonical representatives. If both functions exist, T5a is a thin wrapper; if `Q8Section_E_plus` is missing, **T5a's scope expands** to include adding it, mirroring `D8Section_E_plus`.

#### Tests

`tests/test_restrict_epsilon_to_subgroup.g`:

1. **Stub roundtrip**: define a fake epsilon_data_G with `epsilon(k, h) := E(8)^k` (i.e. a function of just the class index). Restrict to a subgroup H. Verify `restricted.epsilon(k_H, h) = E(8)^{class_to_G_class[k_H].k_G}` for all (k_H, h).
2. **Conjugation invariance check**: pick two different `conj` elements both mapping h ∈ H to elements of C_G(rep_G). Verify the restricted ε gives the same value (this requires β_G ≡ 1 to hold, which is exactly KRR's CT condition).
3. **m = 3 concrete**: restrict an explicit stub epsilon_data_G on E_+(3) to `D8Section_E_plus(3)` and to `MaximalElementaryAbelian_E_plus(3)`. Confirm class counts: |classes of D_8| = 5, |classes of E (= Z_2^4)| = 16.

#### Q_8 section helper (potentially expanded scope)

If `Q8Section_E_plus(m)` doesn't already exist in `quillen_detecting_subgroup.g`:

```gap
Q8Section_E_plus := function(m)
    local G, candidates;
    G := EmGroup(m);
    candidates := Filtered(ConjugacyClassesSubgroups(G), c ->
        StructureDescription(Representative(c)) = "Q8"
    );
    if candidates = [] then
        Error("E_+(", m, ") contains no Q_8 subgroup");
    fi;
    return Representative(candidates[1]);  # canonical pick: first orbit
end;;
```

(Mirror exactly the structure of `D8Section_E_plus`. Add a smoke test verifying that two different Q_8 subgroups give identical K-4a verdicts — important because there can be multiple non-conjugate Q_8 subgroups, and the detecting family is *the union* of all of them, but for our purposes any single representative should give the same triviality verdict assuming the injectivity claim of #193.)

---

### T5b — ComputeCTModularData

**File:** `extraspecial_orbifolds/scripts/ct_modular_data.g`
**Issue:** #199
**Depends on:** T5a (#198). Can be tested against a known-α stub on Q_8.

#### Function

```gap
ComputeCTModularData := function(epsilon_data_H, H)
    local idx, transport, simples, S, T, i, j, W_i, W_j, val, a_i, chi_i;

    idx       := epsilon_data_H.idx;
    transport := BuildTransports(idx);

    # Build the simples list (g, χ) pairs.
    simples := [];
    for i in [1..Length(idx.classes)] do
        for k in [1..Length(idx.centraliser_irreps[i])] do
            Add(simples, rec(class_idx := i, irrep_idx := k));
        od;
    od;

    # Build the K-1-compatible intertwiner_data using the σ from CGR (5.22).
    intertwiner_data := rec(
        group     := H,
        idx       := idx,
        transport := transport,
        trace_on_W := function(class_idx, irrep_idx, h)
            return EvalIrr(idx, class_idx, irrep_idx, h);
        end,
        epsilon := function(g1, g2, a, b)
            # σ(a | b) = ε_a(b) · ε_b(a)
            local k_a, k_b;
            k_a := ClassIndexInIdx(idx, a);
            k_b := ClassIndexInIdx(idx, b);
            return epsilon_data_H.epsilon(k_a, b) * epsilon_data_H.epsilon(k_b, a);
        end
    );

    # Assemble S via the existing ProjectorFormula.
    S := NullMat(Length(simples), Length(simples));
    for i in [1..Length(simples)] do
        for j in [1..Length(simples)] do
            S[i][j] := ProjectorFormula(
                MakeWg(intertwiner_data, simples[i].class_idx, simples[i].irrep_idx),
                MakeWg(intertwiner_data, simples[j].class_idx, simples[j].irrep_idx),
                intertwiner_data
            );
        od;
    od;

    # Assemble T via CGR (5.21).
    T := NullMat(Length(simples), Length(simples));
    for i in [1..Length(simples)] do
        a_i := idx.reps[simples[i].class_idx];
        chi_i := function(h)
            return EvalIrr(idx, simples[i].class_idx, simples[i].irrep_idx, h);
        end;
        T[i][i] := (chi_i(a_i) / chi_i(One(H))) * epsilon_data_H.epsilon(simples[i].class_idx, a_i);
    od;

    return rec(
        S       := S,
        T       := DiagonalMat(List([1..Length(simples)], i -> T[i][i])),
        simples := simples,
        group   := H
    );
end;;
```

#### Math: CGR (5.20)+(5.21)+(5.22) restated

From `hep-th/0001158` Section 5.2 (the CT case):

| Quantity | Formula | Source |
|---|---|---|
| 2-cocycle on C_H(a) | β_a(h, g) | (5.15) |
| 1-cochain trivialisation | ε_a : C_H(a) → U(1), δε_a = β_a | (5.18) |
| Phase | σ(h \| g) := ε_h(g) · ε_g(h) | (5.22) |
| S-matrix | S^α via summation with σ\* factor | (5.20) |
| T-matrix | T^α_{(a,χ),(a,χ)} = (χ(a)/χ(e)) · ε_a(a) | (5.21) |

#### Implementation notes

- **Re-use `ProjectorFormula`**: it already implements (5.20) modulo the σ phase. We supply σ via `intertwiner_data.epsilon`.
- **Complex conjugation**: CGR (5.20) writes σ* (conjugated). `ProjectorFormula` multiplies by `eps` not `conj(eps)`; verify the convention matches and adjust if needed. Likely needs `ComplexConjugate(epsilon_data.epsilon(...))` in the σ wiring.
- **`ClassIndexInIdx(idx, g)`**: helper to look up which class an element belongs to. Should exist in `untwisted_modular_data.g`; if not, add.

#### Tests

`tests/test_ct_modular_data.g`:

1. **Untwisted regression**: feed `epsilon ≡ 1` (constant) on H = Q_8. `ComputeCTModularData` output should equal `LoadModularData(8, 4, 1)` (the trivial cocycle) up to a fixed reordering of simples (decode the simple-list order convention and match).
2. **Modular relations**: at H = Q_8, untwisted: verify `S^2 = (ST)^3` and `S^4 = identity_diagonal`.
3. **Q_8 non-trivial regression**: construct an explicit ε corresponding to the order-2 cocycle on Q_8 (look up the stored cocycle vector in `modular_data/8/4/3-cocycles.txt` and rebuild via `StandardCocycle`; transgress to β; pick a 1-cochain ε trivialising β). `ComputeCTModularData` should output a matrix matching `LoadModularData(8, 4, 2)` up to row/column permutation. Validate via the K-4a-T1 matcher.

#### Open question

CGR's (5.20) requires summing over `H(a, a') := {g ∈ H : g a' g^{-1} ∈ C_H(a)}`. This is implemented in `ProjectorFormula` via the (a, b) enumeration. Verify that the existing implementation matches CGR's domain exactly — in particular the `[a, b commute]` filter. (Spot-check on a tiny H like Z_2 × Z_2.)

---

### T2 — D_8 classifier (mirrors T1)

**File:** `extraspecial_orbifolds/scripts/d8_classifier.g`
**Issue:** #194
**Depends on:** T1 (#192) merged.

This is a near-mechanical clone of T1's `ClassifyOnQ8` for D_8. Spec is in the issue. Key extras:

- D_8 = `SmallGroup(8, 3)` (vs Q_8 = `SmallGroup(8, 4)`).
- **Verify before writing**: number of stored cocycle classes in `modular_data/8/3/`. Compute via:
  ```bash
  ls /Users/thomasgemunden/Projects/group_cohomology/modular_data/8/3/ | grep -c '^[0-9]'
  ```
- H^3(D_8; U(1)) ≅ Z/4 ⊕ Z/2 ⊕ Z/2 → 16 cocycles, but Aut(D_8) acts non-trivially so stored classes < 16. Document the exact count.

---

### T6 — K4aClassify orchestrator

**File:** `extraspecial_orbifolds/scripts/k4a_classify.g`
**Issue:** #200
**Depends on:** T1, T2, T3, T4b, T5a, T5b.

#### Function

```gap
K4aClassify := function(m)
    local G, eps_G, H_list, results, H, eps_H, modular, classifier, classification, all_trivial;

    G := EmGroup(m);
    eps_G := BuildKRREpsilonData(m);   # T4b

    H_list := [
        rec(name := "E",   group := MaximalElementaryAbelian_E_plus(m),
            classify := ClassifyOnAbelianE,         abelian := true),
        rec(name := "D_8", group := D8Section_E_plus(m),
            classify := ClassifyOnD8,                abelian := false),
        rec(name := "Q_8", group := Q8Section_E_plus(m),
            classify := ClassifyOnQ8,                abelian := false)
    ];

    results := rec();
    all_trivial := true;
    for H in H_list do
        eps_H := RestrictEpsilonToSubgroup(eps_G, H.group);     # T5a
        if H.abelian then
            classification := H.classify(eps_H, H.group);        # T3
        else
            modular := ComputeCTModularData(eps_H, H.group);     # T5b
            classification := H.classify(modular.S, modular.T);  # T1 or T2
        fi;
        results.(H.name) := classification;
        all_trivial := all_trivial and _IsTrivialClassification(classification);
    od;

    return rec(
        m            := m,
        group        := G,
        epsilon_data := eps_G,
        E_class      := results.E,
        D8_class     := results.D_8,
        Q8_class     := results.Q_8,
        trivial      := all_trivial,
        verdict      := _MakeVerdict(all_trivial, results)
    );
end;;

_IsTrivialClassification := function(c)
    # Uniform "is trivial cohomology class?" check across the three classifier shapes.
    if IsBound(c.trivial) then return c.trivial; fi;          # ClassifyOnAbelianE shape
    if IsBound(c.class_idx) and c.class_idx <> fail then
        # Need the index of "the trivial class" in the stored modular_data tree.
        # For Q_8: per q8_extension_type/scripts/verify_q8.g, k=1 is the trivial cocycle.
        # For D_8: verify before writing.
        return c.class_idx = _TrivialClassIdxFor(c.group_name);
    fi;
    return false;
end;;

_MakeVerdict := function(all_trivial, results)
    if ForAny(RecNames(results), n -> not _IsClassificationComplete(results.(n))) then
        return "incomplete";
    elif all_trivial then
        return "trivial";
    else
        return "non-trivial";
    fi;
end;;
```

#### CLI driver

`run_k4a.sh`:

```bash
#!/usr/bin/env bash
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR"
m="${1:-3}"
gap -q -b -c "Read(\"k4a_classify.g\");; r := K4aClassify($m);; PrintObj(r);; QUIT;"
```

#### Tests

Covered by T7. Plus a smoke test (`tests/test_k4a_classify_loads.g`) that verifies the file loads and `K4aClassify` is defined.

---

### T7 — m=3 anchor regression

**File:** `extraspecial_orbifolds/scripts/tests/test_k4a_anchor_m3.g`
**Issue:** #201
**Depends on:** T6.

#### Test logic

```gap
Read("../k4a_classify.g");

result := K4aClassify(3);

# Acceptance: Keller's α at m=3 is verified to be trivial (per 2410.18638 §6).
Assert(0, result.verdict = "trivial",
    Concatenation("K-4a m=3 anchor: expected trivial verdict, got ", String(result.verdict)));
Assert(0, result.trivial = true,
    "K-4a m=3 anchor: trivial flag is false");
Assert(0, result.E_class.trivial = true,
    "K-4a m=3 anchor: E component non-trivial");
Assert(0, result.D8_class.class_idx = _TrivialClassIdxFor("D_8"),
    "K-4a m=3 anchor: D_8 component class mismatch");
Assert(0, result.Q8_class.class_idx = _TrivialClassIdxFor("Q_8"),
    "K-4a m=3 anchor: Q_8 component class mismatch");

Print("PASS test_k4a_anchor_m3\n");
QUIT;
```

#### If the test fails

1. Pretty-print all of `result`: verdict, per-subgroup classifications.
2. Pretty-print `result.epsilon_data` for a few class reps — are the ε_a values plausibly characters?
3. Cross-check against D-VAN: `ResIsTrivialOnDetectingFamily(3, ZeroVector)` should also return trivial. If D-VAN says trivial but K-4a says non-trivial, the bug is in K-4a (T4b/T5a/T5b/T6).

#### Budget

T6's K4aClassify(3) should run in < 5 minutes (most cost is `BuildKRREpsilonData(3)` which goes through the optim pipeline; the rest is sub-second). T7 adds < 1 minute on top.

## Test design strategy

Each module has unit tests that exercise that module in isolation against stub inputs. T7 is the only integration test. Levels:

| Level | Test | Coverage |
|---|---|---|
| Unit | test_joint_permutation_matcher (T1) | Backtracker correctness |
| Unit | test_q8_classifier (T1) | 8 stored Q_8 classes round-trip |
| Unit | test_d8_classifier (T2) | All stored D_8 classes round-trip |
| Unit | test_abelian_e_form_check (T3) | HAP H^3 detection on Z_2^k |
| Unit | test_epsilon_extraction (T4b) | ε is a character of C_G(a) at m=3 |
| Unit | test_restrict_epsilon_to_subgroup (T5a) | Stub roundtrip + conjugation invariance |
| Unit | test_ct_modular_data (T5b) | Untwisted regression + Q_8 non-trivial regression + modular relations |
| Smoke | test_k4a_classify_loads (T6) | File loads, function defined |
| Integration | test_k4a_anchor_m3 (T7) | End-to-end verdict at m=3 |

## Acceptance criteria (aggregate)

- All 9 test files pass.
- `K4aClassify(3)` runs in < 5 minutes and returns `verdict = "trivial"`.
- All commits follow CLAUDE.md conventions (`;;`, `local`, no `PrintTo` autowrap).
- Cross-validation with D-VAN at m = 2, 3 agrees on the trivial vs non-trivial verdict for at least one sampled ω-vector.

## Risks and open questions

### High-risk: T4a recipe might not be clean

If T4a's math derivation (#196) concludes that ε_a extraction has a residual gauge ambiguity, or that the "canonical vacuum vector" varies non-trivially across class reps, T4b's signature changes. T5a/T5b need to be re-examined for whether they'd still consume ε in the same shape.

**Mitigation**: T5a/T5b are designed with a function-callable ε interface, not a pre-computed table. As long as T4a produces some `ε(class_idx, h) -> root of unity` callable, T5b is unaffected.

### Medium-risk: σ phase convention mismatch

CGR's (5.20) has σ\* (complex conjugate); the existing `ProjectorFormula` uses raw eps. The σ definition in CGR (5.22) is `σ(h | g) := ε_h(g) · ε_g(h)`. Depending on whether (5.20) means `σ(a | b)` or `σ̄(a | b)`, the wiring in T5b will need a `ComplexConjugate` or not.

**Mitigation**: Verify on the Q_8 untwisted regression test (test #1 in T5b). If S^α at ε ≡ 1 matches `LoadModularData(8, 4, 1)` exactly, the convention is right. If off by `ComplexConjugate`, flip and retest.

### Medium-risk: D_8 stored cocycle coverage

If `modular_data/8/3/` doesn't have all Aut(D_8)-orbits of H^3(D_8; U(1)) classes precomputed, T2 (#194) is incomplete. We'd need to run `SaveModularDataParallel(8, 3, 1, 0, false)` to fill in.

**Mitigation**: T2's first step is the precheck. If missing, file a sub-issue and run the precompute before T2 proper.

### Low-risk: Q_8 conjugacy multiplicity at m ≥ 3

E_+(m) for m ≥ 2 contains multiple conjugacy classes of Q_8 subgroups. `Q8Section_E_plus(m)` picks one canonical representative (orbit 1). The injectivity claim from #193 should imply that **any** Q_8 detects the same cohomology data, but worth a smoke test (pick two Q_8 sections, run K4aClassify on each, verify identical verdict).

### Dependency on #193

The {E, D_8, Q_8} injectivity claim is the load-bearing math result for the entire K-4a workstream. If #193's verdict is "literature doesn't support this", K-4a's conclusion at m = 5, 7 is downgraded from "proves [α] = 0" to "consistent with [α] = 0".

## Implementation order

Optimal critical path:

1. **Now (in parallel, Phase 1)**: T1, T3, T4a, R-1 — all dispatched.
2. **After T1 merges**: T2 (mechanical clone, single small subagent).
3. **After T4a completes**: T4b (implementation subagent based on T4a's Section 5 spec).
4. **After T4b merges**: T5a, T5b in parallel (T5a is stub-testable; T5b needs T5a for full tests but can stub).
5. **After T5a + T5b merge**: T6 (orchestrator, integration).
6. **After T6 merges**: T7 (anchor regression).
7. Then K-4a is complete; proceed to K-4b (m = 5 production), K-4c (m = 7 production).

Approximate timing (assuming one Opus agent at a time per task post-Phase 1):

- T2: 2-3 hours
- T4b: 4-6 hours (depends on T4a clarity)
- T5a: 3-4 hours
- T5b: 4-6 hours
- T6: 3-4 hours
- T7: 1-2 hours
- **Total Phase 2**: ~17-25 hours of focused agent time.

## Out of scope

- K-4b (m = 5 production run) and K-4c (m = 7 production run). Tracked under #187.
- Non-CT twist case (β_a ≠ 0). Outside KRR's verified setting.
- Beyond-modular-data invariants (FS indicators, Galois orbits) — would discriminate further but not needed for the YES/NO triviality verdict.
- Sector reordering by Galois action — see Q_8 work for a precedent if needed.
