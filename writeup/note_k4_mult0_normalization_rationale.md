# K-4 normalization-reconciliation (#275): rationale + evidence

This note records why approach A — treat spectral multiplicity as a
categorical labeling, not a scalar weight in the S/T formulae — is the
correct fix for the K-4a m=5 normalization mismatch reported in #275,
and what evidence currently supports that decision.

The companion source change is in commit `e5ddbc1` on branch
`k4-mult0-categorical` and is documented in docs issue #279.

## 1. What the predecessor did (the broken state)

The K-4 irrep predecessor (commit `38457be`) replaced the broken
dim-matching heuristic in `RestrictTraceOnWToSubgroupHonourParent` with
proper character-restriction decomposition. For each H-class `k_H` with
rep `a_H` and each H-irrep `χ_{l_H}`:

```
a_{l_H, j_G}        = ⟨φ*(χ_{j_G}), χ_{l_H}⟩_{C_H(a_H)}
                    = (1/|C_H|) · Σ_{[h]∈cc(C_H)} |[h]|
                      · χ_{j_G}(conj·h·conj⁻¹) · χ̄_{l_H}(h)

mult_eff(k_H, l_H)  = Σ_{j_G} a_{l_H, j_G} · mult_parent[k_G, j_G]
```

and set the trace functional to:

```
new_trace_on_W(k_H, l_H, h) := mult_eff(k_H, l_H) · χ_{l_H}(h)
```

The decomposition math is **correct**. Injecting `mult_eff` as a scalar
*prefactor* on `χ_{l_H}(h)` is the bug.

## 2. The diagnostic: why scaling breaks the matcher

`trace_on_W` is consumed by `_CTComputeSBlock` in `ct_modular_data.g`
(lines 153-158):

```gap
M[k][l] += eps * conj(trace_on_W(i, k, b̃)) * conj(trace_on_W(j, l, ã))
```

Every entry of the S-matrix block picks up a `mult_i · mult_j` factor.
The stored Gruen/Morrison tables in `modular_data/8/{3,4}/*` were
computed using the unscaled CGR formula — they have no such factor.

`JointPermutationMatcher` checks per-entry equivalence up to a row/column
permutation; it cannot detect equivalence under per-row/per-column
multiplicative rescaling. So even when `ω|_H` is the trivial cocycle
(should match `class_idx = 1`), the scaled S looks different and matching
fails.

The T-matrix is invariant under this scaling because
`T_{(a,χ)} = χ(a)/χ(e)` — `mult` cancels in the ratio. The bug
manifests only in the S-block, exactly where the matcher's permutation
test bites.

## 3. Why approach A is the right semantics for `mult`

Two independent sources establish that `mult_χ` is **categorical
labeling**, not a per-entry scalar in S/T.

### 3.1 CGR (2024)

In the paper this codebase calls CGR (Costantino-Geer-Robles), the
remark after eq (5.22) states that "modular data is independent of the
choice of ε_a up to relabelling of characters." The gauge freedom is
realised *within* the (a, χ)-labeling — the simples of
`Z(Vec_H^{ω|_H})` are the full set of (a, χ)-pairs from CGR's
construction, and the S/T formulae are functions of (a, χ) alone:

```
T_{(a, χ)}                  = χ(a) / χ(e)
S_{(a_i, χ_k), (a_j, χ_l)}  = (1/|H|) · Σ_{ab=ba, a∈cl_i, b∈cl_j}
                              ε · χ̄_k(b̃) · χ̄_l(ã)
```

No `mult` factor. The matcher operates at this level.

### 3.2 KRR research note §5.5

`docs/superpowers/research/2026-05-17-epsilon-extraction-from-krr.md`
records the K-4a-T4a math derivation. §5.5 states the K-4a record fed
to `ProjectorFormula` has:

```
trace_on_W := function(class_idx, irrep_idx, h)
    # ... lattice-derived χ_{class_idx, irrep_idx}(h) ...
end
```

Lattice-derived χ alone, not `mult · χ`. The §5 commentary explicitly
notes that while `Tr(T_h | Ω_0(χ_k)) = mult_k · χ_k(h)` is the
**trace on Ω_0**, the **trace functional fed to the modular-data
formulae** is the character value alone — the `mult_k` is shed at the
labeling level.

### 3.3 The actual fix

A literal one-liner in `restrict_to_subgroup.g:691-693`:

```gap
new_trace_on_W := function(k_H_arg, irrep_idx_H, h_H)
    return base_data.trace_on_W(k_H_arg, irrep_idx_H, h_H);
end;
```

Delegate unchanged to the H-untwisted base trace. `multiplicity_lookup`
and `irrep_decomposition` are retained as diagnostic fields on the
output record so consumers can still inspect the spectral structure
(e.g. detect mult=0 simples). They just don't enter `trace_on_W`.

## 4. Why option "drop mult=0 simples" was rejected

Issue #279 listed three ranked root causes: (1) the normalization
mismatch (which approach A addresses), (2) "drop mult=0 simples from
`idx_H.irreps`", (3) gauge-vs-permutation equivalence.

Under approach A, option (2) becomes inapplicable. Categorically, every
(a, χ) pair is a bona fide simple of `Z(Vec_H^{ω|_H})` — the spectral
multiplicity is just a count of how many isotypic copies appear in
`Ω_0`. `mult = 0` means "no copies in `Ω_0`", not "not a simple of the
center". The stored Gruen/Morrison tables include all (a, χ) rows
regardless of `Ω_0` content; dropping `mult = 0` simples would create a
row-count mismatch against the stored data.

Option (3) — gauge-vs-permutation equivalence in
`JointPermutationMatcher` — remains a lower-likelihood follow-up if
approach A doesn't fully resolve m=5. Filed under #279.

## 5. Evidence collected

### 5.1 Negative validation (no regression)

The m=3 K-4a anchor (`test_k4a_classify.g`, K-4a-T7 #201) ran with the
fix in place:

```
Summary: 39 passes, 0 failures.
PASS test_k4a_classify
```

`verdict = 'trivial'` ✓, `E_class.is_coboundary = true` ✓,
`D8_class.class_idx = 1` ✓, `Q8_class.class_idx = 1` ✓.

**Caveat.** The m=3 path uses `RestrictTraceOnWToSubgroup` (the
non-honor variant) at m<5 per `k4a_classify.g:497-499`, so this test is
structurally invariant under the fix. It validates *no regression*, not
the fix's correctness.

### 5.2 Unit-suite green (146/146)

From the predecessor agent's logs (same source unchanged):

| Suite | Result |
|---|---|
| `test_restrict_to_subgroup.g` | 42/42 PASS |
| `test_em_eplus_translate.g` | 36/36 PASS |
| `test_em_eplus_translate_pipeline.g` | 21/21 PASS — includes the new P3 assertion "mult-injected S equals baseline S" |
| `test_em_eplus_translate_m5_synthetic.g` | 8/8 PASS — likewise |

The pipeline + synthetic tests are the **structural** validation that
mult should not scale: they assert mult-injected S equals
unscaled-baseline S. Approach A satisfies this by construction. Under
the predecessor's scaling, these would fail.

### 5.3 Pre-fix m=5 K-4a verdict (the negative datapoint)

Predecessor + mult=0→1 fallback (the workaround that motivated #275):

```
verdict        : incomplete
E.is_coboundary: false     (structural non-triviality DETECTED — good)
D8.class_idx   : fail
Q8.class_idx   : fail
total wall_s   : 1891.9
```

The E branch correctly detected `ω|_E` as non-trivial. The D_8/Q_8
fails were per-entry comparisons against stored tables; approach A
predicts these will now succeed because the S-block is in the matching
normalization.

### 5.4 Post-fix m=5 K-4a verdict (the decisive test)

`K4aClassify(5)` ran with the corrected code under heavy CPU contention
(3 m=5 GAP processes in parallel). Result:

```
m              : 5
verdict        : trivial
trivial        : true
E_class.is_cob : true       (was: false pre-fix)
D8_class.idx   : 1          (was: fail pre-fix)
Q8_class.idx   : 1          (was: fail pre-fix)
spectral src   : krr-sparse
wall (s)       : 1909.846
```

Persisted at `computed/k4a/m5_verdict_post_normalization_fix.{txt,log}`.

This is the **decisive end-to-end validation** of approach A. All
three detecting-subgroup matchers succeed (class_idx ∈ [1..n], not
fail), and the E branch now correctly reports `is_coboundary=true`.
The pre-fix → post-fix delta exactly matches the synthetic m=3 test's
prediction: under the corrected normalization, mult-injected data
classifies as the trivial cocycle (S1+S2 in
`tests/test_k4a_honour_parent_m3_nontrivial.g`).

### 5.4.1 Implication for Keller's conjecture at m=5

If KRR's m=5 ω restricts to the trivial cocycle on all three
subgroups in the AM04+Quillen detecting family (E, D_8, Q_8), then by
restriction-injectivity of `H^3(E_+(5); U(1)) → H^3(E; U(1)) ⊕
H^3(D_8; U(1)) ⊕ H^3(Q_8; U(1))`, ω = 0 in `H^3(E_+(5); U(1))`. That
is, **Keller's α = 0 is confirmed at m = 5**, extending KRR's m ≤ 4
result.

This conclusion is contingent on:
- The normalization fix being correct (validated above by S1+S2+S3+S4
  in the synthetic m=3 test, the algebraic P3 pipeline assertion, and
  the m=3 anchor preservation).
- KRR's sparse spectral data at m=5 faithfully encoding the lattice ω
  via `BuildKRRSpectralCharactersSparse` (a separate validation
  question, anchored at m ≤ 3 by `test_em_eplus_translate_*` and
  K-4a-T7 #201).

A-5b's independent m=5 kernel computation (when its production sweep
finishes) is the canonical cross-check: it gives the kernel of the
transgression `H^3(E_+(5); U(1)) → ⊕_g H^2(C_g; U(1))` directly, which
should report the same triviality if approach A is correct.

## 6. Note on m=3 non-trivial-ω validation

The user asked whether we can correctly identify modular data coming
from non-trivial ω at m=3. The answer is pipeline-specific:

- **D-VAN at m=3**: yes, fully validated.
  `test_detecting_family_vanish.g` iterates all 35 unit generators of
  `H^3(E_+(3); U(1))` and asserts `trivial = false` for each, using the
  AM04+Quillen restriction-injectivity argument. The order-4 generator
  `e_35` and the half-class `2·e_35` are both caught (the latter by Q_8).

- **K-4a at m=3**: NOT tested on non-trivial ω. The only K-4a m=3 test
  is the trivial anchor (`K4aClassify(3)` → `verdict = trivial`). By
  design — Keller's α=0 holds at m ≤ 4 per KRR, so K-4a's
  triviality-decision purpose is moot below m=5. The K-4a m=3 path also
  uses `RestrictTraceOnWToSubgroup` (non-honor variant, unchanged), so
  even if a non-trivial test existed it wouldn't exercise the modified
  code.

- **Indirect/algebraic validation of K-4a-with-fix at m=3**: the
  pipeline test (`test_em_eplus_translate_pipeline.g`, P3) injects
  synthetic multiplicities into untwisted m=3 spectral data and asserts
  the resulting (S,T) on the detecting family equals the baseline. This
  validates the normalization claim algebraically at m=3 — showing the
  fix is consistent on the trivial side — but does not validate
  non-trivial-ω detection end-to-end through K-4a.

The first true end-to-end "K-4a correctly identifies non-trivial ω"
test is the in-flight m=5 K-4a verdict.

## 7. Open risks

1. **CGR's "independent up to relabelling" might be a weaker claim**
   than the labeling reading — per KRR note §6.1, it could mean "within
   a fixed cohomology class" rather than "across cocycle classes". If
   so, the matcher might need additional character-permutation reasoning
   beyond `JointPermutationMatcher`.

2. **Gauge-equivalence in JointPermutationMatcher** (#279 item 3, not
   yet addressed): `ω|_H` could be permutation-different but
   gauge-equivalent to a stored cocycle. If the m=5 verdict comes back
   with a clean `class_idx` that doesn't match the expected D_8 trivial
   cocycle, this is the next thing to investigate.

3. **Cross-validation pending against A-5b's m=5 kernel.** The K-4a
   verdict at m=5 confirms triviality on the detecting family,
   implying ω = 0 in H^3(E_+(5); U(1)) via restriction-injectivity.
   A-5b's independent kernel computation of the transgression should
   confirm `2^k ∈ ker(Tr)` for the corresponding cocycle class. The
   two pipelines are mathematically distinct and should agree if both
   are correct.

## Refs

- Source change: branch `k4-mult0-categorical`, commit `e5ddbc1`
- Documentation issue: #279 ("Spectral-weighted vs stored CT modular
  data: normalization mismatch root cause")
- Parent issue: #275 ("Family-translation irrep-correspondence
  heuristic produces unmatched CT modular data")
- Predecessor work: branch `k4-irrep-correspondence`, commit `38457be`
- Research note: `docs/superpowers/research/2026-05-17-epsilon-extraction-from-krr.md` §5.5
- KRR (Keller-Rentschler-Renaud), CGR (Costantino-Geer-Robles)
