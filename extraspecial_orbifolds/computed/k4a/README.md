# `computed/k4a/`

Persisted artefacts of the K-4a (EmUnimod-family) production runs at
m = 5 via `K4aClassify(5)` in `k4a_classify.g`.

## Files

- `m5_verdict_post_normalization_fix.txt` — text-format summary of the
  K-4a m=5 verdict after the #275 normalization-reconciliation fix
  (branch `k4-mult0-categorical`, commits `e5ddbc1` + `3ad4cd1` +
  `670f422`). Run wall: 1909.846 s under heavy CPU contention from
  3 parallel m=5 GAP processes.

  The full driver log (with per-branch wall times, sparse build wall,
  and intermediate diagnostics) is written to
  `/tmp/k4mult0_m5_verdict_v2.log` on each run; it is `.gitignore`d
  per the repo's `*.log` policy.

## Verdict summary (post-fix)

```
m              : 5
verdict        : trivial
trivial        : true
E_class.is_cob : true
D8_class.idx   : 1
Q8_class.idx   : 1
spectral src   : krr-sparse
wall (s)       : 1909.846
```

For the pre-fix verdict (predecessor's mult-scaled trace + mult=0→1
fallback) and the full rationale for approach A, see
`writeup/note_k4_mult0_normalization_rationale.md`.

## Mathematical implication

If KRR's m=5 ω restricts to the trivial cocycle class on all three
detecting subgroups (E, D_8, Q_8), then by AM04+Quillen restriction-
injectivity on H^3 of E_+(5), ω = 0 in H^3(E_+(5); U(1)) — confirming
Keller's α = 0 at m = 5.

Literature state: at m = 3, α = 0 is verified by direct construction
of the untwisted holomorphic VOA from the BW(3) = E_8 lattice
orbifold — a well-established result in the VOA literature (the
specific solo-Keller arXiv citation that previous agents recorded in
the codebase, `arXiv:2410.18638`, turns out to be unrelated; the
exact bibliographic pointer needs an audit). At m = 5 and m = 7,
[KRR24] (arXiv:2411.13646) verify only the necessary conditions
(cochain-level c_g ≡ 1 + [vEMS17] level-matching) and conjecture
sufficiency. The verdict here would be the first computational
evidence of [α] = 0 at m = 5.

Cross-validation pending: A-5b's m=5 kernel data (when its production
sweep finishes) gives an independent answer on where ω lives in
H^3(E_+(5); U(1)).
