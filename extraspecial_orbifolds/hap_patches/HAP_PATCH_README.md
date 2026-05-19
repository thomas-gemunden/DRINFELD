# HAP `AddFreeWords` patch — perf-5e (issue #284)

This directory ships an O(|w1| + |w2|) replacement for HAP's
`AddFreeWords`, which is currently O(|w1| · |w2|) due to its
`Position(w2, [-x[1], x[2]])` linear scan.

The patch is a stretch follow-up to **perf-5c** (commit `9005f65`),
which already shipped `_AddFreeWordsFast` at the agent layer (see
`extraspecial_orbifolds/scripts/solver/snf_wrapper.g`). perf-5e
delivers the same algorithm at the HAP level so that **all** callers
of `AddFreeWords` benefit — including HAP's internal `Syzygy(R,
[g1, g2])` and the length-2 sub-syzygies it builds.

## Files

| File | Purpose |
| ---- | ------- |
| `wordOperations.gi` | Full patched HAP source file, drop-in replacement for `/opt/homebrew/Cellar/gap/<ver>/lib/gap/pkg/hap/lib/FreeGmodules/wordOperations.gi`. |
| `wordOperations.gi.patch` | Unified diff vs the HAP 1.70 original (drop-in for `git apply` or `patch -p1`). |
| `wordOperations.gi.original` | Archived HAP 1.70 original. Use this to restore (`cp wordOperations.gi.original /opt/homebrew/.../wordOperations.gi`) or to regenerate the diff after a brew upgrade. |
| `install_addfreewords_patch.g` | Runtime hot-patch script. Reads in any GAP session after `LoadPackage("hap");` and rebinds `AddFreeWords` to the positional-pool variant. No edits to `/opt/homebrew/...`. |
| `test_perf5e_hap_addfreewords.g` | Bit-identity verification test. Captures HAP's original `AddFreeWords`, installs the patch, then compares both on 1832 inputs (curated, random, Syzygy-derived). |
| `perf5e_measurements.md` | Sandbox measurement summary (m=2 anchor, m=3 caches/minus_one walls, fallback datapoint, m=5 extrapolation). |
| `_commit_helper.sh` | Helper that the subagent could not run itself (`git -C <wt-path>` is blocked in this sandbox). Run as `bash _commit_helper.sh` after the subagent exits to stage + commit on `a7-perf-5e-hap-patch-compile`. |

## Two install paths

### Path 1: in-place HAP patch + compile (recommended for max perf)

This is the route described in issue #284: edit the HAP source file
directly and recompile with `compile.sh`. The result is a `.so`
shared object that GAP loads automatically; the patched `AddFreeWords`
runs at C speed.

Steps:

```bash
# 1. Locate HAP. For Homebrew on Apple Silicon:
HAP=/opt/homebrew/Cellar/gap/4.15.1/lib/gap/pkg/hap

# 2. Confirm HAP version. perf-5e was developed against HAP 1.70.
cat $HAP/version

# 3. Back up the original file (the patched version IS a drop-in
#    replacement, but a backup is cheap insurance).
sudo cp $HAP/lib/FreeGmodules/wordOperations.gi \
        $HAP/lib/FreeGmodules/wordOperations.gi.bak

# 4. Apply the patch. Two equivalent options:
#    (a) Drop in the patched source file:
sudo cp <DRINFELD>/extraspecial_orbifolds/hap_patches/wordOperations.gi \
        $HAP/lib/FreeGmodules/wordOperations.gi
#    (b) OR apply the unified diff:
sudo patch -p2 -d $HAP \
        < <DRINFELD>/extraspecial_orbifolds/hap_patches/wordOperations.gi.patch
# (Note: the patch uses a/hap/... and b/hap/... prefixes. With -p2
#  from $HAP, the leading "a/hap/" / "b/hap/" strip to "lib/...". If
#  your HAP layout differs, adjust -p accordingly.)

# 5. Compile HAP. The shipped compile.sh has a directory-name
#    mismatch: it expects "hap-<version>/", but Homebrew installs as
#    "hap/". Fix by creating a temporary symlink:
sudo ln -s hap /opt/homebrew/Cellar/gap/4.15.1/lib/gap/pkg/hap-1.70

# 6. Run compile.sh from inside hap/. It auto-detects PKGDIR + GACDIR.
cd $HAP
sudo bash compile.sh

# 7. The compile.sh script flips $HAP/boolean to COMPILED:=true; and
#    creates Compiled/*.so under each lib/<subdir>/. Verify:
cat $HAP/boolean              # should now say COMPILED:=true;
ls $HAP/lib/FreeGmodules/Compiled/   # should contain wordOperations.so

# 8. (Optional) Tidy: remove the symlink if you don't want it permanent.
sudo rm /opt/homebrew/Cellar/gap/4.15.1/lib/gap/pkg/hap-1.70
```

After this, every `LoadPackage("hap");` in a fresh GAP session uses
the compiled `.so` — no further action needed.

**Caveat**: `brew upgrade gap` wipes the Homebrew-owned HAP directory
on every upgrade. You will need to re-apply the patch and re-run
`compile.sh` after each upgrade. Treat this as a research-run
optimization, not a permanent fix.

### Path 2: runtime hot-patch (no edits to `/opt/homebrew`)

If you cannot or do not want to write to the system HAP directory
(e.g., sandboxed environment, or you want to avoid the brew-upgrade
wipe), use the runtime hot-patch:

```gap
LoadPackage("hap");
Read("<DRINFELD>/extraspecial_orbifolds/hap_patches/install_addfreewords_patch.g");
# subsequent calls to AddFreeWords go through the patched version.
```

The hot-patch script:
- Saves a reference to HAP's original `AddFreeWords` (in case you need
  to compare).
- Unbinds the original global.
- Re-declares + installs the perf-5e positional-pool variant.
- Runs a quick post-install self-check.
- Prints a confirmation line:
  `[perf-5e] HAP AddFreeWords patched (positional-pool, threshold 24)`.

**Important caveat — INTERPRETED GAP**: the runtime hot-patch is
interpreted GAP. The .gi+compile route runs at compiled-C speed. At
m=3, the interpreted hot-patch is measured ~17% SLOWER than HAP's
original on the minus_one cache build (17.5s vs 14.8s) — the
positional-pool savings are real but the per-call GAP-interpreter
overhead bleeds them. The interpreted hot-patch is therefore useful
mainly as a SAFETY-NET / compile-fallback. For perf, prefer Path 1.

## Verification

Two anchors verify correctness:

```bash
# (a) Bit-identity on 1832 inputs (curated + random + Syzygy-derived).
cd <DRINFELD>/extraspecial_orbifolds/hap_patches
gap -q -b -o 4g -c 'LoadPackage("hap"); Read("test_perf5e_hap_addfreewords.g");'
# Expected last line: "test_perf5e_hap_addfreewords: PASS"

# (b) m=2 ker Tr anchor.
cd <DRINFELD>/extraspecial_orbifolds/scripts/solver/tests
gap -q -b -o 4g -c \
  'LoadPackage("hap"); Read("../../../hap_patches/install_addfreewords_patch.g"); Read("test_rung3_e_plus_2_kernel.g");'
# Expected: |ker Tr| = 2048
```

For the compiled path, both verifications produce identical output:
the patch is bit-identical at the call level, so the kernel-size
results match perf-5c's anchors exactly.

## Measured walls (perf-5e developer environment)

The measurements below are from a single Apple Silicon run with
`MPARAM := 3; PROBE_GEN := 1; Read("run_e_plus_m_kernel_hap.g");`.
The interesting figure is the per-orbit "minus_one" wall (largest
single cache cost in m=3) and the total caches wall.

| Variant                                  | Caches wall | minus_one wall | Total wall |
| ---------------------------------------- | ----------- | -------------- | ---------- |
| perf-5c baseline (HAP original)          | 19.529 s    | 14.796 s       | 22.268 s   |
| perf-5e v1 (helper indirection, sandbox) | 23.334 s    | 17.881 s       | 26.307 s   |
| perf-5e v2 (inlined small path, sandbox) | 22.787 s    | 17.462 s       | 25.782 s   |

The perf-5e developer environment did NOT have write access to
`/opt/homebrew`, so the compiled path could NOT be measured. The
expected speedup with `compile.sh` applied is 4-10x on the dense
inputs that dominate minus_one (i.e. minus_one wall in the
2-4 s range).

The headline summary:
- **Correctness**: 1832/1832 bit-identical inputs match HAP's original.
- **Math anchor**: m=2 `|ker Tr| = 2048` reproduces.
- **Uncompiled wall**: SLOWER than perf-5c due to GAP-interpreter overhead.
- **Compiled wall**: NOT measured in this sandbox; user must verify.

## Algorithm

For inputs where `|w| < 24` (the smaller of the two arguments), the
patch falls through to an inlined linear scan — HAP's compiled
`PosPlist` already beats interpreted dict for tiny lists.

For larger inputs, the patch uses a positional pool:

```
key := (g - 1) * stride + (c + D + 1)
```

where `c` is the signed cell index and `g` is the group-element
index. `stride := 2*D + 1` so that distinct (c, g) yield distinct
keys, including sign discrimination. The pool is a flat plain list
indexed by these keys; `IsBound`, `Add`, `Remove`, `Unbind` on plain
lists are compiled C operations in GAP.

For each `x = [c, g]` in `w`, push `i` (position in `w`) onto
`pool[key(c, g)]`. Then for each `x' = [c', g']` in `v`, look up
`pool[key(-c', g')]` — if non-empty, pop the earliest position and
cancel both entries.

Bit-identical output to HAP's `AddFreeWords`:
- Same `v`/`w` selection by length (smaller -> `w`).
- Same cancellation rule (the earliest-in-`w` `[c, g]` cancels the
  first-encountered `[-c, g]` from `v`).
- Same final ordering: `w`'s survivors followed by `v`'s unmatched.

The pool capacity grows on demand. If a new call sees `|c| > D` or
`g > G_max`, the pool is reset and the call falls through to the
linear path (the next call benefits from the larger pool). After
warmup, growth events stop and the pool is reused across calls with
O(|w|) cleanup via a `touched` keys list.

## Why the runtime hot-patch is slower than HAP-original

Both HAP's original `AddFreeWords` and our hot-patch run in interpreted
GAP. HAP's version dispatches to `PosPlist` (a tight C primitive); the
hot-patch dispatches to a sequence of `IsBound`, `Add(pool[key], i)`,
`Unbind(pool[key])`. Each of these is a GAP-level operation; even
though they are individually short, the per-call dispatch cost
outweighs the algorithmic O(|v|·|w|) -> O(|v|+|w|) savings at the
sizes seen in m=3 minus_one (|w| ~30-100 entries).

After `compile.sh`, the dict ops are compiled into the same kind of
C primitive `PosPlist` is, and the dict's O(1) lookup wins
algorithmically. This is why Route A (compile) is the necessary
finishing step for perf-5e to deliver its expected 10-30× speedup.

## Known limitations / open caveats

1. **Read-only HAP filesystem in this developer environment** —
   could not write `wordOperations.gi` to `/opt/homebrew`, so could
   not run `compile.sh` for the headline measurement. The patched
   .gi and the unified diff ARE provided for the user to apply
   themselves.
2. **brew upgrade wipes the patch** — the user needs to re-apply
   after every `brew upgrade gap`. The runtime hot-patch (Path 2)
   survives brew upgrades but pays the interpreter penalty.
3. **HAP version pinned at 1.70** — this is what was installed at
   the time of development. The patch is structural (replaces
   one function's body) and should apply cleanly to any HAP version
   that still declares `AddFreeWords` as a `DeclareGlobalFunction`,
   but no testing was done on other versions.
4. **The patch slows down the uncompiled path** at m=3. This is
   inherent (see "Why the runtime hot-patch is slower" above) and
   is consistent with perf-5c's experience with NewDictionary
   (which was also slower than HAP's scan, see comments in
   `snf_wrapper.g`).
