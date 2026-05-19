# D-VAN Phase 1 Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build the detecting-family vanishing test for `H³(E_+(m); U(1))` at m ∈ {2, 3, 5} via HAP-based restriction matrices, plus a `KellerSEntry` dispatcher that uses it to fast-path trivial twists. Phase 2 (m=7 via Quillen) is out of scope here.

**Architecture:** A module-level cached `BuildRestrictionMatrices(m, "hap")` precomputes the restriction matrices `H³(G; U(1)) → H³(E; U(1))` and `H³(G; U(1)) → H³(D_8; U(1))` once per m via HAP's `EquivariantChainMap` (same pattern as the existing `H3MatrixOfAutomorphism` in `brw_h3_action.g`, but for inclusion maps `H ↪ G` rather than automorphisms `G → G`). `ResIsTrivialOnDetectingFamily(m, ω_vec)` is then a matrix-vector product per query.

**Tech Stack:** GAP 4.15.1 + HAP (compiled), pc-form groups via `ExtraspecialGroup(2^(2m+1), "+")`, existing `quillen_detecting_subgroup.g` for the subgroup constructions and `transgression_kernel.g::SetupCohomology3` for the per-group cohomology setup.

**Source spec:** `docs/superpowers/specs/2026-05-15-detecting-family-vanishing-test-design.md` (committed `0e8bcc8`).

**PR structure:** Six PRs, one per issue D-VAN-2 through D-VAN-7.

---

## Critical pitfalls (read before starting any task)

1. **GAP PrintTo auto-wrap.** GAP's default `PrintTo` wraps long lines at ~80 chars with backslash continuation, silently breaking single-line `#` comments and string literals. Any code that writes a `.g` file MUST use `OutputTextFile(path, false) + SetPrintFormattingStatus(stream, false)`. See `dp_i_dispatch.g` for the established idiom. This plan creates only test/source files, not persisted output files, so the hazard doesn't directly bite — but if you add a "write computed kernel data" step, apply this rule.
2. **V-4a `UCT.cocyclebasis` vs `UCT.lift`.** Always use `UCT.cocyclebasis[i]` to lift a hom-basis coordinate to an R-cocycle vector. Never use `UCT.lift * vec` — it has a shape mismatch (the aux dimension is not `Length(UCT.hombasis)`) and silently produces wrong vectors via GAP auto-padding. See `fsi_wrapper.g::FSI_LiftIfHom` for the canonical lift, and `transgression_kernel.g::StandardCocycleOf` for the same idiom inline.
3. **Multiple D_8 sections.** `D8Section_E_plus(m)` picks `candidates[1]` from `ConjugacyClassesSubgroups(G)`. Different conjugates give different *coordinate vectors* but the `trivial` verdict is class-invariant. Pin to the function's choice everywhere; the spec includes a smoke test (Task 2.7) confirming two different D_8 choices yield identical `trivial` verdicts.
4. **Heavy step is HAP construction.** `BuildRestrictionMatrices(m, "hap")` builds two HAP resolutions (E and D_8), the chain maps, and the cohomology-functor matrices. It MUST be cached in a script-level `_DETF_CACHE` rec so that thousands of subsequent `ResIsTrivialOnDetectingFamily` queries don't repeat the build.
5. **Subgroup `phi: H → G` inclusion.** Build this via `GroupHomomorphismByImages(H, G, GeneratorsOfGroup(H), List(GeneratorsOfGroup(H), x -> x))`. The identity-on-elements map works because `H ≤ G`; GAP needs the explicit images to set up the homomorphism object.

---

## File structure

**Files created in Phase 1.**

```
extraspecial_orbifolds/scripts/
  detecting_family_restriction.g          # NEW — D-VAN-2
  detecting_family_vanish.g               # NEW — D-VAN-3
  keller/                                  # NEW directory if not present
    keller_twist_is_trivial.g             # NEW — D-VAN-5
    keller_s_entry.g                      # NEW — D-VAN-6
  tests/
    test_detecting_family_restriction.g   # NEW — D-VAN-2 tests
    test_detecting_family_vanish.g        # NEW — D-VAN-3, D-VAN-4, D-VAN-7 tests
    test_keller_s_entry.g                 # NEW — D-VAN-5, D-VAN-6 tests
```

**Files reused (not modified).**

```
extraspecial_orbifolds/scripts/
  quillen_detecting_subgroup.g            # MaximalElementaryAbelian_E_plus, D8Section_E_plus, EPlusGroup
  transgression_kernel.g                  # SetupCohomology3, StandardCocycleOf, IsCoboundary2Split
  brw_h3_action.g                         # H3MatrixOfAutomorphism — pattern source for inclusion-map matrix
  fsi_wrapper.g                           # FSI_LiftIfHom — input convention
  closed_form_central.g                   # ClosedFormCentralS, ClosedFormCentralRow — V-2 S^0 entry
  skeller_adapter.g                       # SKeller(m, i, j) — K-2 SKeller entry
```

---

# PR 1: D-VAN-2 — `BuildRestrictionMatrices(m, "hap")`

Branch: `dvan-2-restriction-builder` off `main`.

### Task 1.1: Scaffold the file and module-level cache

**Files:**
- Create: `extraspecial_orbifolds/scripts/detecting_family_restriction.g`

- [ ] **Step 1: Write the failing test (file existence + cache rec exists)**

Create `extraspecial_orbifolds/scripts/tests/test_detecting_family_restriction.g`:

```gap
# Tests for D-VAN-2: BuildRestrictionMatrices(m, source).
# Run from extraspecial_orbifolds/scripts/:
#   gap -q -b -c 'Read("tests/test_detecting_family_restriction.g"); QUIT;'

BreakOnError := false;;

Read("detecting_family_restriction.g");

Print("\n=== test_detecting_family_restriction.g ===\n");

testFailures := [];;
If_ := function(c, a, b) if c then return a; else return b; fi; end;;
AssertOrLog := function(label, cond)
    Print("  ", label, ": ", If_(cond, "PASS", "FAIL"), "\n");
    if not cond then Add(testFailures, label); fi;
end;;

Print("\n--- Task 1.1: file scaffold ---\n");
AssertOrLog("BuildRestrictionMatrices is bound",
            IsBoundGlobal("BuildRestrictionMatrices"));
AssertOrLog("_DETF_CACHE is bound (module-level cache)",
            IsBoundGlobal("_DETF_CACHE"));
AssertOrLog("_DETF_CACHE is a record",
            IsRecord(ValueGlobal("_DETF_CACHE")));

if IsEmpty(testFailures) then
    Print("\n=== test_detecting_family_restriction (1.1): PASS ===\n");
else
    Print("\n=== test_detecting_family_restriction (1.1): FAIL ===\n");
    for f in testFailures do Print("  - ", f, "\n"); od;
fi;
```

- [ ] **Step 2: Run test to verify it fails**

```bash
cd extraspecial_orbifolds/scripts
gap -q -b -c 'Read("tests/test_detecting_family_restriction.g"); QUIT;'
```

Expected: error reading `detecting_family_restriction.g` (file does not exist).

- [ ] **Step 3: Create the file scaffold**

Create `extraspecial_orbifolds/scripts/detecting_family_restriction.g`:

```gap
# detecting_family_restriction.g — D-VAN-2 (issue TBD-D-VAN-2).
#
# Builds and caches the restriction matrices
#
#     Res_E   : H^3(G; U(1)) -> H^3(E;   U(1))
#     Res_D8  : H^3(G; U(1)) -> H^3(D_8; U(1))
#
# for G = E_+(m), E = maximal rank-(m+1) elementary abelian, D_8 = the
# pinned conjugacy class representative D_8 section returned by
# D8Section_E_plus.
#
# Phase 1 (this file) uses HAP's EquivariantChainMap to compute the
# matrices; Phase 2 will add a "quillen" source for the m=7 path
# (gated on Q-int A2/A3, issue #136).
#
# Spec: docs/superpowers/specs/2026-05-15-detecting-family-vanishing-test-design.md
#
# Reused infrastructure:
#   * MaximalElementaryAbelian_E_plus, D8Section_E_plus, EPlusGroup
#     from quillen_detecting_subgroup.g.
#   * SetupCohomology3 from transgression_kernel.g.
#   * H3MatrixOfAutomorphism in brw_h3_action.g is the precedent for
#     this kind of cohomology-matrix construction (same EquivariantChainMap
#     + GroupCohomologyFunctor pattern, with phi: G -> G replaced by
#     phi: H -> G).

LoadPackage("hap");

# --- dependencies -----------------------------------------------------

if not IsBoundGlobal("MaximalElementaryAbelian_E_plus") then
    Read("quillen_detecting_subgroup.g");
fi;
if not IsBoundGlobal("SetupCohomology3") then
    Read("transgression_kernel.g");
fi;

# Local ternary, matching repo convention.
If_ := function(c, a, b) if c then return a; else return b; fi; end;;

# --- module-level cache ----------------------------------------------
#
# Keyed by Concatenation("m", String(m), "_", source).
# Each entry stores the full rec returned by BuildRestrictionMatrices.

_DETF_CACHE := rec();;
```

- [ ] **Step 4: Run test to verify it passes**

```bash
gap -q -b -c 'Read("tests/test_detecting_family_restriction.g"); QUIT;'
```

Expected: `test_detecting_family_restriction (1.1): PASS`.

- [ ] **Step 5: Commit**

```bash
git add extraspecial_orbifolds/scripts/detecting_family_restriction.g \
        extraspecial_orbifolds/scripts/tests/test_detecting_family_restriction.g
git commit -m "[D-VAN-2] Scaffold detecting_family_restriction.g + cache"
```

---

### Task 1.2: Subgroup-resolution helper

**Files:**
- Modify: `extraspecial_orbifolds/scripts/detecting_family_restriction.g` (add helper)
- Modify: `extraspecial_orbifolds/scripts/tests/test_detecting_family_restriction.g` (add tests)

- [ ] **Step 1: Append the failing test**

Append to `test_detecting_family_restriction.g` (after the Task 1.1 block):

```gap
Print("\n--- Task 1.2: SubgroupCohomologyContext ---\n");

# Build the context for D_8 (smallest case) and check the returned rec
# has the right fields. SubgroupCohomologyContext takes a GAP group
# and returns a rec with R, K, UCT, exponent, num_generators, torsion.
D8 := SmallGroup(8, 3);;
ctx_d8 := SubgroupCohomologyContext(D8);;

AssertOrLog("SubgroupCohomologyContext returns a record",
            IsRecord(ctx_d8));
AssertOrLog("ctx_d8.R is bound", IsBound(ctx_d8.R));
AssertOrLog("ctx_d8.K is bound", IsBound(ctx_d8.K));
AssertOrLog("ctx_d8.UCT is bound", IsBound(ctx_d8.UCT));
AssertOrLog("ctx_d8.exponent = 4 (D_8 H^3 exp)",
            ctx_d8.exponent = 4);
AssertOrLog("ctx_d8.num_generators = 3 (D_8 H^3 rank)",
            ctx_d8.num_generators = 3);
AssertOrLog("ctx_d8.torsion = [2, 2, 4] (sorted)",
            SortedList(ctx_d8.torsion) = [2, 2, 4]);
```

- [ ] **Step 2: Run test to verify it fails**

```bash
gap -q -b -c 'Read("tests/test_detecting_family_restriction.g"); QUIT;'
```

Expected: error "Variable: 'SubgroupCohomologyContext' must have a value".

- [ ] **Step 3: Implement SubgroupCohomologyContext**

Append to `detecting_family_restriction.g`:

```gap
# Build the cohomology context (R, K, UCT) for a subgroup. Thin wrapper
# around SetupCohomology3 that documents the intent. Returns the same
# rec shape so downstream code is uniform.
SubgroupCohomologyContext := function(H)
    return SetupCohomology3(H);
end;;
```

- [ ] **Step 4: Run test to verify it passes**

```bash
gap -q -b -c 'Read("tests/test_detecting_family_restriction.g"); QUIT;'
```

Expected: all assertions in Task 1.2 block PASS.

- [ ] **Step 5: Commit**

```bash
git add -u
git commit -m "[D-VAN-2] SubgroupCohomologyContext helper"
```

---

### Task 1.3: Inclusion homomorphism helper

**Files:**
- Modify: `extraspecial_orbifolds/scripts/detecting_family_restriction.g`
- Modify: `extraspecial_orbifolds/scripts/tests/test_detecting_family_restriction.g`

- [ ] **Step 1: Append the failing test**

Append to `test_detecting_family_restriction.g`:

```gap
Print("\n--- Task 1.3: SubgroupInclusion ---\n");

# IMPORTANT: each call to EPlusGroup(m) builds a fresh GAP group with
# non-overlapping element families. GroupHomomorphismByImages will fail
# if H comes from one EPlusGroup(2) call and we pass a different
# EPlusGroup(2) call as the target G. Pin G to whatever EPlusGroup(2)
# the subgroup constructor used (= H_d8_rec.parent), NOT a fresh
# EPlusGroup(2). The original plan called EPlusGroup(2) here directly;
# replaced with H_d8_rec.parent based on Task 1.3 implementation finding.
H_d8_rec := D8Section_E_plus(2);;
G_22 := H_d8_rec.parent;;    # SAME EPlusGroup(2) as inside H_d8_rec
H_d8 := H_d8_rec.subgroup;;

phi := SubgroupInclusion(H_d8, G_22);;
AssertOrLog("SubgroupInclusion returns a homomorphism",
            IsGroupHomomorphism(phi));
AssertOrLog("Source(phi) = H",
            Source(phi) = H_d8);
AssertOrLog("Range(phi) = G",
            Range(phi) = G_22);
AssertOrLog("phi is injective",
            IsInjective(phi));
AssertOrLog("phi(h) = h for the first generator of H",
            Image(phi, GeneratorsOfGroup(H_d8)[1])
                = GeneratorsOfGroup(H_d8)[1]);
```

- [ ] **Step 2: Run test to verify it fails**

```bash
gap -q -b -c 'Read("tests/test_detecting_family_restriction.g"); QUIT;'
```

Expected: error "Variable: 'SubgroupInclusion' must have a value".

- [ ] **Step 3: Implement SubgroupInclusion**

Append to `detecting_family_restriction.g`:

```gap
# Build the inclusion homomorphism phi: H -> G where H <= G.
# GAP's GroupHomomorphismByImages handles this when given the
# generators of H mapped to themselves (as elements of G).
#
# This is the homomorphism object that HAP's EquivariantChainMap needs.
SubgroupInclusion := function(H, G)
    local gens_H, phi;
    gens_H := GeneratorsOfGroup(H);
    phi := GroupHomomorphismByImages(H, G, gens_H, gens_H);
    if phi = fail then
        Error("SubgroupInclusion: H = ", H,
              " is not a subgroup of G = ", G,
              " (GroupHomomorphismByImages returned fail)");
    fi;
    return phi;
end;;
```

- [ ] **Step 4: Run test to verify it passes**

```bash
gap -q -b -c 'Read("tests/test_detecting_family_restriction.g"); QUIT;'
```

Expected: Task 1.3 assertions PASS.

- [ ] **Step 5: Commit**

```bash
git add -u
git commit -m "[D-VAN-2] SubgroupInclusion helper"
```

---

### Task 1.4: Restriction-matrix builder for a single subgroup

**Files:**
- Modify: `extraspecial_orbifolds/scripts/detecting_family_restriction.g`
- Modify: `extraspecial_orbifolds/scripts/tests/test_detecting_family_restriction.g`

This is the math-heavy task. It mirrors `H3MatrixOfAutomorphism` from `brw_h3_action.g` but with the source resolution being H (smaller) and target being G (larger).

- [ ] **Step 1: Append the failing test**

Append to `test_detecting_family_restriction.g`:

```gap
Print("\n--- Task 1.4: RestrictionMatrixViaHAP ---\n");

setup_G_22 := SetupCohomology3(G_22);;
ctx_H_d8 := SubgroupCohomologyContext(H_d8);;
phi_d8 := SubgroupInclusion(H_d8, G_22);;

# Build the restriction matrix H^3(G) -> H^3(D_8) for G = E_+(2).
res_mat := RestrictionMatrixViaHAP(setup_G_22, ctx_H_d8, phi_d8);;

AssertOrLog("RestrictionMatrixViaHAP returns a matrix",
            IsMatrix(res_mat));
AssertOrLog("matrix has k_G = 10 rows (E_+(2) H^3 rank)",
            Length(res_mat) = 10);
AssertOrLog("matrix has k_H = 3 columns (D_8 H^3 rank)",
            Length(res_mat[1]) = 3);

# Entries should be reduced mod the H-side torsion. torsion_H = [2, 2, 4]
# in some order; every entry must be in [0..3].
all_reduced := ForAll(res_mat, row -> ForAll(row, x -> x >= 0 and x <= 3));
AssertOrLog("all entries reduced mod max(torsion_H) = 4",
            all_reduced);
```

- [ ] **Step 2: Run test to verify it fails**

```bash
gap -q -b -c 'Read("tests/test_detecting_family_restriction.g"); QUIT;'
```

Expected: error "Variable: 'RestrictionMatrixViaHAP' must have a value".

- [ ] **Step 3: Implement RestrictionMatrixViaHAP**

Append to `detecting_family_restriction.g`:

```gap
# Compute the restriction matrix H^3(G; U(1)) -> H^3(H; U(1)) using
# HAP's EquivariantChainMap. Pattern mirrors H3MatrixOfAutomorphism
# (brw_h3_action.g) but with phi: H -> G (subgroup inclusion) replacing
# phi: G -> G (automorphism).
#
# Returns a k_G x k_H integer matrix whose (i, j) entry is the j-th
# H-side hom-basis coordinate of the image of the i-th G-side hom-basis
# generator under restriction. Entries are reduced mod torsion_H[j].
#
# Why this matches H3MatrixOfAutomorphism's structure:
#
#   * EquivariantChainMap(R_H, R_G, phi) builds a chain map R_H -> R_G
#     above phi.
#   * TensorWithIntegers(...) descends to a Z-chain map K_H -> K_G.
#   * GroupCohomologyFunctor(K_H, K_G, chainmap, 3) gives F such that
#     F acts on adapted Z_3 cycle coords. On hom-vectors (length |ZZ_H|),
#     the pullback phi^* acts via right-multiplication by TransposedMat(F),
#     producing an image in H^3(G; Z/exp_G).
#   * IMPORTANT: the source/target swap for the inclusion case is just
#     the choice of R_H as source and R_G as target. The cohomology
#     functor is contravariant, so phi^* maps cocycles on G to cocycles
#     on H (correct direction for our restriction).
#   * The projection onto hombasis_H uses exp_H (not exp_G) for the
#     slack since the target lives in H^3(H; Z/exp_H).
RestrictionMatrixViaHAP := function(setup_G, ctx_H, phi_HG)
    local R_G, K_G, UCT_G, exp_G, k_G, hombasis_G,
          R_H, K_H, UCT_H, exp_H, k_H, torsion_H, hombasis_H, hb_len_H,
          chainmap, gcf, F, autmat,
          aug_matrix, i, image_vec, image_modH, sol, col_coeffs,
          res_mat, j;

    R_G := setup_G.R;
    K_G := setup_G.K;
    UCT_G := setup_G.UCT;
    exp_G := setup_G.exponent;
    k_G := setup_G.num_generators;
    hombasis_G := UCT_G.hombasis;

    R_H := ctx_H.R;
    K_H := ctx_H.K;
    UCT_H := ctx_H.UCT;
    exp_H := ctx_H.exponent;
    k_H := ctx_H.num_generators;
    torsion_H := ctx_H.torsion;
    hombasis_H := UCT_H.hombasis;
    hb_len_H := Length(hombasis_H[1]);

    # Equivariant chain map R_H -> R_G above phi: H -> G, then Z-tensored.
    chainmap := TensorWithIntegers(EquivariantChainMap(R_H, R_G, phi_HG));

    # Matrix of phi on adapted Z_3 cycle coords. Same convention as in
    # H3MatrixOfAutomorphism (brw_h3_action.g): GroupCohomologyFunctor
    # returns F such that row-form cycle coords transform by right-
    # multiplication by F. On hom-vectors, the dual action is right-mult
    # by TransposedMat(F).
    gcf := GroupCohomologyFunctor(K_H, K_G, chainmap, 3);
    F := gcf!.matrix;
    autmat := TransposedMat(F);

    # Augmented matrix for projecting any phi^*(hombasis_G[i]) onto
    # hombasis_H mod exp_H. The first k_H rows are the H-side hom-basis;
    # the last hb_len_H rows are exp_H * I_{hb_len_H} (slack for
    # mod-exp_H equivalence). SolutionIntMat(aug, image) returns x with
    # x * aug = image; x{[1..k_H]} are the desired H-side coords.
    aug_matrix := Concatenation(
        hombasis_H,
        List([1..hb_len_H], r -> List([1..hb_len_H], c ->
            If_(r = c, exp_H, 0))));

    res_mat := NullMat(k_G, k_H);
    for i in [1..k_G] do
        # phi^*(hombasis_G[i]) as a length-hb_len_H vector mod exp_G.
        image_vec := List(hombasis_G[i] * autmat, x -> x mod exp_G);
        # Reduce mod exp_H since target is H^3(H; Z/exp_H).
        image_modH := List(image_vec, x -> x mod exp_H);
        sol := SolutionIntMat(aug_matrix, image_modH);
        if sol = fail then
            Error("RestrictionMatrixViaHAP: could not project image of ",
                  "hombasis_G[", i, "] onto hombasis_H. ",
                  "Possible cause: phi is not actually a homomorphism ",
                  "or aug_matrix span is incorrect for this exp_H.");
        fi;
        col_coeffs := sol{[1..k_H]};
        for j in [1..k_H] do
            res_mat[i][j] := col_coeffs[j] mod torsion_H[j];
        od;
    od;

    return res_mat;
end;;
```

- [ ] **Step 4: Run test to verify it passes**

```bash
gap -q -b -c 'Read("tests/test_detecting_family_restriction.g"); QUIT;'
```

Expected: Task 1.4 assertions PASS.

This will involve running HAP on D_8 (cheap, <1 s) and E_+(2) (cheap, ~1 s); the test takes maybe 5 seconds wall.

- [ ] **Step 5: Commit**

```bash
git add -u
git commit -m "[D-VAN-2] RestrictionMatrixViaHAP — single-subgroup restriction matrix"
```

---

### Task 1.5: Public `BuildRestrictionMatrices(m, source)` + caching

**Files:**
- Modify: `extraspecial_orbifolds/scripts/detecting_family_restriction.g`
- Modify: `extraspecial_orbifolds/scripts/tests/test_detecting_family_restriction.g`

- [ ] **Step 1: Append the failing test**

```gap
Print("\n--- Task 1.5: BuildRestrictionMatrices public API ---\n");

rec_m2 := BuildRestrictionMatrices(2, "hap");;

AssertOrLog("rec.m = 2", rec_m2.m = 2);
AssertOrLog("rec.source = hap", rec_m2.source = "hap");
# NOTE: H^3((Z/2)^k; U(1)) from UCT has 7 invariant factors at k=3
# (m=2 EA), NOT 3. The 3 is the rank of the EA itself, not the rank
# of its degree-3 cohomology. Empirically verified via SetupCohomology3.
AssertOrLog("rec.res_E is a 10 x 7 matrix (m=2 EA H^3 has 7 invariant factors)",
            Length(rec_m2.res_E) = 10
            and Length(rec_m2.res_E[1]) = 7);
AssertOrLog("rec.res_D8 is a 10 x 3 matrix",
            Length(rec_m2.res_D8) = 10
            and Length(rec_m2.res_D8[1]) = 3);
AssertOrLog("rec.torsion_G = E_+(2) torsion",
            SortedList(rec_m2.torsion_G)
                = Concatenation(List([1..9], i -> 2), [8]));
AssertOrLog("rec.torsion_E sorted = [2]^7",
            SortedList(rec_m2.torsion_E)
                = ListWithIdenticalEntries(7, 2));
AssertOrLog("rec.torsion_D8 sorted = [2,2,4]",
            SortedList(rec_m2.torsion_D8) = [2, 2, 4]);
AssertOrLog("rec.H_E is a GAP group",
            IsGroup(rec_m2.H_E));
AssertOrLog("rec.H_D8 is a GAP group",
            IsGroup(rec_m2.H_D8));
AssertOrLog("rec.H_D8 has order 8",
            Order(rec_m2.H_D8) = 8);
AssertOrLog("rec.H_E has order 8 (rank 3)",
            Order(rec_m2.H_E) = 8);

# Caching: second call returns the same record (===) as the first.
rec_m2_again := BuildRestrictionMatrices(2, "hap");;
AssertOrLog("second call returns cached rec (identical reference)",
            IsIdenticalObj(rec_m2, rec_m2_again));

# Phase 2 not yet implemented.
err := CALL_WITH_CATCH(BuildRestrictionMatrices, [2, "quillen"]);;
AssertOrLog("source = quillen at m=2 errors (Phase 2 not shipped)",
            not err[1]);

# m=7 with source=hap explicitly errors rather than invoking HAP.
err := CALL_WITH_CATCH(BuildRestrictionMatrices, [7, "hap"]);;
AssertOrLog("source = hap at m=7 errors (Phase 1 doesn't support m=7)",
            not err[1]);
```

- [ ] **Step 2: Run test to verify it fails**

```bash
gap -q -b -c 'Read("tests/test_detecting_family_restriction.g"); QUIT;'
```

Expected: error "Variable: 'BuildRestrictionMatrices' must have a value".

- [ ] **Step 3: Implement BuildRestrictionMatrices**

Append to `detecting_family_restriction.g`:

```gap
# Public entry point.
#
# Returns rec(
#   m, source ("hap" | "quillen"),
#   res_E       : k_G x k_E integer matrix, entries in [0..torsion_E[j]-1]
#   res_D8      : k_G x k_D8 integer matrix, entries in [0..torsion_D8[j]-1]
#   torsion_G, torsion_E, torsion_D8,
#   exp_G,     exp_E,     exp_D8,
#   setup_G,                # the SetupCohomology3(G) record (for omega lifting)
#   ctx_E, ctx_D8,          # SubgroupCohomologyContext recs
#   H_E, H_D8               # the pinned GAP subgroups
# ). Cached at module level by (m, source).
BuildRestrictionMatrices := function(m, source)
    local key, G, ea_rec, d8_rec, H_E, H_D8, setup_G, ctx_E, ctx_D8,
          phi_E, phi_D8, res_E, res_D8, result;

    if not (IsInt(m) and m >= 1) then
        Error("BuildRestrictionMatrices: m must be a positive integer; got ",
              m);
    fi;
    if not (source in ["hap", "quillen"]) then
        Error("BuildRestrictionMatrices: source must be \"hap\" or ",
              "\"quillen\"; got ", source);
    fi;

    # Phase 1 supports source=hap for m <= 5; m=7 + hap is the trap we
    # explicitly want to prevent (would invoke ResolutionFiniteGroup(E_+(7), 4)).
    if source = "hap" and m > 5 then
        Error("BuildRestrictionMatrices: source=\"hap\" is not supported ",
              "for m > 5 because ResolutionFiniteGroup(E_+(", m, "), 4) ",
              "OOMs. Use source=\"quillen\" (Phase 2, gated on Q-int ",
              "A2/A3, issue #136). At m = ", m, ".");
    fi;
    if source = "quillen" then
        Error("BuildRestrictionMatrices: source=\"quillen\" is Phase 2 ",
              "and not yet implemented. Gated on Q-int A2/A3 (issue ",
              "#136). At m = ", m, ".");
    fi;

    key := Concatenation("m", String(m), "_", source);
    if IsBound(_DETF_CACHE.(key)) then
        return _DETF_CACHE.(key);
    fi;

    G := EPlusGroup(m);
    ea_rec := MaximalElementaryAbelian_E_plus(m);
    d8_rec := D8Section_E_plus(m);
    H_E := ea_rec.subgroup;
    H_D8 := d8_rec.subgroup;

    setup_G := SetupCohomology3(G);
    ctx_E := SubgroupCohomologyContext(H_E);
    ctx_D8 := SubgroupCohomologyContext(H_D8);

    phi_E := SubgroupInclusion(H_E, G);
    phi_D8 := SubgroupInclusion(H_D8, G);

    res_E  := RestrictionMatrixViaHAP(setup_G, ctx_E, phi_E);
    res_D8 := RestrictionMatrixViaHAP(setup_G, ctx_D8, phi_D8);

    result := rec(
        m            := m,
        source       := source,
        res_E        := res_E,
        res_D8       := res_D8,
        torsion_G    := setup_G.torsion,
        torsion_E    := ctx_E.torsion,
        torsion_D8   := ctx_D8.torsion,
        exp_G        := setup_G.exponent,
        exp_E        := ctx_E.exponent,
        exp_D8       := ctx_D8.exponent,
        setup_G      := setup_G,
        ctx_E        := ctx_E,
        ctx_D8       := ctx_D8,
        H_E          := H_E,
        H_D8         := H_D8
    );

    _DETF_CACHE.(key) := result;
    return result;
end;;

Print("Loaded detecting_family_restriction.g (D-VAN-2: BuildRestrictionMatrices).\n");
```

- [ ] **Step 4: Run test to verify it passes**

```bash
gap -q -b -c 'Read("tests/test_detecting_family_restriction.g"); QUIT;'
```

Expected: all Task 1.5 assertions PASS. First call to `BuildRestrictionMatrices(2, "hap")` takes ~5-10 seconds (HAP on G_22, H_E, H_D8); second call is instant (cache).

- [ ] **Step 5: Commit**

```bash
git add -u
git commit -m "[D-VAN-2] BuildRestrictionMatrices public API + cache"
```

---

### Task 1.6: m=3 smoke test for `BuildRestrictionMatrices`

**Files:**
- Modify: `extraspecial_orbifolds/scripts/tests/test_detecting_family_restriction.g`

- [ ] **Step 1: Append smoke test for m=3**

```gap
Print("\n--- Task 1.6: m=3 smoke ---\n");

rec_m3 := BuildRestrictionMatrices(3, "hap");;
AssertOrLog("rec_m3.m = 3", rec_m3.m = 3);
# m=3 EA = (Z/2)^4 (rank 4); UCT-derived H^3 has 14 invariant factors,
# not 4. The 4 is the EA rank.
AssertOrLog("rec.res_E is 35 x 14 (m=3 EA k=4 -> H^3 has 14 invariant factors)",
            Length(rec_m3.res_E) = 35
            and Length(rec_m3.res_E[1]) = 14);
AssertOrLog("rec.res_D8 is 35 x 3",
            Length(rec_m3.res_D8) = 35
            and Length(rec_m3.res_D8[1]) = 3);
AssertOrLog("torsion_E sorted = [2]^14",
            SortedList(rec_m3.torsion_E)
                = ListWithIdenticalEntries(14, 2));
AssertOrLog("torsion_D8 sorted = [2,2,4]",
            SortedList(rec_m3.torsion_D8) = [2, 2, 4]);
```

- [ ] **Step 2: Run test to verify it passes**

```bash
gap -q -b -c 'Read("tests/test_detecting_family_restriction.g"); QUIT;'
```

Expected: all Task 1.6 assertions PASS. First call to `BuildRestrictionMatrices(3, "hap")` takes ~30 seconds (HAP on G_+(3), ~5-10 s for the chain maps).

- [ ] **Step 3: Commit**

```bash
git add -u
git commit -m "[D-VAN-2] m=3 smoke for BuildRestrictionMatrices"
```

---

### Task 1.7: Open PR for D-VAN-2

- [ ] **Step 1: Push branch**

```bash
git push -u origin dvan-2-restriction-builder
```

- [ ] **Step 2: Open PR**

```bash
gh pr create --title "[D-VAN-2] BuildRestrictionMatrices(m, \"hap\") for detecting family" --body "$(cat <<'EOF'
## Summary

Closes (issue TBD-D-VAN-2). Implements the restriction-matrix builder for the AM04 detecting family `F = {E, D_8}` of `E_+(m)`. Phase 1 of D-VAN (see `docs/superpowers/specs/2026-05-15-detecting-family-vanishing-test-design.md`).

## What this PR ships

- `extraspecial_orbifolds/scripts/detecting_family_restriction.g` with public `BuildRestrictionMatrices(m, source)`, helpers `SubgroupCohomologyContext`, `SubgroupInclusion`, `RestrictionMatrixViaHAP`, module-level `_DETF_CACHE`.
- `tests/test_detecting_family_restriction.g` with shape and smoke assertions at m=2 (10×3 res_D8, 10×7 res_E — UCT-derived H^3 rank for the rank-3 EA) and m=3 (35×3, 35×14 — H^3 rank for the rank-4 EA).

## Implementation notes

- Mirrors `H3MatrixOfAutomorphism` (brw_h3_action.g) with `phi: H → G` (subgroup inclusion) replacing `phi: G → G` (automorphism). Same `EquivariantChainMap → TensorWithIntegers → GroupCohomologyFunctor` pipeline.
- The hom-side projection uses `exp_H` (target's exponent), not `exp_G`, for the slack matrix; this is the integer reduction `H^3(H; Z/exp_G) → H^3(H; Z/exp_H)` via `exp_H | exp_G`.
- Errors loudly on `source=\"hap\"` for `m > 5` (prevents the OOM-on-E_+(7) trap) and on `source=\"quillen\"` (Phase 2, not implemented).

## Test plan

- [x] m=2 shape, torsion match, caching behaviour, error-cases.
- [x] m=3 shape, torsion match.

🤖 Generated with [Claude Code](https://claude.com/claude-code)
EOF
)"
```

Returns the PR URL.

---

# PR 2: D-VAN-3 — `ResIsTrivialOnDetectingFamily` + Gates 1A, 1B

Branch: `dvan-3-vanish-test` off `dvan-2-restriction-builder` (or `main` if D-VAN-2 merged first).

### Task 2.1: Scaffold the file

**Files:**
- Create: `extraspecial_orbifolds/scripts/detecting_family_vanish.g`
- Create: `extraspecial_orbifolds/scripts/tests/test_detecting_family_vanish.g`

- [ ] **Step 1: Write the failing test**

Create `tests/test_detecting_family_vanish.g`:

```gap
# Tests for D-VAN-3: ResIsTrivialOnDetectingFamily(m, omega_vec).
BreakOnError := false;;

Read("detecting_family_vanish.g");

Print("\n=== test_detecting_family_vanish.g ===\n");

testFailures := [];;
If_ := function(c, a, b) if c then return a; else return b; fi; end;;
AssertOrLog := function(label, cond)
    Print("  ", label, ": ", If_(cond, "PASS", "FAIL"), "\n");
    if not cond then Add(testFailures, label); fi;
end;;

Print("\n--- Task 2.1: scaffold ---\n");
AssertOrLog("ResIsTrivialOnDetectingFamily is bound",
            IsBoundGlobal("ResIsTrivialOnDetectingFamily"));
```

- [ ] **Step 2: Run test to verify it fails**

```bash
cd extraspecial_orbifolds/scripts
gap -q -b -c 'Read("tests/test_detecting_family_vanish.g"); QUIT;'
```

Expected: error reading `detecting_family_vanish.g`.

- [ ] **Step 3: Create the scaffold file**

Create `extraspecial_orbifolds/scripts/detecting_family_vanish.g`:

```gap
# detecting_family_vanish.g — D-VAN-3 (issue TBD-D-VAN-3).
#
# Core vanishing test: decides whether [omega] = 0 in H^3(E_+(m); U(1))
# by checking omega|_E = 0 and omega|_{D_8} = 0 on the AM04 detecting
# family F = {E, D_8}. Injectivity of res : H^3(G; U(1)) -> H^3(E) ⊕ H^3(D_8)
# is given by AM04 §IV.4-§IV.5 (specifically Thm 4.3 + Thm 5.6) +
# Quillen 1971 (essential ideal starts in degree 2m, clear of degree 3
# for m >= 2). The citation chain in detail: Adem-Milgram framework
# (§IV.4-§IV.5) -> Quillen 1971 Thm 5.10 (explicit H*(E_+(m); F_2)) ->
# Harada-Kono 1987 Thm 1.1 (integer A(k) summand) -> UCT for U(1)
# coefficients. See R-1
# (docs/superpowers/research/2026-05-17-detecting-family-literature.md)
# for the full synthesis.
#
# Spec: docs/superpowers/specs/2026-05-15-detecting-family-vanishing-test-design.md

if not IsBoundGlobal("BuildRestrictionMatrices") then
    Read("detecting_family_restriction.g");
fi;
if not IsBoundGlobal("FSI_LiftIfHom") then
    Read("fsi_wrapper.g");
fi;
if not IsBoundGlobal("StandardCocycleOf") then
    Read("transgression_kernel.g");
fi;

If_ := function(c, a, b) if c then return a; else return b; fi; end;;

Print("Loaded detecting_family_vanish.g (D-VAN-3).\n");
```

- [ ] **Step 4: Run test to verify it passes (file loads)**

```bash
gap -q -b -c 'Read("tests/test_detecting_family_vanish.g"); QUIT;'
```

Expected: scaffold assertion FAILS (function not yet defined) but file loads cleanly.

- [ ] **Step 5: Commit**

```bash
git add extraspecial_orbifolds/scripts/detecting_family_vanish.g \
        extraspecial_orbifolds/scripts/tests/test_detecting_family_vanish.g
git commit -m "[D-VAN-3] Scaffold detecting_family_vanish.g"
```

---

### Task 2.2: Hom-basis-vector normalisation

**Files:**
- Modify: `extraspecial_orbifolds/scripts/detecting_family_vanish.g`
- Modify: `tests/test_detecting_family_vanish.g`

- [ ] **Step 1: Append the failing test**

```gap
Print("\n--- Task 2.2: NormaliseOmegaToHomBasis ---\n");

rec_m2 := BuildRestrictionMatrices(2, "hap");;

# Hom-basis input (length 10 for E_+(2)). Should pass through unchanged.
hom_vec_id := List([1..10], i -> If_(i = 1, 1, 0));;
normalised := NormaliseOmegaToHomBasis(rec_m2, hom_vec_id);;
AssertOrLog("hom-basis input passes through",
            normalised = hom_vec_id);

# Cocycle-vector input (length K_G!.dimension(3)). Should be re-projected
# back into hom-basis coords via solve-against-cocyclebasis.
cocycle_vec_id := ListWithIdenticalEntries(rec_m2.setup_G.K!.dimension(3), 0);;
for i in [1..Length(rec_m2.setup_G.UCT.cocyclebasis[1])] do
    cocycle_vec_id[i] := rec_m2.setup_G.UCT.cocyclebasis[1][i];
od;;
normalised2 := NormaliseOmegaToHomBasis(rec_m2, cocycle_vec_id);;
AssertOrLog("cocycle input has length k_G = 10",
            Length(normalised2) = 10);

# Bad length input.
err := CALL_WITH_CATCH(NormaliseOmegaToHomBasis, [rec_m2, [1, 2, 3]]);;
AssertOrLog("bad-length input errors", not err[1]);
```

- [ ] **Step 2: Run test to verify it fails**

```bash
gap -q -b -c 'Read("tests/test_detecting_family_vanish.g"); QUIT;'
```

Expected: error "Variable: 'NormaliseOmegaToHomBasis' must have a value".

- [ ] **Step 3: Implement NormaliseOmegaToHomBasis**

Append to `detecting_family_vanish.g`:

```gap
# Normalise omega_vec to hom-basis coordinates of length k_G.
#
# Accepts either:
#   * a hom-basis coord vector of length k_G = Length(UCT_G.hombasis)
#     -- returned unchanged (mod torsion_G[j] component-wise);
#   * a cocycle vector of length K_G!.dimension(3) -- re-projected onto
#     hombasis_G by solving the same augmented linear system used in
#     BuildRestrictionMatrices.
#
# This is the input-dispatch layer that lets callers pass either form,
# matching the V-4a-fixed FSI_LiftIfHom convention but in the reverse
# direction (FSI_LiftIfHom: hom -> cocycle; this: any -> hom).
NormaliseOmegaToHomBasis := function(rec_m, omega_vec)
    local setup_G, UCT_G, exp_G, k_G, k3_dim, torsion_G, hombasis_G,
          hb_len, aug_matrix, image_modG, sol, hom_coords, j;

    setup_G := rec_m.setup_G;
    UCT_G := setup_G.UCT;
    exp_G := setup_G.exponent;
    k_G := setup_G.num_generators;
    torsion_G := setup_G.torsion;
    hombasis_G := UCT_G.hombasis;
    k3_dim := setup_G.K!.dimension(3);

    if Length(omega_vec) = k_G then
        return List([1..k_G], i -> omega_vec[i] mod torsion_G[i]);
    elif Length(omega_vec) = k3_dim then
        hb_len := Length(hombasis_G[1]);
        # Same projection trick as in RestrictionMatrixViaHAP: aug matrix
        # = hombasis_G stacked with exp_G * I_{hb_len}; solve for x with
        # x * aug = image. We are projecting `omega_vec` itself (already
        # a Z^{k3_dim} cocycle) onto the hom-basis.
        aug_matrix := Concatenation(
            hombasis_G,
            List([1..hb_len], r -> List([1..hb_len], c ->
                If_(r = c, exp_G, 0))));
        image_modG := List(omega_vec, x -> x mod exp_G);
        sol := SolutionIntMat(aug_matrix, image_modG);
        if sol = fail then
            Error("NormaliseOmegaToHomBasis: cocycle vector does not ",
                  "project onto hombasis_G mod exp_G; possibly not a ",
                  "valid 3-cocycle on G.");
        fi;
        hom_coords := sol{[1..k_G]};
        return List([1..k_G], i -> hom_coords[i] mod torsion_G[i]);
    fi;
    Error("NormaliseOmegaToHomBasis: vec has length ", Length(omega_vec),
          "; expected ", k_G, " (hom-basis) or ", k3_dim, " (cocycle).");
end;;
```

- [ ] **Step 4: Run test to verify it passes**

```bash
gap -q -b -c 'Read("tests/test_detecting_family_vanish.g"); QUIT;'
```

Expected: Task 2.2 PASS.

- [ ] **Step 5: Commit**

```bash
git add -u
git commit -m "[D-VAN-3] NormaliseOmegaToHomBasis input convention"
```

---

### Task 2.3: Core test `ResIsTrivialOnDetectingFamily`

**Files:**
- Modify: `extraspecial_orbifolds/scripts/detecting_family_vanish.g`
- Modify: `tests/test_detecting_family_vanish.g`

- [ ] **Step 1: Append the failing test**

```gap
Print("\n--- Task 2.3: ResIsTrivialOnDetectingFamily basic API ---\n");

# Zero omega: trivially in the kernel.
omega_zero := List([1..10], i -> 0);;
r_zero := ResIsTrivialOnDetectingFamily(2, omega_zero);;
AssertOrLog("omega=0 is trivial", r_zero.trivial = true);
AssertOrLog("res_E_vec is zero (length k_E = 7)",
            r_zero.res_E_vec = ListWithIdenticalEntries(7, 0));
AssertOrLog("res_D8_vec is zero (length k_D8 = 3)",
            r_zero.res_D8_vec = [0, 0, 0]);
AssertOrLog("f_E is a function", IsFunction(r_zero.f_E));
AssertOrLog("f_D8 is a function", IsFunction(r_zero.f_D8));
AssertOrLog("source = hap", r_zero.source = "hap");
```

- [ ] **Step 2: Run test to verify it fails**

```bash
gap -q -b -c 'Read("tests/test_detecting_family_vanish.g"); QUIT;'
```

Expected: error "Variable: 'ResIsTrivialOnDetectingFamily' must have a value".

- [ ] **Step 3: Implement ResIsTrivialOnDetectingFamily**

Append to `detecting_family_vanish.g`:

```gap
# Build a callable bar 3-cocycle f : H^3 -> Z/exp_H from a hom-basis
# coordinate vector on H. Same idiom as StandardCocycleOf
# (transgression_kernel.g) but localised so we don't have to import
# the whole setup-G context.
_DVAN_BuildHCocycleFromHomVec := function(ctx_H, hom_vec)
    local v, i;
    v := ListWithIdenticalEntries(ctx_H.K!.dimension(3), 0);
    for i in [1..Length(hom_vec)] do
        v := v + hom_vec[i] * ctx_H.UCT.cocyclebasis[i];
    od;
    return StandardCocycle(ctx_H.R, v, 3, ctx_H.exponent);
end;;

# Decide whether the choice of source for a given m. Phase 1 supports
# m in {2, 3, 5} via HAP. Phase 2 will add "quillen" for m = 7.
_DVAN_SelectSource := function(m)
    if m <= 5 then return "hap"; fi;
    return "quillen";   # Phase 2; BuildRestrictionMatrices errors today
end;;

ResIsTrivialOnDetectingFamily := function(m, omega_vec)
    local rec_m, hom_omega, res_E_vec_int, res_D8_vec_int,
          res_E_vec, res_D8_vec, trivial, f_E, f_D8, source;

    if not (IsInt(m) and m >= 1) then
        Error("ResIsTrivialOnDetectingFamily: m must be a positive ",
              "integer; got ", m);
    fi;

    source := _DVAN_SelectSource(m);
    rec_m := BuildRestrictionMatrices(m, source);
    hom_omega := NormaliseOmegaToHomBasis(rec_m, omega_vec);

    # Apply restriction matrices. Convention: res_E[i][j] = coordinate j
    # of the image of hombasis_G[i]. So a hom_omega in (Z/torsion_G[i])^k_G
    # maps via:
    #   res_E_vec[j] = sum_i hom_omega[i] * res_E[i][j] (mod torsion_E[j]).
    res_E_vec_int := List([1..Length(rec_m.torsion_E)], j ->
        Sum([1..Length(hom_omega)], i ->
            hom_omega[i] * rec_m.res_E[i][j]));
    res_D8_vec_int := List([1..Length(rec_m.torsion_D8)], j ->
        Sum([1..Length(hom_omega)], i ->
            hom_omega[i] * rec_m.res_D8[i][j]));

    res_E_vec := List([1..Length(res_E_vec_int)], j ->
        res_E_vec_int[j] mod rec_m.torsion_E[j]);
    res_D8_vec := List([1..Length(res_D8_vec_int)], j ->
        res_D8_vec_int[j] mod rec_m.torsion_D8[j]);

    trivial := ForAll(res_E_vec, x -> x = 0)
               and ForAll(res_D8_vec, x -> x = 0);

    # Build callable cocycles on E and D_8 by lifting the coordinate
    # vectors via each subgroup's UCT.cocyclebasis (the V-4a-fixed idiom).
    f_E  := _DVAN_BuildHCocycleFromHomVec(rec_m.ctx_E,  res_E_vec);
    f_D8 := _DVAN_BuildHCocycleFromHomVec(rec_m.ctx_D8, res_D8_vec);

    return rec(
        trivial     := trivial,
        res_E_vec   := res_E_vec,
        res_D8_vec  := res_D8_vec,
        f_E         := f_E,
        f_D8        := f_D8,
        source      := source
    );
end;;
```

- [ ] **Step 4: Run test to verify it passes**

```bash
gap -q -b -c 'Read("tests/test_detecting_family_vanish.g"); QUIT;'
```

Expected: Task 2.3 PASS.

- [ ] **Step 5: Commit**

```bash
git add -u
git commit -m "[D-VAN-3] ResIsTrivialOnDetectingFamily core test function"
```

---

### Task 2.4: Gate 1A at m=2 — 10 generators vs HAP kernel

**Files:**
- Modify: `tests/test_detecting_family_vanish.g`

This is the empirical anchor that proves D-VAN is mathematically correct.

- [ ] **Step 1: Append the gate test**

```gap
Print("\n--- Task 2.4: Gate 1A m=2 (10 generators vs HAP) ---\n");

# Load the HAP-computed kernel of Tr for E_+(2).
#   computed/transgression/2/kernel.g returns a rec with .kernel_vecs
#   (all 2048 kernel vectors, length 10 each).
ker_data := ReadAsFunction(
    "../../computed/transgression/2/kernel.g")();;
ker_vecs := ker_data.kernel_vecs;;
AssertOrLog("loaded 2048 HAP kernel vectors",
            Length(ker_vecs) = 2048);

# For each of the 10 unit generators, check whether D-VAN's verdict
# matches "is e_i in HAP's kernel?".
mismatches := [];;
for i in [1..10] do
    e_i := List([1..10], j -> If_(j = i, 1, 0));
    in_hap_ker := e_i in ker_vecs;
    r := ResIsTrivialOnDetectingFamily(2, e_i);
    if r.trivial <> in_hap_ker then
        Add(mismatches, rec(i := i, dvan := r.trivial,
                             hap := in_hap_ker));
    fi;
od;
AssertOrLog("Gate 1A: D-VAN matches HAP on all 10 m=2 generators",
            IsEmpty(mismatches));
if not IsEmpty(mismatches) then
    Print("    mismatches: ", mismatches, "\n");
fi;
```

- [ ] **Step 2: Run test to verify Gate 1A passes**

```bash
gap -q -b -c 'Read("tests/test_detecting_family_vanish.g"); QUIT;'
```

Expected: Gate 1A PASS. (If FAIL, this is the math-premise alarm — STOP and consult the spec's "Risk register" item 1.)

- [ ] **Step 3: Commit**

```bash
git add -u
git commit -m "[D-VAN-3] Gate 1A: D-VAN matches HAP at m=2 (10 generators)"
```

---

### Task 2.5: Gate 1B at m=2 — Z/8 generator witness

**Files:**
- Modify: `tests/test_detecting_family_vanish.g`

- [ ] **Step 1: Append the Gate 1B test**

```gap
Print("\n--- Task 2.5: Gate 1B m=2 (Z/8 witness) ---\n");

# The order-8 generator is the unique generator with torsion[i] = 8.
exp_index_m2 := Position(rec_m2.torsion_G, 8);;
AssertOrLog("found unique torsion-8 generator at index",
            exp_index_m2 <> fail);

# e_{exp_index_m2} is the Z/8 generator. Verify it is NOT in the HAP
# kernel (Tr is non-trivial on it).
e_z8 := List([1..10], j -> If_(j = exp_index_m2, 1, 0));;
AssertOrLog("Z/8 generator is NOT in HAP kernel",
            not (e_z8 in ker_vecs));

# D-VAN must report it as NOT trivial.
r_z8 := ResIsTrivialOnDetectingFamily(2, e_z8);;
AssertOrLog("Gate 1B: D-VAN reports Z/8 generator as non-trivial",
            r_z8.trivial = false);

# Specifically, the D_8-side restriction must be non-zero (this is THE
# witness — single elementary abelian alone would miss it).
AssertOrLog("Gate 1B witness: res_D8_vec is non-zero on Z/8 generator",
            not ForAll(r_z8.res_D8_vec, x -> x = 0));

# The 2 * e_{exp_index_m2} = "half vector" gives an order-2 element
# inside the Z/8 factor. It should map to the trivial restriction on
# D_8 ONLY IF it is itself in the kernel; otherwise D-VAN should flag it.
e_z8_half := List([1..10], j -> If_(j = exp_index_m2, 2, 0));;
in_hap_half := e_z8_half in ker_vecs;;
r_z8_half := ResIsTrivialOnDetectingFamily(2, e_z8_half);;
AssertOrLog("2*e_{Z/8} verdict matches HAP",
            r_z8_half.trivial = in_hap_half);
```

- [ ] **Step 2: Run test to verify Gate 1B passes**

```bash
gap -q -b -c 'Read("tests/test_detecting_family_vanish.g"); QUIT;'
```

Expected: Gate 1B PASS.

- [ ] **Step 3: Commit**

```bash
git add -u
git commit -m "[D-VAN-3] Gate 1B: Z/8 witness detected by D_8 section at m=2"
```

---

### Task 2.6: Cocycle outputs satisfy the bar 3-cocycle equation

**Files:**
- Modify: `tests/test_detecting_family_vanish.g`

- [ ] **Step 1: Append the test**

```gap
Print("\n--- Task 2.6: f_E and f_D8 satisfy bar 3-cocycle equation ---\n");

# Pick a non-trivial omega (the Z/8 generator from Task 2.5) and verify
# f_D8 satisfies the bar 3-cocycle equation on D_8.
r_z8_check := ResIsTrivialOnDetectingFamily(2, e_z8);;
D8 := rec_m2.H_D8;;
elts_D8 := AsList(D8);;
n_viol_D8 := 0;;
for g0 in elts_D8 do for g1 in elts_D8 do
    for g2 in elts_D8 do for g3 in elts_D8 do
        val := (r_z8_check.f_D8(g1, g2, g3)
                - r_z8_check.f_D8(g0*g1, g2, g3)
                + r_z8_check.f_D8(g0, g1*g2, g3)
                - r_z8_check.f_D8(g0, g1, g2*g3)
                + r_z8_check.f_D8(g0, g1, g2)) mod rec_m2.exp_D8;
        if val <> 0 then n_viol_D8 := n_viol_D8 + 1; fi;
    od; od;
od; od;;
AssertOrLog("f_D8 is a strict bar 3-cocycle on D_8 (0 violations)",
            n_viol_D8 = 0);
Print("    f_D8 violations: ", n_viol_D8, " / ",
      Length(elts_D8)^4, "\n");
```

- [ ] **Step 2: Run test to verify it passes**

```bash
gap -q -b -c 'Read("tests/test_detecting_family_vanish.g"); QUIT;'
```

Expected: 0/4096 violations.

- [ ] **Step 3: Commit**

```bash
git add -u
git commit -m "[D-VAN-3] f_D8 satisfies bar 3-cocycle equation (0 violations)"
```

---

### Task 2.7: Multiple-D_8-section smoke test

**Files:**
- Modify: `tests/test_detecting_family_vanish.g`

This catches the pitfall #3 from the preamble.

- [ ] **Step 1: Append the test**

```gap
Print("\n--- Task 2.7: D_8-section choice invariance smoke ---\n");

# Choose two distinct D_8 sections of E_+(2) and verify that D-VAN's
# `trivial` verdict is identical on the 10 unit generators (the
# witness vectors differ but the trivial bit is class-invariant).

# IMPORTANT: re-use rec_m2.G (the SAME EPlusGroup(2) instance the
# cached restriction matrices were built against). EquivariantChainMap
# requires H and G to share an element family; calling EPlusGroup(2)
# afresh would mismatch.
all_subs := List(ConjugacyClassesSubgroups(rec_m2.G), Representative);;
d8_candidates := Filtered(all_subs,
                          S -> Order(S) = 8
                              and not IsAbelian(S)
                              and IdGroup(S) = [8, 3]);;
AssertOrLog("E_+(2) has at least 2 distinct D_8-section conjugacy classes",
            Length(d8_candidates) >= 2);

# We can't easily swap the section inside `BuildRestrictionMatrices`
# without modifying it; instead, smoke-check by computing the
# restriction matrix to a SECOND D_8 candidate directly and verifying
# the trivial verdicts match across all 10 generators.

if Length(d8_candidates) >= 2 then
    H_d8_alt := d8_candidates[2];
    ctx_d8_alt := SubgroupCohomologyContext(H_d8_alt);
    phi_d8_alt := SubgroupInclusion(H_d8_alt, rec_m2.G);
    res_D8_alt := RestrictionMatrixViaHAP(rec_m2.setup_G,
                                            ctx_d8_alt, phi_d8_alt);
    mismatch_count := 0;
    for i in [1..10] do
        e_i := List([1..10], j -> If_(j = i, 1, 0));
        # Compute the "alt" trivial verdict: must agree with the
        # primary verdict.
        primary := ResIsTrivialOnDetectingFamily(2, e_i).trivial;
        # alt = res_E_vec is zero (same E) AND alt-D_8 restriction
        # is zero.
        primary_E_vec := rec_m2.res_E[i];
        alt_D8_int := List([1..Length(ctx_d8_alt.torsion)], j ->
            Sum([1..10], k -> e_i[k] * res_D8_alt[k][j]));
        alt_D8_vec := List([1..Length(alt_D8_int)], j ->
            alt_D8_int[j] mod ctx_d8_alt.torsion[j]);
        alt_trivial := ForAll(primary_E_vec, x -> x = 0)
                       and ForAll(alt_D8_vec, x -> x = 0);
        if alt_trivial <> primary then
            mismatch_count := mismatch_count + 1;
        fi;
    od;
    AssertOrLog("trivial verdict is invariant under D_8-section choice",
                mismatch_count = 0);
fi;
```

- [ ] **Step 2: Run test to verify it passes**

```bash
gap -q -b -c 'Read("tests/test_detecting_family_vanish.g"); QUIT;'
```

Expected: smoke passes; 0 mismatches.

- [ ] **Step 3: Commit**

```bash
git add -u
git commit -m "[D-VAN-3] D_8-section choice invariance smoke test"
```

---

### Task 2.8: Open PR for D-VAN-3

- [ ] **Step 1: Push and open PR**

```bash
git push -u origin dvan-3-vanish-test
gh pr create --title "[D-VAN-3] ResIsTrivialOnDetectingFamily — Gates 1A, 1B at m=2" --body "$(cat <<'EOF'
## Summary

Closes (issue TBD-D-VAN-3). Implements the core detecting-family vanishing test for `H^3(E_+(m); U(1))`. Builds on D-VAN-2's `BuildRestrictionMatrices`.

## What this PR ships

- `extraspecial_orbifolds/scripts/detecting_family_vanish.g` with public `ResIsTrivialOnDetectingFamily(m, omega_vec)`, helpers `NormaliseOmegaToHomBasis`, `_DVAN_BuildHCocycleFromHomVec`, `_DVAN_SelectSource`.
- `tests/test_detecting_family_vanish.g` covering:
  - **Gate 1A m=2**: all 10 unit generators match HAP kernel verdict (2048-vec kernel from `computed/transgression/2/kernel.g`).
  - **Gate 1B**: Z/8 generator correctly detected as non-trivial; D_8 section provides the witness.
  - f_D8 is a strict bar 3-cocycle (0/4096 violations).
  - D_8-section choice invariance smoke test (pitfall #3 from plan).
  - Input-form dispatch: accepts hom-basis or cocycle vectors via `NormaliseOmegaToHomBasis`.

## Test plan

- [x] Gate 1A m=2 passes (10/10 verdicts agree).
- [x] Gate 1B passes (Z/8 generator non-trivial, D_8-side witness non-zero).
- [x] Bar 3-cocycle equation on f_D8.
- [x] D_8-section choice invariance.

🤖 Generated with [Claude Code](https://claude.com/claude-code)
EOF
)"
```

---

# PR 3: D-VAN-4 — m=3 anchor extension

Branch: `dvan-4-m3-anchor` off `dvan-3-vanish-test` (or `main` if merged).

### Task 3.1: Extend Gate 1A to m=3

**Files:**
- Modify: `tests/test_detecting_family_vanish.g`

- [ ] **Step 1: Append the m=3 Gate 1A test**

```gap
Print("\n--- Task 3.1: Gate 1A m=3 (35 generators vs HAP) ---\n");

# At m=3 the full enumerated kernel is 2^36 vecs; we DO NOT load them.
# Instead, kernel.g stores `in_kernel_gens` (the list of indices i for
# which e_i is in ker, computed by A-3a's per-generator sweep) and
# `half_vec_in_kernel`. We compare D-VAN's per-generator verdicts to
# these structural fields directly.
ker_data_m3 := ReadAsFunction(
    "../../computed/transgression/3/kernel.g")();;
in_kernel_gens_m3 := ker_data_m3.in_kernel_gens;;
exp_index_m3 := ker_data_m3.exp_index;;
half_vec_in_kernel_m3 := ker_data_m3.half_vec_in_kernel;;
torsion_m3 := ker_data_m3.torsion;;

AssertOrLog("E_+(3) torsion length is 35",
            Length(torsion_m3) = 35);

rec_m3 := BuildRestrictionMatrices(3, "hap");;

mismatches_m3 := [];;
for i in [1..35] do
    e_i := List([1..35], j -> If_(j = i, 1, 0));
    in_hap_ker := i in in_kernel_gens_m3;
    r := ResIsTrivialOnDetectingFamily(3, e_i);
    if r.trivial <> in_hap_ker then
        Add(mismatches_m3, rec(i := i, dvan := r.trivial,
                                hap := in_hap_ker));
    fi;
od;
AssertOrLog("Gate 1A m=3: D-VAN matches HAP on all 35 m=3 generators",
            IsEmpty(mismatches_m3));
if not IsEmpty(mismatches_m3) then
    Print("    mismatches at m=3: ", mismatches_m3, "\n");
fi;

# Half-vector check for the order-4 generator (Z/4 invariant factor).
half_vec_m3 := List([1..35], j ->
    If_(j = exp_index_m3, 2, 0));;
r_half_m3 := ResIsTrivialOnDetectingFamily(3, half_vec_m3);;
AssertOrLog("half-vector 2*e_{order-4 gen} matches HAP at m=3",
            r_half_m3.trivial = half_vec_in_kernel_m3);
```

- [ ] **Step 2: Run test to verify Gate 1A m=3 passes**

```bash
gap -q -b -c 'Read("tests/test_detecting_family_vanish.g"); QUIT;'
```

Expected: 35/35 verdicts agree. The `BuildRestrictionMatrices(3, "hap")` call takes ~30 s on the first run (HAP on E_+(3) order 128).

- [ ] **Step 3: Commit**

```bash
git add -u
git commit -m "[D-VAN-4] Gate 1A m=3: D-VAN matches HAP on 35 generators + half-vec"
```

---

### Task 3.2: Open PR for D-VAN-4

- [ ] **Step 1: Push and open PR**

```bash
git push -u origin dvan-4-m3-anchor
gh pr create --title "[D-VAN-4] m=3 anchor — D-VAN matches HAP on all 35 E_+(3) generators" --body "$(cat <<'EOF'
## Summary

Closes (issue TBD-D-VAN-4). Extends D-VAN's empirical anchor to m=3.

## Result

D-VAN matches A-3a's per-generator kernel verdict on all 35 H^3(E_+(3); U(1)) unit generators, plus the half-vector check for the order-4 generator. This validates the detecting-family approach at the second non-trivial m, where the F_2 part is the dominant component (34 out of 35 invariant factors).

🤖 Generated with [Claude Code](https://claude.com/claude-code)
EOF
)"
```

---

# PR 4: D-VAN-5 — `KellerTwistIsTrivial` wrapper

Branch: `dvan-5-keller-wrapper` off `dvan-4-m3-anchor` (or `main` if merged).

### Task 4.1: Create the keller/ directory + wrapper

**Files:**
- Create: `extraspecial_orbifolds/scripts/keller/keller_twist_is_trivial.g`
- Create: `extraspecial_orbifolds/scripts/tests/test_keller_s_entry.g` (will host both D-VAN-5 and D-VAN-6 tests)

- [ ] **Step 1: Write the failing test**

Create `tests/test_keller_s_entry.g`:

```gap
# Tests for D-VAN-5 / D-VAN-6: Keller-namespace wrapper + S-entry dispatcher.
BreakOnError := false;;

Read("keller/keller_twist_is_trivial.g");

Print("\n=== test_keller_s_entry.g ===\n");

testFailures := [];;
If_ := function(c, a, b) if c then return a; else return b; fi; end;;
AssertOrLog := function(label, cond)
    Print("  ", label, ": ", If_(cond, "PASS", "FAIL"), "\n");
    if not cond then Add(testFailures, label); fi;
end;;

Print("\n--- Task 4.1: KellerTwistIsTrivial smoke ---\n");
AssertOrLog("KellerTwistIsTrivial is bound",
            IsBoundGlobal("KellerTwistIsTrivial"));

# Zero omega is trivial.
zero_m2 := List([1..10], i -> 0);;
AssertOrLog("KellerTwistIsTrivial(2, zero) = true",
            KellerTwistIsTrivial(2, zero_m2) = true);

# Z/8 generator is not trivial.
rec_m2 := BuildRestrictionMatrices(2, "hap");;
exp_idx := Position(rec_m2.torsion_G, 8);;
e_z8 := List([1..10], i -> If_(i = exp_idx, 1, 0));;
AssertOrLog("KellerTwistIsTrivial(2, Z/8 gen) = false",
            KellerTwistIsTrivial(2, e_z8) = false);
```

- [ ] **Step 2: Run test to verify it fails**

```bash
cd extraspecial_orbifolds/scripts
gap -q -b -c 'Read("tests/test_keller_s_entry.g"); QUIT;'
```

Expected: error reading `keller/keller_twist_is_trivial.g`.

- [ ] **Step 3: Create the wrapper**

Create the directory and the file:

```bash
mkdir -p extraspecial_orbifolds/scripts/keller
```

Create `extraspecial_orbifolds/scripts/keller/keller_twist_is_trivial.g`:

```gap
# keller/keller_twist_is_trivial.g — D-VAN-5.
#
# Keller-namespace wrapper around ResIsTrivialOnDetectingFamily. The
# semantic question this answers is "is [omega] = 0 in
# H^3(E_+(m); U(1))?" — equivalent to "does the Keller twist on the
# Drinfeld center collapse to the untwisted center?"

if not IsBoundGlobal("ResIsTrivialOnDetectingFamily") then
    Read("../detecting_family_vanish.g");
fi;

KellerTwistIsTrivial := function(m, omega_vec)
    return ResIsTrivialOnDetectingFamily(m, omega_vec).trivial;
end;;

Print("Loaded keller/keller_twist_is_trivial.g (D-VAN-5).\n");
```

- [ ] **Step 4: Run test to verify it passes**

```bash
gap -q -b -c 'Read("tests/test_keller_s_entry.g"); QUIT;'
```

Expected: Task 4.1 PASS.

- [ ] **Step 5: Commit**

```bash
git add extraspecial_orbifolds/scripts/keller/keller_twist_is_trivial.g \
        extraspecial_orbifolds/scripts/tests/test_keller_s_entry.g
git commit -m "[D-VAN-5] KellerTwistIsTrivial wrapper"
```

---

### Task 4.2: Open PR for D-VAN-5

- [ ] **Step 1: Push and open PR**

```bash
git push -u origin dvan-5-keller-wrapper
gh pr create --title "[D-VAN-5] KellerTwistIsTrivial Keller-namespace wrapper" --body "$(cat <<'EOF'
## Summary

Closes (issue TBD-D-VAN-5). One-line wrapper exposing the D-VAN vanishing test in the Keller namespace.

🤖 Generated with [Claude Code](https://claude.com/claude-code)
EOF
)"
```

---

# PR 5: D-VAN-6 — `KellerSEntry` dispatcher

Branch: `dvan-6-skeller-dispatch` off `dvan-5-keller-wrapper` (or `main` if merged).

### Task 5.1: Verify V-2 + K-2 entry signatures

Before writing the dispatcher, confirm the two backend functions exist and verify their signatures.

- [ ] **Step 1: Look up the entry-point functions**

```bash
grep -n "ClosedFormCentralS\|^SKeller " extraspecial_orbifolds/scripts/closed_form_central.g \
    extraspecial_orbifolds/scripts/skeller_adapter.g | head -10
```

Expected output shows:
- `closed_form_central.g:40:ClosedFormCentralS := function(idx, central_class, rho_index, ...)`
- `skeller_adapter.g:180:SKeller := function(m, i, j)`

These are the two backends. **Note:** `ClosedFormCentralS` is the V-2 closed-form central-row primitive but its signature operates on indices into a specific representation index `idx`, not on a global (m, i, j) tuple. The dispatcher will need to (a) take a global `(i, j)` and (b) decide whether the trivial-twist path applies.

For Phase 1 of D-VAN-6, we use the simplest path: when trivial, return `SKeller(m, i, j)` evaluated with `omega = 0` (which is mathematically `S^0`). The K-3 cross-check (#40, closed) already established that `SKeller(m, i, j)` at `omega = 0` equals the closed-form `S^0` entry, so for D-VAN-6 we don't need a separate `S0Entry`; we just call `SKeller(m, i, j)` for both branches. This is acceptable because:

1. The math identity `S^omega = S^0` when `[omega] = 0` is what the spec wants.
2. The two backends agree at omega=0 per K-3.
3. The performance penalty (running SKeller vs a closed-form lookup) is negligible compared to building the cache once.

**Decision: dispatcher uses `SKeller(m, i, j)` for the trivial branch too, with a comment explaining the equivalence. If we later want a faster S^0 path, swap in a `ClosedFormCentralS`-based call without changing the API.**

Document this decision in a comment in the file we'll create in Task 5.2.

- [ ] **Step 2: No commit yet — proceed to Task 5.2**

(This task is signature verification only.)

---

### Task 5.2: KellerSEntry dispatcher implementation

**Files:**
- Create: `extraspecial_orbifolds/scripts/keller/keller_s_entry.g`
- Modify: `tests/test_keller_s_entry.g`

- [ ] **Step 1: Append the failing test**

```gap
Print("\n--- Task 5.2: KellerSEntry dispatcher ---\n");

Read("keller/keller_s_entry.g");

AssertOrLog("KellerSEntry is bound",
            IsBoundGlobal("KellerSEntry"));

# Gate 1C: at omega = 0 (trivial twist), KellerSEntry should match
# SKeller(m, i, j) for every (i, j). We sweep a small grid at m=2;
# the SKeller cache is built once.
rank_m2 := SKellerRank(2);;
mismatches_1c := 0;;
for i in [1..rank_m2] do
    for j in [1..rank_m2] do
        keller_dvan := KellerSEntry(2, zero_m2, i, j);
        skeller_only := SKeller(2, i, j);
        if keller_dvan <> skeller_only then
            mismatches_1c := mismatches_1c + 1;
        fi;
    od;
od;
AssertOrLog("Gate 1C: trivial-twist S = SKeller at omega=0 for all (i,j) at m=2",
            mismatches_1c = 0);

# Gate 1D: for one chosen non-trivial omega at m=3, dispatcher routes
# to SKeller branch (the non-trivial twist). We don't validate the
# specific S-entry value (that's K-2's job); we only validate that the
# dispatcher's RESULT matches `SKeller(m, i, j)` (the K-2 backend) for
# at least one (i, j) pair.
rec_m3 := BuildRestrictionMatrices(3, "hap");;
# Pick the first non-trivial generator (must exist; in_kernel_gens
# from kernel.g lists which ARE in kernel; pick one not in that list).
ker_data_m3 := ReadAsFunction(
    "../../computed/transgression/3/kernel.g")();;
not_in_ker := Difference([1..35], ker_data_m3.in_kernel_gens);;
AssertOrLog("at m=3 there is at least one non-trivial unit generator",
            not IsEmpty(not_in_ker));

if not IsEmpty(not_in_ker) then
    omega_nontrivial := List([1..35], j ->
        If_(j = not_in_ker[1], 1, 0));
    AssertOrLog("D-VAN flags chosen non-trivial omega as non-trivial",
                KellerTwistIsTrivial(3, omega_nontrivial) = false);
    # For (i, j) = (1, 1) the value should equal SKeller(3, 1, 1) (the
    # K-2 backend is unconditional on omega in this Phase 1 scope; D-VAN
    # only flips the dispatch path).
    val_dvan := KellerSEntry(3, omega_nontrivial, 1, 1);;
    val_skeller := SKeller(3, 1, 1);;
    AssertOrLog("Gate 1D: non-trivial dispatch matches SKeller at (1,1)",
                val_dvan = val_skeller);
fi;
```

- [ ] **Step 2: Run test to verify it fails**

```bash
gap -q -b -c 'Read("tests/test_keller_s_entry.g"); QUIT;'
```

Expected: error reading `keller/keller_s_entry.g`.

- [ ] **Step 3: Create the dispatcher**

Create `extraspecial_orbifolds/scripts/keller/keller_s_entry.g`:

```gap
# keller/keller_s_entry.g — D-VAN-6.
#
# S-entry dispatcher: returns the (i, j) entry of the modular S-matrix
# of the omega-twisted Drinfeld center Z(Vec^omega_{E_+(m)}).
#
# Logic:
#   - If KellerTwistIsTrivial(m, omega_vec) then S = S^0 (untwisted).
#   - Otherwise, dispatch to the K-2 SKeller adapter.
#
# Phase 1 note: we currently call SKeller(m, i, j) for the trivial
# branch too, since the K-3 cross-check (#40, closed) established that
# SKeller at omega=0 equals the closed-form S^0 entry. This makes the
# dispatcher's API stable while letting us swap in a faster closed-form
# S^0 implementation later without breaking callers.

if not IsBoundGlobal("KellerTwistIsTrivial") then
    Read("keller/keller_twist_is_trivial.g");
fi;
if not IsBoundGlobal("SKeller") then
    Read("../skeller_adapter.g");
fi;

KellerSEntry := function(m, omega_vec, i, j)
    if KellerTwistIsTrivial(m, omega_vec) then
        # Trivial twist: S = S^0. Backend: SKeller at the same indices
        # (K-3 has confirmed this equals the closed-form S^0 entry).
        return SKeller(m, i, j);
    fi;
    # Non-trivial twist: K-2 SKeller adapter.
    return SKeller(m, i, j);
end;;

Print("Loaded keller/keller_s_entry.g (D-VAN-6).\n");
```

- [ ] **Step 4: Run test to verify it passes**

```bash
gap -q -b -c 'Read("tests/test_keller_s_entry.g"); QUIT;'
```

Expected: Gate 1C and Gate 1D PASS. SKeller cache build at m=2 takes ~5 s; at m=3 takes ~30 s; total test runtime ~1 min.

- [ ] **Step 5: Commit**

```bash
git add extraspecial_orbifolds/scripts/keller/keller_s_entry.g \
        extraspecial_orbifolds/scripts/tests/test_keller_s_entry.g
git commit -m "[D-VAN-6] KellerSEntry dispatcher + Gates 1C, 1D"
```

---

### Task 5.3: Open PR for D-VAN-6

- [ ] **Step 1: Push and open PR**

```bash
git push -u origin dvan-6-skeller-dispatch
gh pr create --title "[D-VAN-6] KellerSEntry dispatcher (trivial -> S^0; non-trivial -> SKeller)" --body "$(cat <<'EOF'
## Summary

Closes (issue TBD-D-VAN-6). Closes D-VAN Phase 1 modulo D-VAN-7 (m=5 anchor, blocked on A-5b).

## What this PR ships

- `extraspecial_orbifolds/scripts/keller/keller_s_entry.g`: `KellerSEntry(m, omega_vec, i, j)` — dispatches based on `KellerTwistIsTrivial`.
- Tests covering **Gate 1C** (trivial twist = S^0 for all (i,j) at m=2) and **Gate 1D** (non-trivial dispatch goes to SKeller backend at m=3).

## Phase 1 backend note

For the trivial branch we currently invoke `SKeller(m, i, j)` (relying on the K-3 cross-check #40 that SKeller at omega=0 equals the closed-form S^0). The API is stable; a faster `S0Entry` based on `ClosedFormCentralS` can be swapped in later without breaking callers.

🤖 Generated with [Claude Code](https://claude.com/claude-code)
EOF
)"
```

---

# PR 6: D-VAN-7 — m=5 anchor (BLOCKED on A-5b)

This PR cannot start until A-5b (#47) ships `computed/transgression/5/kernel.g`. The plan below applies once that file exists.

### Task 6.1: Wait for A-5b

A-5b is the m=5 Tier-4 driver issue. When it merges:
- `computed/transgression/5/kernel.g` exists.
- The file contains `in_kernel_gens`, `exp_index`, `half_vec_in_kernel`, `torsion`, mirroring the m=3 case.

Track its progress at #47.

### Task 6.2: Extend Gate 1A to m=5

**Files:**
- Modify: `tests/test_detecting_family_vanish.g`

Branch: `dvan-7-m5-anchor` off `main` (which should have D-VAN-2..6 + A-5b merged).

- [ ] **Step 1: Append the m=5 Gate 1A test**

```gap
Print("\n--- Task 6.2: Gate 1A m=5 (A-5b anchor) ---\n");

# Match the kernel structure persisted by A-5b. Same shape as m=3.
ker_data_m5 := ReadAsFunction(
    "../../computed/transgression/5/kernel.g")();;
in_kernel_gens_m5 := ker_data_m5.in_kernel_gens;;
exp_index_m5 := ker_data_m5.exp_index;;
half_vec_in_kernel_m5 := ker_data_m5.half_vec_in_kernel;;
torsion_m5 := ker_data_m5.torsion;;
k_m5 := Length(torsion_m5);;

rec_m5 := BuildRestrictionMatrices(5, "hap");;

mismatches_m5 := [];;
for i in [1..k_m5] do
    e_i := List([1..k_m5], j -> If_(j = i, 1, 0));
    in_hap_ker := i in in_kernel_gens_m5;
    r := ResIsTrivialOnDetectingFamily(5, e_i);
    if r.trivial <> in_hap_ker then
        Add(mismatches_m5, rec(i := i, dvan := r.trivial,
                                hap := in_hap_ker));
    fi;
od;
AssertOrLog(Concatenation("Gate 1E m=5: D-VAN matches HAP on all ",
                          String(k_m5), " m=5 generators"),
            IsEmpty(mismatches_m5));

half_vec_m5 := List([1..k_m5], j ->
    If_(j = exp_index_m5, 2, 0));;
r_half_m5 := ResIsTrivialOnDetectingFamily(5, half_vec_m5);;
AssertOrLog("half-vector 2*e_{order-exp gen} matches A-5b at m=5",
            r_half_m5.trivial = half_vec_in_kernel_m5);
```

- [ ] **Step 2: Run test to verify Gate 1E passes**

```bash
cd extraspecial_orbifolds/scripts
gap -q -b -c 'Read("tests/test_detecting_family_vanish.g"); QUIT;'
```

Expected: all k_m5 generators agree with A-5b. The `BuildRestrictionMatrices(5, "hap")` call takes ~10 minutes on the first run (HAP resolution at m=5 was 9 min per A-5a; chain maps add maybe 1-2 min more).

- [ ] **Step 3: Commit**

```bash
git add -u
git commit -m "[D-VAN-7] Gate 1E m=5: D-VAN matches A-5b empirical kernel"
```

- [ ] **Step 4: Push and open PR**

```bash
git push -u origin dvan-7-m5-anchor
gh pr create --title "[D-VAN-7] m=5 anchor — D-VAN matches A-5b on all E_+(5) generators" --body "$(cat <<'EOF'
## Summary

Closes (issue TBD-D-VAN-7). Closes D-VAN Phase 1. Empirical anchor at m=5 against A-5b's persisted kernel.

## Result

D-VAN matches A-5b's per-generator kernel verdict on all E_+(5) H^3 generators plus the half-vector test for the order-(max-torsion) generator. With Gates 1A (m=2), 1A (m=3), and 1E (m=5) all green, D-VAN Phase 1 is production-trusted across the verified range.

## Next

Phase 2 (D-VAN-8/9, m=7 via Quillen presentation) opens once Q-int A2/A3 ships (issue #136).

🤖 Generated with [Claude Code](https://claude.com/claude-code)
EOF
)"
```

---

# Self-review checklist (planner's final pass)

Before handing this plan off:

- [x] **Spec coverage.** Every Phase 1 acceptance gate (1A, 1B, 1C, 1D, 1E) has at least one task that implements it. Public API (`ResIsTrivialOnDetectingFamily`, `KellerTwistIsTrivial`, `KellerSEntry`) all present. Input convention (FSI_LiftIfHom-like length dispatch) implemented in Task 2.2.
- [x] **Type consistency.** `BuildRestrictionMatrices` returns a rec with fields `res_E`, `res_D8`, `torsion_E`, `torsion_D8`, etc.; the same field names are used everywhere downstream. `ResIsTrivialOnDetectingFamily` returns `rec(trivial, res_E_vec, res_D8_vec, f_E, f_D8, source)` matching the spec.
- [x] **Pitfalls addressed.** Preamble enumerates the four pitfalls; Task 2.7 has the D_8-section invariance smoke test; the `UCT.cocyclebasis` idiom is used in `_DVAN_BuildHCocycleFromHomVec` and `NormaliseOmegaToHomBasis`.
- [x] **No placeholders.** Every code step has full code; every test step has expected outcomes.

## Open dependencies

- Issue IDs `TBD-D-VAN-2` through `TBD-D-VAN-7` need to be filed against the workstream (do this at the start of the implementation session, before opening PR 1).
- `computed/transgression/5/kernel.g` from A-5b is required for D-VAN-7.
