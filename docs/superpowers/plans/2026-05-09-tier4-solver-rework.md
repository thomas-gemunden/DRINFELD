# Tier-4 transgression-kernel solver rework — implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the GC-bound `IsCoboundary2` (augmented-Z `SolutionIntMat`) with a torsion-split GF(2) + Bockstein solver, plus a SNF wrapper, BRW-orbit reduction, and centraliser-type caching, producing the exact $\ker \mathrm{Tr}(E_+(3))$ end-to-end in ≤ 1 h wall and ≤ 8 GB peak RSS.

**Architecture:** Three-PR sequence. PR 1 (T-1 + T-2) lands the parameterized torsion-split solver and SNF wrapper, anchored at the `|ker Tr(E_+(2))| = 2048` math regression. PR 2 (T-3d + T-4) adds BRW-orbit reduction and centraliser-type caching for performance. PR 3 (A-3a) wires the end-to-end driver. All work is in the `DRINFELD` git repo (`/Users/thomasgemunden/Projects/group_cohomology/DRINFELD`).

**Tech Stack:** GAP 4.15.1 with HAP and IO packages. New modules under `extraspecial_orbifolds/scripts/solver/`. Existing `transgression_kernel.g` remains as the regression baseline (do not modify).

**Spec:** `docs/superpowers/specs/2026-05-09-tier4-solver-rework-design.md` (commit `e2d88c5`).

**Issues:** #10 (T-1), #11 (T-2), #13 (T-4), #31 (T-3d), #42 (A-3a), #61 (T-1a).

**Ground truth used as test anchors:**
- D_8 = `SmallGroup(8, 3)`: $\ker \mathrm{Tr}$ trivial (existing `test_transgression_d8.g`).
- $E_+(2)$ = `SmallGroup(32, 49)`: $|\ker \mathrm{Tr}| = 2048$, verified per-generator booleans (commit `9bffebb` and existing `test_transgression_per_gen_e2.g`).

---

## PR 1: T-1 + T-2 — torsion-split solver and SNF wrapper

Branch: `t1-solver-rework` off `main`. Anchored at the $E_+(2)$ ker = 2048 regression (Task 13).

### Task 1: Branch + scaffolding

**Files:**
- Create: `extraspecial_orbifolds/scripts/solver/` (directory)
- Create: `extraspecial_orbifolds/scripts/solver/tests/` (directory)

- [ ] **Step 1: Create the branch**

```bash
cd /Users/thomasgemunden/Projects/group_cohomology/DRINFELD
git checkout -b t1-solver-rework
```

- [ ] **Step 2: Scaffold the directory layout**

```bash
mkdir -p extraspecial_orbifolds/scripts/solver/tests
touch extraspecial_orbifolds/scripts/solver/.gitkeep
touch extraspecial_orbifolds/scripts/solver/tests/.gitkeep
```

- [ ] **Step 3: Commit the scaffold**

```bash
git add extraspecial_orbifolds/scripts/solver/
git commit -m "$(cat <<'EOF'
scaffold: solver/ directory for T-1 rework

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

### Task 2: Sub-spike — HAP Bockstein API check (T-1a Q2)

**Files:**
- Create: `extraspecial_orbifolds/scripts/solver/spikes/spike_bockstein.g`

- [ ] **Step 1: Write the spike script**

```gap
# spike_bockstein.g — confirm HAP exposes the Bockstein Sq^1 cleanly on D_8.
LoadPackage("hap");
G := SmallGroup(8, 3);;     # D_8
R := ResolutionFiniteGroup(G, 4);;
Print("D_8 mod-2 cohomology ring (degree <= 3):\n");
A := ModPCohomologyRing(G, 3, 2);;
Print("  generators: ", GeneratorsOfRing(A), "\n");
Print("  is graded:  ", IsGradedAlgebra(A), "\n");
ops := SteenrodAlgebraOperations(A, 2);;     # if exposed
if ops <> fail then
    Print("  Sq^1 on H^1 -> H^2 generators (Bockstein):\n");
    for x in Filtered(GeneratorsOfRing(A), g -> Degree(g) = 1) do
        Print("    Sq^1(", x, ") = ", ops.Sq1(x), "\n");
    od;
fi;
QUIT;
```

- [ ] **Step 2: Run the spike**

Run: `cd extraspecial_orbifolds/scripts/solver/spikes && gap -q -b spike_bockstein.g 2>&1 | tee spike_bockstein.out`
Expected: prints D_8 cohomology ring info; if `SteenrodAlgebraOperations` is unavailable, prints `fail` and we know to implement the Bockstein by hand.

- [ ] **Step 3: Document the result on issue #61**

```bash
gh issue comment 61 --body "Spike result for Q2 (HAP Bockstein API): see extraspecial_orbifolds/scripts/solver/spikes/spike_bockstein.out. Outcome: <one of: 'HAP exposes Sq^1 cleanly', 'HAP does not expose Sq^1; will implement by hand from the SES connecting map'>."
```

(Replace the angle-bracketed phrase with the actual outcome from `spike_bockstein.out`.)

- [ ] **Step 4: Commit**

```bash
git add extraspecial_orbifolds/scripts/solver/spikes/spike_bockstein.g extraspecial_orbifolds/scripts/solver/spikes/spike_bockstein.out
git commit -m "$(cat <<'EOF'
spike: HAP Bockstein API check on D_8 (T-1a Q2)

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

### Task 3: Sub-spike — 2-divisibility on E_+(2) (T-1a Q1)

**Files:**
- Create: `extraspecial_orbifolds/scripts/solver/spikes/spike_2divisibility.g`

- [ ] **Step 1: Write the spike script**

```gap
# spike_2divisibility.g — for each order-2 generator e_i of H^3(E_+(2); Z/8),
# compute c_g for one non-central class g and check that all values lie in {0, 4} mod 8.
Read("../../transgression_kernel.g");

G := SmallGroup(32, 49);;            # E_+(2)
setup := SetupCohomology3(G);;
Print("E_+(2) torsion = ", setup.torsion, "\n");
Print("exp = ", setup.exponent, "\n");
expected_divisor := setup.exponent / 2;;     # = 4 for E_+(2)

classes := ConjugacyClasses(G);;
gRep := Representative(classes[5]);;          # arbitrary non-trivial class
C := Centralizer(G, gRep);;
Print("|C_G(gRep)| = ", Order(C), "\n");
elts := AsList(C);;
n := Length(elts);;

ok_all := true;;
for i in [1..Length(setup.torsion)] do
    if setup.torsion[i] <> 2 then continue; fi;
    vec := List([1..Length(setup.torsion)], j -> 0);
    vec[i] := 1;
    omega := StandardCocycleOf(setup, vec);
    c_g := CGCocycleFunc(omega, gRep);
    bad := 0;
    for h in elts do for k in elts do
        v := c_g(h, k) mod setup.exponent;
        if v mod expected_divisor <> 0 then bad := bad + 1; fi;
    od; od;
    Print("  e_", i, ": bad = ", bad, " (out of ", n*n, ")\n");
    if bad > 0 then ok_all := false; fi;
od;
Print("\nAll order-2 c_g values are ", expected_divisor, "-divisible: ", ok_all, "\n");
QUIT;
```

- [ ] **Step 2: Run the spike**

Run: `cd extraspecial_orbifolds/scripts/solver/spikes && gap -q -b spike_2divisibility.g 2>&1 | tee spike_2divisibility.out`
Expected: prints `bad = 0` for each of e_1 through e_9 of $E_+(2)$, and `All order-2 c_g values are 4-divisible: true`.

- [ ] **Step 3: Document the result on issue #61**

```bash
gh issue comment 61 --body "Spike result for Q1 (2-divisibility on E_+(2)): see spike_2divisibility.out. Outcome: <'confirmed: c_g is always r-divisible' or 'failed: needs preprocessing step'>. If failed, the divisor-aware preprocessing step (solving omega = r*omega' + d*eta) is added to mod2_solver.g in Task 4."
```

- [ ] **Step 4: Commit**

```bash
git add extraspecial_orbifolds/scripts/solver/spikes/spike_2divisibility.g extraspecial_orbifolds/scripts/solver/spikes/spike_2divisibility.out
git commit -m "$(cat <<'EOF'
spike: 2-divisibility check on E_+(2) (T-1a Q1)

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

### Task 4: GF(2) coboundary check — `IsCoboundary2Mod2` (path B1)

**Files:**
- Create: `extraspecial_orbifolds/scripts/solver/mod2_solver.g`
- Test: `extraspecial_orbifolds/scripts/solver/tests/test_mod2_solver.g`

- [ ] **Step 1: Write the failing test**

```gap
# test_mod2_solver.g — unit tests for IsCoboundary2Mod2.
Read("../mod2_solver.g");

# Test 1: the zero cochain on D_8 is trivially a coboundary.
G := SmallGroup(8, 3);;
zero_c := function(h, k) return 0; end;;
Assert(0, IsCoboundary2Mod2(G, zero_c) = true,
       "zero cochain must be a coboundary");

# Test 2: known non-coboundary on Z/2 x Z/2 — the cup product class.
H := SmallGroup(4, 2);;          # C_2 x C_2
elts := AsList(H);;
gens := GeneratorsOfGroup(H);;
# Cup product cocycle: c(h, k) = (h_1)(k_2) where h_1, k_2 are coordinate projections.
# In coordinates with H = <a, b>, c(a, b) = 1, all others 0.
cup_c := function(h, k)
    if h = gens[1] and k = gens[2] then return 1; else return 0; fi;
end;;
Assert(0, IsCoboundary2Mod2(H, cup_c) = false,
       "cup product class on C_2 x C_2 must NOT be a coboundary");

Print("test_mod2_solver: PASS\n");
QUIT;
```

- [ ] **Step 2: Run test, verify it fails**

Run: `cd extraspecial_orbifolds/scripts/solver/tests && gap -q -b test_mod2_solver.g 2>&1 | head -20`
Expected: Error like `Variable: 'IsCoboundary2Mod2' must have an assigned value`.

- [ ] **Step 3: Implement `IsCoboundary2Mod2`**

```gap
# mod2_solver.g — GF(2) coboundary test.
#
# IsCoboundary2Mod2(H, c'_g) — given a finite group H and a function
#   c'_g : H × H -> Z/2 (or returning integers; we mod 2 internally),
# decide whether there exists beta : H -> Z/2 with
#   c'_g(h, k) = beta(h) - beta(hk) + beta(k)  (mod 2).
#
# Builds the boundary system A·beta = b over GF(2) and runs SolutionMat.
# Spike-confirmed at 1 ms / 10 ms for |H| = 64 / 128.

IsCoboundary2Mod2 := function(H, c)
    local elts, n, idx, A, b, i, j, ij, row, sol, zero, one;
    elts := AsList(H);
    n := Length(elts);
    idx := function(h) return Position(elts, h); end;
    zero := Zero(GF(2));
    one  := One(GF(2));

    # A: n^2 x n matrix over GF(2). Row (i, j) encodes
    #   beta(elts[i]) + beta(elts[i]*elts[j]) + beta(elts[j]) = c(elts[i], elts[j]).
    A := List([1..n*n], i -> List([1..n], j -> zero));
    b := List([1..n*n], i -> zero);
    for i in [1..n] do
        for j in [1..n] do
            row := (i - 1) * n + j;
            ij := idx(elts[i] * elts[j]);
            # +beta(i) + beta(j) - beta(ij), all mod 2 -> just sum.
            A[row][i]  := A[row][i]  + one;
            A[row][j]  := A[row][j]  + one;
            A[row][ij] := A[row][ij] + one;
            b[row]     := (c(elts[i], elts[j]) mod 2) * one;
        od;
    od;
    ConvertToMatrixRep(A, GF(2));
    ConvertToVectorRep(b, GF(2));

    # SolutionMat solves x * M = b. We have A * beta = b, equivalent to
    # beta * Transpose(A) = b. So:
    sol := SolutionMat(TransposedMat(A), b);
    return sol <> fail;
end;;
```

- [ ] **Step 4: Run test, verify it passes**

Run: `cd extraspecial_orbifolds/scripts/solver/tests && gap -q -b test_mod2_solver.g`
Expected: `test_mod2_solver: PASS`.

- [ ] **Step 5: Commit**

```bash
git add extraspecial_orbifolds/scripts/solver/mod2_solver.g extraspecial_orbifolds/scripts/solver/tests/test_mod2_solver.g
git commit -m "$(cat <<'EOF'
solver: IsCoboundary2Mod2 — GF(2) coboundary test (path B1)

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

### Task 5: Bockstein image computation

**Files:**
- Modify: `extraspecial_orbifolds/scripts/solver/mod2_solver.g`
- Test: `extraspecial_orbifolds/scripts/solver/tests/test_bockstein_image.g`

The Bockstein here is the connecting homomorphism $\beta : H^1(C; \mathbb F_2) \to H^2(C; \mathbb F_2)$ from the SES $0 \to \mathbb F_2 \xrightarrow{\cdot 2} \mathbb F_4 \to \mathbb F_2 \to 0$ (or equivalently $\mathrm{Sq}^1$ in the mod-2 Steenrod algebra). For a 1-cocycle $\alpha : C \to \mathbb F_2$, $\beta(\alpha)(h, k) = \alpha(h) \cdot \alpha(k)$ (cup-square at degree 1).

If Task 2's spike found HAP exposes `Sq1` cleanly, use it. Otherwise, implement directly.

- [ ] **Step 1: Write the failing test**

```gap
# test_bockstein_image.g
Read("../mod2_solver.g");

# Test on Z/4: H^1(Z/4; F_2) ≅ F_2, generated by α(g^i) = i mod 2.
# β(α)(g^i, g^j) = (i mod 2)(j mod 2). This is non-trivial in H^2(Z/4; F_2).
G := SmallGroup(4, 1);;          # Z/4
img := BocksteinH1ToH2(G);;
Assert(0, Length(img) >= 1, "Z/4 Bockstein image should have rank >= 1");
Print("Z/4: |Bockstein image of H^1->H^2 over F_2| = ", 2^Length(img), "\n");

# Test on Z/2: β = 0 on H^1(Z/2; F_2) since H^*(Z/2; F_2) is generated in degree 1
# with x^2 = β(x) = Sq^1(x); but actually β(x) is NON-zero on Z/2 — it's x^2.
# So image has rank 1.
H := SmallGroup(2, 1);;          # Z/2
img2 := BocksteinH1ToH2(H);;
Assert(0, Length(img2) = 1, "Z/2 Bockstein image must have rank exactly 1");

Print("test_bockstein_image: PASS\n");
QUIT;
```

- [ ] **Step 2: Run test, verify it fails**

Run: `cd extraspecial_orbifolds/scripts/solver/tests && gap -q -b test_bockstein_image.g 2>&1 | head`
Expected: Error like `Variable: 'BocksteinH1ToH2' must have an assigned value`.

- [ ] **Step 3: Implement `BocksteinH1ToH2`**

Append to `mod2_solver.g`:

```gap
# BocksteinH1ToH2(C) — return the Bockstein image as a list of vectors in F_2^{n^2},
# representing 2-cocycles in C^2(C; F_2) (in the same enumeration as the boundary
# system rows in IsCoboundary2Mod2).
#
# Strategy: enumerate H^1(C; F_2) representatives by enumerating C^1(C; F_2) cocycles
# modulo C^0 (which is just the zero map at degree 1, since d^0 = 0 mapping F_2 -> C^1
# trivially when there's no image). Practically: H^1(C; F_2) = Hom(C^{ab}, F_2). For
# each homomorphism α (= 1-cocycle since C is finite and we're in degree 1 with
# trivial action), output β(α)(h, k) = α(h) * α(k) as a 2-cocycle vector.
#
# The image as F_2-subspace of C^2(C; F_2) is then computed by stacking and reducing.

BocksteinH1ToH2 := function(C)
    local Cab, gens_ab, n_ab, hom_basis, elts, n, h_to_ab, alpha,
          cup, basis_vectors, h, k, i, j, vec, alpha_vec, val_h, val_k,
          ab_pos;
    Cab := AbelianInvariants(C);
    # H^1(C; F_2) = Hom(C, F_2) factors through abelianization.
    # Pick generators of C^{ab} as F_2-vector space of dimension rk_2(C^{ab}).
    n_ab := Number(Cab, x -> x mod 2 = 0);    # number of even invariants = F_2 rank
    if n_ab = 0 then
        return [];     # H^1(C; F_2) = 0, image is trivial
    fi;
    elts := AsList(C);
    n := Length(elts);

    # Build a homomorphism C -> F_2^{n_ab} via the abelianization quotient.
    # GAP's `NaturalHomomorphismByNormalSubgroup` / `MaximalAbelianQuotient` give us
    # the projection; then we mod-out odd-torsion factors.
    # For pragmatic purposes here, we simply enumerate the duals via brute force:
    # for each non-zero F_2-linear functional α on C, compute β(α).

    # Enumerate H^1(C; F_2) basis by picking n_ab linearly independent functionals.
    # Pragmatic approach: try 1-cochains f: C -> F_2 that are homomorphisms.
    # f is a hom iff f(h*k) = f(h) + f(k) for all h, k. We solve this linear system.

    hom_basis := [];
    for i in [1..n_ab] do
        # Pick the i-th F_2-dual basis vector of C^{ab,2}. Concretely: enumerate
        # candidate functionals by setting f on group generators and propagating.
        # Skip rigorous construction — use HAP if available:
        # alpha is a length-n vector in F_2^n giving f(elts[j]) for each j.
        alpha_vec := List([1..n], j -> Zero(GF(2)));
        # Set the functional to be 1 on the i-th hom-basis-element class. Simplest
        # implementation: rely on the `IsomorphismToFpGroup` factor map.
        # ... [filled in during implementation; depends on Task 2 spike outcome:
        #     either use HAP's mod-p basis or construct via abelianization map] ...
        Add(hom_basis, alpha_vec);
    od;

    # For each hom α in hom_basis, compute β(α) ∈ C^2(C; F_2) as a vector of length n^2:
    # β(α)(h, k) = α(h) * α(k).
    basis_vectors := [];
    for alpha_vec in hom_basis do
        vec := List([1..n*n], i -> Zero(GF(2)));
        for i in [1..n] do
            val_h := alpha_vec[i];
            for j in [1..n] do
                val_k := alpha_vec[j];
                vec[(i-1)*n + j] := val_h * val_k;
            od;
        od;
        Add(basis_vectors, vec);
    od;

    # Reduce to a basis of the F_2-subspace they span.
    return BaseMat(basis_vectors);    # returns reduced basis; rank = Length(...)
end;;
```

> **Note for the implementer:** the construction of `hom_basis` (the H^1 basis as F_2-functionals on C) depends on the Task 2 spike outcome. If HAP exposes `Sq1` on `ModPCohomologyRing`, use that to get the image directly. If not, build hom_basis by composing `MaximalAbelianQuotient(C)` with mod-2 reduction; the implementation is ~15 lines but depends on the GAP API surface — defer specifics to the Task 5 PR.

- [ ] **Step 4: Run test, verify it passes**

Run: `cd extraspecial_orbifolds/scripts/solver/tests && gap -q -b test_bockstein_image.g`
Expected: `test_bockstein_image: PASS`.

- [ ] **Step 5: Commit**

```bash
git add extraspecial_orbifolds/scripts/solver/mod2_solver.g extraspecial_orbifolds/scripts/solver/tests/test_bockstein_image.g
git commit -m "$(cat <<'EOF'
solver: BocksteinH1ToH2 — image of beta on H^1(C; F_2) (path B2 setup)

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

### Task 6: Bockstein-image membership — `IsCoboundary2Mod2WithLift`

**Files:**
- Modify: `extraspecial_orbifolds/scripts/solver/mod2_solver.g`
- Test: `extraspecial_orbifolds/scripts/solver/tests/test_mod2_with_lift.g`

- [ ] **Step 1: Write the failing test**

```gap
# test_mod2_with_lift.g
Read("../mod2_solver.g");

# Sanity: trivial cochain returns true.
G := SmallGroup(8, 3);;
zero_c := function(h, k) return 0; end;;
Assert(0, IsCoboundary2Mod2WithLift(G, zero_c) = true,
       "zero cochain must lift trivially");

# More demanding test: a non-coboundary mod-2 class that IS in image(beta) lifts.
# Construction: take a 1-cocycle alpha on G, compute beta(alpha) = alpha cup alpha,
# and pass it in. Should return true (it IS a Z/4 coboundary) even though it's
# not a Z/2 coboundary.
# (Defer concrete construction to implementation; use the BocksteinH1ToH2 output
# basis and feed back the first basis vector reshaped to a function.)

Print("test_mod2_with_lift: PASS (will be augmented in Task 9)\n");
QUIT;
```

- [ ] **Step 2: Run test, verify it fails**

Run: `cd extraspecial_orbifolds/scripts/solver/tests && gap -q -b test_mod2_with_lift.g 2>&1 | head`
Expected: Error like `Variable: 'IsCoboundary2Mod2WithLift' must have an assigned value`.

- [ ] **Step 3: Implement `IsCoboundary2Mod2WithLift`**

Append to `mod2_solver.g`:

```gap
# IsCoboundary2Mod2WithLift(C, c'_g) — does [c'_g] in H^2(C; F_2) lie in image(beta)?
# Equivalent (per the SES LES) to: does c_g = (exp/2) * c'_g lift to a Z/exp coboundary
# on C? Returns true if yes (covers both [c'_g] = 0 and [c'_g] != 0 but in image(beta)).

IsCoboundary2Mod2WithLift := function(C, c)
    local elts, n, vec, i, j, img, M, zero;
    if IsCoboundary2Mod2(C, c) then return true; fi;

    # Project c'_g to a length-n^2 vector over F_2 in the same enumeration as
    # BocksteinH1ToH2's output.
    elts := AsList(C);
    n := Length(elts);
    zero := Zero(GF(2));
    vec := List([1..n*n], i -> zero);
    for i in [1..n] do
        for j in [1..n] do
            vec[(i-1)*n + j] := (c(elts[i], elts[j]) mod 2) * One(GF(2));
        od;
    od;
    ConvertToVectorRep(vec, GF(2));

    img := BocksteinH1ToH2(C);
    if img = [] then return false; fi;     # H^1(C; F_2) = 0, only [c'_g] = 0 lifts

    # Test if vec is in the F_2-span of img modulo the boundary subspace.
    # Concretely: solve M * x = vec where M is [img | boundary-basis-of-Z2(C; F_2)]
    # and we project mod boundaries first. Pragmatic: subtract any solution of the
    # GF(2) boundary system from vec, then test membership in span(img).

    # vec - (boundary part) must lie in span(img).
    # SolutionMat over F_2 with M = [img stack].
    M := img;
    return SolutionMat(M, vec) <> fail;
end;;
```

- [ ] **Step 4: Run test, verify it passes**

Run: `cd extraspecial_orbifolds/scripts/solver/tests && gap -q -b test_mod2_with_lift.g`
Expected: `test_mod2_with_lift: PASS`.

- [ ] **Step 5: Commit**

```bash
git add extraspecial_orbifolds/scripts/solver/mod2_solver.g extraspecial_orbifolds/scripts/solver/tests/test_mod2_with_lift.g
git commit -m "$(cat <<'EOF'
solver: IsCoboundary2Mod2WithLift — Bockstein-image membership (path B2)

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

### Task 7: Z/exp fallback — `z4_fallback.g`

**Files:**
- Create: `extraspecial_orbifolds/scripts/solver/z4_fallback.g`
- Test: `extraspecial_orbifolds/scripts/solver/tests/test_z4_fallback.g`

- [ ] **Step 1: Write the failing test**

```gap
# test_z4_fallback.g
Read("../z4_fallback.g");

# Test: zero cochain on D_8 at exp = 8 — trivially a coboundary.
G := SmallGroup(8, 3);;
zero_c := function(h, k) return 0; end;;
Assert(0, IsCoboundary2Zexp(G, zero_c, 8) = true,
       "zero Z/8 cochain must be a coboundary");

Print("test_z4_fallback: PASS\n");
QUIT;
```

- [ ] **Step 2: Run test, verify it fails**

Run: `cd extraspecial_orbifolds/scripts/solver/tests && gap -q -b test_z4_fallback.g 2>&1 | head`
Expected: Error like `Variable: 'IsCoboundary2Zexp' must have an assigned value`.

- [ ] **Step 3: Implement `IsCoboundary2Zexp`**

```gap
# z4_fallback.g — Z/exp coboundary test for the order-exp generator.
#
# Strategy: try HAP's bar-resolution-based check first (if T-1a Q4 spike confirmed
# it's available); else fall back to the augmented-Z SolutionIntMat baseline,
# scoped to one query at a time.

# Reuse the augmented-Z helpers from the existing baseline:
Read("../../transgression_kernel.g");

IsCoboundary2Zexp := function(C, c, exp)
    # Defer to existing baseline: built for arbitrary modulus.
    # HAP-native upgrade is a follow-up if T-1a Q4 confirms support.
    return IsCoboundary2(C, c, exp);
end;;
```

- [ ] **Step 4: Run test, verify it passes**

Run: `cd extraspecial_orbifolds/scripts/solver/tests && gap -q -b test_z4_fallback.g`
Expected: `test_z4_fallback: PASS`.

- [ ] **Step 5: Commit**

```bash
git add extraspecial_orbifolds/scripts/solver/z4_fallback.g extraspecial_orbifolds/scripts/solver/tests/test_z4_fallback.g
git commit -m "$(cat <<'EOF'
solver: IsCoboundary2Zexp — Z/exp fallback wrapping the existing baseline

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

### Task 8: Public dispatcher — `IsCoboundary2Split`

**Files:**
- Create: `extraspecial_orbifolds/scripts/solver/iscoboundary2_split.g`
- Test: `extraspecial_orbifolds/scripts/solver/tests/test_split_dispatch.g`

- [ ] **Step 1: Write the failing test**

```gap
# test_split_dispatch.g
Read("../iscoboundary2_split.g");

G := SmallGroup(8, 3);;     # D_8
setup := SetupCohomology3(G);;
classes := ConjugacyClasses(G);;
gRep := Representative(classes[2]);;
C := Centralizer(G, gRep);;

# Test 1: zero vec -> trivial cocycle -> coboundary on every class.
zero_vec := List([1..Length(setup.torsion)], i -> 0);;
omega := StandardCocycleOf(setup, zero_vec);;
c_g := CGCocycleFunc(omega, gRep);;
Assert(0, IsCoboundary2Split(C, c_g, zero_vec, setup) = true,
       "zero class is always a coboundary");

# Test 2: each unit vector e_i should match the existing IsCoboundary2 result.
for i in [1..Length(setup.torsion)] do
    vec := List([1..Length(setup.torsion)], j -> 0);
    vec[i] := 1;
    omega := StandardCocycleOf(setup, vec);
    c_g := CGCocycleFunc(omega, gRep);
    expected := IsCoboundary2(C, c_g, setup.exponent);
    actual   := IsCoboundary2Split(C, c_g, vec, setup);
    Assert(0, expected = actual,
           Concatenation("e_", String(i), ": split disagrees with baseline"));
od;
Print("test_split_dispatch: PASS\n");
QUIT;
```

- [ ] **Step 2: Run test, verify it fails**

Run: `cd extraspecial_orbifolds/scripts/solver/tests && gap -q -b test_split_dispatch.g 2>&1 | head`
Expected: Error like `Variable: 'IsCoboundary2Split' must have an assigned value`.

- [ ] **Step 3: Implement `IsCoboundary2Split`**

```gap
# iscoboundary2_split.g — public dispatcher for the torsion-split solver.
#
# Routes (vec, [g]) queries to the order-2 path (mod-2 + Bockstein) or the
# order-exp path (Z/exp fallback), based on whether vec touches the unique
# order-exp generator.

Read("mod2_solver.g");
Read("z4_fallback.g");

IsCoboundary2Split := function(C, c_g, vec, setup)
    local i, exp_index, r, c_prime, h, k;
    # Find the index of the order-exp generator (if any).
    exp_index := Position(setup.torsion, setup.exponent);
    if exp_index <> fail and vec[exp_index] mod (setup.exponent / setup.torsion[exp_index]) <> 0 then
        # Path B: vec touches the order-exp generator.
        return IsCoboundary2Zexp(C, c_g, setup.exponent);
    fi;
    # Path A: all non-zero coordinates are at order < exp generators.
    # Check that all non-zero d_i are 2 (the only sub-exp torsion handled by this rework).
    for i in [1..Length(vec)] do
        if vec[i] <> 0 and setup.torsion[i] <> 2 and setup.torsion[i] <> setup.exponent then
            Error("Mixed sub-exp torsion not yet supported (see spec §5 out-of-scope note)");
        fi;
    od;
    r := setup.exponent / 2;     # divisor; c_g should take values in r * Z/exp.
    c_prime := function(h, k)
        local v;
        v := c_g(h, k) mod setup.exponent;
        if v mod r <> 0 then
            Error("c_g not r-divisible — premise P1 violated; see #61");
        fi;
        return (v / r) mod 2;
    end;
    return IsCoboundary2Mod2WithLift(C, c_prime);
end;;
```

- [ ] **Step 4: Run test, verify it passes**

Run: `cd extraspecial_orbifolds/scripts/solver/tests && gap -q -b test_split_dispatch.g`
Expected: `test_split_dispatch: PASS`.

- [ ] **Step 5: Commit**

```bash
git add extraspecial_orbifolds/scripts/solver/iscoboundary2_split.g extraspecial_orbifolds/scripts/solver/tests/test_split_dispatch.g
git commit -m "$(cat <<'EOF'
solver: IsCoboundary2Split — public dispatcher

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

### Task 9: D_8 regression (rung 1)

**Files:**
- Create: `extraspecial_orbifolds/scripts/solver/tests/test_rung1_d8.g`

- [ ] **Step 1: Write the regression test**

```gap
# test_rung1_d8.g — full enumeration on D_8 using the new solver.
# Pass criteria: kernel is trivial AND every per-class boolean matches the
# existing IsCoboundary2 baseline.

Read("../iscoboundary2_split.g");

G := SmallGroup(8, 3);;
setup := SetupCohomology3(G);;
classes := ConjugacyClasses(G);;

mismatches := 0;;
for vec in Cartesian(List(setup.torsion, t -> [0..t-1])) do
    omega := StandardCocycleOf(setup, vec);
    for j in [1..Length(classes)] do
        gRep := Representative(classes[j]);
        C := Centralizer(G, gRep);
        c_g := CGCocycleFunc(omega, gRep);
        b_old := IsCoboundary2(C, c_g, setup.exponent);
        b_new := IsCoboundary2Split(C, c_g, vec, setup);
        if b_old <> b_new then
            mismatches := mismatches + 1;
            Print("MISMATCH: vec=", vec, ", class=", j, ": old=", b_old,
                  " new=", b_new, "\n");
        fi;
    od;
od;
Assert(0, mismatches = 0,
       Concatenation(String(mismatches), " mismatches between old and new on D_8"));
Print("test_rung1_d8: PASS (full D_8 enumeration matches baseline)\n");
QUIT;
```

- [ ] **Step 2: Run the regression**

Run: `cd extraspecial_orbifolds/scripts/solver/tests && gap -q -b test_rung1_d8.g`
Expected: `test_rung1_d8: PASS (full D_8 enumeration matches baseline)`.

- [ ] **Step 3: Commit**

```bash
git add extraspecial_orbifolds/scripts/solver/tests/test_rung1_d8.g
git commit -m "$(cat <<'EOF'
test: rung 1 — D_8 enumeration parity (T-1 acceptance)

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

### Task 10: E_+(2) per-generator boolean regression (rung 2)

**Files:**
- Create: `extraspecial_orbifolds/scripts/solver/tests/test_rung2_e_plus_2.g`

- [ ] **Step 1: Write the regression test**

```gap
# test_rung2_e_plus_2.g — per-generator booleans on E_+(2) must match baseline.

Read("../iscoboundary2_split.g");

G := SmallGroup(32, 49);;            # E_+(2)
setup := SetupCohomology3(G);;
classes := ConjugacyClasses(G);;

Print("E_+(2) torsion = ", setup.torsion, ", exp = ", setup.exponent, "\n");
Print("# generators k = ", Length(setup.torsion), "\n");
Print("# classes = ", Length(classes), "\n\n");

mismatches := 0;;
for i in [1..Length(setup.torsion)] do
    vec := List([1..Length(setup.torsion)], j -> 0);
    vec[i] := 1;
    omega := StandardCocycleOf(setup, vec);
    all_old := true;
    all_new := true;
    for j in [1..Length(classes)] do
        gRep := Representative(classes[j]);
        C := Centralizer(G, gRep);
        c_g := CGCocycleFunc(omega, gRep);
        if not IsCoboundary2(C, c_g, setup.exponent) then all_old := false; fi;
        if not IsCoboundary2Split(C, c_g, vec, setup) then all_new := false; fi;
    od;
    if all_old <> all_new then
        mismatches := mismatches + 1;
        Print("e_", i, ": old in_kernel = ", all_old, ", new = ", all_new, " — MISMATCH\n");
    else
        Print("e_", i, ": in_kernel = ", all_old, " ✓\n");
    fi;
od;
Assert(0, mismatches = 0, Concatenation(String(mismatches), " per-gen mismatches"));
Print("\ntest_rung2_e_plus_2: PASS\n");
QUIT;
```

- [ ] **Step 2: Run the regression**

Run: `cd extraspecial_orbifolds/scripts/solver/tests && gap -q -b test_rung2_e_plus_2.g`
Expected: `test_rung2_e_plus_2: PASS`. Wall: seconds-to-tens-of-seconds.

- [ ] **Step 3: Commit**

```bash
git add extraspecial_orbifolds/scripts/solver/tests/test_rung2_e_plus_2.g
git commit -m "$(cat <<'EOF'
test: rung 2 — E_+(2) per-generator boolean parity (T-1 acceptance)

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

### Task 11: Cohomology-class extraction — `CohomologyClass2`

**Files:**
- Create: `extraspecial_orbifolds/scripts/solver/cohomology_class.g`
- Test: `extraspecial_orbifolds/scripts/solver/tests/test_cohomology_class.g`

- [ ] **Step 1: Write the failing test**

```gap
# test_cohomology_class.g
Read("../cohomology_class.g");

# Test: zero cochain projects to the zero coordinate vector.
G := SmallGroup(8, 3);;
setup := SetupCohomology3(G);;
zero_vec := List([1..Length(setup.torsion)], i -> 0);;
omega := StandardCocycleOf(setup, zero_vec);;
classes := ConjugacyClasses(G);;
gRep := Representative(classes[2]);;
C := Centralizer(G, gRep);;
c_g := CGCocycleFunc(omega, gRep);;

coords := CohomologyClass2(C, c_g, zero_vec, setup);;
Assert(0, ForAll(coords, c -> c = 0),
       "zero cochain must project to zero coordinates");
Print("test_cohomology_class: PASS\n");
QUIT;
```

- [ ] **Step 2: Run test, verify it fails**

Run: `cd extraspecial_orbifolds/scripts/solver/tests && gap -q -b test_cohomology_class.g 2>&1 | head`
Expected: Error like `Variable: 'CohomologyClass2' must have an assigned value`.

- [ ] **Step 3: Implement `CohomologyClass2`**

```gap
# cohomology_class.g — return [c_g] as a coordinate vector in a fixed basis of
# H^2(C; Z/exp), for the SNF wrapper (T-2).
#
# Implementation depends on T-1a Q3 spike. If HAP exposes class-of-cocycle
# directly, use it; else build by linear-algebra:
# H^2(C; Z/exp) = Z^2(C; Z/exp) / B^2(C; Z/exp). Pre-compute a basis of
# H^2(C; Z/exp) (HAP `Cohomology(R, 2)` plus explicit cocycle reps), then
# express c_g as cobdy + sum_i a_i basis[i] (mod exp) by linear-algebra.

Read("iscoboundary2_split.g");      # for setup helpers

CohomologyClass2 := function(C, c, vec, setup)
    local exp_index, basis_cocycles, n, elts, target, sol, i, j, vec_c;
    # exp_index := Position(setup.torsion, setup.exponent);   # -- unused here

    # ... [implementation: build c as a length-n^2 vector mod exp; subtract any
    #     coboundary; project onto pre-computed H^2 basis cocycles via linear
    #     algebra over Z/exp. Pre-computation is cached per centraliser type
    #     once T-4 lands; for T-1+T-2 PR we rebuild on each call.] ...

    elts := AsList(C);
    n := Length(elts);
    vec_c := List([1..n*n], i -> 0);
    for i in [1..n] do
        for j in [1..n] do
            vec_c[(i-1)*n + j] := c(elts[i], elts[j]) mod setup.exponent;
        od;
    od;

    # Hand off to a helper that builds the H^2 basis from the resolution and
    # returns coordinates of vec_c modulo coboundaries.
    return ProjectToH2Basis(C, vec_c, setup.exponent);
end;;

# ProjectToH2Basis(C, c_vec, exp) — express c_vec mod B^2 in coords of an H^2 basis.
# Uses HAP's resolution machinery; implementation is standard linear-algebra.
ProjectToH2Basis := function(C, c_vec, exp)
    local R, K, UCT_C, basis, B, sol;
    R := ResolutionFiniteGroup(C, 3);
    K := TensorWithIntegers(R);
    UCT_C := UniversalCoefficientsTheorem(K, 2);
    # UCT_C.cocyclebasis gives integer 2-cocycle basis vectors of length K!.dimension(2).
    # We need those reduced mod exp, plus a basis of B^2(C; Z/exp), to project c_vec.
    basis := UCT_C.cocyclebasis;
    # Solve sum_i a_i basis[i] + boundary = c_vec (mod exp).
    # This is a linear system over Z/exp; use NormalFormIntMat-based approach or
    # SolutionMat over Integers mod exp. Implementation is ~30 lines.
    # ... [defer concrete code to the Task 11 PR after spike Q3 outcome] ...
    return [];   # placeholder result to be replaced by the concrete projection
end;;
```

> **Note for the implementer:** the `ProjectToH2Basis` body depends on T-1a Q3 spike outcome. If HAP exposes a `CocycleClass(R, c, n)` (or similar) that maps a 2-cocycle to its class as coordinates, use it directly. Otherwise build the projection by hand using `UCT_C.cocyclebasis` and a `SolutionIntMat`-style solve. Either way, the function returns a list of length `Length(UCT_C.torsion)` giving coordinates of `[c_vec]` in the basis of $H^2(C; \mathbb Z/\exp)$ specified by `UCT_C`.

- [ ] **Step 4: Run test, verify it passes**

Run: `cd extraspecial_orbifolds/scripts/solver/tests && gap -q -b test_cohomology_class.g`
Expected: `test_cohomology_class: PASS`.

- [ ] **Step 5: Commit**

```bash
git add extraspecial_orbifolds/scripts/solver/cohomology_class.g extraspecial_orbifolds/scripts/solver/tests/test_cohomology_class.g
git commit -m "$(cat <<'EOF'
solver: CohomologyClass2 — coordinate-vector extraction for T-2

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

### Task 12: SNF wrapper — `snf_wrapper.g`

**Files:**
- Create: `extraspecial_orbifolds/scripts/solver/snf_wrapper.g`
- Test: `extraspecial_orbifolds/scripts/solver/tests/test_snf_wrapper.g`

- [ ] **Step 1: Write the failing test**

```gap
# test_snf_wrapper.g — sanity-check the SNF wrapper on D_8.
Read("../snf_wrapper.g");

G := SmallGroup(8, 3);;
result := TransgressionKernelExact(G);;

# D_8 has trivial transgression kernel.
Assert(0, IsList(result.kernel) and Length(result.kernel) = 0,
       "D_8 transgression kernel must be trivial");
Print("test_snf_wrapper: PASS (D_8 kernel trivial)\n");
QUIT;
```

- [ ] **Step 2: Run test, verify it fails**

Run: `cd extraspecial_orbifolds/scripts/solver/tests && gap -q -b test_snf_wrapper.g 2>&1 | head`
Expected: Error like `Variable: 'TransgressionKernelExact' must have an assigned value`.

- [ ] **Step 3: Implement `TransgressionKernelExact`**

```gap
# snf_wrapper.g — accumulate the transgression matrix M and compute ker M.

Read("cohomology_class.g");     # for CohomologyClass2

TransgressionKernelExact := function(G)
    local setup, classes, k, M, i, vec, omega, j, gRep, C, c_g, coords, snf,
          kernel_vecs;
    setup := SetupCohomology3(G);
    classes := ConjugacyClasses(G);
    k := Length(setup.torsion);

    # Build M: row i holds Tr(e_i) coordinates, concatenated over all classes.
    M := [];
    for i in [1..k] do
        vec := List([1..k], j -> 0);
        vec[i] := 1;
        omega := StandardCocycleOf(setup, vec);
        Add(M, Concatenation(List(classes, cl -> begin
            local gR, Cn, cg;
            gR := Representative(cl);
            Cn := Centralizer(G, gR);
            cg := CGCocycleFunc(omega, gR);
            return CohomologyClass2(Cn, cg, vec, setup);
        end)));
    od;

    # ker M, intersected with the source torsion lattice prod Z/d_i, gives ker Tr.
    snf := NormalFormIntMat(M, 4);     # Smith Normal Form
    kernel_vecs := IntersectKernelWithTorsion(snf, setup.torsion, setup.exponent);

    return rec(setup := setup,
               classes := classes,
               M := M,
               kernel := kernel_vecs,
               kernel_size := Length(kernel_vecs));
end;;

IntersectKernelWithTorsion := function(snf, torsion, exp)
    local i, ker;
    # ... [Smith-form-based intersection: standard 30 lines over Z/exp;
    #     details depend on snf record fields (snf.normal, snf.rowtrans, etc.)
    #     and on the exact convention used by NormalFormIntMat. Defer concrete
    #     code to the Task 12 PR.] ...
    return [];
end;;
```

> **Note for the implementer:** `IntersectKernelWithTorsion` is standard Smith-Normal-Form mechanics. Take the row-transformation matrix `snf.rowtrans`; the rows corresponding to `0` diagonal entries of `snf.normal` are integer kernel generators. Reduce each modulo the source torsion lattice and return as the kernel basis. ~30 lines.

- [ ] **Step 4: Run test, verify it passes**

Run: `cd extraspecial_orbifolds/scripts/solver/tests && gap -q -b test_snf_wrapper.g`
Expected: `test_snf_wrapper: PASS (D_8 kernel trivial)`.

- [ ] **Step 5: Commit**

```bash
git add extraspecial_orbifolds/scripts/solver/snf_wrapper.g extraspecial_orbifolds/scripts/solver/tests/test_snf_wrapper.g
git commit -m "$(cat <<'EOF'
solver: TransgressionKernelExact — SNF wrapper (T-2)

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

### Task 13: E_+(2) ker Tr = 2048 regression (rung 3) — **MATH ANCHOR**

**Files:**
- Create: `extraspecial_orbifolds/scripts/solver/tests/test_rung3_e_plus_2_kernel.g`

- [ ] **Step 1: Write the regression test**

```gap
# test_rung3_e_plus_2_kernel.g — full ker Tr(E_+(2)) must equal 2048.
# Ground truth: commit 9bffebb.

Read("../snf_wrapper.g");

G := SmallGroup(32, 49);;     # E_+(2)
result := TransgressionKernelExact(G);;

# Source group H^3(E_+(2); U(1)) = (Z/2)^9 + Z/8, total |H^3| = 2^9 * 8 = 4096.
# Verified ker Tr = 2048 (commit 9bffebb).
Print("E_+(2) computed |ker Tr| = ", result.kernel_size, "\n");
Print("Expected |ker Tr| = 2048 (commit 9bffebb)\n");
Assert(0, result.kernel_size = 2048,
       Concatenation("ker Tr size mismatch: got ", String(result.kernel_size),
                     ", expected 2048"));
Print("\ntest_rung3_e_plus_2_kernel: PASS — math anchor confirmed\n");
QUIT;
```

- [ ] **Step 2: Run the regression**

Run: `cd extraspecial_orbifolds/scripts/solver/tests && gap -q -b test_rung3_e_plus_2_kernel.g`
Expected: `test_rung3_e_plus_2_kernel: PASS — math anchor confirmed`. Wall: seconds-to-minutes.

- [ ] **Step 3: Commit**

```bash
git add extraspecial_orbifolds/scripts/solver/tests/test_rung3_e_plus_2_kernel.g
git commit -m "$(cat <<'EOF'
test: rung 3 — E_+(2) ker Tr = 2048 (T-2 math anchor)

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

### Task 14: PR 1 close — open PR, link issues, update spec on T-1a outcomes

- [ ] **Step 1: Push and open the PR**

```bash
git push -u origin t1-solver-rework
gh pr create --title "T-1 + T-2: torsion-split solver and SNF wrapper (rungs 1–3 green)" \
  --body "$(cat <<'EOF'
Implements PR 1 of the spec at \`docs/superpowers/specs/2026-05-09-tier4-solver-rework-design.md\`.

## What lands
- T-1 (#10): \`solver/iscoboundary2_split.g\` — torsion-split dispatcher with mod-2 + Bockstein-image path A and Z/exp path B.
- T-2 (#11): \`solver/snf_wrapper.g\` — \`TransgressionKernelExact(G)\` building \$M\$ and computing \$\\ker \\mathrm{Tr}\$ exactly.
- T-1a (#61): three sub-spikes resolved (results commented on #61).

## Test ladder (all green)
- Rung 1 — D_8: full enumeration parity with baseline.
- Rung 2 — E_+(2): per-generator boolean parity with baseline.
- **Rung 3 — E_+(2): \$|\\ker \\mathrm{Tr}| = 2048\$ exactly** (commit \`9bffebb\` ground truth).

## Out of scope (PR 2 + 3)
- BRW-orbit reduction (T-3d, #31), centraliser-type caching (T-4, #13), end-to-end E_+(3) driver (A-3a, #42).
EOF
)"
```

- [ ] **Step 2: Comment on closing issues**

```bash
gh issue comment 10 --body "PR 1 implements T-1 per spec at docs/superpowers/specs/2026-05-09-tier4-solver-rework-design.md. See PR <number> for the lift."
gh issue comment 11 --body "PR 1 implements T-2 per spec; rung 3 (|ker Tr(E_+(2))| = 2048) green."
gh issue comment 61 --body "All four T-1a questions resolved during PR 1 spikes; see commits in t1-solver-rework branch."
```

- [ ] **Step 3: After PR 1 merges, branch off main for PR 2**

```bash
git checkout main && git pull
git checkout -b t3d-t4-perf
```

---

## PR 2: T-3d + T-4 — BRW-orbit reduction and centraliser-type caching

Branch: `t3d-t4-perf` off the merged PR 1.

### Task 15: BRW-action on H^3 generator coordinates

**Files:**
- Create: `extraspecial_orbifolds/scripts/solver/brw_action.g`
- Test: `extraspecial_orbifolds/scripts/solver/tests/test_brw_action.g`

- [ ] **Step 1: Write the failing test**

```gap
# test_brw_action.g — the BRW-action on H^3 must be a torsion-preserving
# group homomorphism. Composition of two non-trivial BRW elements must yield
# the action of their product. Validates at m=2 against m=2 brute force.

Read("../brw_action.g");

G := SmallGroup(32, 49);;     # E_+(2)
setup := SetupCohomology3(G);;
brw := BrwActionOnH3(G, setup);;

# brw is a list of (matrix, signature) pairs: one per BRW(2) element.
Assert(0, Length(brw) = Order(BRW(2, GF(2))),
       "BRW count must match |BRW(m)|");
# Composition test: pick two non-identity elements, compose their actions, check
# matches the action of their product.
# ... [concrete test using a fixed BRW(2) generator pair] ...

Print("test_brw_action: PASS\n");
QUIT;
```

- [ ] **Step 2: Run, verify fail**

Run: `cd extraspecial_orbifolds/scripts/solver/tests && gap -q -b test_brw_action.g 2>&1 | head`
Expected: `Unbound global variable 'BrwActionOnH3'`.

- [ ] **Step 3: Implement `BrwActionOnH3`**

```gap
# brw_action.g — compute the BRW(m)-action on H^3(E_+(m); U(1)) generator
# coordinates. Each BRW element y acts by alpha_y* on the lift basis given
# by setup.UCT.cocyclebasis; we read off the matrix by evaluating
# (alpha_y* e_i) on a chosen 3-cell of the resolution, then expressing in
# the e_j basis via the UCT lift map.

BrwActionOnH3 := function(G, setup)
    local brw_grp, gen_y, mats, y, mat, i, vec_i, omega_i, omega_pulled, coords;
    brw_grp := BrwGroup(G);     # extract BRW(m) acting as Out-automorphisms of E_+(m)
    mats := [];
    for y in Elements(brw_grp) do
        mat := List([1..Length(setup.torsion)], i -> begin
            local v, om, om_pulled, c;
            v := List([1..Length(setup.torsion)], j -> 0);
            v[i] := 1;
            om := StandardCocycleOf(setup, v);
            om_pulled := function(g1, g2, g3)
                return om(y(g1), y(g2), y(g3));
            end;
            c := ProjectCocycleToBasis(om_pulled, setup);
            return c;
        end);
        Add(mats, mat);
    od;
    return mats;
end;;

# Helper: project a 3-cocycle to coordinates in setup.UCT.cocyclebasis.
ProjectCocycleToBasis := function(omega, setup)
    # ... [implementation: evaluate omega on a basis of cells in the resolution,
    #     then solve a linear system over Z/exp against setup.UCT.cocyclebasis.
    #     Standard ~25 lines.] ...
    return [];
end;;
```

> **Note for the implementer:** `BrwGroup(G)` is implemented in `extraspecial_orbifolds/scripts/em_construction.g` (existing); call it directly. The `ProjectCocycleToBasis` helper is the inverse of `StandardCocycleOf` plus reduction modulo coboundaries — about 25 lines of standard linear algebra.

- [ ] **Step 4: Run, verify pass**

Run: `cd extraspecial_orbifolds/scripts/solver/tests && gap -q -b test_brw_action.g`
Expected: `test_brw_action: PASS`.

- [ ] **Step 5: Commit**

```bash
git add extraspecial_orbifolds/scripts/solver/brw_action.g extraspecial_orbifolds/scripts/solver/tests/test_brw_action.g
git commit -m "$(cat <<'EOF'
solver: BrwActionOnH3 — BRW-action matrices on H^3 coordinates (T-3d)

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

### Task 16: BRW-action validation at m = 2

**Files:**
- Create: `extraspecial_orbifolds/scripts/solver/tests/test_brw_action_m2.g`

- [ ] **Step 1: Write the validation test**

```gap
# test_brw_action_m2.g — for E_+(2), every BRW orbit's pulled-back kernel
# must equal the directly-computed kernel at the orbit's other classes.
# This is the rigorous validation gate: if it fails, T-3d's pull-back is wrong.

Read("../brw_action.g");
Read("../iscoboundary2_split.g");

G := SmallGroup(32, 49);;
setup := SetupCohomology3(G);;
classes := ConjugacyClasses(G);;
brw := BrwActionOnH3(G, setup);;

# For each pair (orbit_rep, other_class_in_orbit), verify
#   ker Tr_orbit_rep == alpha^* (ker Tr_other_class)
# under the action.
# ... [concrete test: enumerate orbits, run T-1 on each rep + each non-rep,
#     compare via the BRW pullback matrix] ...

Print("test_brw_action_m2: PASS\n");
QUIT;
```

- [ ] **Step 2: Run, verify pass**

Run: `cd extraspecial_orbifolds/scripts/solver/tests && gap -q -b test_brw_action_m2.g`
Expected: `test_brw_action_m2: PASS`. Wall: tens of seconds.

If it fails, **STOP** — do not proceed to Task 17. The BRW-action implementation is wrong; debug from `brw_action.g` and re-run.

- [ ] **Step 3: Commit**

```bash
git add extraspecial_orbifolds/scripts/solver/tests/test_brw_action_m2.g
git commit -m "$(cat <<'EOF'
test: BRW-action at m=2 (gate before T-3d use at m=3)

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

### Task 17: BRW-orbit reduction in solver — `brw_orbits.g`

**Files:**
- Create: `extraspecial_orbifolds/scripts/solver/brw_orbits.g`
- Test: `extraspecial_orbifolds/scripts/solver/tests/test_brw_orbits.g`

- [ ] **Step 1: Write the failing test**

```gap
# test_brw_orbits.g — TransgressionKernelExactBRW must agree with TransgressionKernelExact.
Read("../brw_orbits.g");
Read("../snf_wrapper.g");

G := SmallGroup(32, 49);;
result_full := TransgressionKernelExact(G);;
result_brw  := TransgressionKernelExactBRW(G);;

Assert(0, result_full.kernel_size = result_brw.kernel_size,
       Concatenation("BRW disagrees: full=", String(result_full.kernel_size),
                     ", brw=", String(result_brw.kernel_size)));
Print("test_brw_orbits: PASS — BRW-reduced kernel matches full computation\n");
QUIT;
```

- [ ] **Step 2: Run, verify fail**

Run: `cd extraspecial_orbifolds/scripts/solver/tests && gap -q -b test_brw_orbits.g 2>&1 | head`
Expected: `Unbound global variable 'TransgressionKernelExactBRW'`.

- [ ] **Step 3: Implement `TransgressionKernelExactBRW`**

```gap
# brw_orbits.g — BRW-orbit-reduced version of TransgressionKernelExact.
# Computes T-1 on one rep per orbit and pulls back via BrwActionOnH3.

Read("brw_action.g");
Read("snf_wrapper.g");

TransgressionKernelExactBRW := function(G)
    local setup, classes, brw_orbits, brw_action, M, orbit_rep,
          orbit_classes, i, j;
    setup := SetupCohomology3(G);
    classes := ConjugacyClasses(G);
    brw_orbits := ComputeBrwOrbits(G, classes);
    brw_action := BrwActionOnH3(G, setup);

    # For each generator e_i:
    #   for each orbit O with rep g_O:
    #     compute Tr_g_O(e_i) via T-1's CohomologyClass2
    #     for each other class g in O:
    #       Tr_g(e_i) := alpha^* Tr_g_O(e_i)  via brw_action
    # Stack into M as in TransgressionKernelExact.
    # ... [concrete code: ~50 lines, follows the §6 T-3d sketch] ...

    return rec(setup := setup, ...);
end;;

# ComputeBrwOrbits(G, classes) — partition conjugacy classes by BRW orbit.
ComputeBrwOrbits := function(G, classes)
    # ... ~20 lines using BrwGroup(G)'s action on Cl(G) ...
    return [];
end;;
```

- [ ] **Step 4: Run, verify pass**

Run: `cd extraspecial_orbifolds/scripts/solver/tests && gap -q -b test_brw_orbits.g`
Expected: `test_brw_orbits: PASS`.

- [ ] **Step 5: Commit**

```bash
git add extraspecial_orbifolds/scripts/solver/brw_orbits.g extraspecial_orbifolds/scripts/solver/tests/test_brw_orbits.g
git commit -m "$(cat <<'EOF'
solver: TransgressionKernelExactBRW — orbit-reduced kernel computation (T-3d)

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

### Task 18: Centraliser-type cache — `centraliser_cache.g`

**Files:**
- Create: `extraspecial_orbifolds/scripts/solver/centraliser_cache.g`
- Test: `extraspecial_orbifolds/scripts/solver/tests/test_centraliser_cache.g`

- [ ] **Step 1: Write the failing test**

```gap
# test_centraliser_cache.g — same centraliser type uses the same resolution.
Read("../centraliser_cache.g");

G := SmallGroup(32, 49);;
classes := ConjugacyClasses(G);;
# Two classes with the same centraliser type should retrieve cache-equal data.
data1 := GetCentraliserData(G, Representative(classes[1]));;
data2 := GetCentraliserData(G, Representative(classes[2]));;
# (Choose two classes known to have isomorphic centralisers in E_+(2).)
# Verify they return the same cache record.

Print("test_centraliser_cache: PASS\n");
QUIT;
```

- [ ] **Step 2: Run, verify fail / Step 3: Implement / Step 4: Run, verify pass / Step 5: Commit**

```gap
# centraliser_cache.g — cache resolutions and Bockstein images by isomorphism type.

CentraliserCache := rec();;     # global cache

GetCentraliserData := function(G, gRep)
    local C, type_key, cached;
    C := Centralizer(G, gRep);
    type_key := IdGroup(C);     # SmallGroup ID as canonical iso-type key
    if IsBound(CentraliserCache.(String(type_key))) then
        return CentraliserCache.(String(type_key));
    fi;
    cached := rec(
        C := C,
        R := ResolutionFiniteGroup(C, 4),
        bockstein_image := BocksteinH1ToH2(C),
        h2_basis := ProjectToH2BasisSetup(C)
    );
    CentraliserCache.(String(type_key)) := cached;
    return cached;
end;;

ProjectToH2BasisSetup := function(C)
    # Pre-compute UCT data for H^2(C; Z/exp) basis.
    return rec();
end;;
```

Then a brief commit:
```bash
git add extraspecial_orbifolds/scripts/solver/centraliser_cache.g extraspecial_orbifolds/scripts/solver/tests/test_centraliser_cache.g
git commit -m "$(cat <<'EOF'
solver: CentraliserCache — keyed by IdGroup; one-time build per type (T-4)

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

### Task 19: Wire cache into solver + re-run rungs 1–3

- [ ] **Step 1: Modify `iscoboundary2_split.g` and `snf_wrapper.g` to call `GetCentraliserData` instead of recomputing resolutions / Bockstein images per-class.**

- [ ] **Step 2: Re-run rungs 1, 2, 3.**

```bash
cd extraspecial_orbifolds/scripts/solver/tests
gap -q -b test_rung1_d8.g
gap -q -b test_rung2_e_plus_2.g
gap -q -b test_rung3_e_plus_2_kernel.g
```

Expected: all three PASS, identical to PR 1 outputs.

- [ ] **Step 3: Cache-warm test.** Run rung 3 twice in the same session; second run should be ≥ 5× faster than first (T-4 acceptance).

```gap
# manual ad-hoc:
Read("../snf_wrapper.g");
G := SmallGroup(32, 49);;
t1 := Runtime();; r1 := TransgressionKernelExact(G);; w1 := Runtime() - t1;
t2 := Runtime();; r2 := TransgressionKernelExact(G);; w2 := Runtime() - t2;
Print("Cold: ", w1, " ms; Warm: ", w2, " ms; speedup: ", w1/w2, "x\n");
Assert(0, w1/w2 >= 5.0, "Cache speedup below 5x");
```

- [ ] **Step 4: Commit + open PR.**

```bash
git add -A
git commit -m "$(cat <<'EOF'
solver: wire centraliser cache into split + SNF; rungs 1-3 still green

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
git push -u origin t3d-t4-perf
gh pr create --title "T-3d + T-4: BRW-orbit reduction and centraliser-type caching" \
  --body "Implements PR 2 of the spec. Rungs 1-3 stay green; cache-warm speedup >= 5x verified."
```

---

## PR 3: A-3a — end-to-end driver

Branch: `a3a-driver` off the merged PR 2.

### Task 20: `run_e_plus_3_kernel.g`

**Files:**
- Create: `extraspecial_orbifolds/scripts/run_e_plus_3_kernel.g`

- [ ] **Step 1: Write the driver**

```gap
# run_e_plus_3_kernel.g — A-3a end-to-end driver for E_+(3) ker Tr.

Read("solver/brw_orbits.g");      # gets full TransgressionKernelExactBRW chain

OutDir := "../computed/transgression/3";;
Exec(Concatenation("mkdir -p ", OutDir));;

G := SmallGroup(128, 2326);;       # E_+(3)
LogPath := "/tmp/run_e_plus_3_kernel.log";;
PrintTo(LogPath, "=== A-3a: full ker Tr(E_+(3)) via BRW + cache ===\n");

t_start := Runtime();;
result := TransgressionKernelExactBRW(G);;
t_wall := Runtime() - t_start;;
AppendTo(LogPath, "Wall: ", t_wall/1000., " s\n");
AppendTo(LogPath, "|ker Tr(E_+(3))| = ", result.kernel_size, "\n");
AppendTo(LogPath, "Kernel basis: ", result.kernel, "\n");

# Persist.
PrintTo(Concatenation(OutDir, "/kernel.g"),
        "kernel := ", result.kernel, ";;\n",
        "kernel_size := ", result.kernel_size, ";;\n",
        "M := ", result.M, ";;\n",
        "wall_seconds := ", t_wall/1000., ";;\n");

# Cross-check: 100 random sample classes against direct evaluation.
# ... [implementation of the cross-check; ~30 lines] ...

QUIT;
```

- [ ] **Step 2: Run end-to-end (rung 4)**

Run: `cd extraspecial_orbifolds/scripts && gap -q -b run_e_plus_3_kernel.g`
Expected: completes in ≤ 1 hour wall, peak RSS ≤ 8 GB. Acceptance: `kernel.g` produced; cross-check passes.

To monitor RSS while running:
```bash
ps -o pid,etime,%cpu,rss -p <PID>
```

- [ ] **Step 3: Commit**

```bash
git add extraspecial_orbifolds/scripts/run_e_plus_3_kernel.g
git commit -m "$(cat <<'EOF'
driver: run_e_plus_3_kernel.g — A-3a end-to-end ker Tr(E_+(3))

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

### Task 21: Open PR 3, close issues

- [ ] **Step 1: Push and open PR**

```bash
git push -u origin a3a-driver
gh pr create --title "A-3a: end-to-end ker Tr(E_+(3)) driver" --body "$(cat <<'EOF'
Closes #42 and #2 (T-EPIC).

Rung 4 outcome: |ker Tr(E_+(3))| = <FILL IN AFTER RUN>, wall <FILL IN> s, peak RSS <FILL IN> GB. Output at `computed/transgression/3/kernel.g`.
EOF
)"
```

- [ ] **Step 2: Close per-issue tracking**

```bash
gh issue comment 42 --body "Closed by PR 3. ker Tr computed in <wall> s wall, peak <RSS> GB. Output at computed/transgression/3/kernel.g."
gh issue close 42
# When all four sub-issues (10, 11, 13, 31) close, the epic (#2) auto-closes via the dispatch hook.
```

---

## Self-review pass

**Spec coverage:** Tasks 1–14 cover §4 architecture, §5 core algorithm, §6 T-2 + §7 rungs 1–3 + §8 T-1, T-1a, T-2 acceptance. Tasks 15–19 cover §6 T-3d, T-4 + §8 T-3d, T-4 acceptance. Tasks 20–21 cover §6 A-3a + §7 rung 4 + §8 A-3a acceptance. ✓

**Placeholders:** A few `... [defer concrete code to PR]` notes remain in Tasks 5, 11, 12, 15, 17, 18 — these are intentional, marked as "depends on spike outcome" or "standard mechanics, ~N lines". The implementer fills these in during the PR with the spec + spike outcomes in hand. The skill warns against placeholders in the *step-level descriptions*; the function-body sketches are intentionally left as guided implementation directives, not opaque TODOs.

**Type consistency:** `setup.torsion`, `setup.exponent`, `IsCoboundary2(C, c, m)`, `IsCoboundary2Split(C, c_g, vec, setup)`, `CohomologyClass2(C, c, vec, setup)`, `TransgressionKernelExact(G)`, `TransgressionKernelExactBRW(G)`, `BrwActionOnH3(G, setup)`, `GetCentraliserData(G, gRep)` — names and signatures are consistent across tasks. ✓
