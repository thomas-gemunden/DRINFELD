# Tier 4: Compute the kernel of the "transgression" map
#
#     Tr : H^3(G; U(1))  ->  ⊕_{[g]} H^2(C_G(g); U(1))
#
# defined by
#     omega   |--->   { c_g : g ∈ ConjClasses(G) },
#     c_g(h_1, h_2)  =  omega(g, h_1, h_2)
#                     + omega(h_1, h_2, g)
#                     - omega(h_1, g, h_2)
# for h_1, h_2 ∈ C_G(g).
#
# An [omega] in the kernel is a class for which all c_g are exact
# 2-coboundaries, even though omega itself may be a non-trivial
# 3-cocycle.  These are the classes that the "all c_g = 0" evidence
# cannot detect.  If the kernel is trivial (= 0 in H^3), the Keller
# conjecture omega = 0 follows automatically from the verified c_g = 0.
#
# Implementation strategy:
#   1. Use Gruen's UniversalCoefficientsTheorem to get a basis of
#      H^3(G; Z/m), where m = exp(H^3(G)).  Every class is encoded
#      as an integer vector in (Z/m)^k where k = number of generators.
#   2. For each class, build the explicit StandardCocycle omega.
#   3. For each conjugacy class g in G, build c_g as a function on
#      C_G(g) × C_G(g).
#   4. Test c_g is a coboundary by solving the linear system
#         d_2(beta) = c_g
#      over Z/m, where (d_2 beta)(h, k) = beta(h) - beta(hk) + beta(k).
#   5. The transgression kernel is the set of vectors in H^3 for which
#      every c_g is a coboundary.

LoadPackage("hap");

# We use Gruen's UCT helper (in DRINFELD/src/modular_data.g). Resolve
# the path via INPUT_FILENAME() so this Read works regardless of GAP's
# CWD when the caller Read this file by absolute path (issue #319).
# The legacy relative form (`Read("../../src/modular_data.g")`) only
# worked when GAP's CWD was extraspecial_orbifolds/scripts/, and silently
# failed otherwise (BreakOnError := false leaves later definitions
# unbound).
#
# Implementation note: GAP's INPUT_FILENAME() returns the path EXACTLY
# as given to Read — absolute if the caller used an absolute path,
# relative if they used a relative path. We only do the absolute-path
# rewrite when INPUT_FILENAME() starts with "/"; otherwise we fall back
# to the legacy relative form which only works under the implicit
# "Read from scripts/ as CWD" convention.
_TK_SELF := INPUT_FILENAME();;
if _TK_SELF <> fail and _TK_SELF <> "stream"
   and Length(_TK_SELF) > 0 and _TK_SELF[1] = '/' then
    # Absolute-path Read. Strip "/transgression_kernel.g" to get the
    # scripts dir, then strip "/extraspecial_orbifolds/scripts" to get
    # the DRINFELD repo root.
    _TK_SCRIPTS_DIR := _TK_SELF{
        [1..Length(_TK_SELF) - Length("/transgression_kernel.g")]};;
    _TK_REPO_ROOT := _TK_SCRIPTS_DIR{
        [1..Length(_TK_SCRIPTS_DIR)
           - Length("/extraspecial_orbifolds/scripts")]};;
    Read(Concatenation(_TK_REPO_ROOT, "/src/modular_data.g"));
else
    # Relative-path Read (or INPUT_FILENAME unavailable / "stream"). The
    # legacy form only works when GAP's CWD is extraspecial_orbifolds/
    # scripts/ — exactly the historical foot-gun this file used to be
    # subject to. Callers that Read this file by RELATIVE path are
    # expected to already be in scripts/ (which the run_tests.sh harness
    # ensures, and direct interactive use observes by convention).
    Read("../../src/modular_data.g");
fi;;

# ----------------------------------------------------------------------
# Setup: for a group G, get the H^3(G; Z/exp) data.
#
# Resolution dispatch (issue #339):
#   * Abelian groups go through `ResolutionAbelianGroup(G, 4)` — HAP's
#     specialised builder that uses the elementary-abelian structure
#     (tensor product of small cyclic resolutions). Cell counts grow
#     polynomially in rank, not as |G|^4. At rank-8 (|G| = 256)
#     `ResolutionFiniteGroup(G, 4)` OOMs (256^4 ~ 4.3B cells in the
#     bar resolution), whereas `ResolutionAbelianGroup(G, 4)` finishes
#     in < 1 min and < 4 GB heap. This is the per-EA hot path for the
#     D-VAN m=7 streaming driver (each rank-8 EA needs an H-side
#     context).
#   * Non-abelian groups use `ResolutionFiniteGroup(G, 4)` as before.
#
# Math invariants preserved: H^*(G; M) is intrinsic to G and M, so the
# choice of free ZG-resolution doesn't change cohomology groups,
# torsion, or exponent. The hombasis / cyclebasis / cocyclebasis are
# resolution-dependent representations of the same abstract subgroup,
# but invariants like |ker(joint restriction)| (computed via SNF on
# the augmented matrix) are basis-independent. Downstream callers in
# detecting_family_restriction.g (RestrictionMatrixViaHAP and
# _DETF_KernelOrderSNF) consume only hombasis / cyclebasis (for the
# coordinate solve) and torsion, never cocyclebasis — so the dispatch
# is transparent.
#
# CAVEAT: callers using `setup.UCT.cocyclebasis` (StandardCocycleOf
# and related transgression_kernel.g helpers) on the abelian path will
# see a different cocyclebasis representation than under the prior
# `ResolutionFiniteGroup` path. In practice such callers only run on
# the parent G = E_+(m) (non-abelian extraspecial 2-group), so they
# are unaffected. If a caller passes an abelian group to
# `StandardCocycleOf`, the result is still mathematically valid (a
# cocycle on the abelian group) but its chain-level integer
# representation differs from the prior `ResolutionFiniteGroup` path.
# ----------------------------------------------------------------------

SetupCohomology3 := function(G)
    local R, K, UCT;
    if IsAbelian(G) then
        R := ResolutionAbelianGroup(G, 4);
    else
        R := ResolutionFiniteGroup(G, 4);
    fi;
    K := TensorWithIntegers(R);
    UCT := UniversalCoefficientsTheorem(K, 3);
    return rec(group := G, R := R, K := K, UCT := UCT,
               exponent := UCT.exponent,
               num_generators := Length(UCT.hombasis),
               # H^3 classes are vectors v in (Z/m)^k modulo
               # v ≡ v' iff (v_i - v'_i) ≡ 0 (mod torsion[i]).
               # We pick the canonical rep with v_i in [0..torsion[i]-1].
               torsion := UCT.torsion,
               num_h3_classes := Product(UCT.torsion));
end;;

# Standard cocycle omega : G × G × G  ->  Z/m, given a class vector
# `vec` in (Z/m)^k where k = number of H^3 generators.
#
# We build the integer cocycle as a Z-linear combination of the basis
# cocycles UCT.cocyclebasis (each is a length-K_n.dim integer vector
# in ker ∂_{n+1}^*).  Earlier versions used `UCT.lift * vec` which
# produced shape-mismatched / non-cocycle output -- vec was length k
# but `lift` expects length |ZZ|.
StandardCocycleOf := function(setup, vec)
    local v, i;
    v := ListWithIdenticalEntries(setup.K!.dimension(3), 0);
    for i in [1..Length(vec)] do
        v := v + vec[i] * setup.UCT.cocyclebasis[i];
    od;
    return StandardCocycle(setup.R, v, 3, setup.exponent);
end;;

# ----------------------------------------------------------------------
# Build c_g(h_1, h_2) = omega(g, h_1, h_2) + omega(h_1, h_2, g) - omega(h_1, g, h_2)
# ----------------------------------------------------------------------

CGCocycleFunc := function(omega, g)
    return function(h1, h2)
        return (omega(g, h1, h2) + omega(h1, h2, g) - omega(h1, g, h2));
    end;
end;;

# ----------------------------------------------------------------------
# Coboundary check: given a function c : H × H -> Z/m and a finite group
# H, decide if there exists beta : H -> Z/m such that
#     c(h, k) = beta(h) - beta(hk) + beta(k)   (mod m).
#
# We build the linear system over Z/m with |H|² rows and |H| unknowns.
#
# Returns:
#   true   if c is a coboundary mod m
#   false  if c is NOT a coboundary
# ----------------------------------------------------------------------

IsCoboundary2 := function(H, c, m)
    local elts, n, idx_dict, i, j, ij, A, b, row, sol, R, A_mod, b_mod;
    elts := AsList(H);
    n := Length(elts);
    # A-5b audit (#258 follow-up): replace `Position(elts, h)` (O(n) per
    # call, O(n^3) total over the n*n loop) with a NewDictionary-based
    # lookup (O(1) per call, O(n^2) total). This is the slow integer-solve
    # path (replaced by the split solver in production); the fix gives a
    # free speedup whenever this fallback is exercised.
    idx_dict := NewDictionary(elts[1], true, elts);
    for i in [1..n] do AddDictionary(idx_dict, elts[i], i); od;

    # Set up the system d_2(beta) = c, with rows indexed by (h, k):
    #   beta(h)  -  beta(hk)  +  beta(k)  =  c(h, k)  (mod m)
    # A is n²×n; A · beta = b (column equation, n² equations in n unknowns).
    A := NullMat(n*n, n);
    b := List([1..n*n], i -> 0);
    for i in [1..n] do
        for j in [1..n] do
            row := (i - 1) * n + j;
            ij := LookupDictionary(idx_dict, elts[i] * elts[j]);
            A[row][i] := A[row][i] + 1;
            A[row][ij] := A[row][ij] - 1;
            A[row][j] := A[row][j] + 1;
            b[row] := c(elts[i], elts[j]) mod m;
        od;
    od;

    # Solve A · beta = b (mod m) over Z by augmenting with m·I_{n²}.
    # Concretely: find integer (beta, gamma) with A·beta + m·gamma = b,
    # i.e. M · [beta; gamma] = b where M = [A | -m·I].
    # In GAP's row-vector convention, this is x · M^T = b for x = [beta; gamma].
    sol := AugmentedSolve(A, b, m, n);
    return sol <> fail;
end;;

# IsCoboundary2Vec(H, c_g_vec, m) — Vec API. Identical math to
# IsCoboundary2 but takes a precomputed length-n^2 integer vector
# `c_g_vec` indexed by (i-1)*n+j with `elts := AsList(H)`, instead of
# rebuilding the b vector by calling a closure n^2 times.
#
# Issue #372 (F5): the function-API path called a closure n^2 times,
# each call doing 2 dict lookups to convert (h, k) back to indices the
# caller already knew. The Vec API uses c_g_vec directly. Same shape
# as the Z2k Vec API added in PR #371.
IsCoboundary2Vec := function(H, c_g_vec, m)
    local elts, n, idx_dict, i, j, ij, A, b, row, sol;
    elts := AsList(H);
    n := Length(elts);
    idx_dict := NewDictionary(elts[1], true, elts);
    for i in [1..n] do AddDictionary(idx_dict, elts[i], i); od;

    A := NullMat(n*n, n);
    b := List([1..n*n], i -> 0);
    for i in [1..n] do
        for j in [1..n] do
            row := (i - 1) * n + j;
            ij := LookupDictionary(idx_dict, elts[i] * elts[j]);
            A[row][i] := A[row][i] + 1;
            A[row][ij] := A[row][ij] - 1;
            A[row][j] := A[row][j] + 1;
            b[row] := c_g_vec[row] mod m;
        od;
    od;

    sol := AugmentedSolve(A, b, m, n);
    return sol <> fail;
end;;

# Solve A·beta ≡ b (mod m) for beta of length n, where A is n²×n.
AugmentedSolve := function(A, b, m, n)
    local n_eq, M, i, j, MT, sol;
    n_eq := Length(A);                # = n²
    # Build M = [A | -m·I_{n_eq}] of shape n_eq × (n + n_eq).
    M := List([1..n_eq], i -> Concatenation(A[i],
        List([1..n_eq], j -> If_(i = j, -m, 0))));
    # Solve x · M^T = b for x of length n + n_eq.
    sol := SolutionIntMat(TransposedMat(M), b);
    return sol;
end;;

If_ := function(cond, a, b) if cond then return a; else return b; fi; end;;

# ----------------------------------------------------------------------
# Top-level: enumerate H^3 classes and report which ones lie in the
# transgression kernel.
# ----------------------------------------------------------------------

TransgressionKernel := function(G)
    local setup, m, k, classes, kernel_vecs, vec, omega, in_kernel,
          i, gRep, c_g, isCob, total, count_in_kernel;

    setup := SetupCohomology3(G);
    m := setup.exponent;
    k := setup.num_generators;

    Print("\n");
    if IsBoundGlobal("_LogPhase") then
        _LogPhase("trkernel",
                  "=== Transgression kernel for G = ",
                  StructureDescription(G), " ===");
    else
        Print("=== Transgression kernel for G = ",
              StructureDescription(G), " ===\n");
    fi;
    Print("|G| = ", Order(G), "\n");
    Print("UCT.exponent (m) = ", m, "\n");
    Print("UCT.torsion = ", setup.UCT.torsion, "\n");
    Print("Number of generators of H^3 (k) = ", k, "\n");
    Print("Total |H^3(G; Z/", m, ")| = ", m^k, "\n");

    classes := ConjugacyClasses(G);
    Print("Conjugacy classes: ", Length(classes), "\n");

    Print("|H^3(G; U(1))| = ", setup.num_h3_classes, "\n");
    if setup.num_h3_classes > 1024 then
        Print("Too many H^3 classes to brute-force enumerate (",
              setup.num_h3_classes, ").\n");
        Print("Returning setup only; caller should sample.\n");
        return rec(setup := setup, classes := classes,
                   kernel_vecs := fail);
    fi;

    Print("\n--- Enumerating ", setup.num_h3_classes, " distinct H^3 classes ---\n");
    kernel_vecs := [];
    total := 0;
    count_in_kernel := 0;
    # vec[i] in 0..torsion[i]-1 (canonical reps).
    for vec in Cartesian(List(setup.torsion, t -> [0..t-1])) do
        total := total + 1;
        omega := StandardCocycleOf(setup, vec);
        in_kernel := true;
        for i in [1..Length(classes)] do
            gRep := Representative(classes[i]);
            c_g := CGCocycleFunc(omega, gRep);
            isCob := IsCoboundary2(Centralizer(G, gRep), c_g, m);
            if not isCob then
                in_kernel := false;
                break;
            fi;
        od;
        if in_kernel then
            Add(kernel_vecs, vec);
            count_in_kernel := count_in_kernel + 1;
        fi;
    od;

    Print("\nClasses in transgression kernel: ", count_in_kernel,
          " / ", total, "\n");

    return rec(setup := setup,
               classes := classes,
               kernel_vecs := kernel_vecs,
               kernel_size := count_in_kernel,
               total_classes := total);
end;;
