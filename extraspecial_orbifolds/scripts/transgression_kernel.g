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

# We use Gruen's UCT helper (in DRINFELD/src/modular_data.g):
Read("../../src/modular_data.g");

# ----------------------------------------------------------------------
# Setup: for a group G, get the H^3(G; Z/exp) data.
# ----------------------------------------------------------------------

SetupCohomology3 := function(G)
    local R, K, UCT;
    R := ResolutionFiniteGroup(G, 4);
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
    local elts, n, idx, i, j, ij, A, b, row, sol, R, A_mod, b_mod;
    elts := AsList(H);
    n := Length(elts);
    idx := function(h) return Position(elts, h); end;

    # Set up the system d_2(beta) = c, with rows indexed by (h, k):
    #   beta(h)  -  beta(hk)  +  beta(k)  =  c(h, k)  (mod m)
    # A is n²×n; A · beta = b (column equation, n² equations in n unknowns).
    A := NullMat(n*n, n);
    b := List([1..n*n], i -> 0);
    for i in [1..n] do
        for j in [1..n] do
            row := (i - 1) * n + j;
            ij := idx(elts[i] * elts[j]);
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

    Print("\n=== Transgression kernel for G = ", StructureDescription(G), " ===\n");
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
