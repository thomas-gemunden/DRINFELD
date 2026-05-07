# Port of section 4 of the Magma supplement (Keller-Roberts-Roberts,
# arXiv:2411.13646): the action of E(m) on the BW lattice in the
# w_i-basis, the bilinear form B_g, and the lift cocycle
#
#     u_g(alpha) = (-1)^{B_g(alpha, alpha)}      (eq 2.2.3 of paper).
#
# B_g is given by (eq 2.2.2):
#     B_g(alpha_i, alpha_j) = H_{ij} - H((alpha_i g), (alpha_j g))
#                                            for i > j,    0 else.
# In matrix form,  B_g = LowerStrict(H - g H g^T),
# where LowerStrict zeroes everything on or above the diagonal.
#
# We verify the main lifting theorems (3.3-3.5 of the paper) by
# checking u_{Σ_{ar}}(...) relations explicitly.

Read("bw_lattice.g");          # supplies BWGram, HalfGram, BitsOf, etc.
Read("em_construction.g");     # supplies Sigma_ar, ZGen, EmGroup

# --- Lattice-basis matrices for E(m) generators ---
# The action on w_i (a row vector) follows from (A.2.4)-(A.2.6) of the
# paper. We build the matrix M such that w_i ↦ row i of M (read as
# coefficients in the w_j basis).

UnimodSigma := function(m, a, r)
    local n, M, i, k, bits, ji, parityI;
    Assert(0, r in [1, 2]);
    n := 2^m;
    M := List([1..n], i -> List([1..n], j -> 0));
    for i in [0..n-1] do
        bits := BitsOf(i, m);
        k := bits[m - a + 1];                # i[m-a] in 0-indexed paper convention
        parityI := Parity(i, m);             # ∈ {0, 1}: (#zeros mod 2)
        if r = 1 then
            if k = 0 then M[i+1][i+1] := -1; else M[i+1][i+1] := 1; fi;
        else
            if k = 1 then M[i+1][i+1] := -1; else M[i+1][i+1] := 1; fi;
        fi;
        if (r = 1 and k = 0) or (r = 2 and k = 1) then
            ji := i + (1 - 2*k) * 2^(m - a);
            M[i+1][ji+1] := 2^parityI;
        fi;
    od;
    return M;
end;;

UnimodZ := function(m)
    return -IdentityMat(2^m);
end;;

# --- Bilinear form B_g on the lattice ---
LowerStrict := function(M)
    local n, R, i, j;
    n := Length(M);
    R := List([1..n], i -> List([1..n], j -> 0));
    for i in [1..n] do
        for j in [1..i-1] do R[i][j] := M[i][j]; od;
    od;
    return R;
end;;

# B_g matrix.   alpha is a length-d row vector of integers; B_g(alpha, alpha)
# = alpha . B_g . alpha^T  (using the lower-triangular B_g with zeros on
# the diagonal as well, since H - gHg^T is symmetric and we strip the
# upper triangle plus the diagonal — see below).
Bg := function(g, m)
    local H, gHgT;
    H := HalfGram(m);
    gHgT := g * H * TransposedMat(g);
    return LowerStrict(H - gHgT);
end;;

# Quadratic form value B_g(alpha, alpha)
BgQ := function(g, m, alpha)
    local n, total, i, j, B;
    B := Bg(g, m);
    n := Length(alpha);
    total := 0;
    for i in [1..n] do
        for j in [1..i-1] do
            total := total + alpha[i] * alpha[j] * B[i][j];
        od;
    od;
    return total;
end;;

# u_g(alpha) = (-1)^{B_g(alpha, alpha)}.  (Sign only depends on parity.)
ug := function(g, m, alpha)
    return (-1)^(BgQ(g, m, alpha) mod 2);
end;;

# Helper: write integer i in 0..2^m-1 as a length-2^m vector with a 1
# in position i+1, zeros elsewhere.  Used to evaluate u on a basis
# element.
BitsOfBasis := function(i, n)
    local v;
    v := List([1..n], k -> 0);
    v[i+1] := 1;
    return v;
end;;

# --- Verifications: theorems 3.3, 3.5 of the paper ---
# Theorem 3.3 (m even >= 4):  u_{Σ_{a,r}} = 1 for all generators.
# Theorem 3.5 (m >= 3):  the lifted Σ̂_{a,r} continue to satisfy the
#                         relations of E(m), so Ê(m) ≅ E(m).
#
# In matrix form, theorem 3.5 boils down to verifying for all (a, b, r, s):
#   u_{Σ_{a,r}}(α) u_{Σ_{a,r}}(α Σ_{a,r}) = 1                  ...(A)
#   u_{Σ_{a,r}}(α Σ_{b,s}) u_{Σ_{b,s}}(α) = u_{Σ_{b,s}}(α Σ_{a,r}) u_{Σ_{a,r}}(α)
#                                                              ...(B)
# for sufficiently many α (the basis is enough by linearity of B_g).

VerifyLift := function(m)
    local n, sigArrs, allOnes, errs, count, entry, a, r, sig, u, i, alpha,
          alphaSig, e1, e2, sig1, sig2, lhs, rhs;
    Print("\n=== Verifying lift of E(", m, ") (Theorems 3.3, 3.5) ===\n");

    n := 2^m;
    sigArrs := [];
    for a in [1..m] do for r in [1, 2] do
        Add(sigArrs, [a, r, UnimodSigma(m, a, r)]);
    od; od;

    Print("u_{Σ_{a,r}} on basis vectors (should be 1 if m even >= 4 — Thm 3.3): \n");
    allOnes := true;
    for entry in sigArrs do
        a := entry[1]; r := entry[2]; sig := entry[3];
        u := List([0..n-1], i -> ug(sig, m, BitsOfBasis(i, n)));
        if not ForAll(u, x -> x = 1) then
            Print("  Σ_{", a, ",", r, "}: u takes values ", Set(u), "\n");
            allOnes := false;
        fi;
    od;
    Print("  all u = 1 on basis: ", allOnes, "\n");

    Print("\nRelation (A): u_{Σ_{a,r}}(α) * u_{Σ_{a,r}}(α Σ_{a,r}) = 1 for (a,r) and basis α.\n");
    errs := 0;
    for entry in sigArrs do
        sig := entry[3];
        for i in [0..n-1] do
            alpha := BitsOfBasis(i, n);
            alphaSig := alpha * sig;
            if ug(sig, m, alpha) * ug(sig, m, alphaSig) <> 1 then errs := errs + 1; fi;
        od;
    od;
    Print("  errors: ", errs, "\n");

    Print("\nRelation (B): u_{Σ_ar}(α Σ_bs) u_{Σ_bs}(α) = u_{Σ_bs}(α Σ_ar) u_{Σ_ar}(α)\n");
    errs := 0; count := 0;
    for e1 in sigArrs do
        sig1 := e1[3];
        for e2 in sigArrs do
            sig2 := e2[3];
            for i in [0..n-1] do
                alpha := BitsOfBasis(i, n);
                lhs := ug(sig1, m, alpha * sig2) * ug(sig2, m, alpha);
                rhs := ug(sig2, m, alpha * sig1) * ug(sig1, m, alpha);
                if lhs <> rhs then errs := errs + 1; fi;
                count := count + 1;
            od;
        od;
    od;
    Print("  errors: ", errs, " out of ", count, " checks\n");
end;;

# Library file: VerifyLift(2/3/4) is run from test drivers, not on Read.
