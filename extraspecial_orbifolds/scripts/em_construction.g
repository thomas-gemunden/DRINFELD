# Port of section 2 of the Magma supplement (Keller-Roberts-Roberts,
# arXiv:2411.13646): construction of the extraspecial 2-group
# E(m) = 2_+^{2m+1} as a matrix subgroup of O(2^m, R), with the
# generators
#
#     z = -I_{2^m}
#     Σ_{a,r} = I_2 ⊗ ... ⊗ I_2 ⊗ σ_r ⊗ I_2 ⊗ ... ⊗ I_2     (σ_r in slot a)
#
# where σ_1 = [[0,1],[1,0]], σ_2 = [[1,0],[0,-1]].
#
# The Magma originals are sig1, sig2, E(m) on lines 156-275.

sigma1 := [[0, 1], [1, 0]];;
sigma2 := [[1, 0], [0, -1]];;
sigma3 := sigma1 * sigma2;;   # = [[0, -1], [1, 0]]; equals σ_1 σ_2
I2 := [[1, 0], [0, 1]];;

# Tensor (Kronecker) product of a list of 2x2 matrices.
TensorList := function(matrices)
    local result, m;
    result := matrices[1];
    for m in matrices{[2..Length(matrices)]} do
        result := KroneckerProduct(result, m);
    od;
    return result;
end;;

# Σ_{a,r}: σ_r in slot a (1-indexed from the LEFT, matching Magma's "nth slot"
# but we'll be careful about ordering convention later if needed).
Sigma_ar := function(m, a, r)
    local factors, i;
    Assert(0, 1 <= a and a <= m, "a must be in 1..m");
    Assert(0, r in [1, 2], "r must be 1 or 2");
    factors := [];
    for i in [1..m] do
        if i = a then
            if r = 1 then Add(factors, sigma1);
            else            Add(factors, sigma2);
            fi;
        else
            Add(factors, I2);
        fi;
    od;
    return TensorList(factors);
end;;

# z = -1 (the central element).
ZGen := function(m)
    return -IdentityMat(2^m);
end;;

# E(m) as a matrix group.
EmGroup := function(m)
    local gens, a;
    gens := [ZGen(m)];
    for a in [1..m] do
        Add(gens, Sigma_ar(m, a, 1));
        Add(gens, Sigma_ar(m, a, 2));
    od;
    return Group(gens);
end;;

# ---- Verification ----

VerifyEm := function(m)
    local G, z, gensAr, expectedSize, idG, sgn, fid, fG, found;
    Print("\n=== Verifying E(m) for m = ", m, " ===\n");
    G := EmGroup(m);
    expectedSize := 2^(2*m + 1);
    Print("|E(", m, ")| computed: ", Order(G),
          ",  expected: ", expectedSize,
          ",  match: ", Order(G) = expectedSize, "\n");
    z := ZGen(m);
    gensAr := List([1..m], a -> [Sigma_ar(m, a, 1), Sigma_ar(m, a, 2)]);

    # z central
    Print("z is central: ",
          ForAll(GeneratorsOfGroup(G), g -> z*g = g*z), "\n");
    # z^2 = 1
    Print("z^2 = I: ", z*z = IdentityMat(2^m), "\n");
    # Σ_{a,r}^2 = 1
    Print("Σ_{a,r}^2 = I for all (a,r): ",
          ForAll(gensAr, pair -> ForAll(pair, S -> S*S = IdentityMat(2^m))), "\n");
    # commutators: [Σ_{a,1}, Σ_{a,2}] = z and 1 otherwise.
    # For a, b ∈ 1..m and r, s ∈ {1,2},
    #   Σ_ar Σ_bs = z^{δ_{ab} δ_{r ≠ s}} Σ_bs Σ_ar
    Print("Commutator pattern Σ_{a,r}Σ_{b,s} = z^{a=b ∧ r≠s} Σ_{b,s}Σ_{a,r}: ");
    Print(ForAll([1..m], a -> ForAll([1..m], b ->
        ForAll([1, 2], r -> ForAll([1, 2], s ->
            gensAr[a][r]*gensAr[b][s] =
            (function() if a = b and r <> s then return z*gensAr[b][s]*gensAr[a][r];
                       else return gensAr[b][s]*gensAr[a][r]; fi; end)()
        )))), "\n");

    # Identify against the GAP small-group library
    if expectedSize <= 256 then
        idG := IdSmallGroup(G);
        Print("IdSmallGroup: ", idG,
              ",  StructureDescription: ", StructureDescription(G), "\n");
        # Compare to GAP's ExtraspecialGroup(_, "+")
        fG := ExtraspecialGroup(expectedSize, "+");
        fid := IdSmallGroup(fG);
        Print("Reference E_+(", m, ") = SmallGroup(", expectedSize,
              ", ", fid[2], "),  matches: ", idG = fid, "\n");
    fi;
end;;

# Tests run via test_em_construction.g, not on Read.
