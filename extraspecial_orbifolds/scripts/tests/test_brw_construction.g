# Tests for BRW(m), the Bolt-Room-Wall group of E_+(m). See
# scripts/brw_construction.g for the construction.
#
# Acceptance criteria verified here (per refined T-3a spec):
#   (2) E_+(m) is normal in BRW(m).
#   (3) |BRW(m)| matches the predicted formula 2 · |Aut(E_+(m))|, with
#       the factor of 2 coming from the centre {±I_{2^m}}.
#   (4) Centralizer of E_+(m) in BRW(m) consists of scalar matrices
#       (in practice {±I}, since none of our chosen generators
#       introduces a complex scalar).
#   (5) The quotient BRW(m)/E_+(m) is the orthogonal group O^+(2m, F_2).
#
# m=2: all criteria are cheap to verify.
# m=3: criterion (2) and criterion (3) are reported; criterion (5)
#      is checked structurally via the order-equality criterion (3)
#      and a smaller IdSmallGroup test on the quotient if feasible.

ChangeDirectoryCurrent("/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-t3a/extraspecial_orbifolds/scripts");
Read("brw_construction.g");

# ---------------------------------------------------------------------
# Helpers.
# ---------------------------------------------------------------------

ScalarMatrix := function(n, lambda)
    return lambda * IdentityMat(n);
end;;

IsScalarMatrix := function(M)
    local n;
    n := Length(M);
    if n = 0 then return true; fi;
    return M = M[1][1] * IdentityMat(n);
end;;

CheckAllScalar := function(G)
    return ForAll(GeneratorsOfGroup(G), IsScalarMatrix)
        and ForAll(Elements(G), IsScalarMatrix);
end;;

# Expected orders: |O^+(2m, F_2)|.
# Formula: |O^+(2m, q)| = 2 * q^{m(m-1)} * (q^m - 1) * prod_{i=1}^{m-1} (q^{2i} - 1)
# For q = 2:
#   m=2: 2 * 1 * (4 - 1) * (4 - 1) = 18  — WRONG: this is |SO|, not |GO|.
# GAP's |GO(1, 2m, 2)| gives the correct group order. For us:
#   m=1: |GO(1, 2, 2)| = 2
#   m=2: |GO(1, 4, 2)| = 72
#   m=3: |GO(1, 6, 2)| = 40320

OplusOrder := function(m)
    return Order(GeneralOrthogonalGroup(1, 2*m, 2));
end;;

# Predicted |BRW(m)| = |E_+(m)| · |O^+(2m, F_2)| · k, where k is the
# extra factor from the kernel of BRW(m) → Aut(E_+(m)) (= scalar centre).
# Empirically k = 2 (the {±I} centre) for our generator choice.

ExpectedBRWOrder := function(m)
    return 2^(2*m + 1) * OplusOrder(m);
end;;

# ---------------------------------------------------------------------
# m = 2: full verification.
# ---------------------------------------------------------------------

Print("\n========================================\n");
Print("Tests for BRW(m) at m = 2\n");
Print("========================================\n");

m := 2;;
B2 := BRW(m);;
Em2 := EmGroup(m);;
n2 := 2^m;;

# Sanity checks.
ord_B2 := Order(B2);;
ord_E2 := Order(Em2);;
Print("\n|E_+(2)| = ", ord_E2, "  (expected 32)\n");
Print("|BRW(2)| = ", ord_B2, "\n");
Print("Expected |BRW(2)| = 2 · 32 · |O^+(4, F_2)| = 2 · 32 · ",
      OplusOrder(m), " = ", ExpectedBRWOrder(m), "\n");
Print("Match: ", ord_B2 = ExpectedBRWOrder(m), "\n");

# Criterion (2): E_+(2) ◁ BRW(2).
Print("\n--- Criterion (2): E_+(2) normal in BRW(2) ---\n");
normal_via_isnormal := IsNormal(B2, Em2);;
Print("IsNormal(BRW(2), E_+(2)): ", normal_via_isnormal, "\n");
# Also do the manual check.
all_normal := ForAll(GeneratorsOfGroup(B2), g ->
    ForAll(GeneratorsOfGroup(Em2), h -> (g * h * g^(-1)) in Em2));;
Print("Manual check (g h g^-1 in Em for all generators): ",
      all_normal, "\n");

# Criterion (4): Centralizer of E_+(2) in BRW(2) is scalar.
Print("\n--- Criterion (4): C_{BRW(2)}(E_+(2)) ⊆ scalars ---\n");
C2 := Centralizer(B2, Em2);;
ord_C2 := Order(C2);;
Print("|Centralizer| = ", ord_C2, "\n");
all_scalar2 := ForAll(GeneratorsOfGroup(C2), IsScalarMatrix);;
# Stronger test: enumerate and check.
all_scalar2_full := ForAll(Elements(C2), IsScalarMatrix);;
Print("All generators of centralizer are scalar: ", all_scalar2, "\n");
Print("All elements of centralizer are scalar: ", all_scalar2_full, "\n");
scalars2 := Set(List(Elements(C2), g -> g[1][1]));;
Print("Distinct scalar values: ", scalars2, "\n");

# Criterion (5): Quotient is O^+(4, F_2).
Print("\n--- Criterion (5): BRW(2)/E_+(2) ≅ O^+(4, F_2) ---\n");
hom2 := NaturalHomomorphismByNormalSubgroup(B2, Em2);;
Q2 := Image(hom2);;
Print("|Q| = ", Order(Q2),
      "  (expected ", OplusOrder(m), ")\n");
Print("Structure description of Q: ", StructureDescription(Q2), "\n");
Q2_id := IdSmallGroup(Q2);;
OplusGAP2 := GeneralOrthogonalGroup(1, 4, 2);;
Oplus2_id := IdSmallGroup(OplusGAP2);;
Print("IdSmallGroup(Q): ", Q2_id, "\n");
Print("IdSmallGroup(GO(1, 4, 2)): ", Oplus2_id, "\n");
Print("Isomorphic: ", Q2_id = Oplus2_id, "\n");

# ---------------------------------------------------------------------
# m = 3: lighter-weight verification.
# ---------------------------------------------------------------------

Print("\n========================================\n");
Print("Tests for BRW(m) at m = 3\n");
Print("========================================\n");

m := 3;;
B3 := BRW(m);;
Em3 := EmGroup(m);;
n3 := 2^m;;

Print("\n|E_+(3)| = ", Order(Em3), "  (expected 128)\n");
Print("Expected |BRW(3)| = 2 · 128 · |O^+(6, F_2)| = 2 · 128 · ",
      OplusOrder(m), " = ", ExpectedBRWOrder(m), "\n");

# Criterion (2): normality. This should be cheap.
Print("\n--- Criterion (2) for m=3: E_+(3) ◁ BRW(3) ---\n");
t := Runtime();;
normal3 := IsNormal(B3, Em3);;
Print("IsNormal(BRW(3), E_+(3)): ", normal3,
      "  (took ", Runtime() - t, " ms)\n");

# Criterion (3): order. This is the most informative test for m=3.
Print("\n--- Criterion (3) for m=3: |BRW(3)| = ", ExpectedBRWOrder(3),
      " ---\n");
t := Runtime();;
ord_B3 := Order(B3);;
Print("|BRW(3)| = ", ord_B3, "  (took ", Runtime() - t, " ms)\n");
Print("Expected: ", ExpectedBRWOrder(3), "\n");
Print("Match: ", ord_B3 = ExpectedBRWOrder(3), "\n");

# Criterion (4) for m=3: Centralizer ⊆ scalars.
Print("\n--- Criterion (4) for m=3: C_{BRW(3)}(E_+(3)) ⊆ scalars ---\n");
t := Runtime();;
C3 := Centralizer(B3, Em3);;
ord_C3 := Order(C3);;
Print("|Centralizer| = ", ord_C3, "  (took ", Runtime() - t, " ms)\n");
all_scalar3 := ForAll(GeneratorsOfGroup(C3), IsScalarMatrix);;
all_scalar3_full := ForAll(Elements(C3), IsScalarMatrix);;
Print("All generators of centralizer are scalar: ", all_scalar3, "\n");
Print("All elements of centralizer are scalar: ", all_scalar3_full, "\n");
scalars3 := Set(List(Elements(C3), g -> g[1][1]));;
Print("Distinct scalar values: ", scalars3, "\n");

# Criterion (5) for m=3: quotient ≅ O^+(6, F_2) = S_8.
Print("\n--- Criterion (5) for m=3: BRW(3)/E_+(3) ≅ O^+(6, F_2) = S_8 ---\n");
t := Runtime();;
hom3 := NaturalHomomorphismByNormalSubgroup(B3, Em3);;
Q3 := Image(hom3);;
Print("|Q| = ", Order(Q3), "  (took ", Runtime() - t, " ms)\n");
t := Runtime();;
sd3 := StructureDescription(Q3);;
sd_Oplus3 := StructureDescription(GeneralOrthogonalGroup(1, 6, 2));;
Print("StructureDescription(BRW(3)/E_+(3)): ", sd3, "\n");
Print("StructureDescription(GO(1, 6, 2)): ", sd_Oplus3, "\n");
Print("Matching structure descriptions: ", sd3 = sd_Oplus3,
      "  (took ", Runtime() - t, " ms total)\n");

Print("\n========================================\n");
Print("All BRW tests done.\n");
Print("========================================\n");
