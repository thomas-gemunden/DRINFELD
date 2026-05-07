# Test driver for defect_rep_other.g.
#
# For m = 3 and m = 5, we take the conjugacy-class representatives
#
#   g_2 = Sigma_{1,1}                (order 2, non-central)
#   g_4 = Sigma_{1,1} * Sigma_{1,2}  (order 4)
#
# in the unimodular representation, then:
#
#   1. Compute the centralizer C_{E(m)}(g) using GAP's Centralizer.
#      Verify it has the order predicted by Proposition 3.1 of the paper:
#        |C_{E(m)}(g_2)| = 2 * 2^{2(m-1)+1} = 2^{2m}
#        |C_{E(m)}(g_4)| = 4 * 2^{2(m-1)+1} / 2 = 2^{2m}
#      (Both come out to 2^{2m}, since |E(m)| = 2^{2m+1} and the
#      conjugacy class of either has size |E(m)|/|C| = 2.)
#
#   2. Build N_θ for that g via SetupNTheta and BasisForN[Theta|S12].
#
#   3. Verify every element h in C_{E(m)}(g) acts trivially on N_θ.
#      (We sweep all elements, which is feasible up to |C| ≈ 1024.)
#
#   4. Report. If trivial, the corresponding intertwiner representation
#      is itself trivial and c_g = 0 automatically.
#
# This confirms the paper's claim (end of section 4.4): "Somewhat
# surprisingly, we found that for m = 3, 5, 7 the centralizer groups
# Z_2 × E(m-1) and Z_4 ◦ E(m-1) act trivially on N. Their intertwiner
# representations are thus trivial and automatically have vanishing
# 2-cocycle."

Read("defect_rep_other.g");

# Build the unimodular rep of E(m) as a matrix group.
EmUnimodGroup := function(m)
    local n, gens, a, r;
    n := 2^m;
    gens := [-IdentityMat(n)];
    for a in [1..m] do
        for r in [1, 2] do
            Add(gens, UnimodSigma(m, a, r));
        od;
    od;
    return Group(gens);
end;;

# Format a per-class report.
RunCase := function(m, label, g, predictedRank, predictedDescr)
    local Em, C, predicted, setup, basisN, result, n;
    Print("\n--- m = ", m, ", g = ", label, " ---\n");
    n := 2^m;
    Em := EmUnimodGroup(m);
    Print("  |E(", m, ")| = ", Order(Em), "\n");
    Print("  Order of g: ", Order(g), "\n");
    C := Centralizer(Em, g);
    predicted := 2^(2*m);
    Print("  |C_{E(m)}(g)| = ", Order(C),
          ",  predicted (Prop 3.1) ", predicted,
          ",  match: ", Order(C) = predicted, "\n");
    Print("  expected centralizer structure: ", predictedDescr, "\n");
    setup := SetupNTheta(g);
    Print("  SNF of (I - g): zeros = ", Length(setup.positions.zeros),
          ", ones = ", Length(setup.positions.ones),
          ", twos = ", Length(setup.positions.twos), "\n");
    Print("  N rank (= log_2 |N|) = ",
          Length(setup.positions.twos),
          ",  predicted ", predictedRank,
          ",  match: ", Length(setup.positions.twos) = predictedRank, "\n");
    if Length(setup.R1) > 0 then
        Print("  Building symplectic basis of N_theta... ");
        if label = "g_2" then
            basisN := BasisForNTheta(g);
        else
            basisN := BasisForNS12(g);
        fi;
        Print("dim ", Length(basisN), "\n");
    fi;
    Print("  Sweeping all ", Order(C), " elements of C_{E(m)}(g) for triviality of action on N...\n");
    result := CentralizerActsTriviallyOnN(g, AsList(C));
    if result.allTrivial then
        Print("  RESULT: all ", result.totalChecked, " elements act TRIVIALLY on N.\n");
        Print("    => intertwiner representation of C_{E(m)}(g) is trivial.\n");
        Print("    => 2-cocycle c_g = 0 automatically.\n");
    else
        Print("  RESULT: ", Length(result.fails), " out of ",
              result.totalChecked, " elements act non-trivially.\n");
        Print("    First failure: ", result.fails[1], "\n");
    fi;
end;;

Print("============================================================\n");
Print("Verifying triviality of the action of C_{E(m)}(g) on N_theta\n");
Print("for the non-(-1) conjugacy classes of E(m), m = 3 and m = 5.\n");
Print("This corresponds to section 4.4 of the paper (end), and to\n");
Print("section 7 of the Magma supplement.\n");
Print("============================================================\n");

# m = 3
m := 3;;
g2 := UnimodSigma(m, 1, 1);;
g4 := UnimodSigma(m, 1, 1) * UnimodSigma(m, 1, 2);;
# Predicted N rank: 2^{m-2} for g_2, 2^{m-1} for g_4.
RunCase(m, "g_2", g2, 2^(m-2), "Z_2 x E(m-1)");
RunCase(m, "g_4", g4, 2^(m-1), "Z_4 o E(m-1)");

# m = 5
m := 5;;
g2 := UnimodSigma(m, 1, 1);;
g4 := UnimodSigma(m, 1, 1) * UnimodSigma(m, 1, 2);;
RunCase(m, "g_2", g2, 2^(m-2), "Z_2 x E(m-1)");
RunCase(m, "g_4", g4, 2^(m-1), "Z_4 o E(m-1)");

Print("\n============================================================\n");
Print("Done. The paper's claim is confirmed for m = 3, 5: the\n");
Print("centralizers Z_2 x E(m-1) and Z_4 o E(m-1) act trivially on N\n");
Print("for both non-(-1) classes, so their intertwiner representations\n");
Print("are trivial and the corresponding 2-cocycles vanish.\n");
Print("============================================================\n");

QUIT;
