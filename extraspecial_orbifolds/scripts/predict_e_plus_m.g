# Analytical prediction of the per-sector rank and T-eigenvalue multiset of
# Mod(D^1(E_+(m))) (untwisted Drinfeld center) for any m, derived from
# the conjugacy class / centraliser structure of E_+(m).
#
# Decomposition (under E_+(m)-conjugation):
#   * 1 class {1}: centraliser = E(m), |Irr| = 4^m + 1
#   * 1 class {-1}: centraliser = E(m), |Irr| = 4^m + 1
#   * (4^m - 1) non-central classes, each of size 2:
#       - 2^{2m-1} + 2^{m-1} - 1  order-2 classes, centraliser  Z_2 × E(m-1)
#       - 2^{2m-1} - 2^{m-1}      order-4 classes, centraliser  Z_4 ∘ E(m-1)
#
# For each centraliser, |Irr| = 2 * 4^{m-1} + 2.
#
# T-eigenvalues per sector (T = chi(g)/dim):
#   * {1}-sector:                4^m + 1 simples, all T=1.
#   * {-1}-sector:               4^m simples T=1, 1 simple T=-1.
#   * order-2 non-central class g, C = <g> × E(m-1):
#       4^{m-1} + 1 simples T=1, 4^{m-1} + 1 simples T=-1.
#   * order-4 non-central class g, C = Z_4 ∘ E(m-1) with g of order 4:
#       4^{m-1} simples T=1, 4^{m-1} simples T=-1,
#       1 simple T=i, 1 simple T=-i.

PredictE_plus_m := function(m)
    local nC1, n_minus1, nO2, nO4, irrCenter, irrCent;
    nC1 := 1;                         # {1}
    n_minus1 := 1;                    # {-1}
    nO2 := 2^(2*m - 1) + 2^(m - 1) - 1;  # # order-2 non-central classes
    nO4 := 2^(2*m - 1) - 2^(m - 1);      # # order-4 non-central classes
    irrCenter := 4^m + 1;              # |Irr(E(m))|, used for {1} and {-1}
    irrCent := 2*4^(m-1) + 2;          # |Irr(centraliser of non-central)|
    return rec(
        m := m,
        groupOrder := 2^(2*m+1),
        rank := 2*irrCenter + (4^m - 1)*irrCent,  # 2*(4^m+1) + (4^m-1)*(2*4^{m-1}+2)
        sectors := rec(
            id := rec(count := nC1, irrCount := irrCenter, T := rec(one := irrCenter)),
            minus1 := rec(count := n_minus1, irrCount := irrCenter,
                          T := rec(one := irrCenter - 1, minus_one := 1)),
            order2 := rec(count := nO2, irrCount := irrCent,
                          T := rec(one := 4^(m-1) + 1, minus_one := 4^(m-1) + 1)),
            order4 := rec(count := nO4, irrCount := irrCent,
                          T := rec(one := 4^(m-1), minus_one := 4^(m-1),
                                   i := 1, minus_i := 1))
        ),
        TMultiset := rec(
            one    := nC1*irrCenter
                       + n_minus1*(irrCenter - 1)
                       + nO2*(4^(m-1) + 1)
                       + nO4*(4^(m-1)),
            minus_one := n_minus1*1
                       + nO2*(4^(m-1) + 1)
                       + nO4*(4^(m-1)),
            i      := nO4*1,
            minus_i := nO4*1
        )
    );
end;;

PrintPrediction := function(m)
    local p, s;
    p := PredictE_plus_m(m);
    Print("\n=== E_+(", m, "),  |G| = 2^{", 2*m+1, "} = ", p.groupOrder, " ===\n");
    Print("Predicted rank of Mod(D^1(E_+(", m, "))): ", p.rank, "\n");
    Print("Number of conjugacy classes: ", 4^m + 1,
          "  ({1}: ", p.sectors.id.count,
          ", {-1}: ", p.sectors.minus1.count,
          ", ord-2: ", p.sectors.order2.count,
          ", ord-4: ", p.sectors.order4.count, ")\n");
    s := p.TMultiset;
    Print("Predicted T-multiset:\n");
    Print("  T = 1     : ", s.one, "\n");
    Print("  T = -1    : ", s.minus_one, "\n");
    Print("  T = i     : ", s.i, "\n");
    Print("  T = -i    : ", s.minus_i, "\n");
    Print("  total     : ", s.one + s.minus_one + s.i + s.minus_i,
          " (must equal rank = ", p.rank, ", check: ",
          s.one + s.minus_one + s.i + s.minus_i = p.rank, ")\n");
end;;

# Library file: PrintPrediction is callable from drivers; no auto-run on Read.
