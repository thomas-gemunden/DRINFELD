Read("compute_e_plus_7_T_analytical.g");

# Cross-check on m = 1, 2, 3 against the analytical predictor (and
# against the actually-computed T data for m = 2, 3, 5).
for m in [1, 2, 3, 5, 7] do
    CheckAgainstPredictor(m);
od;

# Persist E_+(7) data
SaveStructuralT(7, "../computed/E_plus_7");

# Print full headline result
agg7 := AggregateTMultiset(7);;
Print("\n=== E_+(7) full T-multiset (structural / Phase F') ===\n");
Print("  rank: ", agg7.total_rank, "\n");
Print("  T=1:  ", agg7.TMultiset.one, "\n");
Print("  T=-1: ", agg7.TMultiset.minus_one, "\n");
Print("  T=i:  ", agg7.TMultiset.i_val, "\n");
Print("  T=-i: ", agg7.TMultiset.minus_i, "\n");

QUIT;
