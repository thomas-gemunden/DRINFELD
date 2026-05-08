# Test feasibility: can GAP compute CharacterTable of E_+(6) (|G|=8192)
# and centralizers of E_+(7) class reps (|G|=16384) on this machine?

LoadPackage("IO");

t0 := Runtime();;
Print("Constructing E_+(6) = ExtraspecialGroup(8192, '+')...\n");
E6 := ExtraspecialGroup(8192, "+");;
Print("  |E_+(6)| = ", Order(E6), "  in ", (Runtime() - t0)/1000., " s\n");

t0 := Runtime();;
Print("\nConjugacyClasses(E_+(6))...\n");
ccE6 := ConjugacyClasses(E6);;
Print("  ", Length(ccE6), " classes  in ", (Runtime() - t0)/1000., " s\n");

t0 := Runtime();;
Print("\nCharacterTable(E_+(6))...\n");
ctE6 := CharacterTable(E6);;
Print("  done in ", (Runtime() - t0)/1000., " s\n");
Print("  |Irr| = ", Length(Irr(ctE6)), "  (predicted ", 4^6 + 1, ")\n");

t0 := Runtime();;
Print("\nConstructing E_+(7) = ExtraspecialGroup(32768, '+')...\n");
E7 := ExtraspecialGroup(32768, "+");;
Print("  |E_+(7)| = ", Order(E7), "  in ", (Runtime() - t0)/1000., " s\n");

# Pick canonical sigma2 element: a generator of order 2 with non-trivial commutator
# with another generator.  By GAP's PC group convention for extraspecial groups,
# the FIRST generator should work.
t0 := Runtime();;
gens := GeneratorsOfGroup(E7);;
Print("  generators: ", Length(gens), "  orders: ", List(gens, Order), "\n");
g_sigma2 := gens[1];;
Print("  picked g_sigma2 = gens[1], order ", Order(g_sigma2),
      ", in centre? ", g_sigma2 in Centre(E7), "\n");

t0 := Runtime();;
Print("\nCentralizer(E_+(7), g_sigma2)...\n");
C_sigma2 := Centralizer(E7, g_sigma2);;
Print("  |C_sigma2| = ", Order(C_sigma2),
      "  predicted ", Order(E7) / 2, "  in ", (Runtime() - t0)/1000., " s\n");

t0 := Runtime();;
Print("\nConjugacyClasses(C_sigma2)...\n");
cc_C := ConjugacyClasses(C_sigma2);;
Print("  ", Length(cc_C), " classes  in ", (Runtime() - t0)/1000., " s\n");

t0 := Runtime();;
Print("\nCharacterTable(C_sigma2)...\n");
ct_C := CharacterTable(C_sigma2);;
Print("  done in ", (Runtime() - t0)/1000., " s\n");
Print("  |Irr| = ", Length(Irr(ct_C)),
      "  (predicted ", 2*4^6 + 2, ")\n");

QUIT;
