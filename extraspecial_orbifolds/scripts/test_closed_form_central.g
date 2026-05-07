# Verify closed-form central-row formulas against the direct library
# on E_+(2) (where we have the full S to compare to).

Read("untwisted_modular_data.g");
Read("closed_form_central.g");

G := SmallGroup(32, 49);;
Print("=== E_+(2): testing closed-form central-row formulas ===\n");
idx := BuildSimpleIndex(G);;
transport := BuildTransports(idx);;

# Locate the {1} class (z = identity) and the {-1} class.
class_id_one := ClassIndexOf(idx, One(G));;
class_id_minus1 := ClassIndexOf(idx, idx.reps[Filtered([1..Length(idx.classes)],
    i -> idx.class_sizes[i] = 1 and Order(idx.reps[i]) = 2)[1]]);;
Print("Class index of identity: ", class_id_one, "\n");
Print("Class index of -1 (central order 2): ", class_id_minus1, "\n");

# Sanity: verify a few rho indices for both central classes.
all_ok := true;;
for rho_idx in [1, 2, 5, idx.num_irreps[class_id_one]] do
    if not VerifyClosedFormAgainstDirect(idx, transport,
                                          class_id_one, rho_idx) then
        all_ok := false;
    fi;
od;
for rho_idx in [1, 2, 5, idx.num_irreps[class_id_minus1]] do
    if not VerifyClosedFormAgainstDirect(idx, transport,
                                          class_id_minus1, rho_idx) then
        all_ok := false;
    fi;
od;
Print("\n=== Summary: ", all_ok, " ===\n");

QUIT;
