# Phase D: closed-form S-matrix entries for the central-class rows.
#
# For any finite group G with central element z and the untwisted
# Drinfeld center Mod(D^1(G)), the entry
#
#     S_{((g_1, rho_1), (h, sigma))}
#
# admits a closed form whenever g_1 is central. Specifically:
#
#     g_1 = 1:    S = (dim(sigma) / |C_G(h)|) * conj( rho_1(h) )
#     g_1 = -1:   S = (sigma(-1)  / |C_G(h)|) * conj( rho_1(h) )
#
# Here rho_1 is an irreducible character of G (since C_G(g_1) = G when
# g_1 is central), sigma is an irreducible character of C_G(h),
# sigma(-1) = epsilon * dim sigma with epsilon in {+1, -1} (because -1
# is central and acts as a scalar on irreducible representations).
#
# These formulas are O(1) per entry given the character tables and
# can be applied to any m up to 7 (where we cannot store the full S
# but can answer single-entry queries instantly).

# `idx` is the BuildSimpleIndex(G) record produced by
# untwisted_modular_data.g.

# Index of the {1} class (typically 1, but verify) and {-1} class.
ClassIndexOf := function(idx, g)
    local i;
    for i in [1..Length(idx.classes)] do
        if g in idx.classes[i] then return i; fi;
    od;
    return fail;
end;;

# Compute S_{((g_central, rho_1), (h, sigma))} via the closed form.
# `central_class` is the class index of the central element used as g_1
# (must be a singleton class).
# `rho_index` is the index of an irrep in Irr(C_G(g_central)) = Irr(G).
# `target_class` is the class index of h in idx.classes.
# `sigma_index` is the index of an irrep in Irr(C_G(h)).
ClosedFormCentralS := function(idx, central_class, rho_index,
                               target_class, sigma_index)
    local rep_central, rep_target, rho, sigma, dim_sigma, sigma_at_central,
          rho_at_target, denom;
    rep_central := idx.reps[central_class];
    rep_target := idx.reps[target_class];

    # rho ∈ Irr(C_G(g_central)) = Irr(G).  For us, g_central is in {1, -1},
    # both of which have C_G = G, so the centraliser at central_class IS G
    # and the irreps are Irr(G) = idx.irreps[central_class].
    rho := idx.irreps[central_class][rho_index];
    sigma := idx.irreps[target_class][sigma_index];

    # dim sigma
    dim_sigma := idx.irrep_dims[target_class][sigma_index];

    # rho(rep_target) — evaluate via class lookup in Irr of central_class
    # (which is Irr of G).
    rho_at_target := EvalIrr(idx, central_class, rho_index, rep_target);

    # sigma(rep_central) — evaluate via class lookup in Irr of target_class
    # (Irr of C_G(rep_target)).  rep_central must be in C_G(rep_target);
    # this holds whenever rep_central is central in G (it commutes with
    # everything).
    sigma_at_central := EvalIrr(idx, target_class, sigma_index, rep_central);

    # Issue #449 A1': lazy centraliser materialisation for closed-form
    # E_+(m) idxs. No-op for eager idxs.
    if IsBoundGlobal("_EPlusCentraliserOf") then
        denom := Order(_EPlusCentraliserOf(idx, target_class));
    else
        denom := Order(idx.centralisers[target_class]);
    fi;
    return sigma_at_central * ComplexConjugate(rho_at_target) / denom;
end;;

# Convenience: compute the full row corresponding to (g_central, rho).
# Returns a list of length idx.rank with entries
#    S_((g_central, rho), (h, sigma)) for each simple (h, sigma).
ClosedFormCentralRow := function(idx, central_class, rho_index)
    local row, i, k, rep, val;
    row := [];
    for i in [1..Length(idx.classes)] do
        rep := idx.reps[i];
        for k in [1..idx.num_irreps[i]] do
            val := ClosedFormCentralS(idx, central_class, rho_index, i, k);
            Add(row, val);
        od;
    od;
    return row;
end;;

# Verify a single S-entry from the closed form against a direct
# computation via ComputeSBlock (use this for sanity checking).
VerifyClosedFormAgainstDirect := function(idx, transport, central_class, rho_index)
    local block_to_target, target_class, k_sigma, computed, closed, ok;
    Print("Verifying closed-form (g_", central_class, ", rho=",
          rho_index, ") rows against direct ComputeSBlock...\n");
    ok := true;
    for target_class in [1..Length(idx.classes)] do
        block_to_target := ComputeSBlock(idx, transport,
                                         central_class, target_class);
        for k_sigma in [1..idx.num_irreps[target_class]] do
            computed := block_to_target[rho_index][k_sigma];
            closed := ClosedFormCentralS(idx, central_class, rho_index,
                                         target_class, k_sigma);
            if computed <> closed then
                Print("  MISMATCH at target_class=", target_class,
                      " k_sigma=", k_sigma,
                      " : direct=", computed, " closed=", closed, "\n");
                ok := false;
            fi;
        od;
    od;
    if ok then Print("  match: all ", idx.rank, " entries agree.\n"); fi;
    return ok;
end;;
