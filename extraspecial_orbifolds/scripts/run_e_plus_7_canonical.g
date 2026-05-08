# E_BRW m=7: 22 canonical S-blocks of Mod(D^1(E_+(7))).
#
# Bypasses ConjugacyClasses(E_+(7)) (which OOMs even at 60 GB heap)
# by:
#
#   * Computing only the centralisers of the 6 canonical class
#     representatives we need (orders 16384 or 32768):
#     id, -1, sigma2_canon, sigma2_second, sigma1sigma2_canon,
#     sigma1sigma2_second.
#
#   * For NON-CENTRAL × NON-CENTRAL blocks (centraliser order 16384):
#     GAP's `Centralizer` and `CharacterTable` work at this size; we
#     use the standard Bantay/CGR formula via ComputeSBlock-like
#     evaluation.
#
#   * For CENTRAL × * blocks (rows or cols indexed by Irr(E_+(7))
#     itself): the closed forms
#       S_((1, rho), (h, sigma))  = dim(sigma)/|C_G(h)| * conj(rho(h))
#       S_((-1, rho), (h, sigma)) = sigma(-1)/|C_G(h)| * conj(rho(h))
#     are computable analytically from the structural Irr(E_+(7))
#     (16384 linear characters from E_+(7)/Z = (Z/2)^14, plus 1
#     faithful character of dim 2^7 = 128 with values
#     128 at 1, -128 at z, 0 elsewhere).  No GAP CharacterTable
#     needed.

LoadPackage("IO");

Read("untwisted_modular_data.g");
Read("compute_canonical_blocks.g");

# ---------------------------------------------------------------
# Build the 6 canonical class representatives
# ---------------------------------------------------------------

t0 := Runtime();;
Print("Constructing E_+(7)...\n");
G := ExtraspecialGroup(32768, "+");;
gens := GeneratorsOfGroup(G);;
Print("  done (", Length(gens), " generators)\n");

Z_G := Centre(G);;
z := First(GeneratorsOfGroup(Z_G), x -> Order(x) = 2);;
Assert(0, z <> One(G));
Assert(0, z * z = One(G));
Print("  found central z, z^2 = 1\n");

g_id := One(G);;
g_minus := z;;
g_sigma2_canon := gens[1];;       # a_1, order 2 non-central
g_sigma2_second := gens[3];;      # a_2, order 2 non-central, commutes with a_1
g_sigma1sigma2_canon := gens[1] * gens[2];;       # a_1 b_1, order 4
g_sigma1sigma2_second := gens[3] * gens[4];;      # a_2 b_2, order 4

# Sanity
Print("  g_sigma2_canon order: ", Order(g_sigma2_canon), "\n");
Print("  g_sigma2_second order: ", Order(g_sigma2_second), "\n");
Print("  g_sigma1sigma2_canon order: ", Order(g_sigma1sigma2_canon), "\n");
Print("  g_sigma1sigma2_second order: ", Order(g_sigma1sigma2_second), "\n");
Print("  [a_1, a_2] (should be 1): ",
      g_sigma2_canon * g_sigma2_second
      = g_sigma2_second * g_sigma2_canon, "\n");
Print("  [a_1*b_1, a_2*b_2] (should be 1): ",
      g_sigma1sigma2_canon * g_sigma1sigma2_second
      = g_sigma1sigma2_second * g_sigma1sigma2_canon, "\n");

# ---------------------------------------------------------------
# Compute centralisers and character tables for the 4 non-central canonicals
# ---------------------------------------------------------------

ComputeCentraliserData := function(rep, label)
    local C, ct, cc, irr, dims, t;
    Print("\nCentraliser of ", label, "...\n");
    t := Runtime();
    C := Centralizer(G, rep);
    Print("  |C| = ", Order(C), "  in ", (Runtime() - t)/1000., " s\n");
    t := Runtime();
    ct := CharacterTable(C);
    cc := ConjugacyClasses(ct);
    irr := Irr(ct);
    dims := List(irr, chi -> chi[1]);
    Print("  CharacterTable + Irr: ", Length(irr), " irreps, dims sum-of-sq = ",
          Sum(dims, d -> d^2), "  in ", (Runtime() - t)/1000., " s\n");
    return rec(rep := rep, label := label, centraliser := C, ct := ct,
               cc := cc, irreps := irr, dims := dims);
end;;

# Pre-define class-map machinery (used by EvalIrr below).
BuildClassMap := function(centraliser_data)
    local map, cc, j, elt;
    map := NewDictionary(One(centraliser_data.centraliser), true,
                         centraliser_data.centraliser);
    cc := centraliser_data.cc;
    for j in [1..Length(cc)] do
        for elt in AsSSortedList(cc[j]) do
            AddDictionary(map, elt, j);
        od;
    od;
    centraliser_data.class_map := map;
    return centraliser_data;
end;;

data_sigma2_canon := ComputeCentraliserData(g_sigma2_canon, "sigma2_canon (a_1)");;
BuildClassMap(data_sigma2_canon);;
Print("  built class-map for sigma2_canon (", Order(data_sigma2_canon.centraliser), " elements)\n");
data_sigma2_second := ComputeCentraliserData(g_sigma2_second, "sigma2_second (a_2)");;
BuildClassMap(data_sigma2_second);;
Print("  built class-map for sigma2_second\n");
data_sigma1sigma2_canon := ComputeCentraliserData(g_sigma1sigma2_canon, "sigma1sigma2_canon (a_1 b_1)");;
BuildClassMap(data_sigma1sigma2_canon);;
Print("  built class-map for sigma1sigma2_canon\n");
data_sigma1sigma2_second := ComputeCentraliserData(g_sigma1sigma2_second, "sigma1sigma2_second (a_2 b_2)");;
BuildClassMap(data_sigma1sigma2_second);;
Print("  built class-map for sigma1sigma2_second\n");

# ---------------------------------------------------------------
# For each non-central canonical class, build transport: list of class
# elements + conjugating elements t_a.
# ---------------------------------------------------------------

BuildTransportSingle := function(G, canonical_data)
    local rep, C, elements, t_of, e, t;
    rep := canonical_data.rep;
    # Class elements: {rep, -rep} (size-2 class)
    elements := [rep, rep * z];
    t_of := [];
    for e in elements do
        t := RepresentativeAction(G, rep, e);
        if t = fail then
            Error("RepresentativeAction failed for class element of ", canonical_data.label);
        fi;
        Add(t_of, t);
    od;
    return rec(elements := elements, t_of := t_of);
end;;

t_sigma2_canon := BuildTransportSingle(G, data_sigma2_canon);;
t_sigma2_second := BuildTransportSingle(G, data_sigma2_second);;
t_sigma1sigma2_canon := BuildTransportSingle(G, data_sigma1sigma2_canon);;
t_sigma1sigma2_second := BuildTransportSingle(G, data_sigma1sigma2_second);;

# ---------------------------------------------------------------
# Class lookup in centraliser.
# ---------------------------------------------------------------

ClassIdxInCentraliser := function(centraliser_data, x)
    return LookupDictionary(centraliser_data.class_map, x);
end;;

EvalIrr := function(centraliser_data, k, x)
    return centraliser_data.irreps[k][ClassIdxInCentraliser(centraliser_data, x)];
end;;

# ---------------------------------------------------------------
# Compute a non-central x non-central canonical block.
# ---------------------------------------------------------------

ComputeNonCentralBlock := function(data_first, transport_first,
                                    data_second, transport_second)
    local Ni, Nj, M, ai, bi, a, b, t_a, s_b, b_tilde, a_tilde, k, l;
    Ni := Length(data_first.irreps);
    Nj := Length(data_second.irreps);
    M := List([1..Ni], k -> List([1..Nj], l -> 0));
    for ai in [1..Length(transport_first.elements)] do
        a := transport_first.elements[ai];
        t_a := transport_first.t_of[ai];
        for bi in [1..Length(transport_second.elements)] do
            b := transport_second.elements[bi];
            if a * b <> b * a then continue; fi;
            s_b := transport_second.t_of[bi];
            b_tilde := t_a^-1 * b * t_a;
            a_tilde := s_b^-1 * a * s_b;
            for k in [1..Ni] do
                for l in [1..Nj] do
                    M[k][l] := M[k][l]
                        + ComplexConjugate(EvalIrr(data_first, k, b_tilde))
                        * ComplexConjugate(EvalIrr(data_second, l, a_tilde));
                od;
            od;
        od;
    od;
    return M / Order(G);
end;;

# ---------------------------------------------------------------
# Closed-form Irr(E_+(7))
# ---------------------------------------------------------------
# 1-dim irreps: chi_v for v in (F_2)^14.  chi_v(x) = (-1)^{<v, pi(x)>}
#   where pi: E_+(7) -> E_+(7)/Z = (F_2)^14.  Since Z = <z>, pi is the
#   natural projection.
# Faithful irrep: dim 128, chi(1) = 128, chi(z) = -128, chi(x) = 0 for non-central x.
#
# We don't materialise all 16385 chars; we provide an evaluation function
# rho_index(x) -> value, where rho_index in [1..16384] indexes 1-dim
# chars by binary representation of v, and rho_index = 16385 is the
# faithful char.

# Project x in E_+(7) to a vector in (F_2)^14 = E_+(7)/Z.
# Use the fact that GeneratorsOfGroup(G) = (a_1, b_1, ..., a_7, b_7, z).
# We obtain pi(x) by writing x in PC normal form and reading the
# coefficients of the first 14 generators (mod 2).

# For PC groups, ExponentsOfPcElement returns the PC exponent vector.
# Coefficients on generators 1..14 (mod 2) give pi(x).
PiOfElement := function(x)
    local exps;
    exps := ExponentsOfPcElement(FamilyPcgs(G), x);
    return List([1..14], i -> exps[i] mod 2);
end;;

# Pre-compute pi(x) for the canonical reps and class elements.
Print("\nPrecomputing pi(x) for class elements...\n");
pi_id := PiOfElement(g_id);;
pi_minus := PiOfElement(z);;
pi_sigma2_canon := PiOfElement(g_sigma2_canon);;
pi_sigma2_second := PiOfElement(g_sigma2_second);;
pi_sigma1sigma2_canon := PiOfElement(g_sigma1sigma2_canon);;
pi_sigma1sigma2_second := PiOfElement(g_sigma1sigma2_second);;
Print("  pi(id) = ", pi_id, "\n");
Print("  pi(z) = ", pi_minus, "\n");
Print("  pi(sigma2_canon) = ", pi_sigma2_canon, "\n");
Print("  pi(sigma2_second) = ", pi_sigma2_second, "\n");
Print("  pi(sigma1sigma2_canon) = ", pi_sigma1sigma2_canon, "\n");

# Eval rho(x) for rho in Irr(E_+(7)) at x in G.
# rho_index in [1..16384]: 1-dim irrep indexed by v_index (1-based).
# rho_index = 16385: the dim-128 faithful irrep.
EvalIrr_Eplus7 := function(rho_index, x_pi, x_is_central, x_is_identity)
    local v;
    if rho_index <= 16384 then
        # 1-dim, v = bits of (rho_index - 1)
        v := List([0..13], k -> QuoInt(rho_index - 1, 2^k) mod 2);
        # chi_v(x) = (-1)^(v . x_pi mod 2)
        return (-1)^((v * x_pi) mod 2);
    else
        if x_is_identity then return 128;
        elif x_is_central then return -128;       # x = z
        else return 0;
        fi;
    fi;
end;;

# ---------------------------------------------------------------
# Closed-form S-blocks involving central index 1.
# ---------------------------------------------------------------
# For (rho, h, sigma) with rho ∈ Irr(E_+(7)), h non-central canonical,
# sigma ∈ Irr(C_G(h)):
#   S_((1, rho), (h, sigma)) = dim(sigma) / |C_G(h)| * conj(rho(h))
#   S_((-1, rho), (h, sigma)) = sigma(-1) / |C_G(h)| * conj(rho(h))

ComputeCentralBlock := function(central_g_pi, central_g_is_central,
                                 central_g_is_identity,
                                 data_h, h_eval_at_central)
    # Block size 16385 x N_h where N_h = |Irr(C_G(h))|.
    # Rows: rho_index = 1..16385 (Irr(E_+(7))).
    # Cols: sigma_index = 1..N_h.
    # central_g_pi: pi-image of g in E_+(7)/Z, used for evaluating rho(g).
    # central_g_is_central, central_g_is_identity: flags for the dim-128 evaluation.
    # data_h: centraliser data for h.
    # h_eval_at_central: evaluator for sigma at the central element.
    #   For (1, h) blocks: this is dim(sigma).
    #   For (-1, h) blocks: this is sigma(-1).
    local Ni, Nj, M, h_factor_per_sigma, k, l, denom, h_pi, rho_at_h_inv;
    Ni := 16385; Nj := Length(data_h.irreps);
    denom := Order(data_h.centraliser);
    # Pre-compute sigma(central_g_value) for each sigma:
    # h_factor_per_sigma[l] = sigma(central_g) for sigma the l-th irrep.
    h_factor_per_sigma := List([1..Nj], l -> h_eval_at_central(data_h, l));
    # Pre-compute rho(h)^* for each rho.
    h_pi := PiOfElement(data_h.rep);
    M := List([1..Ni], k -> List([1..Nj], l -> 0));
    for k in [1..Ni] do
        rho_at_h_inv := ComplexConjugate(EvalIrr_Eplus7(k, h_pi,
            data_h.rep = z, data_h.rep = One(G)));
        for l in [1..Nj] do
            M[k][l] := h_factor_per_sigma[l] * rho_at_h_inv / denom;
        od;
    od;
    return M;
end;;

# Evaluator for sigma at g_id (= dim sigma)
EvalSigmaAtId := function(data_h, l)
    return data_h.dims[l];
end;;

# Evaluator for sigma at z
EvalSigmaAtZ := function(data_h, l)
    # z is central in C_G(h); sigma(z) = epsilon * dim(sigma) for some
    # epsilon in {1, -1}.  Evaluate sigma at z.
    return EvalIrr(data_h, l, z);
end;;

# ---------------------------------------------------------------
# Driver: compute the canonical blocks
# ---------------------------------------------------------------

results := rec();

Print("\n--- Computing non-central x non-central canonical blocks ---\n");

# (sigma2/sigma2/diag): canonical (sigma2_canon, sigma2_canon)
t := Runtime();;
results.sigma2_sigma2_diag := ComputeNonCentralBlock(
    data_sigma2_canon, t_sigma2_canon,
    data_sigma2_canon, t_sigma2_canon);
Print("  sigma2/sigma2/diag: ", (Runtime()-t)/1000., " s\n");

# (sigma2/sigma2/off, commute): canonical (sigma2_canon, sigma2_second)
t := Runtime();;
results.sigma2_sigma2_off := ComputeNonCentralBlock(
    data_sigma2_canon, t_sigma2_canon,
    data_sigma2_second, t_sigma2_second);
Print("  sigma2/sigma2/off: ", (Runtime()-t)/1000., " s\n");

# (sigma2/sigma1sigma2/off): canonical (sigma2_canon, sigma1sigma2_second)
t := Runtime();;
results.sigma2_sigma1sigma2_off := ComputeNonCentralBlock(
    data_sigma2_canon, t_sigma2_canon,
    data_sigma1sigma2_second, t_sigma1sigma2_second);
Print("  sigma2/sigma1sigma2/off: ", (Runtime()-t)/1000., " s\n");

# (sigma1sigma2/sigma1sigma2/diag)
t := Runtime();;
results.sigma1sigma2_sigma1sigma2_diag := ComputeNonCentralBlock(
    data_sigma1sigma2_canon, t_sigma1sigma2_canon,
    data_sigma1sigma2_canon, t_sigma1sigma2_canon);
Print("  sigma1sigma2/sigma1sigma2/diag: ", (Runtime()-t)/1000., " s\n");

# (sigma1sigma2/sigma1sigma2/off, commute)
t := Runtime();;
results.sigma1sigma2_sigma1sigma2_off := ComputeNonCentralBlock(
    data_sigma1sigma2_canon, t_sigma1sigma2_canon,
    data_sigma1sigma2_second, t_sigma1sigma2_second);
Print("  sigma1sigma2/sigma1sigma2/off: ", (Runtime()-t)/1000., " s\n");

Print("\n--- Computing central x noncentral canonical blocks (closed-form) ---\n");
# (id/sigma2/off): canonical (id, sigma2_canon)
t := Runtime();;
results.id_sigma2_off := ComputeCentralBlock(
    pi_id, false, true, data_sigma2_canon, EvalSigmaAtId);
Print("  id/sigma2/off: ", (Runtime()-t)/1000., " s\n");

t := Runtime();;
results.id_sigma1sigma2_off := ComputeCentralBlock(
    pi_id, false, true, data_sigma1sigma2_canon, EvalSigmaAtId);
Print("  id/sigma1sigma2/off: ", (Runtime()-t)/1000., " s\n");

t := Runtime();;
results.minus_one_sigma2_off := ComputeCentralBlock(
    pi_minus, true, false, data_sigma2_canon, EvalSigmaAtZ);
Print("  minus_one/sigma2/off: ", (Runtime()-t)/1000., " s\n");

t := Runtime();;
results.minus_one_sigma1sigma2_off := ComputeCentralBlock(
    pi_minus, true, false, data_sigma1sigma2_canon, EvalSigmaAtZ);
Print("  minus_one/sigma1sigma2/off: ", (Runtime()-t)/1000., " s\n");

# Save
outdir := "../computed/E_plus_7/structural";;
Exec(Concatenation("mkdir -p ", outdir));;
PrintTo(Concatenation(outdir, "/canonical_blocks.g"),
    "# E_+(7) canonical S-blocks (subset; central x central blocks omitted)\n",
    "canonical_blocks := ", results, ";;\n");

Print("\nWrote ", outdir, "/canonical_blocks.g\n");

# Print sizes
Print("\n--- Canonical block sizes ---\n");
for k in RecNames(results) do
    Print("  ", k, ": ", Length(results.(k)), " x ",
          Length(results.(k)[1]), "\n");
od;

QUIT;
