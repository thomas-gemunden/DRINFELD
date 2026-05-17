# test_b2_4_m3_anchor.g — Q-int B2-4 m=3 anchor (issue #164).
#
# Verifies that the Z/4 3-cocycle produced by the Pontryagin→integration
# pipeline (B3-2 #171 / B3-3 #172) on E_+(3) represents the SAME class
# in H^3(E_+(3); Z/4) as HAP's omega_4 generator (the Z/4 summand of
# H^3 = (Z/2)^34 ⊕ Z/4), up to a Z/4 unit.
#
# # Pipeline.
#
# 1. G := pc-form of E_+(3) = Image(IsomorphismPcGroup(EmGroup(3))).
# 2. R := HAP_PontryaginGetResolution(G, 5) (= ResolutionFiniteGroup(G, 6)).
# 3. Build omega_4 := HAP_Z4Generator(G).vec, a Z/4-valued 3-cocycle on R.
# 4. Enumerate F_2 2-cocycles alpha on R with sparse support; for each,
#    compute P(alpha) and check Stage A solvability of
#    HAP_IntegrateToZ4Cocycle (i.e. β_4([P(alpha)]) = 0 in H^5(G; Z)).
# 5. For the first valid alpha: compute f := result.f, a Z/4 3-cocycle.
# 6. Class-equality test: solve δh = c·f - omega_4 over Z/4 for
#    c ∈ {1, 2, 3}. If any c works, [c·f] = [omega_4] in H^3(G; Z/4).
#
# # Z/4 unit ambiguity.
#
# omega_4 is *a* generator of the Z/4 summand; (- omega_4 = 3·omega_4)
# is another. Pontryagin → integration may land on c·omega_4 for some
# c ∈ {1, 2, 3} (c=0 would mean f is a coboundary — non-triviality test
# guards against this). Testing c ∈ {1, 2, 3} covers all options:
#   - c ∈ {1, 3}: f generates the same Z/4 cyclic subgroup as omega_4.
#   - c = 2:      f generates the order-2 subgroup ⟨2·omega_4⟩ ≅ Z/2.
#
# # Wall-time.
#
# HAP setup at E_+(3) is the main cost: ~10-15 min for
# ResolutionFiniteGroup(G, 6) + ~1-2 min for Δ/h_1 build. Subsequent
# Pontryagin square + integration runs in ~minutes on R-sized linear
# systems.

BreakOnError := false;;
LoadPackage("hap");

# Layered loads: anchor everything off the R-resolution / UCT helpers.
Read("hap_pontryagin_square.g");
Read("hap_integrate_to_z4_cocycle.g");
Read("hap_h3_z4_generator.g");
Read("em_construction.g");

Print("\n=== test_b2_4_m3_anchor.g (issue #164) ===\n");

testFailures := [];;
If_loc := function(c, a, b) if c then return a; else return b; fi; end;;
AssertOrLog := function(label, cond)
    Print("  ", label, ": ", If_loc(cond, "PASS", "FAIL"), "\n");
    if not cond then Add(testFailures, label); fi;
end;;

t_total_start := Runtime();;

# ------------------------------------------------------------------
# Setup: build G = pc-form of E_+(3), then R, K, UCT.
# ------------------------------------------------------------------

Print("\n--- Setup: G = pc-form of E_+(3) ---\n");
t0 := Runtime();;
em_mat := EmGroup(3);;
iso_em := IsomorphismPcGroup(em_mat);;
G := Image(iso_em);;
Print("  |G| = ", Order(G), " (expected 128)\n");
Print("  G is pc: ", IsPcGroup(G), "\n");
AssertOrLog("G = E_+(3) has order 128", Order(G) = 128);

# ------------------------------------------------------------------
# Build R via HAP_PontryaginGetResolution (the EXPENSIVE step).
# ------------------------------------------------------------------

Print("\n--- Build R = HAP_PontryaginGetResolution(G, 5) ---\n");
Print("  (this calls ResolutionFiniteGroup(G, 6) + Δ + h_1)\n");
t1 := Runtime();;
R := HAP_PontryaginGetResolution(G, 5);;
wall_R := (Runtime() - t1) / 1000.;;
Print("  R build wall: ", wall_R, " s\n");
Print("  R characteristic: ", EvaluateProperty(R, "characteristic"), "\n");
Print("  R!.dimension(d) for d=0..5: ",
      List([0..5], d -> R!.dimension(d)), "\n");

AssertOrLog("R has characteristic 0", EvaluateProperty(R, "characteristic") = 0);

dim2 := R!.dimension(2);;
dim3 := R!.dimension(3);;
dim4 := R!.dimension(4);;
dim5 := R!.dimension(5);;
Print("  dim2 = ", dim2, ", dim3 = ", dim3,
      ", dim4 = ", dim4, ", dim5 = ", dim5, "\n");

# ------------------------------------------------------------------
# Build omega_4 via UCT on the SAME R.
# ------------------------------------------------------------------

Print("\n--- Build omega_4 = Z/4 generator of H^3(G; Z/4) ---\n");
t2 := Runtime();;
omega_4_data := HAP_Z4Generator(G);;
wall_omega := (Runtime() - t2) / 1000.;;
Print("  omega_4 build wall: ", wall_omega, " s\n");

omega_4 := omega_4_data.vec;;
m_exp   := omega_4_data.exponent;;
Print("  exponent (lcm of torsion) = ", m_exp, "\n");
Print("  torsion = ", omega_4_data.torsion, "\n");
Print("  idx (selected gen) = ", omega_4_data.idx, "\n");
Print("  order at idx = ", omega_4_data.order, "\n");
Print("  |omega_4| = ", Length(omega_4),
      " (= R!.dimension(3) = ", dim3, ")\n");
Print("  omega_4 entries in [0..", m_exp - 1, "] : ",
      ForAll(omega_4, x -> x >= 0 and x < m_exp), "\n");

# At E_+(3) we expect torsion = [2,...,2,4] (34 twos + one 4),
# exponent = 4, order at last idx = 4.
AssertOrLog("UCT.exponent = 4 (H^3 exponent at E_+(3))", m_exp = 4);
AssertOrLog("order at selected idx = 4",  omega_4_data.order = 4);
AssertOrLog("|omega_4| = R!.dimension(3)", Length(omega_4) = dim3);
AssertOrLog(Concatenation("omega_4 is a Z/", String(m_exp),
                          " cocycle on R"),
            omega_4_data.is_cocycle);

# Defensive: explicit re-check that omega_4 is a Z/4 cocycle on R.
d_omega := HAP_BarCoboundary(R, omega_4, 3);;
omega_viol := Length(Filtered(d_omega, x -> x mod 4 <> 0));;
Print("  omega_4 explicit recheck: δ(omega_4) mod 4 violations = ",
      omega_viol, " / ", dim4, "\n");
AssertOrLog("δ(omega_4) ≡ 0 mod 4 (explicit recheck)",
            omega_viol = 0);

# Non-triviality of omega_4 itself: should be non-zero entries.
AssertOrLog("omega_4 is not identically zero",
            not ForAll(omega_4, x -> x = 0));

# ------------------------------------------------------------------
# Enumerate F_2 2-cocycles α; find one with β_4([P(α)]) = 0.
#
# Strategy:
#   1. Compute the F_2 cocycle space Z^2(R; F_2) as
#      ker(M_2 mod 2) in F_2^dim2 (basis as F_2-row vectors).
#   2. Enumerate elements of Z^2 by HAMMING WEIGHT in the basis-vector
#      coordinates: weight-1 basis vectors first, then weight-2 sums,
#      etc.  Up to a budget cap.
#   3. For each F_2 cocycle α, compute P(α) and check Stage A
#      solvability of HAP_IntegrateToZ4Cocycle — i.e. that
#      [δ(F_int)/4] is the zero class in H^5(G; Z) (so the integer
#      Bockstein β_4([P(α)]) vanishes).
# Stop at first success.
#
# Tradeoff: enumerating in the cocycle basis (vs. all of F_2^dim2)
# saves a factor ~ 2^{rk(δ_2)} but still skips F_2-coboundaries (which
# are also F_2-cocycles, so we'd be testing some classes redundantly —
# acceptable since we just want ANY success).
# ------------------------------------------------------------------

Print("\n--- Enumerate F_2 2-cocycles; pick first with β_4([P(α)]) = 0 ---\n");

# Build M_4 once for the Stage A check (cached internally by HAP_BoundaryMatrixZ).
t3 := Runtime();;
M_4_check := HAP_BoundaryMatrixZ(R, 4);;
Print("  M_4 build wall: ", (Runtime() - t3) / 1000., " s\n");
Print("  M_4 shape: ", Length(M_4_check), " x ", Length(M_4_check[1]), "\n");

# Pre-transpose M_4 once for the SolutionIntMat calls.
t3b := Runtime();;
M_4_T := TransposedMat(M_4_check);;
Print("  TransposedMat(M_4) wall: ", (Runtime() - t3b) / 1000., " s\n");
Print("  M_4^T shape: ", Length(M_4_T), " x ", Length(M_4_T[1]), "\n");

# Compute the F_2 cocycle space Z^2(R; F_2) basis.
# δ: C^2 → C^3 has matrix HAP_BoundaryMatrixZ(R, 2) of shape dim3 × dim2
# (column-vec convention: δα = M_2 · α). So Z^2 = ker(M_2 mod 2). In
# GAP row-vector form: Z^2 = NullspaceMat(TransposedMat(M_2 mod 2)).
t3c := Runtime();;
M_2_for_Z2 := HAP_BoundaryMatrixZ(R, 2);;  # shape dim3 × dim2
M_2_F2 := List(M_2_for_Z2,
               row -> List(row, x -> (x mod 2) * Z(2)^0));;  # F_2 cast
Z2_basis_F2 := NullspaceMat(TransposedMat(M_2_F2));;
n_Z2 := Length(Z2_basis_F2);;
Print("  Z^2(R; F_2) basis: ", n_Z2, " vectors in F_2^", dim2,
      " (cocycle rank)\n");
Print("  cocycle space build wall: ", (Runtime() - t3c) / 1000., " s\n");

# Cast Z2 basis to integer {0,1} for convenience.
Z2_basis_int := [];;
for v_f2 in Z2_basis_F2 do
    Add(Z2_basis_int, List(v_f2,
        x -> If_loc(x = 0 * Z(2), 0, 1)));
od;;

# Sanity: each basis vector is in fact a cocycle.
for v_f2 in Z2_basis_int do
    if not ForAll(HAP_BarCoboundary(R, v_f2, 2), x -> x mod 2 = 0) then
        Error("Z2 basis vector is not an F_2 cocycle on R — bug");
    fi;
od;

# Safety cap on candidates tried. Each candidate costs one
# HAP_PontryaginSquare (sub-second after Δ, h_1 are cached) plus one
# SolutionIntMat on M_4_T (shape dim4+dim5 × dim4). For E_+(3) we
# expect dim4, dim5 in the tens, so SolutionIntMat is sub-second.
# 5000 should fit comfortably in 5 minutes.
MAX_CANDIDATES := 5000;;

alpha_F2 := fail;;
alpha_int := fail;;
PQ := fail;;
n_F2_cocycles := 0;;
n_bockstein_zero := 0;;
n_candidates_tried := 0;;

t_enum_start := Runtime();;

# Enumerate by Hamming weight in Z2 basis coordinates.
# weight w: Binomial(n_Z2, w) candidates per weight.
weight := 0;;
while alpha_F2 = fail and weight < n_Z2 and n_candidates_tried < MAX_CANDIDATES do
    weight := weight + 1;
    if Binomial(n_Z2, weight) + n_candidates_tried > MAX_CANDIDATES then
        Print("  weight ", weight, " in Z2 basis: Binomial(", n_Z2, ", ",
              weight, ") = ", Binomial(n_Z2, weight),
              " > remaining budget (",
              MAX_CANDIDATES - n_candidates_tried,
              "); stopping enumeration.\n");
        break;
    fi;
    Print("  weight ", weight, " in Z2 basis: testing ",
          Binomial(n_Z2, weight), " candidates...\n");
    for support in Combinations([1..n_Z2], weight) do
        if alpha_F2 <> fail then break; fi;
        n_candidates_tried := n_candidates_tried + 1;
        # Build F_2 cocycle as sum of basis vectors (mod 2).
        v := ListWithIdenticalEntries(dim2, 0);
        for i in support do
            for j in [1..dim2] do
                v[j] := (v[j] + Z2_basis_int[i][j]) mod 2;
            od;
        od;
        # Skip the zero vector.
        if ForAll(v, x -> x = 0) then continue; fi;
        # Should be a cocycle by construction. Defensive check:
        if not ForAll(HAP_BarCoboundary(R, v, 2), x -> x mod 2 = 0) then
            continue;  # bug — shouldn't happen
        fi;
        n_F2_cocycles := n_F2_cocycles + 1;
        # Build F_2 cocycle vector + compute P(alpha).
        aF2_cand := List(v, x -> If_loc(x = 0, 0 * Z(2), Z(2)^0));
        P_cand := HAP_PontryaginSquare(G, aF2_cand, 2);
        dP_cand := M_4_check * P_cand;
        # Stage A precondition: dP_cand ∈ 4Z componentwise.
        if not ForAll(dP_cand, x -> x mod 4 = 0) then
            continue;  # P(alpha) is not a Z/4 cocycle — bug.
        fi;
        dP_div4 := List(dP_cand, x -> x / 4);
        # Stage A solve.
        sol_cand := SolutionIntMat(M_4_T, dP_div4);
        if sol_cand <> fail then
            n_bockstein_zero := n_bockstein_zero + 1;
            alpha_F2 := aF2_cand;
            alpha_int := v;
            PQ := P_cand;
            Print("  FOUND at weight ", weight,
                  " in Z2 basis, support ", support, "\n");
            break;
        fi;
    od;
od;

wall_enum := (Runtime() - t_enum_start) / 1000.;;
Print("  enumeration wall: ", wall_enum, " s\n");
Print("  candidates tried: ", n_candidates_tried, "\n");
Print("  F_2 cocycles found: ", n_F2_cocycles, "\n");
Print("  with β_4([P(α)]) = 0: ", n_bockstein_zero, "\n");

if alpha_F2 = fail then
    AssertOrLog("setup: F_2 2-cocycle with vanishing β_4 found", false);
    Print("\n=== Summary ===\n");
    Print("test_b2_4_m3_anchor: FAIL (enumeration exhausted without ",
          "finding a valid α)\n");
    QUIT;
fi;

Print("  selected α_int = ", alpha_int, "\n");
Print("  selected P(α)  = ", PQ, "\n");
AssertOrLog("setup: F_2 2-cocycle with β_4([P(α)]) = 0 found", true);

# Sanity precondition: P(α) is a Z/4 4-cocycle on R.
dPQ_check := HAP_BarCoboundary(R, PQ, 4);;
AssertOrLog("precondition: P(α) is a Z/4 4-cocycle on R",
            ForAll(dPQ_check, x -> x mod 4 = 0));

# ------------------------------------------------------------------
# Run the integration: f := HAP_IntegrateToZ4Cocycle(R, P(α), 2).f.
# ------------------------------------------------------------------

Print("\n--- Run HAP_IntegrateToZ4Cocycle(R, P(α), 2) ---\n");
t4 := Runtime();;
result := HAP_IntegrateToZ4Cocycle(R, PQ, 2);;
wall_integrate := (Runtime() - t4) / 1000.;;
Print("  integration wall: ", wall_integrate, " s\n");

f := result.f;;
Print("  |f|   = ", Length(f), "\n");
Print("  f values distinct = ", Set(f), "\n");

AssertOrLog("f has length R!.dimension(3)", Length(f) = dim3);
AssertOrLog("f entries in {0, 1, 2, 3}",
            ForAll(f, x -> x in [0, 1, 2, 3]));

# Defensive: f is a Z/4 cocycle on R.
df_int := HAP_BarCoboundary(R, f, 3);;
viol_f := Length(Filtered(df_int, x -> x mod 4 <> 0));;
Print("  δ(f) mod 4 violations: ", viol_f, " / ", dim4, "\n");
AssertOrLog("δ(f) ≡ 0 mod 4 on R", viol_f = 0);
AssertOrLog("f is not identically zero",
            not ForAll(f, x -> x = 0));

# ------------------------------------------------------------------
# Class equality: is [c·f] = [omega_4] in H^3(G; Z/4) for some
# c ∈ {1, 2, 3}? Solve δh = c·f - omega_4 mod 4.
#
# Concrete linear system over Z:
#   M_2 · h - 4·k = c·f - omega_4
# i.e. find (h, k) integer vectors of lengths dim2, dim3 with
#   [M_2 | -4·I_{dim3}] · [h; k]^T = c·f - omega_4
#
# In GAP row-vector convention with SolutionIntMat(A^T, b):
#   x · TransposedMat([M_2 | -4·I]) = c·f - omega_4
# where x = [h; k].
# ------------------------------------------------------------------

Print("\n--- Class equality: solve δh ≡ c·f - omega_4 mod 4 ---\n");

t5 := Runtime();;
M_2 := HAP_BoundaryMatrixZ(R, 2);;
Print("  M_2 build wall: ", (Runtime() - t5) / 1000., " s\n");
Print("  M_2 shape: ", Length(M_2), " x ", Length(M_2[1]), "\n");

# Augment with -4·I_{dim3} on the right: [M_2 | -4·I_{dim3}], shape
# dim3 × (dim2 + dim3).
t5b := Runtime();;
A_aug := List([1..dim3], k -> Concatenation(
    M_2[k],
    List([1..dim3], j -> If_loc(j = k, -4, 0))));;
A_aug_T := TransposedMat(A_aug);;
Print("  Augment + transpose wall: ", (Runtime() - t5b) / 1000., " s\n");
Print("  A_aug shape: ", Length(A_aug), " x ", Length(A_aug[1]), "\n");
Print("  A_aug^T shape: ", Length(A_aug_T), " x ",
      Length(A_aug_T[1]), "\n");

found_c := 0;;
sol_h_for_c := fail;;
sol_k_for_c := fail;;
for c in [1, 2, 3] do
    Print("  trying c = ", c, "...\n");
    target := List([1..dim3], i -> c * f[i] - omega_4[i]);
    t_solve := Runtime();
    sol := SolutionIntMat(A_aug_T, target);
    Print("    SolutionIntMat wall: ", (Runtime() - t_solve) / 1000., " s\n");
    if sol <> fail then
        # Verify the solution.
        h_part := sol{[1..dim2]};
        k_part := sol{[dim2+1..dim2+dim3]};
        # Check A_aug · [h; k] = target.
        lhs := List([1..dim3], i -> 0);
        for i in [1..dim3] do
            row_sum := 0;
            for j in [1..dim2] do
                row_sum := row_sum + M_2[i][j] * h_part[j];
            od;
            lhs[i] := row_sum - 4 * k_part[i];
        od;
        if lhs = target then
            Print("    c = ", c, ": SOLVED. (verified A_aug * [h; k] = target)\n");
            Print("    |h| = ", Length(h_part), ", max|h| = ",
                  Maximum(List(h_part, AbsInt)), "\n");
            # Alternatively verify δh ≡ c·f - omega_4 mod 4.
            dh := M_2 * h_part;
            mod_match := true;
            for i in [1..dim3] do
                if (dh[i] - target[i]) mod 4 <> 0 then
                    mod_match := false;
                    break;
                fi;
            od;
            if mod_match then
                Print("    δh ≡ c·f - omega_4 mod 4: PASS\n");
                if found_c = 0 then
                    found_c := c;
                    sol_h_for_c := h_part;
                    sol_k_for_c := k_part;
                fi;
            else
                Print("    WARN: solution found but mod 4 mismatch — debug\n");
            fi;
        else
            Print("    WARN: SolutionIntMat returned a vector but ",
                  "A_aug * sol != target (debug)\n");
        fi;
    else
        Print("    c = ", c, ": SolutionIntMat returned fail\n");
    fi;
od;

Print("\n--- Class equality result ---\n");
Print("  found c = ", found_c, "\n");
if found_c = 0 then
    AssertOrLog("[c·f] = [omega_4] for some c ∈ {1, 2, 3}", false);
else
    AssertOrLog(Concatenation("[c·f] = [omega_4] for c = ",
                              String(found_c)),
                true);
    if found_c = 2 then
        Print("  NOTE: c = 2 means [f] generates only the order-2 ",
              "subgroup ⟨2·omega_4⟩ of H^3(G; Z/4).\n");
        Print("        Pontryagin → integration on this α landed on the ",
              "Z/2 sub-class, not the Z/4 generator.\n");
    elif found_c in [1, 3] then
        Print("  NOTE: c ∈ {1, 3} means [f] generates the SAME Z/4 ",
              "subgroup as omega_4 (up to a Z/4 unit).\n");
    fi;
fi;

# ------------------------------------------------------------------
# Wall-clock budget check.
# ------------------------------------------------------------------

wall_total := (Runtime() - t_total_start) / 1000.;;
Print("\n--- Total wall: ", wall_total, " s ---\n");
Print("  R build:        ", wall_R, " s\n");
Print("  omega_4 build:  ", wall_omega, " s\n");
Print("  enumeration:    ", wall_enum, " s\n");
Print("  integration:    ", wall_integrate, " s\n");

# The acceptance criterion is wall <= ~5 min after R is built, not
# counting R's own ~10-15 min. So we don't strictly fail on total wall.
# But we report it so callers can see if anything's off.

# ------------------------------------------------------------------
# Summary.
# ------------------------------------------------------------------

Print("\n=== Summary ===\n");
if IsEmpty(testFailures) then
    Print("test_b2_4_m3_anchor: ALL PASS\n");
else
    Print("test_b2_4_m3_anchor: FAIL (", Length(testFailures),
          " failures)\n");
    for f_msg in testFailures do
        Print("  - ", f_msg, "\n");
    od;
fi;
