# run_e_plus_m_kernel_quillen.g — Quillen-route driver: compute and persist
# ker(Tr) for E_+(m) via the Quillen / B3-chain resolution path.
#
# Issue #234 (Q-int B3-5: m=5 Z/4 unit generator via HAP-Pontryagin chain).
# Sibling of A-5b (#47) `run_e_plus_5_kernel.g`, which does the same
# computation on the HAP-route resolution.
#
# # Independence claim.
#
# A-5b anchors all per-class cocycle work on
#       R_A := ResolutionFiniteGroup(em, 4)
# via `SetupCohomology3(em)`. The Quillen-route driver here anchors on
#       R_B := ResolutionFiniteGroup(em, 6) = HAP_PontryaginGetResolution(em, 5)
# via `QuillenSetupOnR(m)` (issue #234 helper `quillen_z4_cocycle.g`). The
# two resolutions produce DIFFERENT presentations of H^3(em; U(1)) but
# the SAME abstract cohomology group (UCT.torsion is identical up to
# ordering). When both drivers' kernel computations agree on |ker Tr| +
# basis_summary (modulo basis-change), that's an independent cross-
# validation: a basis-change-invariant property.
#
# # F_2 + Z/4 verdicts at m=5.
#
# At E_+(5), H^3(em; U(1)) = (Z/2)^164 ⊕ Z/4 (k = 165 generators per
# Harada-Kono + Bockstein, see `quillen_h4_torsion.g`). For the 164
# Z/2 generators the per-class transgression check uses the standard
# Path A (mod-2 + Bockstein lift) inside `IsCoboundary2Split`. For the
# single Z/4 generator (idx = 165 by Smith-normal-form convention) the
# B3 chain provides a Z/4-valued 3-cocycle directly on R_B via
# `QuillenZ4Cocycle(m, 165)` — no integration round-trip needed at sweep
# time, because `UCT.cocyclebasis[165]` is already a Z/4 cocycle on R_B.
#
# # The "F_2 path that's already there" (per issue text).
#
# At m=5, the 164 F_2 generators are extracted via the SAME mechanism as
# the Z/4 generator — they are `UCT.cocyclebasis[1..164]` on R_B. The
# difference is in the SOLVER: order-2 generators take the mod-2 +
# Bockstein-image fast path (Path A in `IsCoboundary2Split`), while the
# order-4 generator takes the iterated-Bockstein Z/2^k path (Path Z).
# Both are dispatched automatically by `IsCoboundary2Split(C, c_g, vec,
# setup)` based on `vec[exp_index]`.
#
# # Output.
#
# Writes `computed/transgression/<m>/kernel_quillen.g` with the same
# schema as A-5b's `computed/transgression/<m>/kernel.g`:
#   group, id, torsion, exponent, kernel_size, kernel_vecs (or fail),
#   in_kernel_gens, exp_index, half_vec_in_kernel, basis_summary.
# Cross-validation: compare against A-5b's kernel.g (modulo basis change).
#
# # Wall budget.
#
# At m=5: dominated by `ResolutionFiniteGroup(em, 6)` (~10-15 min) +
# Δ / h_1 build (~few min) + 4 per-orbit cocycle-basis caches (~5-10 min
# each on |C| up to 2048). Per-generator sweep itself is sub-second per
# generator on the cached caches. Total: ≤ 1 day on a single CPU per spec.
#
# # Usage.
#
#   gap -q -b -c 'Read("run_e_plus_m_kernel_quillen.g");'
#
# Default m = 5. Set the global `M_QB35` before reading to override:
#
#   gap -q -b -c 'M_QB35 := 3; Read("run_e_plus_m_kernel_quillen.g");'
#
# from extraspecial_orbifolds/scripts/. The output dir is
# computed/transgression/<m>/.

# ----------------------------------------------------------------------
# Setup: load helpers + B3 chain + BRW.
# ----------------------------------------------------------------------

driver_orig_cwd_qb35 := DirectoryCurrent();;

# Cohomology + per-class basis helpers (HAP route on R_A — we'll override
# the setup below with QuillenSetupOnR but reuse BuildPerClassCocycleBasis).
Read("transgression_per_generator_brw.g");
# Resumable state (sweep_state.g format).
Read("transgression_resume.g");
# B3 chain: Pontryagin + integration + Z/4 generator helper.
Read("hap_pontryagin_square.g");
Read("hap_integrate_to_z4_cocycle.g");
Read("hap_h3_z4_generator.g");
# Quillen-route helpers (this issue #234).
Read("quillen_z4_cocycle.g");

# Restore CWD (Read above may have chdir'd via internal shim chains).
ChangeDirectoryCurrent(Filename(driver_orig_cwd_qb35, ""));;

# Local If_ ternary helper (some sibling drivers define this in
# transgression_per_generator_brw.g; ensure it's available here).
if not IsBound(If_) then
    If_ := function(cond, a, b)
        if cond then return a; else return b; fi;
    end;;
fi;

t_start_qb35 := Runtime();;

# Default m = 5 unless caller sets it.
if not IsBoundGlobal("M_QB35") then
    m := 5;;
else
    m := M_QB35;;
fi;

Print("\n=== Q-int B3-5 driver: ker(Tr) for E_+(", m,
      ") via the Quillen / B3-chain resolution ===\n");

# ----------------------------------------------------------------------
# Step 1: build BRW conjugacy + Quillen-route setup + BRW H^3 action.
#
# The conjugacy action is resolution-independent (it's defined on em
# itself, via class enumeration + BRW automorphism conjugation). We can
# reuse the same _brw_conjugacy_action_cache as A-5b — no harm done.
#
# The cohomology setup must be anchored on R_B (the B3-chain resolution).
# We use `QuillenSetupOnR(m)` from `quillen_z4_cocycle.g`. This produces
# a setup-shaped record compatible with `BuildPerClassCocycleBasis(...,
# setup)` and `H3MatrixOfAutomorphism(setup, phi)` from the existing
# A-5b machinery.
#
# The BRW H^3 action matrices need to be rebuilt on R_B (the A-5b cached
# action matrices are valid for R_A's hombasis, not R_B's). We use
# `H3MatrixOfAutomorphism` directly with our Quillen setup.
# ----------------------------------------------------------------------

Print("\n--- Step 1: BRW conjugacy + Quillen-route setup ---\n");

OutDir := Concatenation("../../computed/transgression/", String(m));;
Exec(Concatenation("mkdir -p ", OutDir));
StateFile := Concatenation(OutDir, "/sweep_state_quillen.g");;
Print("State file: ", StateFile, "\n");

t_brw := Runtime();;
Print("Building BRW conjugacy action for m = ", m, "...\n");
conj_action := BRWConjugacyAction(m);;
Print("BRW conjugacy wall: ", (Runtime() - t_brw) / 1000., " s\n");

G := conj_action.em;;
Print("|G| = ", Order(G), "  (expected 2^", 2*m+1, " = ", 2^(2*m+1), ")\n");

t_quil := Runtime();;
Print("Building Quillen-route setup on R_B = HAP_PontryaginGetResolution(em, 5)...\n");
Print("  (this calls ResolutionFiniteGroup(em, 6) + UCT — the expensive step)\n");
# IMPORTANT: pass conj_action.em as em_in so HAP_Z4Generator caches its
# R against the SAME group object the BRW conjugacy classes use. This
# ensures Centralizer(quil_setup.group, Representative(conj_action.classes[i]))
# works without parent-object mismatch.
quil_setup := QuillenSetupOnR(m, G);;
Print("Quillen-route setup wall: ", (Runtime() - t_quil) / 1000., " s\n");

# Belt-and-braces: assert quil_setup.group IS conj_action.em (object id).
Assert(0, IsIdenticalObj(quil_setup.group, G),
       "QuillenSetupOnR did not adopt the supplied em_in as .group");

torsion := quil_setup.torsion;;
exp := quil_setup.exponent;;
k := quil_setup.num_generators;;
Print("Quillen-route torsion = ", torsion, "\n");
Print("Quillen-route exponent = ", exp, "\n");
Print("Quillen-route k = ", k, " generators\n");

# Sanity: at m=5 we expect k = 165 (164 Z/2 + 1 Z/4 per Harada-Kono).
# At m=3 we expect k = 35 (34 Z/2 + 1 Z/4). The resolution differs from
# A-5b's R_A but the abstract group must match.
if m = 5 then
    Assert(0, k = 165,
           Concatenation("expected k = 165 at m=5; got ", String(k)));
    Assert(0, exp = 4,
           Concatenation("expected exponent = 4 at m=5; got ", String(exp)));
fi;
if m = 3 then
    Assert(0, k = 35,
           Concatenation("expected k = 35 at m=3; got ", String(k)));
fi;

sorted_torsion := ShallowCopy(torsion);;
Sort(sorted_torsion);;
Assert(0, ForAll(torsion, t -> IsInt(t) and t >= 2 and IsPrimePowerInt(t)
                              and SmallestRootInt(t) = 2),
       Concatenation("expected all torsion entries to be 2-powers; got ",
                     String(torsion)));

# Build BRW H^3 action matrices on the Quillen-route setup. This is one
# `H3MatrixOfAutomorphism` per BRW generator. At m=5 there are 4 BRW
# generators (per A-5b experience), so ~4 SolutionIntMat calls — cheap.
#
# IMPORTANT: H3MatrixOfAutomorphism needs phi : quil_setup.group ->
# quil_setup.group. We translate BRW matrix generators through
# IsomorphismPcGroup(EmGroup(m)) again to land in the quil_setup.group
# parent. This mirrors `ConjugationAutomorphismThroughIso` from
# brw_h3_action.g but with the Quillen-route group.
Print("\nBuilding BRW H^3 action matrices on Quillen-route setup...\n");
t_h3 := Runtime();;

ConjugationAutomorphismToQuilGroup := function(quil_group, quil_iso, y)
    local gens_pc, images_pc, phi;
    gens_pc := GeneratorsOfGroup(quil_group);
    images_pc := List(gens_pc, g_pc ->
        Image(quil_iso, y * PreImagesRepresentative(quil_iso, g_pc) * y^(-1)));
    phi := GroupHomomorphismByImages(quil_group, quil_group,
                                     gens_pc, images_pc);
    if phi = fail then
        Error("ConjugationAutomorphismToQuilGroup: y not an automorphism");
    fi;
    return phi;
end;;

brw_gens := conj_action.gens;;     # matrix BRW generators
# Use conj_action.iso_em (NOT quil_setup.iso_em, which is `fail` when we
# passed em_in to QuillenSetupOnR). Both refer to the same matrix->pc
# iso since quil_setup.group is identical to conj_action.em.
brw_iso_em := conj_action.iso_em;;
h3_matrices := [];;
for i_brw in [1..Length(brw_gens)] do
    y_brw := brw_gens[i_brw];
    phi_brw := ConjugationAutomorphismToQuilGroup(quil_setup.group,
                                                   brw_iso_em, y_brw);
    Print("  H3MatrixOfAutomorphism for BRW gen ", i_brw,
          " ... ");
    t_one := Runtime();
    M_y := H3MatrixOfAutomorphism(quil_setup, phi_brw);
    Add(h3_matrices, M_y);
    Print((Runtime() - t_one) / 1000., " s\n");
od;
Print("BRW H^3 action wall (Quillen-route): ",
      (Runtime() - t_h3) / 1000., " s\n");

perm_gens := conj_action.perms;;
Assert(0, Length(perm_gens) = Length(h3_matrices),
       "perm_gens / h3_matrices length mismatch");

classes := conj_action.classes;;
n_classes := Length(classes);;
Print("n_classes = ", n_classes, "\n");
Assert(0, n_classes >= 1,
       Concatenation("expected at least 1 conjugacy class; got ",
                     String(n_classes)));

# BFS-traverse class action under BRW perm_gens to identify orbits and
# Schreier vectors.
Print("Identifying BRW orbits + Schreier vectors over ", n_classes,
      " classes...\n");
visited_all := BlistList([1..n_classes], []);;
orbits_data := [];;
for start_idx in [1..n_classes] do
    if visited_all[start_idx] then continue; fi;
    sv := OrbitWithSchreierVec(perm_gens, n_classes, start_idx);
    for target_idx in sv.orbit do
        visited_all[target_idx] := true;
    od;
    Add(orbits_data, rec(start_idx := start_idx,
                          orbit := sv.orbit,
                          parent := sv.parent,
                          gen_used := sv.gen_used));
od;
Print("Found ", Length(orbits_data), " BRW orbits.\n");
for orb_info in orbits_data do
    Print("  orbit at class ", orb_info.start_idx, ": ",
          Length(orb_info.orbit),
          " members, |C_G(rep)| = ",
          Order(Centralizer(quil_setup.group,
                            Representative(classes[orb_info.start_idx]))), "\n");
od;

# Build per-orbit cocycle-basis caches on the Quillen-route setup. Same
# pattern as A-5b but anchored on R_B's cocyclebasis (length R_B!.dimension(3)).
# Identity-orbit short-circuit retained.
Print("Building per-orbit cocycle-basis caches on R_B...\n");
t_caches := Runtime();;
orbit_caches := [];;
for orb_info in orbits_data do
    rep := Representative(classes[orb_info.start_idx]);
    C := Centralizer(quil_setup.group, rep);
    Print("  orbit start ", orb_info.start_idx, " (|C| = ", Order(C),
          ", n*n*k = ", Order(C)^2 * k,
          ", rep order = ", Order(rep), ") ... ");
    t_one := Runtime();
    if IsOne(rep) then
        cache_elts := AsList(C);
        cache_n := Length(cache_elts);
        cache_table := List([1..cache_n * cache_n],
                            r -> List([1..k], i -> 0));
        cache_idx_map := NewDictionary(cache_elts[1], true, cache_elts);
        for cache_a in [1..cache_n] do
            AddDictionary(cache_idx_map, cache_elts[cache_a], cache_a);
        od;
        Add(orbit_caches, rec(C := C, table := cache_table,
                               elts := cache_elts, n := cache_n,
                               idx_map := cache_idx_map));
        Print((Runtime() - t_one) / 1000., " s (degenerate, identity class)\n");
    else
        Add(orbit_caches, BuildPerClassCocycleBasis(quil_setup, rep, C));
        Print((Runtime() - t_one) / 1000., " s\n");
    fi;
od;
Print("Per-orbit caches wall: ", (Runtime() - t_caches) / 1000., " s total\n");

# ----------------------------------------------------------------------
# Step 2: per-generator sweep using shared caches.
# Same algorithm as A-5b but on the Quillen-route setup. All 165
# generators (164 F_2 + 1 Z/4) get the same treatment — the dispatcher
# routes Z/2 vs Z/4 internally via `IsCoboundary2SplitVec`.
# ----------------------------------------------------------------------

Print("\n--- Step 2: per-generator sweep on Quillen-route R_B ---\n");

completed_idx := Set(LoadResumeState(StateFile), r -> r.generator);;
Print("\nAlready completed (resume): ", Length(completed_idx), " / ", k,
      "  ", completed_idx, "\n");

# Helper: BRW-amortised per-vec transgression check using cached caches.
# Adapted from `run_e_plus_5_kernel.g`'s PerVecTransgressionShared. The
# Path A precondition (every coord that's non-zero must have torsion in
# {2, exponent}) is the same here — at m >= 3 torsion = [2,...,2,4] so
# trivially true.
PerVecTransgressionShared := function(vec)
    local results, oi, orb_info, basis_cache, target_idx, vec_target,
          c_g_table, exp_index, r, exp, batch_inputs, batch_targets,
          c_prime_bits, batch_results, j, ti, one_gf2;
    results := List([1..n_classes], j -> "?");
    for ti in [1..Length(quil_setup.torsion)] do
        Assert(0, quil_setup.torsion[ti] = 2 or quil_setup.torsion[ti] = quil_setup.exponent,
               Concatenation("PerVecTransgressionShared: torsion[",
                             String(ti), "] = ", String(quil_setup.torsion[ti]),
                             " not in {2, exponent=", String(quil_setup.exponent),
                             "} — mixed sub-exp torsion not supported"));
    od;
    exp_index := Position(quil_setup.torsion, quil_setup.exponent);
    exp := quil_setup.exponent;
    r := exp / 2;
    one_gf2 := One(GF(2));
    for oi in [1..Length(orbits_data)] do
        orb_info := orbits_data[oi];
        basis_cache := orbit_caches[oi];
        batch_inputs := [];
        batch_targets := [];
        for target_idx in orb_info.orbit do
            vec_target := H3VecAtTarget(orb_info.start_idx, target_idx,
                                         orb_info.parent, orb_info.gen_used,
                                         h3_matrices, torsion, vec);
            c_g_table := basis_cache.table * vec_target;
            if exp_index <> fail and vec_target[exp_index] <> 0 then
                results[target_idx] :=
                    IsCoboundary2SplitVec(basis_cache.C, c_g_table, vec_target,
                                           quil_setup);
            else
                c_prime_bits := List(c_g_table,
                                     x -> ((((x mod exp) / r) mod 2)
                                           * one_gf2));
                ConvertToVectorRep(c_prime_bits, GF(2));
                Add(batch_inputs, c_prime_bits);
                Add(batch_targets, target_idx);
            fi;
        od;
        if not IsEmpty(batch_inputs) then
            batch_results := IsCoboundary2Mod2WithLiftVecBatch(
                basis_cache.C, batch_inputs);
            for j in [1..Length(batch_targets)] do
                results[batch_targets[j]] := batch_results[j];
            od;
        fi;
    od;
    return results;
end;;

# Sweep loop: all 165 unit generators at m=5 (or k at other m).
t_sweep := Runtime();;
for i in [1..k] do
    if i in completed_idx then
        Print("Skipping generator ", i, " (already done)\n");
        continue;
    fi;
    t_gen := Runtime();
    e_i := List([1..k], j -> 0);
    e_i[i] := 1;
    per_class := PerVecTransgressionShared(e_i);
    all_in_kernel := ForAll(per_class, x -> x = true);
    PersistGenerator(StateFile, i, all_in_kernel, per_class);
    Print("Computing generator ", i, "...",
          If_(i = Position(torsion, exp), " [Z/4 unit]", " [Z/2 unit]"), " ",
          If_(all_in_kernel, "IN", "NOT"), " kernel  (",
          (Runtime() - t_gen) / 1000., " s)\n");
od;
sweep_wall := (Runtime() - t_sweep) / 1000.;;
Print("Per-generator sweep wall (this invocation): ", sweep_wall, " s\n");

final_state := LoadResumeState(StateFile);;
in_kernel_gens := List(Filtered(final_state, r -> r.all_in_kernel),
                        r -> r.generator);;
Print("In-kernel unit generators: ", Length(in_kernel_gens), " / ", k, "\n");
Print("  indices: ", in_kernel_gens, "\n");

exp_index := Position(torsion, exp);;
Print("Order-", exp, " generator index: ", exp_index, "\n");

# ----------------------------------------------------------------------
# Step 3: half-vector check for the order-4 generator.
# ----------------------------------------------------------------------

Print("\n--- Step 3: half-vector check (2 * e_", exp_index, ") ---\n");
half_in_ker := fail;;
if exp_index in in_kernel_gens then
    half_in_ker := true;
    Print("e_", exp_index, " (order 4) is in ker; 2*e_", exp_index,
          " is therefore also in ker (trivially).\n");
else
    half_vec := List([1..k], j -> 0);
    half_vec[exp_index] := 2;
    Print("Testing 2 * e_", exp_index, " via Quillen-route BRW path...\n");
    t_half := Runtime();
    half_per_class := PerVecTransgressionShared(half_vec);
    half_wall := (Runtime() - t_half) / 1000.;
    Print("Half-vector test wall: ", half_wall, " s\n");
    half_in_ker := ForAll(half_per_class, x -> x = true);
    Print("2 * e_", exp_index, " in ker: ", half_in_ker, "\n");
    if not half_in_ker then
        Print("Witness classes (per_class = false): ",
              Filtered([1..Length(half_per_class)],
                       j -> half_per_class[j] = false), "\n");
    fi;
fi;

# ----------------------------------------------------------------------
# Step 4: assemble the kernel (same shape as A-5b's output).
# ----------------------------------------------------------------------

Print("\n--- Step 4: assemble kernel ---\n");

zero_vec := List(torsion, t -> 0);;

basis_vecs := [];;
basis_orders := [];;
for i in in_kernel_gens do
    e_i := List([1..k], j -> 0);
    e_i[i] := 1;
    Add(basis_vecs, e_i);
    Add(basis_orders, torsion[i]);
od;
if not (exp_index in in_kernel_gens) and half_in_ker = true then
    half_vec := List([1..k], j -> 0);
    half_vec[exp_index] := 2;
    Add(basis_vecs, half_vec);
    Add(basis_orders, 2);
fi;

kernel_size := Product(basis_orders);;
Print("Basis vectors: ", Length(basis_vecs), "\n");
Print("Basis orders:  ", basis_orders, "\n");
Print("|ker Tr|       ", kernel_size, "\n");

ReduceModTorsion := function(v, t)
    return List([1..Length(v)], j -> v[j] mod t[j]);
end;;

KernelVecFromCoeffs := function(coeffs)
    local v, t;
    v := ShallowCopy(zero_vec);
    for t in [1..Length(basis_vecs)] do
        v := v + coeffs[t] * basis_vecs[t];
    od;
    return ReduceModTorsion(v, torsion);
end;;

ENUM_LIMIT := 2^16;;
kernel_vecs := fail;;
if kernel_size <= ENUM_LIMIT then
    kernel_vecs := [];
    if IsEmpty(basis_vecs) then
        Add(kernel_vecs, zero_vec);
    else
        for coeffs in Cartesian(List(basis_orders, o -> [0..o-1])) do
            Add(kernel_vecs, KernelVecFromCoeffs(coeffs));
        od;
    fi;
    kernel_vecs := Set(kernel_vecs);
    Assert(0, Length(kernel_vecs) = kernel_size,
           Concatenation("kernel enumeration size ",
                         String(Length(kernel_vecs)),
                         " disagrees with basis-product ",
                         String(kernel_size)));
    Print("Full kernel enumerated (", Length(kernel_vecs), " vecs).\n");
else
    Print("Kernel too large to enumerate explicitly (", kernel_size,
          " > ", ENUM_LIMIT, "); persisting structurally only.\n");
fi;

# ----------------------------------------------------------------------
# Step 5: deterministic-stride cross-check.
# ----------------------------------------------------------------------

Print("\n--- Step 5: deterministic-stride cross-check ---\n");

TestVecAllClasses := function(vec)
    local per_class, j;
    per_class := PerVecTransgressionShared(vec);
    for j in [1..n_classes] do
        if per_class[j] = false then
            return rec(in_kernel := false, witness_class := j);
        fi;
    od;
    return rec(in_kernel := true, witness_class := fail);
end;;

DecodeCoeffs := function(n)
    local coeffs, t;
    coeffs := List(basis_orders, o -> 0);
    if IsEmpty(basis_orders) then return coeffs; fi;
    for t in [Length(basis_orders), Length(basis_orders) - 1 .. 1] do
        coeffs[t] := n mod basis_orders[t];
        n := QuoInt(n, basis_orders[t]);
    od;
    return coeffs;
end;;

sample_size := Minimum(100, kernel_size);;
random_kernel_sample := [];;
if Length(basis_vecs) = 0 then
    Add(random_kernel_sample, zero_vec);
else
    stride := QuoInt(kernel_size, sample_size);
    if stride < 1 then stride := 1; fi;
    for s in [0..sample_size - 1] do
        encoded := (s * stride) mod kernel_size;
        Add(random_kernel_sample, KernelVecFromCoeffs(DecodeCoeffs(encoded)));
    od;
fi;

t_check_k := Runtime();;
kernel_ok := true;;
kernel_failures := [];;
for v in random_kernel_sample do
    r := TestVecAllClasses(v);
    if not r.in_kernel then
        kernel_ok := false;
        Add(kernel_failures, rec(vec := v, witness := r.witness_class));
    fi;
od;
Print("Kernel-sample cross-check: ", sample_size, " vecs, all in ker: ",
      kernel_ok, " (", (Runtime() - t_check_k) / 1000., " s)\n");
if not IsEmpty(kernel_failures) then
    Print("FAILURES (first 5): ",
          kernel_failures{[1..Minimum(5, Length(kernel_failures))]}, "\n");
fi;
Assert(0, kernel_ok,
       "Random kernel sample failed: some vec we claim is in ker is detected by some class");

not_in_ker_indices := Difference([1..k], in_kernel_gens);;
non_ker_ok := true;;
non_ker_failures := [];;
if IsEmpty(not_in_ker_indices) then
    Print("All ", k, " unit gens in ker; skip non-ker sample.\n");
else
    Print("Non-ker base indices (first 10 of ", Length(not_in_ker_indices),
          "): ",
          not_in_ker_indices{[1..Minimum(10, Length(not_in_ker_indices))]},
          "\n");
    sample_size_nk := Minimum(100, kernel_size * Length(not_in_ker_indices));;
    t_check_nk := Runtime();;
    stride_k := Maximum(1, QuoInt(kernel_size, sample_size_nk));;
    for s in [0..sample_size_nk - 1] do
        encoded := (s * stride_k) mod kernel_size;
        if Length(basis_vecs) = 0 then
            v := ShallowCopy(zero_vec);
        else
            v := KernelVecFromCoeffs(DecodeCoeffs(encoded));
        fi;
        idx_nk := not_in_ker_indices[(s mod Length(not_in_ker_indices)) + 1];
        v[idx_nk] := (v[idx_nk] + 1) mod torsion[idx_nk];
        v := ReduceModTorsion(v, torsion);
        r := TestVecAllClasses(v);
        if r.in_kernel then
            non_ker_ok := false;
            Add(non_ker_failures, rec(vec := v));
        fi;
    od;
    Print("Non-ker-sample cross-check: ", sample_size_nk,
          " vecs, none in ker: ", non_ker_ok,
          " (", (Runtime() - t_check_nk) / 1000., " s)\n");
    if not IsEmpty(non_ker_failures) then
        Print("UNEXPECTED IN-KER (first 5): ",
              non_ker_failures{[1..Minimum(5, Length(non_ker_failures))]}, "\n");
    fi;
fi;

# ----------------------------------------------------------------------
# Step 6: persist to computed/transgression/<m>/kernel_quillen.g
# ----------------------------------------------------------------------

OutPath := Concatenation(OutDir, "/kernel_quillen.g");;
Print("\n--- Step 6: persist to ", OutPath, " ---\n");

basis_summary := [];;
for i in in_kernel_gens do
    Add(basis_summary, rec(vec := basis_vecs[Position(in_kernel_gens, i)],
                            order := torsion[i],
                            kind := Concatenation("e_", String(i)),
                            generator_index := i));
od;
if not (exp_index in in_kernel_gens) and half_in_ker = true then
    Add(basis_summary, rec(vec := basis_vecs[Length(basis_vecs)],
                            order := 2,
                            kind := Concatenation("2 * e_", String(exp_index)),
                            generator_index := exp_index));
fi;

# Group id: at m=5, E_+(5) is not in SmallGroup library (order 2048 > 2000).
# At m=3, E_+(3) = SmallGroup(128, 2326). For m=1, 2, 3 we can record id;
# at m=5 use fail.
group_id := fail;;
if Order(G) <= 2000 then
    group_id := IdSmallGroup(G);
fi;

kernel_out_stream := OutputTextFile(OutPath, false);;
SetPrintFormattingStatus(kernel_out_stream, false);
PrintTo(kernel_out_stream,
    "# ker(Tr : H^3(E_+(", String(m), "); U(1)) -> ⊕_g H^2(C_g; U(1)))\n",
    "# QUILLEN-ROUTE WITNESS (issue #234, Q-int B3-5).\n",
    "#\n",
    "# Generated by extraspecial_orbifolds/scripts/run_e_plus_m_kernel_quillen.g\n",
    "# (issue #234: m=", String(m), " Z/4 unit generator via HAP-Pontryagin chain).\n",
    "#\n",
    "# G = E_+(", String(m), "), |G| = 2^", String(2*m+1),
    " = ", String(Order(G)), ".\n",
    "# H^3(G; U(1)) torsion = ", String(torsion), ",\n",
    "# exponent = ", String(exp), ".\n",
    "# |H^3(G; U(1))| = ", String(Product(torsion)), "\n",
    "# |ker Tr|       = ", String(kernel_size), "\n",
    "#\n",
    "# Resolution anchor: R_B := ResolutionFiniteGroup(em, 6)\n",
    "#                  = HAP_PontryaginGetResolution(em, 5).\n",
    "# This is the B3-chain resolution (#170-#172), DIFFERENT from\n",
    "# A-5b's R_A := ResolutionFiniteGroup(em, 4) (issue #47). The two\n",
    "# resolutions present H^3 in different bases; cross-validation\n",
    "# of |ker Tr| and basis_summary against A-5b's kernel.g (modulo\n",
    "# basis change) is the independence claim.\n",
    "#\n",
    "# Method:\n",
    "#   * Per-generator BRW-amortised transgression sweep on R_B.\n",
    "#   * For the 164 Z/2 generators: dispatched to Path A (mod-2 +\n",
    "#     Bockstein-image lift) inside IsCoboundary2Split.\n",
    "#   * For the Z/4 generator (idx ", String(exp_index),
    "): dispatched to Path Z\n",
    "#     (iterated-Bockstein Z/2^k) inside IsCoboundary2Split.\n",
    "#   * Half-vector check for 2 * e_", String(exp_index),
    " when the Z/4 unit is\n",
    "#     not in ker.\n",
    "#\n",
    "# Format: same as A-5b's computed/transgression/<m>/kernel.g.\n",
    "#\n",
    "# Reload via:\n",
    "#   data := ReadAsFunction(\"kernel_quillen.g\")();\n",
    "\n",
    "local kernel_vecs;\n",
    "kernel_vecs := ", kernel_vecs, ";\n",
    "return rec(\n",
    "    group              := \"E_+(", String(m), ")\",\n",
    "    id                 := ", group_id, ",\n",
    "    route              := \"quillen-b3\",\n",
    "    resolution_anchor  := \"HAP_PontryaginGetResolution(em, 5)\",\n",
    "    torsion            := ", torsion, ",\n",
    "    exponent           := ", exp, ",\n",
    "    kernel_size        := ", kernel_size, ",\n",
    "    kernel_vecs        := kernel_vecs,\n",
    "    in_kernel_gens     := ", in_kernel_gens, ",\n",
    "    exp_index          := ", exp_index, ",\n",
    "    half_vec_in_kernel := ", half_in_ker, ",\n",
    "    basis_summary      := ", basis_summary, "\n",
    ");;\n");
CloseStream(kernel_out_stream);

Print("Wrote ", OutPath, "\n");

# ----------------------------------------------------------------------
# Step 7: summary.
# ----------------------------------------------------------------------

total_wall_qb35 := (Runtime() - t_start_qb35) / 1000.;;
Print("\n=== Q-int B3-5 driver: DONE ===\n");
Print("Total wall: ", total_wall_qb35, " s\n");
Print("|ker Tr|     = ", kernel_size, "\n");
Print("|H^3|        = ", Product(torsion), "\n");
Print("|coker Tr|   = ", Product(torsion) / kernel_size, "\n");
Print("In-ker gens: ", Length(in_kernel_gens), " / ", k, "\n");
Print("Half-vec 2 * e_", exp_index, " in ker: ", half_in_ker, "\n");
Print("Z/4 unit (idx ", exp_index, ") in ker: ",
      exp_index in in_kernel_gens, "\n");
Print("Sample cross-check: ker=", If_(kernel_ok, "PASS", "FAIL"),
      ", non-ker=", If_(non_ker_ok, "PASS", "WARN"), "\n");
Print("Output: ", OutPath, "\n");

QUIT;
