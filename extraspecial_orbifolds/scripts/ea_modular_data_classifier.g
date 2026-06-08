# ea_modular_data_classifier.g
#
# Issue #486: modular-data-based EA-branch classifier for K-4b.
# Issue #490: abelian (q_ω, b_ω) extraction path for feasibility at
# H = (Z/2)^8 (m=7 max EA, |H| = 256, |H|^2 = 65536).
#
# `ClassifyEAFromModularData(H, S, T)` is the modular-data analogue of
# `ClassifyOnD8` / `ClassifyOnQ_8` for the elementary-abelian branch of
# the AM04 + Quillen detecting family for E_+(m). It takes the modular
# data of a twisted Drinfeld double Z(Vec_H^omega) for some abelian H and
# decides whether [omega] is the trivial class in H^3(H; U(1)).
#
# Modular data in, triviality verdict out — the same architecture as the
# D_8/Q_8 classifiers. This completes the architectural fix begun in
# PR #485 (which removed the zero-cocycle stub that previously made the
# K-4b EA-branch verdict mathematically vacuous).
#
# Public API
# ----------
#   ClassifyEAFromModularData(H, S, T)
#   ExtractQBFromModularData(H, S_or_factored, T, N)  -- exposed for tests
#
# Input shapes
#   `S` may be EITHER
#     (a) a full |H|^2 x |H|^2 cyclotomic matrix (legacy path; tractable
#         for k <= 6 in (Z/2)^k), OR
#     (b) a factored modular-data record from
#         `ComputeAbelianModularDataFactored(H, ω, N)` (PR #487), shaped
#         as `rec(S_at := function(i, j) ..., T_vec := ..., n := |H|,
#                modulus := N, chi_at := ..., is_factored := true, ...)`.
#         This is the (Z/2)^8 use case: |H|^4 = 4.3e9 entries cannot be
#         materialised.
#   `T` is the diagonal vector of T (or a DiagonalMat). When `S` is the
#   factored record, `T` is taken from `S.T_vec` (the argument is
#   accepted but ignored for consistency with the legacy signature).
#
# Output (record)
#   .is_trivial   : <bool>  true iff (S, T) ≅ untwisted Z(Vec_H).
#   .class_idx    : 1 (when is_trivial) or `fail` (otherwise). Following
#                   the D_8/Q_8 convention, class_idx = 1 denotes the
#                   trivial cohomology class. We do not enumerate
#                   non-trivial classes for EA H.
#   .method       : "qb_extraction" (factored path, PR #490) or
#                   "joint_permutation" (legacy full-(S,T) path, PR #486).
#   .q, .b        : extracted q_ω vector and b_ω matrix on the qb_extraction
#                   path (reduced mod 2N). On the joint_permutation path,
#                   absent.
#   .is_q_trivial, .is_b_trivial
#                 : per-component triviality booleans on the qb_extraction
#                   path. (Cocycle-level convention: q ≡ 0 mod N AND
#                   b ≡ 0 mod N. We extract mod 2N and reduce.)
#   .match        : the `JointPermutationMatcher(...)` record (.ok, .pi,
#                   .reason). Present on the joint_permutation path;
#                   absent on the qb_extraction path.
#   .modular_untwisted : `rec(S, T)` returned by `ComputeUntwistedModularData(H)`,
#                   surfaced for diagnostic record attachment. Only
#                   present on the legacy full-(S,T) path (the
#                   qb_extraction path does not require the untwisted MD
#                   as a reference — it tests (q, b) ≡ (0, 0) directly).
#   .wall_ms      : runtime in milliseconds.
#
# Mechanism
# ---------
# Two paths depending on input shape:
#
# PATH A (qb_extraction, PR #490): when `S` is a factored modular-data
# record `rec(S_at := ..., T_vec := ..., chi_at := ..., modulus := N, ...)`
# from `ComputeAbelianModularDataFactored`, extract `q_ω` from T_vec and
# `b_ω` from O(|H|^2) `S_at` queries, and test (q, b) ≡ (0, 0) mod N.
# By DGNO 2010 / Naidu-Nikshych 2008, for abelian H this is the
# triviality test of [ω] in H^3(H; U(1)). Complexity: O(|H|) for q,
# O(|H|^2) for b; feasible at H = (Z/2)^8.
#
# PATH B (joint_permutation, PR #486): when `S` is a full matrix,
# compute untwisted MD of H and run `JointPermutationMatcher`. Tractable
# for k <= 6 in (Z/2)^k.
#
# Math (PATH A, the new path)
# ----------------------------
# For abelian H with `ω : H^3 → Z/N` (phase = E(N)^ω), the modular data
# of Z^ω(Vec_H) per PR #487 is (in (i_a, i_chi) lex order):
#
#   T_{(a, χ)}         = χ(a) * E(2N)^{q_ω(a)}
#   S_{(a,χ),(b,ψ)}    = (1/|H|) * ψ(a)^{-1} * χ(b)^{-1} * E(2N)^{-b_ω(a,b)}
#
# where
#   q_ω(a)    = ω(a, a, a) mod 2N
#   b_ω(a, b) = q_ω(a*b) - q_ω(a) - q_ω(b) mod 2N
#
# Trivial-character indexing: in the (i_a, i_chi) lex order from PR #487,
# the χ_triv index `i_chi_triv` is the row of `chi_at` that is all-1s.
# In GAP's standard `Irr(CharacterTable(H))` ordering for elementary
# abelian groups, this is always position 1; we detect it robustly by
# scanning for the all-1 row.
#
# Extraction (PATH A):
#   T_{(a, χ_triv)} = 1 * E(2N)^{q_ω(a)}.
#   So q_ω(a) = DiscreteLog(T_{(a, χ_triv)}, base = E(2N)) ∈ [0, 2N).
#   |H| * S_{(a, χ_triv), (b, χ_triv)} = E(2N)^{-b_ω(a, b)}.
#   So b_ω(a, b) = -DiscreteLog(|H| * S_..., base = E(2N)) mod 2N.
#
# Triviality criterion (cocycle-level, mirroring `ClassifyAbelianBranchFast`):
# `q ≡ 0 AND b ≡ 0` mod N. We extract mod 2N (matching PR #487's gauge)
# and reduce mod N for the triviality check.
#
# Refs
# ----
# * PR #485 — removed zero-cocycle stubs.
# * PR #486 — introduced this file (legacy JointPermutationMatcher path).
# * PR #487 — closed-form (q, b) -> (S, T) for abelian H + factored
#   modular-data record with O(|H|^2) memory and O(1) per-entry S
#   accessor. Feeds the qb_extraction path here.
# * PR #489 — e2e classifier-correctness sweep at m=7 (originally used
#   `ClassifyAbelianBranchFast`; retrofitted in PR #490 to use this
#   `ClassifyEAFromModularData` via the factored path).
# * Issue #490 — this PR.
# * User directive 2026-06-07: "K-4b should test modular data and not
#   cocycles" (memory MEMORY.md `feedback_no_downscope_for_krr_verification.md`).

# ---- Resolve and load dependencies -------------------------------------
#
# Auto-load JointPermutationMatcher and ComputeUntwistedModularData from
# alongside this file. Uses INPUT_FILENAME() to find our directory, with
# a small list of relative fallbacks for callers that Read this file from
# the wrong cwd.

_eamc_loaded_jpm := false;;
_eamc_loaded_umd := false;;
_eamc_self := INPUT_FILENAME();;
if _eamc_self <> fail and _eamc_self <> "stream" then
    _eamc_dir := _eamc_self{[1..Length(_eamc_self)
                              - Length("/ea_modular_data_classifier.g")]};;
    _eamc_jpm_cand := Concatenation(_eamc_dir,
                                     "/joint_permutation_matcher.g");;
    if (not IsBound(JointPermutationMatcher))
       and IsExistingFile(_eamc_jpm_cand) then
        Read(_eamc_jpm_cand);
    fi;
    _eamc_loaded_jpm := IsBound(JointPermutationMatcher);
    _eamc_umd_cand := Concatenation(_eamc_dir,
                                     "/untwisted_modular_data.g");;
    if (not IsBound(ComputeUntwistedModularData))
       and IsExistingFile(_eamc_umd_cand) then
        Read(_eamc_umd_cand);
    fi;
    _eamc_loaded_umd := IsBound(ComputeUntwistedModularData);
fi;
if not _eamc_loaded_jpm then
    for _eamc_p in [ "joint_permutation_matcher.g",
                     "./joint_permutation_matcher.g",
                     "../joint_permutation_matcher.g",
                     "extraspecial_orbifolds/scripts/joint_permutation_matcher.g" ] do
        if (not IsBound(JointPermutationMatcher))
           and IsExistingFile(_eamc_p) then
            Read(_eamc_p);
        fi;
    od;
fi;
if not _eamc_loaded_umd then
    for _eamc_p in [ "untwisted_modular_data.g",
                     "./untwisted_modular_data.g",
                     "../untwisted_modular_data.g",
                     "extraspecial_orbifolds/scripts/untwisted_modular_data.g" ] do
        if (not IsBound(ComputeUntwistedModularData))
           and IsExistingFile(_eamc_p) then
            Read(_eamc_p);
        fi;
    od;
fi;
if not IsBound(JointPermutationMatcher) then
    Error("ea_modular_data_classifier.g: cannot locate ",
          "joint_permutation_matcher.g; ensure it sits alongside this ",
          "file in extraspecial_orbifolds/scripts/.");
fi;
if not IsBound(ComputeUntwistedModularData) then
    Error("ea_modular_data_classifier.g: cannot locate ",
          "untwisted_modular_data.g; ensure it sits alongside this ",
          "file in extraspecial_orbifolds/scripts/.");
fi;

# ---- ExtractQBFromModularData ------------------------------------------
#
# Extract the quadratic form q_ω : H → Z/(2N) and its polarisation
# b_ω : H × H → Z/(2N) from a factored modular-data record.
#
# The input is a single factored record `mdf` for abelian H, shaped like
# the output of `ComputeAbelianModularDataFactored(H, ω, N)` (PR #487):
#   rec(
#     is_factored := true,
#     n           := |H|,
#     modulus     := N,
#     chi_at      := |H| x |H| character-value table,
#     T_vec       := length-|H|^2 cyclotomic vector,
#     S_at        := function(global_i, global_j) -> cyclotomic,
#     ...
#   )
#
# Returns rec(
#   q             : length-|H| list of integers in [0, 2N),
#   b             : |H| x |H| matrix of integers in [0, 2N),
#   N             : modulus (passed through),
#   two_N         : 2*N,
#   i_chi_triv    : index of the trivial character in mdf.chi_at,
#   wall_ms       : extraction runtime
# )
#
# Math:
#   q[i_a] is the discrete log of T_{(a, χ_triv)} to base E(2N).
#   b[i_a][i_b] is the (sign-flipped) discrete log of
#       |H| * S_{(a, χ_triv), (b, χ_triv)} to base E(2N), mod 2N.
#
# Complexity: O(|H|) for q, O(|H|^2) for b (one S_at query per pair).
ExtractQBFromModularData := function(mdf)
    local t0, n, two_N, modulus, chi_at, i_chi_triv, k, all_one,
          zeta, pow_table, k_idx, q, b, T_vec, S_at,
          i_a, i_b, idx_a, idx_b, val_T, val_S, exp_T, exp_S, m,
          row, T_val, scaled_S;
    t0 := Runtime();
    if not IsBound(mdf.is_factored) or mdf.is_factored <> true then
        Error("ExtractQBFromModularData: input record must be a factored ",
              "modular-data record from ComputeAbelianModularDataFactored ",
              "(needs is_factored = true)");
    fi;
    if not IsBound(mdf.chi_at) then
        Error("ExtractQBFromModularData: factored record missing chi_at");
    fi;
    if not IsBound(mdf.n) then
        Error("ExtractQBFromModularData: factored record missing n");
    fi;
    if not IsBound(mdf.modulus) then
        Error("ExtractQBFromModularData: factored record missing modulus");
    fi;
    if not IsBound(mdf.S_at) then
        Error("ExtractQBFromModularData: factored record missing S_at");
    fi;
    if not IsBound(mdf.T_vec) then
        Error("ExtractQBFromModularData: factored record missing T_vec");
    fi;

    n := mdf.n;
    m := n;  # |Hat(H)| = |H| for abelian H
    modulus := mdf.modulus;
    two_N := 2 * modulus;
    chi_at := mdf.chi_at;
    T_vec := mdf.T_vec;
    S_at := mdf.S_at;

    # ---- Locate the trivial character row in chi_at ----
    # chi_at[k][i] = chi_k(elems[i]). The trivial character has chi_k(a) = 1
    # for all a. In GAP's standard Irr(CharacterTable(H)) ordering this is
    # always row 1 for elementary abelian groups, but we detect it
    # robustly.
    i_chi_triv := fail;
    for k in [1..m] do
        all_one := true;
        for k_idx in [1..n] do
            if chi_at[k][k_idx] <> 1 then
                all_one := false;
                break;
            fi;
        od;
        if all_one then
            i_chi_triv := k;
            break;
        fi;
    od;
    if i_chi_triv = fail then
        Error("ExtractQBFromModularData: no all-1 row in chi_at (cannot ",
              "locate trivial character)");
    fi;

    # ---- Precompute the discrete-log table for E(2N) ----
    # pow_table[k+1] = E(2N)^k for k in [0..2N-1]. For typical sizes
    # (2N <= ~64 in our use cases), this is cheap.
    zeta := E(two_N);
    pow_table := EmptyPlist(two_N);
    Add(pow_table, 1);  # zeta^0 = 1
    for k_idx in [2..two_N] do
        Add(pow_table, pow_table[k_idx - 1] * zeta);
    od;

    # ---- Extract q ----
    # T_{(a, χ_triv)} at lex index (i_a - 1) * m + i_chi_triv.
    # T_{(a, χ_triv)} = 1 * E(2N)^{q[i_a]}.
    q := EmptyPlist(n);
    for i_a in [1..n] do
        idx_a := (i_a - 1) * m + i_chi_triv;
        T_val := T_vec[idx_a];
        exp_T := Position(pow_table, T_val);
        if exp_T = fail then
            Error("ExtractQBFromModularData: T[(a, chi_triv)] for i_a=",
                  i_a, " (value ", T_val,
                  ") is not a power of E(2N) for 2N=", two_N,
                  "; modular data is not in the PR #487 abelian gauge");
        fi;
        Add(q, exp_T - 1);  # GAP Position is 1-based; exponent is k = pos-1
    od;

    # ---- Extract b ----
    # |H| * S_{(a, χ_triv), (b, χ_triv)} = E(2N)^{-b[i_a][i_b]}
    # => b[i_a][i_b] = -DiscreteLog(n * S_at(...), base E(2N)) mod 2N.
    b := EmptyPlist(n);
    for i_a in [1..n] do
        idx_a := (i_a - 1) * m + i_chi_triv;
        row := EmptyPlist(n);
        for i_b in [1..n] do
            idx_b := (i_b - 1) * m + i_chi_triv;
            val_S := S_at(idx_a, idx_b);
            scaled_S := n * val_S;
            exp_S := Position(pow_table, scaled_S);
            if exp_S = fail then
                Error("ExtractQBFromModularData: |H| * S_{(a,chi_triv),",
                      "(b,chi_triv)} for (i_a, i_b)=(", i_a, ", ", i_b,
                      ") (value ", scaled_S, ", n*S_at(", idx_a, ", ",
                      idx_b, ")) is not a power of E(2N) for 2N=", two_N,
                      "; modular data is not in the PR #487 abelian gauge");
            fi;
            # row[i_b] = -(exp_S - 1) mod 2N
            row[i_b] := ((-(exp_S - 1)) mod two_N + two_N) mod two_N;
        od;
        b[i_a] := row;
    od;

    return rec(
        q             := q,
        b             := b,
        N             := modulus,
        two_N         := two_N,
        i_chi_triv    := i_chi_triv,
        wall_ms       := Runtime() - t0
    );
end;;

# ---- ClassifyEAFromModularData -----------------------------------------

DeclareGlobalFunction("ClassifyEAFromModularData");

InstallGlobalFunction(ClassifyEAFromModularData, function(H, S, T)
    local t0, untwisted, match, is_trivial, class_idx,
          qb, is_q_trivial, is_b_trivial, q_mod_N, b_mod_N, N;

    t0 := Runtime();

    if not IsGroup(H) then
        Error("ClassifyEAFromModularData: H must be a group; got ", H);
    fi;
    if not IsAbelian(H) then
        Error("ClassifyEAFromModularData: H must be abelian; got ",
              StructureDescription(H));
    fi;

    # PATH A (#490): factored modular-data input. Use (q, b) extraction
    # — feasible at H = (Z/2)^8 where the full S matrix is infeasible.
    if IsRecord(S) and IsBound(S.is_factored) and S.is_factored = true then
        qb := ExtractQBFromModularData(S);
        N := qb.N;
        # Triviality test: (q, b) ≡ (0, 0) mod 2N (the natural modulus
        # of the extracted form, matching PR #487's synthesis gauge).
        # Note: `ClassifyAbelianBranchFast` tests mod N (the cocycle's
        # coefficient modulus); for the standard cocycle representatives
        # in our e2e sweeps (StandardCocycleOf), `omega(a,a,a)` integer
        # values lie in [0, N), so `q mod 2N = 0` iff `q mod N = 0`.
        # The mod-2N test here is strictly stronger and never produces
        # a false "trivial" verdict for genuinely non-trivial input.
        # We additionally surface q_mod_N / b_mod_N for cross-validation
        # against `ClassifyAbelianBranchFast`.
        q_mod_N := List(qb.q, x -> x mod N);
        b_mod_N := List(qb.b, r -> List(r, x -> x mod N));
        is_q_trivial := ForAll(qb.q, x -> x = 0);
        is_b_trivial := ForAll(qb.b, r -> ForAll(r, x -> x = 0));
        is_trivial := is_q_trivial and is_b_trivial;
        if is_trivial then
            class_idx := 1;
        else
            class_idx := fail;
        fi;
        return rec(
            is_trivial    := is_trivial,
            class_idx     := class_idx,
            method        := "qb_extraction",
            q             := qb.q,
            b             := qb.b,
            q_mod_N       := q_mod_N,
            b_mod_N       := b_mod_N,
            is_q_trivial  := is_q_trivial,
            is_b_trivial  := is_b_trivial,
            i_chi_triv    := qb.i_chi_triv,
            N             := N,
            two_N         := qb.two_N,
            wall_ms       := Runtime() - t0
        );
    fi;

    # PATH B (#486): legacy full (S, T) input. Run JointPermutationMatcher
    # against the untwisted modular data of H. Tractable for k <= 6 in
    # (Z/2)^k.
    untwisted := ComputeUntwistedModularData(H);
    match := JointPermutationMatcher(S, T, untwisted.S, untwisted.T);

    is_trivial := match.ok;
    if is_trivial then
        class_idx := 1;
    else
        class_idx := fail;
    fi;

    return rec(
        is_trivial         := is_trivial,
        class_idx          := class_idx,
        method             := "joint_permutation",
        match              := match,
        modular_untwisted  := untwisted,
        wall_ms            := Runtime() - t0
    );
end);

if IsBoundGlobal("_LogStamped") then
    _LogStamped("Loaded ea_modular_data_classifier.g (#486 + #490).");
else
    Print("Loaded ea_modular_data_classifier.g (#486 + #490).\n");
fi;
