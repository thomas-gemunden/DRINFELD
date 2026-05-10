# K-3 verification driver: SKeller(m, i, j) vs the writeup §4.3 closed
# form on every central-row entry at m = 3.
#
# ISSUE (#40, task #45)
# =====================
# Goal: a regression script confirming SKeller(3, i, j) agrees with the
# writeup §4.3 closed form on every central-row entry of S^0 for
# Z(Vec_{E_+(3)}).
#
# Acceptance: 100% agreement on the central-row entries (the issue body
# mentions "16 × 2272 = 36 352"; the actual count of central-row entries
# for E_+(3) is 130 × 2272 = 295 360 — 130 = |Irr(E_+(3))| × 2 central
# singleton classes × |Irr| each. We verify ALL of them, which subsumes
# any subset).
#
# RELATION TO K-2
# ===============
# K-2's Test B already cross-checks SKeller vs the dense untwisted S
# (via ComputeSBlock from untwisted_modular_data.g), and matched exactly
# 295 360 / 295 360 entries. K-3 is distinct in that it uses the §4.3
# CLOSED FORM (a per-entry O(1) algebraic identity) rather than the
# O(|G|) sum implementation. Two independent ground truths agreeing
# yields stronger confidence.
#
# V-2 STAND-IN
# ============
# V-2 (closed-form S^ω at central rows) is a separate workstream. For
# ω = 0 the V-2 formula collapses to the classical §4.3 expression
#
#     S^0_{((1, ρ), (h, σ))}  = (dim σ / |C_G(h)|) * conj(ρ(h))
#     S^0_{((-1, ρ), (h, σ))} = (σ(-1)  / |C_G(h)|) * conj(ρ(h))
#
# which is what we implement INLINE here (function
# `CentralSEntryClosedForm` below) and cross-check against:
#   - `ClosedFormCentralS` in `closed_form_central.g` (helper),
#   - `SKeller`                in `skeller_adapter.g`     (K-2 adapter).
#
# Three-way agreement on all entries is the acceptance condition.
#
# RUNTIME
# =======
# K-2's central-row sweep took ~13 s on E_+(3). The closed-form
# evaluation is O(1) per entry (one character lookup × one conjugate ×
# one division), so K-3 should finish in well under a minute.
#
# Run from the scripts/ directory:
#   gap -q -b -A tests/test_krr_vs_central_closed_form.g

BreakOnError := false;
SetInfoLevel(InfoWarning, 0);

# ----- load all dependencies, in order -----
Read("em_construction.g");
Read("untwisted_modular_data.g");
Read("krr_projector.g");
Read("skeller_adapter.g");
Read("closed_form_central.g");


# ================================================================
# Inline implementation of the writeup §4.3 closed form.
#
# This is the verbatim §4.3 formula, recomputed from scratch from the
# group's character tables, with no shared code with
# `ClosedFormCentralS` other than the index record produced by
# `BuildSimpleIndex`. We do this deliberately: a regression script that
# checks A against B must not have A and B share an implementation that
# could have a common bug.
#
# Inputs:
#   idx      : BuildSimpleIndex(G) record
#   ci       : index in idx.classes of the CENTRAL element used as g_1.
#              Must satisfy idx.class_sizes[ci] = 1 and idx.reps[ci]
#              central in G. (We do NOT verify centrality here — the
#              caller is responsible; behaviour on non-central ci is
#              meaningless.)
#   k1       : irrep index in Irr(C_G(g_1)) = Irr(G) for the row irrep ρ
#   tj       : index in idx.classes of the target class element h
#              (a.k.a. g_2); arbitrary (central or not).
#   k2       : irrep index in Irr(C_G(h)) for the column irrep σ
#
# Returns the cyclotomic value of the §4.3 closed-form expression.
# ================================================================
CentralSEntryClosedForm := function(idx, ci, k1, tj, k2)
    local g1, h, rho, sigma, dim_sigma, sigma_at_g1, rho_at_h,
          C_h_size, value;

    # Class representatives.
    g1 := idx.reps[ci];   # central element of G (=1 or =-1 for E_+(m))
    h  := idx.reps[tj];   # target element (any class)

    # Row irrep ρ ∈ Irr(C_G(g_1)). Because g_1 is central, C_G(g_1) = G,
    # so ρ is an irreducible character of G; idx.irreps[ci] holds these.
    rho := idx.irreps[ci][k1];

    # Column irrep σ ∈ Irr(C_G(h)).
    sigma := idx.irreps[tj][k2];

    # dim σ = σ(1). Stored separately for the g_1 = 1 branch but we
    # evaluate σ(g_1) generally below and let it specialise.
    dim_sigma := idx.irrep_dims[tj][k2];

    # σ(g_1): g_1 is central, so g_1 ∈ Z(G) ⊆ C_G(h), and σ(g_1) makes
    # sense via the centraliser character table. We use the index
    # helper `EvalIrr` (which looks up the class of g_1 in C_G(h)).
    sigma_at_g1 := EvalIrr(idx, tj, k2, g1);

    # ρ(h): ρ is a character of C_G(g_1) = G, so just evaluate at h via
    # the centraliser table for the central class.
    rho_at_h := EvalIrr(idx, ci, k1, h);

    # |C_G(h)|.
    C_h_size := Order(idx.centralisers[tj]);

    # §4.3 formula:
    #   g_1 = 1   :  S = (dim σ / |C_G(h)|) * conj(ρ(h))   = (σ(1) / |C|) * conj(ρ(h))
    #   g_1 = -1  :  S = (σ(-1) / |C_G(h)|) * conj(ρ(h))
    # Both cases are captured by σ(g_1) / |C_G(h)| * conj(ρ(h)).
    # (For dim_sigma sanity we also confirm σ(1) = dim σ — used below.)
    value := sigma_at_g1 * ComplexConjugate(rho_at_h) / C_h_size;

    return rec(
        value := value,
        dim_sigma := dim_sigma,
        sigma_at_g1 := sigma_at_g1,
        rho_at_h := rho_at_h,
        C_h_size := C_h_size
    );
end;;


# ================================================================
# Sanity: when g_1 = 1, σ(g_1) must equal dim σ for every σ.
# This is a precondition for the §4.3 formula reducing to the
# "g_1 = 1" branch and also tests that idx.irrep_dims is consistent
# with EvalIrr(., ., 1) (one-class lookup in the centraliser table).
# ================================================================
SanityIdentityIsDimension := function(idx, identity_class_idx)
    local g1, ti, k, sigma_at_one, dim_sigma, problems;
    g1 := idx.reps[identity_class_idx];
    if g1 <> One(idx.group) then
        return rec(
            ok := false,
            reason := Concatenation(
                "identity_class_idx points to a non-identity rep: ",
                String(g1))
        );
    fi;
    problems := [];
    for ti in [1..Length(idx.classes)] do
        for k in [1..idx.num_irreps[ti]] do
            sigma_at_one := EvalIrr(idx, ti, k, g1);
            dim_sigma := idx.irrep_dims[ti][k];
            if sigma_at_one <> dim_sigma then
                Add(problems, [ti, k, sigma_at_one, dim_sigma]);
            fi;
        od;
    od;
    return rec(
        ok := Length(problems) = 0,
        problems := problems
    );
end;;


# ================================================================
# Test driver: build E_+(3) data via SKeller's cache.
# ================================================================
Print("\n=================================================================\n");
Print("  K-3: SKeller(3, i, j) vs §4.3 closed form on central rows\n");
Print("=================================================================\n");

t_cache0 := Runtime();;
entry3 := SKellerGetCache(3);;
data3 := entry3.data;;
idx3  := data3.idx;;
t_cache1 := Runtime();;

Print("E_+(3): order ", Order(entry3.group),
      ", classes ", Length(idx3.classes),
      ", rank ", idx3.rank, "\n");
Print("Cache build/fetch: ", t_cache1 - t_cache0, " ms\n");


# Identify the central singleton classes.
central3_classes := [];;
for i in [1..Length(idx3.classes)] do
    if idx3.class_sizes[i] <> 1 then continue; fi;
    g_c := idx3.reps[i];;
    ok := true;;
    for h_gen in GeneratorsOfGroup(idx3.group) do
        if g_c * h_gen <> h_gen * g_c then ok := false; break; fi;
    od;
    if ok then Add(central3_classes, i); fi;
od;
Print("Central singleton class indices: ", central3_classes,
      "  (", Length(central3_classes), " classes)\n");

# Locate the identity class for the sanity check.
identity_class_idx := fail;;
for i in central3_classes do
    if idx3.reps[i] = One(idx3.group) then
        identity_class_idx := i;
        break;
    fi;
od;
Print("Identity class index: ", identity_class_idx, "\n");


# ---------------------------------------------------------------
# Sanity check A: idx.irrep_dims agrees with EvalIrr at the identity.
# Without this, the §4.3 g_1=1 branch and the "σ(g_1)/|C|" general
# branch could disagree at the identity for some bookkeeping reason.
# ---------------------------------------------------------------
Print("\n--- Sanity check A: σ(1) = dim σ for all σ ---\n");
sanityA := SanityIdentityIsDimension(idx3, identity_class_idx);;
if sanityA.ok then
    Print("PASS (σ(1) = dim σ on all ", idx3.rank, " irreps)\n");
else
    Print("FAIL: ", Length(sanityA.problems), " irreps had σ(1) ≠ dim σ\n");
    for prob in sanityA.problems{[1..Minimum(3, Length(sanityA.problems))]} do
        Print("  class ", prob[1], " irrep ", prob[2],
              ": σ(1) = ", prob[3], ", dim σ = ", prob[4], "\n");
    od;
fi;
sanityA_ok := sanityA.ok;;


# ---------------------------------------------------------------
# Main acceptance check: 3-way agreement on every central-row entry.
#
#   • A := SKeller(3, gi, gj)                      (K-2 adapter)
#   • B := CentralSEntryClosedForm(idx3, ci, k1, tj, k2).value
#                                                 (§4.3 inline)
#   • C := ClosedFormCentralS(idx3, ci, k1, tj, k2)
#                                                 (helper script)
#
# For each central class ci, for each target class tj, for each
# (k1, k2) ∈ [1..|Irr(G)|] × [1..|Irr(C_G(h))|]:
#   compare A, B, C exactly (cyclotomic equality).
#
# Counters track:
#   - total entries checked
#   - mismatches A vs B (the headline acceptance)
#   - mismatches A vs C, B vs C (corroboration)
# ---------------------------------------------------------------
Print("\n--- Main check: SKeller vs §4.3 inline closed form ---\n");
Print("Looping over ", Length(central3_classes), " central classes × ",
      Length(idx3.classes), " target classes × (Ni × Nj) entries...\n");

t_main0 := Runtime();;
total_entries := 0;;
mismatch_AB := 0;;      # SKeller vs inline §4.3
mismatch_AC := 0;;      # SKeller vs existing helper
mismatch_BC := 0;;      # Inline §4.3 vs existing helper
first_AB_examples := [];;

for ci in central3_classes do
    Print("  ci = ", ci, "  (rep = ", idx3.reps[ci], ") ...\n");
    Ni := idx3.num_irreps[ci];;
    for tj in [1..Length(idx3.classes)] do
        Nj := idx3.num_irreps[tj];;
        for k1 in [1..Ni] do
            for k2 in [1..Nj] do
                total_entries := total_entries + 1;
                gi := SKellerEncodeIndex(3, ci, k1);;
                gj := SKellerEncodeIndex(3, tj, k2);;

                vA := SKeller(3, gi, gj);;
                vB := CentralSEntryClosedForm(idx3, ci, k1, tj, k2).value;;
                vC := ClosedFormCentralS(idx3, ci, k1, tj, k2);;

                if vA <> vB then
                    mismatch_AB := mismatch_AB + 1;
                    if Length(first_AB_examples) < 3 then
                        Add(first_AB_examples,
                            rec(ci := ci, k1 := k1, tj := tj, k2 := k2,
                                gi := gi, gj := gj,
                                SKeller := vA, closed_form := vB));
                    fi;
                fi;
                if vA <> vC then
                    mismatch_AC := mismatch_AC + 1;
                fi;
                if vB <> vC then
                    mismatch_BC := mismatch_BC + 1;
                fi;
            od;
        od;
    od;
od;
t_main1 := Runtime();;

Print("\nEntries checked: ", total_entries, "\n");
Print("Mismatches (SKeller vs inline §4.3 closed form): ", mismatch_AB, "\n");
Print("Mismatches (SKeller vs helper ClosedFormCentralS): ", mismatch_AC, "\n");
Print("Mismatches (inline §4.3 vs helper ClosedFormCentralS): ", mismatch_BC, "\n");
Print("Main sweep wall time: ", t_main1 - t_main0, " ms (",
      (t_main1 - t_main0) / 1000., " s)\n");

if Length(first_AB_examples) > 0 then
    Print("\nFirst few mismatches (SKeller vs inline §4.3):\n");
    for ex in first_AB_examples do
        Print("  ci=", ex.ci, " k1=", ex.k1,
              " tj=", ex.tj, " k2=", ex.k2,
              "  (gi=", ex.gi, ", gj=", ex.gj, ")\n");
        Print("    SKeller     = ", ex.SKeller, "\n");
        Print("    closed form = ", ex.closed_form, "\n");
    od;
fi;

main_ok := mismatch_AB = 0 and mismatch_AC = 0 and mismatch_BC = 0;;
Print("\nMain check PASS: ", main_ok, "\n");


# ---------------------------------------------------------------
# Summary
# ---------------------------------------------------------------
Print("\n=================================================================\n");
Print("  K-3 Summary\n");
Print("=================================================================\n");
Print("Sanity A (σ(1) = dim σ):                 ", sanityA_ok, "\n");
Print("Main 3-way agreement on central rows:    ", main_ok, "\n");
Print("Entries verified: ", total_entries, "\n");
Print("Wall time (main sweep): ", (t_main1 - t_main0) / 1000., " s\n");

acceptance_pass := sanityA_ok and main_ok;;
Print("\nK-3 ACCEPTANCE (SKeller = §4.3 closed form on central rows): ",
      acceptance_pass, "\n");

if acceptance_pass then
    Print("\nK-3 REGRESSION: SKeller agrees with the writeup §4.3 closed form ",
          "on every central-row entry of S^0 for Z(Vec_{E_+(3)}).\n");
else
    Print("\nK-3 FAILURE: see mismatch examples above.\n");
fi;

QUIT;
