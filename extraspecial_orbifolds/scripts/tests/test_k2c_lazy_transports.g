# test_k2c_lazy_transports.g
#
# K-2c (#129) follow-up: verify `BuildTransportsLazy` + `GetTransport`
# deliver byte-for-byte equivalence with the eager `BuildTransports`,
# materialise only on demand, and unblock the single-query
# `SKeller(m, i, j)` path at m=7.
#
# Tests:
#   T1: m=2 anchor — `BuildTransportsLazy` and `BuildTransports` produce
#       element-equal records per class on E_+(2).
#   T2: m=3 equivalence — same on E_+(3) (65 classes, full sweep).
#   T3: laziness at m=5 — `BuildTransportsLazy(idx)` completes in
#       sub-second wall time; touching k slots materialises only those
#       slots; previously-untouched slots remain `fail`.
#   T4: single-query m=7 — `BuildIntertwinerDataUntwistedLazy(E_+(7))`
#       and `SKeller(7, i, j)` on the central-row identity pair complete
#       without hitting the eager 20-min cache build wall. We check the
#       value matches the central-row closed form
#         S^0_{((1, triv), (1, triv))} = 1 / |G|
#       (per `closed_form_central.g` style; trivially derivable).
#
# Invoke by absolute path (K-4a-T1 convention):
#   /opt/homebrew/bin/gap -q -b -c \
#     'Read("/abs/path/to/test_k2c_lazy_transports.g");'

BreakOnError := false;;
SetInfoLevel(InfoWarning, 0);;

# ---- Test bookkeeping --------------------------------------------------

K2C_PASSES   := 0;;
K2C_FAILURES := [];;

K2CAssertEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
        K2C_PASSES := K2C_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Print("         expected: ", expected, "\n");
        Print("         got:      ", got, "\n");
        Add(K2C_FAILURES, label);
    fi;
end;;

K2CAssertTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
        K2C_PASSES := K2C_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Add(K2C_FAILURES, label);
    fi;
end;;

# ---- Locate worktree, scripts, sibling files ---------------------------

K2C_SELF := INPUT_FILENAME();;
if K2C_SELF = fail or K2C_SELF = "stream" then
    Error("test_k2c_lazy_transports.g: INPUT_FILENAME() unavailable; ",
          "Read the file by its absolute path.");
fi;
K2C_SELFDIR := K2C_SELF{
    [1..Length(K2C_SELF) - Length("/test_k2c_lazy_transports.g")]};;
K2C_SCRIPTSDIR := K2C_SELFDIR{
    [1..Length(K2C_SELFDIR) - Length("/tests")]};;

Read(Concatenation(K2C_SCRIPTSDIR, "/em_construction.g"));
Read(Concatenation(K2C_SCRIPTSDIR, "/untwisted_modular_data.g"));
Read(Concatenation(K2C_SCRIPTSDIR, "/krr_projector.g"));
Read(Concatenation(K2C_SCRIPTSDIR, "/skeller_adapter.g"));

K2CAssertTrue("BuildTransports bound",       IsBound(BuildTransports));
K2CAssertTrue("BuildTransportsLazy bound",   IsBound(BuildTransportsLazy));
K2CAssertTrue("BuildTransportForClass bound",IsBound(BuildTransportForClass));
K2CAssertTrue("GetTransport bound",          IsBound(GetTransport));

# ---- Helper: per-class record equality ---------------------------------

# Compares two transport records (eager vs materialised-lazy) for one
# class. Tests:
#   - .elements element-wise equal
#   - .t_of element-wise equal
#   - .elt_to_idx maps every element to the same index
# Returns true on equality, prints first mismatch otherwise.
K2C_TransportsEqualForClass := function(label, eager_rec, lazy_rec)
    local ne, i, e1, e2, t1, t2, idx_e, idx_l;
    if Length(eager_rec.elements) <> Length(lazy_rec.elements) then
        Print("    ", label, ": .elements length mismatch  eager=",
              Length(eager_rec.elements), " lazy=",
              Length(lazy_rec.elements), "\n");
        return false;
    fi;
    ne := Length(eager_rec.elements);
    for i in [1..ne] do
        e1 := eager_rec.elements[i];
        e2 := lazy_rec.elements[i];
        if e1 <> e2 then
            Print("    ", label, ": .elements[", i, "] differ\n");
            return false;
        fi;
        t1 := eager_rec.t_of[i];
        t2 := lazy_rec.t_of[i];
        if t1 <> t2 then
            Print("    ", label, ": .t_of[", i, "] differ\n");
            return false;
        fi;
        idx_e := LookupDictionary(eager_rec.elt_to_idx, e1);
        idx_l := LookupDictionary(lazy_rec.elt_to_idx, e1);
        if idx_e <> idx_l or idx_e <> i then
            Print("    ", label, ": .elt_to_idx[elements[", i,
                  "]] differ  eager=", idx_e, " lazy=", idx_l, "\n");
            return false;
        fi;
    od;
    return true;
end;;

# ========================================================================
# T1. m=2 anchor — eager and lazy agree on every class.
# ========================================================================

Print("\n=== T1. m=2 anchor: BuildTransports vs BuildTransportsLazy ===\n");

G2 := SmallGroup(32, 49);;
idx2_eager := BuildSimpleIndex(G2);;
idx2_lazy  := BuildSimpleIndexLazy(G2);;
trans2_eager := BuildTransports(idx2_eager);;
trans2_lazy  := BuildTransportsLazy(idx2_lazy);;

K2CAssertEqual("E_+(2) lazy transport length = #classes",
               Length(trans2_lazy), Length(idx2_lazy.classes));
K2CAssertTrue("E_+(2) every lazy slot starts as `fail`",
              ForAll(trans2_lazy, x -> x = fail));

K2C_t1_mismatches := 0;;
K2C_t1_total := Length(idx2_eager.classes);;
for K2C_i in [1..K2C_t1_total] do
    K2C_lazy_rec := GetTransport(trans2_lazy, idx2_lazy, K2C_i);;
    if not K2C_TransportsEqualForClass(
            Concatenation("m=2 class ", String(K2C_i)),
            trans2_eager[K2C_i], K2C_lazy_rec) then
        K2C_t1_mismatches := K2C_t1_mismatches + 1;
    fi;
od;
K2CAssertEqual(Concatenation(
    "E_+(2) lazy vs eager: all ", String(K2C_t1_total),
    " classes agree element-wise"), K2C_t1_mismatches, 0);

# After GetTransport on every class, every slot should be a record.
K2C_t1_all_materialised := ForAll(trans2_lazy, x -> x <> fail);;
K2CAssertTrue("E_+(2) all slots materialised after full sweep",
              K2C_t1_all_materialised);

# ========================================================================
# T2. m=3 equivalence — full sweep on 65 classes.
# ========================================================================

Print("\n=== T2. m=3 equivalence: full sweep on E_+(3) ===\n");

G3 := SmallGroup(128, 2326);;
idx3_eager := BuildSimpleIndex(G3);;
idx3_lazy  := BuildSimpleIndexLazy(G3);;
trans3_eager := BuildTransports(idx3_eager);;
trans3_lazy  := BuildTransportsLazy(idx3_lazy);;

K2CAssertEqual("E_+(3) eager #classes = 65",
               Length(idx3_eager.classes), 65);
K2CAssertEqual("E_+(3) lazy transport length = #classes",
               Length(trans3_lazy), Length(idx3_lazy.classes));

K2C_t2_mismatches := 0;;
K2C_t2_total := Length(idx3_eager.classes);;
for K2C_i in [1..K2C_t2_total] do
    K2C_lazy_rec := GetTransport(trans3_lazy, idx3_lazy, K2C_i);;
    if not K2C_TransportsEqualForClass(
            Concatenation("m=3 class ", String(K2C_i)),
            trans3_eager[K2C_i], K2C_lazy_rec) then
        K2C_t2_mismatches := K2C_t2_mismatches + 1;
    fi;
od;
K2CAssertEqual(Concatenation(
    "E_+(3) lazy vs eager: all ", String(K2C_t2_total),
    " classes agree element-wise"), K2C_t2_mismatches, 0);

# Eager BuildTransports still returns full records (regression — no slot
# in the eager list is `fail`).
K2C_t2_eager_all_records := ForAll(trans3_eager,
    r -> IsRecord(r) and IsBound(r.elements) and IsBound(r.t_of)
         and IsBound(r.elt_to_idx));;
K2CAssertTrue("E_+(3) BuildTransports (eager) returns full records",
              K2C_t2_eager_all_records);

# GetTransport on an already-materialised eager record returns it
# unchanged (the .elements list is *identical* — same GAP object).
K2C_t2_idempotent := IsIdenticalObj(GetTransport(trans3_eager,
                                                  idx3_eager, 1),
                                     trans3_eager[1]);;
K2CAssertTrue("GetTransport on eager slot is identity (no rebuild)",
              K2C_t2_idempotent);

# ========================================================================
# T3. Laziness at m=5 — BuildTransportsLazy is sub-second; only queried
# slots are materialised.
# ========================================================================

Print("\n=== T3. Laziness at m=5: build is fast, only queried slots materialise ===\n");

# E_+(5) = ExtraspecialGroup(2048, "+"). We construct it directly to
# avoid depending on the SmallGroups library for order 2048 (which is
# not always installed; the standard GAP smallgrp package goes up to
# order 1023 and 2*p^n cases beyond that).
G5_mat := EmGroup(5);;
# Convert to a faster representation for centraliser/conjugacy work.
G5_iso := IsomorphismPcGroup(G5_mat);;
if G5_iso = fail then
    G5_iso := IsomorphismPermGroup(G5_mat);;
fi;
if G5_iso = fail then
    G5 := G5_mat;;
else
    G5 := Image(G5_iso);;
fi;
K2CAssertEqual("E_+(5) order = 2048", Order(G5), 2048);

K2C_t3_t_idx_start := Runtime();;
idx5_lazy := BuildSimpleIndexLazy(G5);;
K2C_t3_idx_ms := Runtime() - K2C_t3_t_idx_start;;

K2C_t3_t_lazytr_start := Runtime();;
trans5_lazy := BuildTransportsLazy(idx5_lazy);;
K2C_t3_lazytr_ms := Runtime() - K2C_t3_t_lazytr_start;;
Print("  BuildSimpleIndexLazy at m=5: ", K2C_t3_idx_ms, " ms (",
      Length(idx5_lazy.classes), " classes)\n");
Print("  BuildTransportsLazy   at m=5: ", K2C_t3_lazytr_ms, " ms\n");
# The headline laziness property: BuildTransportsLazy itself does NO
# per-class BFS work; it just allocates a length-|classes| list of
# `fail`. So its wall time must be trivially small, regardless of the
# group size.
K2CAssertTrue("E_+(5) BuildTransportsLazy is sub-second (no per-class BFS)",
              K2C_t3_lazytr_ms < 1000);
K2CAssertTrue("E_+(5) lazy transport length = #classes",
              Length(trans5_lazy) = Length(idx5_lazy.classes));
K2CAssertTrue("E_+(5) every lazy slot starts as `fail`",
              ForAll(trans5_lazy, x -> x = fail));

# Touch 3 specific slots and verify only those materialise.
K2C_t3_touch_indices := [1, 2, QuoInt(Length(idx5_lazy.classes), 2)];;
for K2C_i in K2C_t3_touch_indices do
    K2C_x := GetTransport(trans5_lazy, idx5_lazy, K2C_i);;
od;

K2C_t3_materialised_count := Number(trans5_lazy, x -> x <> fail);;
K2C_t3_expected_materialised := Length(K2C_t3_touch_indices);;
K2CAssertEqual("E_+(5) only touched slots materialised",
               K2C_t3_materialised_count,
               K2C_t3_expected_materialised);

# The slot we DIDN'T touch should still be `fail`.
K2C_t3_untouched := Filtered([1..Length(idx5_lazy.classes)],
                              i -> not (i in K2C_t3_touch_indices));;
K2C_t3_untouched_all_fail := ForAll(K2C_t3_untouched,
                                     i -> trans5_lazy[i] = fail);;
K2CAssertTrue("E_+(5) untouched slots remain `fail`",
              K2C_t3_untouched_all_fail);

# A second GetTransport on a touched slot is a list lookup, no rebuild.
K2C_t3_first := GetTransport(trans5_lazy, idx5_lazy, 1);;
K2C_t3_second := GetTransport(trans5_lazy, idx5_lazy, 1);;
K2CAssertTrue("GetTransport(class=1) returns identical object on 2nd call",
              IsIdenticalObj(K2C_t3_first, K2C_t3_second));

# ========================================================================
# T4. Single-query at m=7 — BuildIntertwinerDataUntwistedLazy + SKeller(7,
# 1, 1) succeed within a reasonable wall time. The central-row identity
# entry is the cheapest sanity check (both classes are singletons of size
# 1).
#
# WHY THIS MATTERS: pre-K-2c, building the K-2 cache for E_+(7) hit a 20-
# minute eager wall (per #129 acceptance test C). With both lazy index
# and lazy transports, only 2 classes ever materialise per single-query.
# Conservative wall budget: ~10 min for the full single-entry path
# including the centraliser construction (which is by far the dominant
# cost: |G| = 2^15 means C_G(g_1) = G has 32768 elements; AsList on this
# may dominate at m=7).
# ========================================================================

Print("\n=== T4. Single-query at m=7: BuildIntertwinerDataUntwistedLazy + SKeller ===\n");

# Gate by env: T4 is the long one and we want it to be opt-in for CI.
# `K2C_RUN_M7` = "1" enables; default skip.
if not IsBound(K2C_RUN_M7) then
    K2C_RUN_M7 := "0";
fi;
# Allow env override (GAP doesn't expose env vars universally, so honour
# the GAP global if set in advance by the caller).

if K2C_RUN_M7 = "1" then
    Print("  T4 enabled via K2C_RUN_M7=1.\n");

    K2C_t4_t_start := Runtime();;

    # Build E_+(7). EmGroup(7) returns a matrix group; SKellerAdapter
    # converts to PC/Perm internally so SKeller(7, ...) is the right
    # entry point.
    K2C_t4_G7 := EmGroup(7);;
    K2C_t4_t_built_g := Runtime() - K2C_t4_t_start;;
    Print("  EmGroup(7) build: ", K2C_t4_t_built_g, " ms\n");

    # SKeller(7, 1, 1) triggers the full lazy pipeline:
    #   - SKellerGetCache(7) -> SKellerRebuildCache(7)
    #     -> SKellerBuildEmAsPcOrPerm(7) -> IsomorphismPcGroup
    #     -> BuildIntertwinerDataUntwistedLazy
    #         -> BuildSimpleIndexLazy: ConjugacyClasses, Centralizer,
    #            NrConjugacyClasses on each class
    #         -> BuildTransportsLazy: list of `fail` (no BFS)
    #     The first SKeller call then materialises 2 class slots
    #     (transport + CT) and computes the one entry.
    K2C_t4_t_q1_start := Runtime();;
    K2C_t4_v_11 := SKeller(7, 1, 1);;
    K2C_t4_t_q1_ms := Runtime() - K2C_t4_t_q1_start;;
    Print("  SKeller(7, 1, 1) wall (first query, incl. cache build): ",
          K2C_t4_t_q1_ms, " ms (", K2C_t4_t_q1_ms / 1000., " s)\n");

    # The closed-form expected value for the (identity-row, identity-col)
    # central-row entry of S^0 at E_+(m):
    #   S^0_{(1, triv), (1, triv)} = (dim(triv) / |C_G(1)|) * conj(triv(1))
    #                              = 1 / |G|
    # For E_+(7), |G| = 2^(2*7+1) = 32768.
    K2C_t4_expected_11 := 1 / 32768;;
    K2CAssertEqual("SKeller(7, 1, 1) = 1/|E_+(7)|",
                   K2C_t4_v_11, K2C_t4_expected_11);

    # The post-cache state must have minimal transport materialisation.
    K2C_t4_entry := SKellerCache.m7;;
    K2C_t4_trans := K2C_t4_entry.data.transport;;
    K2C_t4_materialised := Number(K2C_t4_trans, x -> x <> fail);;
    Print("  Transport slots materialised after SKeller(7,1,1): ",
          K2C_t4_materialised, " / ", Length(K2C_t4_trans), "\n");
    K2CAssertTrue("E_+(7) at most 2 transport slots materialised",
                  K2C_t4_materialised <= 2);

    # Repeat-query sanity check (should be much faster — both classes
    # cached, no rebuild).
    K2C_t4_t_q2_start := Runtime();;
    K2C_t4_v_11_again := SKeller(7, 1, 1);;
    K2C_t4_t_q2_ms := Runtime() - K2C_t4_t_q2_start;;
    Print("  SKeller(7, 1, 1) wall (second query, no cache build): ",
          K2C_t4_t_q2_ms, " ms\n");
    K2CAssertEqual("Second SKeller(7,1,1) call returns same value",
                   K2C_t4_v_11_again, K2C_t4_v_11);

    K2C_t4_total_ms := Runtime() - K2C_t4_t_start;;
    Print("  T4 total wall: ", K2C_t4_total_ms, " ms (",
          K2C_t4_total_ms / 60000., " min)\n");
else
    Print("  T4 SKIPPED. Set K2C_RUN_M7 := \"1\"; before Read() ",
          "to enable the m=7 path (long; usually 5-15 minutes).\n");
    Print("  Reason: T4 builds AsList(C_G(g_1)) for E_+(7) which is\n");
    Print("  the dominant cost (|G| = 32768) and is gated for fast\n");
    Print("  test-suite runs.\n");
fi;

# ========================================================================
# Summary.
# ========================================================================

Print("\n=================================================================\n");
Print("  K-2c lazy transports test summary\n");
Print("=================================================================\n");
Print("  Passes:   ", K2C_PASSES, "\n");
Print("  Failures: ", Length(K2C_FAILURES), "\n");
if Length(K2C_FAILURES) > 0 then
    Print("  Failure labels:\n");
    for K2C_l in K2C_FAILURES do
        Print("    - ", K2C_l, "\n");
    od;
    Print("\nFAIL\n");
else
    Print("\nPASS\n");
fi;

QUIT;
