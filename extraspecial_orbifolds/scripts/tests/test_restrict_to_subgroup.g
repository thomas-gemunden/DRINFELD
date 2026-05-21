# test_restrict_to_subgroup.g — K-4a-T5a (issue #199).
#
# Regression tests for `RestrictTraceOnWToSubgroup` in
# `extraspecial_orbifolds/scripts/restrict_to_subgroup.g`.
#
# Test cases (per the K-4a-T5a task spec, downscoped per T4a):
#
#   1. Stub roundtrip on E_+(2) -> Z_2 x Z_2 subgroup:
#      build untwisted intertwiner_data_G for E_+(2), restrict to a
#      rank-2 elementary abelian subgroup, verify the result is
#      internally consistent (class_to_G well-defined; trace_on_W
#      callable on (k_H, irrep_idx, h) for h in C_H(a_H)).
#
#   2. m = 3 D_8 restriction:
#      build untwisted intertwiner_data_G for E_+(3), restrict to
#      D8Section_E_plus(3). Verify D_8 has 5 conjugacy classes
#      (standard structure) and class_to_G is well-defined.
#
#   3. m = 3 E (max elementary abelian) restriction:
#      restrict to MaximalElementaryAbelian_E_plus(3) ~= Z_2^4
#      (16 conjugacy classes).
#
#   4. m = 3 Q_8 section restriction:
#      Q8Section_E_plus(3) (added by this PR). Q_8 has 5 conjugacy
#      classes (standard). Verify class_to_G is well-defined.
#
# Usage:
#   gap -q -b /abs/path/to/test_restrict_to_subgroup.g

# ---- Test harness ------------------------------------------------------

RTS_PASSES   := 0;;
RTS_FAILURES := [];;

RTSAssertEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
        RTS_PASSES := RTS_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Print("         expected: ", expected, "\n");
        Print("         got:      ", got, "\n");
        Add(RTS_FAILURES, label);
    fi;
end;;

RTSAssertTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
        RTS_PASSES := RTS_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Add(RTS_FAILURES, label);
    fi;
end;;

# ---- Locate and load the module under test ----------------------------

RTS_SELF := INPUT_FILENAME();;
if RTS_SELF = fail or RTS_SELF = "stream" then
    Error("test_restrict_to_subgroup.g: INPUT_FILENAME() unavailable; ",
          "Read by absolute path.");
fi;
# Issue #325: when this file is Read via a relative path,
# INPUT_FILENAME() returns the relative path as-given and the slicing
# below would produce wrong/empty results. Promote to absolute first.
if Length(RTS_SELF) > 0 and RTS_SELF[1] <> '/' then
    RTS_SELF := Filename(DirectoryCurrent(), RTS_SELF);
fi;
RTS_SELFDIR := RTS_SELF{[1..Length(RTS_SELF)
                            - Length("/test_restrict_to_subgroup.g")]};;
RTS_SCRIPTSDIR := RTS_SELFDIR{
    [1..Length(RTS_SELFDIR) - Length("/tests")]};;

Read(Concatenation(RTS_SCRIPTSDIR, "/untwisted_modular_data.g"));
Read(Concatenation(RTS_SCRIPTSDIR, "/krr_projector.g"));
Read(Concatenation(RTS_SCRIPTSDIR, "/quillen_detecting_subgroup.g"));
Read(Concatenation(RTS_SCRIPTSDIR, "/restrict_to_subgroup.g"));

RTSAssertTrue("RestrictTraceOnWToSubgroup bound",
              IsBound(RestrictTraceOnWToSubgroup));
RTSAssertTrue("BuildIntertwinerDataUntwisted bound",
              IsBound(BuildIntertwinerDataUntwisted));
RTSAssertTrue("D8Section_E_plus bound", IsBound(D8Section_E_plus));
RTSAssertTrue("Q8Section_E_plus bound", IsBound(Q8Section_E_plus));
RTSAssertTrue("MaximalElementaryAbelian_E_plus bound",
              IsBound(MaximalElementaryAbelian_E_plus));

# ---- Helper: verify the class_to_G mapping satisfies its contract ----
#
# For each H-class k_H with rep a_H, check:
#   * class_to_G[k_H].k_G is a valid G-class index in 1..|classes(G)|.
#   * idx_G.reps[k_G] = conj * a_H * conj^-1 where conj = class_to_G[k_H].conj.
#   * conj is an element of the parent group G (it may not lie in H).

CheckClassToGWellDefined := function(restricted, label)
    local idx_H, idx_G, G, k_H, a_H, m, k_G, conj, expected, got, count_ok, all_ok;
    idx_H := restricted.idx;
    idx_G := restricted.parent_data.idx;
    G := restricted.parent_G;
    count_ok := 0;
    all_ok := true;
    for k_H in [1..Length(idx_H.reps)] do
        a_H := idx_H.reps[k_H];
        m := restricted.class_to_G[k_H];
        k_G := m.k_G;
        conj := m.conj;
        if not (k_G in [1..Length(idx_G.classes)]) then
            Print("    BAD: k_H=", k_H, " has k_G=", k_G,
                  " out of range\n");
            all_ok := false;
        elif not (conj in G) then
            Print("    BAD: k_H=", k_H, " has conj not in G\n");
            all_ok := false;
        else
            expected := idx_G.reps[k_G];
            got := conj * a_H * conj^-1;
            if got <> expected then
                Print("    BAD: k_H=", k_H,
                      ": conj * a_H * conj^-1 = ", got,
                      ", expected ", expected, "\n");
                all_ok := false;
            else
                count_ok := count_ok + 1;
            fi;
        fi;
    od;
    RTSAssertTrue(Concatenation(label,
                                 ": class_to_G well-defined for all ",
                                 String(Length(idx_H.reps)),
                                 " H-classes (verified ",
                                 String(count_ok), ")"),
                  all_ok and count_ok = Length(idx_H.reps));
end;;

# ---- Helper: verify trace_on_W is callable on all H-classes -----------
#
# For each H-class k_H and each irrep_idx in 1..num_irreps[k_H], pick a
# representative h in C_H(a_H) (specifically: the rep a_H itself, which
# is always in its own centraliser) and call trace_on_W(k_H, irrep_idx,
# h). Verify the result is a cyclotomic.

CheckTraceCallable := function(restricted, label)
    local idx_H, k_H, num, k, a_H, h, val, all_ok, count;
    idx_H := restricted.idx;
    all_ok := true;
    count := 0;
    for k_H in [1..Length(idx_H.reps)] do
        num := idx_H.num_irreps[k_H];
        a_H := idx_H.reps[k_H];
        for k in [1..num] do
            h := a_H;            # a_H in C_H(a_H) always.
            val := restricted.trace_on_W(k_H, k, h);
            if not IsCyclotomic(val) then
                Print("    BAD: trace_on_W(", k_H, ", ", k,
                      ", a_H) = ", val, " (not cyclotomic)\n");
                all_ok := false;
            else
                count := count + 1;
            fi;
        od;
    od;
    RTSAssertTrue(Concatenation(label,
                                 ": trace_on_W callable on all ",
                                 String(count), " (k_H, k) pairs (a_H)"),
                  all_ok);
end;;

# ---- Helper: verify epsilon == 1 (T4a downscope) -----------------------

CheckEpsilonTrivial := function(restricted, label)
    local G, idx_H, a, b, val, all_ok;
    G := restricted.group;
    idx_H := restricted.idx;
    all_ok := true;
    if Length(idx_H.reps) >= 2 then
        a := idx_H.reps[1];
        b := idx_H.reps[2];
        val := restricted.epsilon(a, b, a, b);
        if val <> 1 then
            Print("    BAD: epsilon(a, b, a, b) = ", val,
                  ", expected 1\n");
            all_ok := false;
        fi;
    fi;
    RTSAssertTrue(Concatenation(label, ": epsilon evaluates to 1"),
                  all_ok);
end;;

# ---- Test 1: Stub roundtrip on E_+(2) -> Z_2 x Z_2 -------------------

Print("\n=================================================================\n");
Print("Test 1: E_+(2) -> Z_2 x Z_2 subgroup, internal consistency\n");
Print("=================================================================\n");

G2 := EPlusGroup(2);;             # |G2| = 32
data_G2 := BuildIntertwinerDataUntwisted(G2);;
Print("E_+(2) order: ", Order(G2), "\n");
Print("E_+(2) |classes|: ", Length(data_G2.idx.classes), "\n");

# Build a rank-2 elementary abelian subgroup inside E_+(2). The centre z
# together with any single non-central commuting generator works. Use
# the first non-central generator that is order-2 (every sigma_{a,1} or
# sigma_{a,2} qualifies) along with z.
z2 := First(AsList(Centre(G2)), x -> not IsOne(x));;
RTSAssertTrue("E_+(2) has a non-trivial centre element", z2 <> fail);

gens_G2 := GeneratorsOfGroup(G2);;
non_central_order2 := First(gens_G2,
                              g -> not (g in Centre(G2))
                                   and Order(g) = 2);;
RTSAssertTrue("E_+(2) has a non-central order-2 generator",
              non_central_order2 <> fail);

H_22 := Subgroup(G2, [z2, non_central_order2]);;
RTSAssertEqual("|H_22| = 4 (= Z_2 x Z_2)", Order(H_22), 4);
RTSAssertTrue("H_22 elementary abelian", IsElementaryAbelian(H_22));

restricted_22 := RestrictTraceOnWToSubgroup(data_G2, H_22);;
RTSAssertTrue("restricted record has .group", IsBound(restricted_22.group));
RTSAssertTrue("restricted record has .idx", IsBound(restricted_22.idx));
RTSAssertTrue("restricted record has .transport",
              IsBound(restricted_22.transport));
RTSAssertTrue("restricted record has .trace_on_W",
              IsBound(restricted_22.trace_on_W));
RTSAssertTrue("restricted record has .epsilon",
              IsBound(restricted_22.epsilon));
RTSAssertTrue("restricted record has .class_to_G",
              IsBound(restricted_22.class_to_G));
RTSAssertTrue("restricted record has .parent_G",
              IsBound(restricted_22.parent_G));

# Z_2 x Z_2 has 4 conjugacy classes (one per element since abelian).
RTSAssertEqual("|classes(H_22)| = 4",
               Length(restricted_22.idx.classes), 4);

CheckClassToGWellDefined(restricted_22, "Test 1");
CheckTraceCallable(restricted_22, "Test 1");
CheckEpsilonTrivial(restricted_22, "Test 1");

# Extra: for an abelian subgroup, C_H(a_H) = H for every a_H, so
# trace_on_W should be callable for h ranging over all of H, not just a_H.
all_ok_22 := true;;
for k_H_22 in [1..Length(restricted_22.idx.reps)] do
    for h_22 in AsList(H_22) do
        for irrep_idx_22 in [1..restricted_22.idx.num_irreps[k_H_22]] do
            val_22 := restricted_22.trace_on_W(k_H_22, irrep_idx_22, h_22);
            if not IsCyclotomic(val_22) then
                all_ok_22 := false;
            fi;
        od;
    od;
od;
RTSAssertTrue("Test 1: trace_on_W callable on all (k_H, irrep, h in H)",
              all_ok_22);

# ---- Test 2: m = 3 D_8 restriction ------------------------------------
#
# Convention: `D8Section_E_plus(m)` returns a record with a `.parent`
# field that is the SPECIFIC `EPlusGroup(m)` instance the subgroup
# was constructed within. We must build the intertwiner_data record
# from THIS instance (not a fresh `EPlusGroup(3)`), because GAP's
# group identity (and hence element membership tests) is by Family,
# and two calls to `ExtraspecialGroup(...)` return groups in different
# families.

Print("\n=================================================================\n");
Print("Test 2: E_+(3) -> D8Section_E_plus(3), class count = 5\n");
Print("=================================================================\n");

d8_rec := D8Section_E_plus(3);;
G3 := d8_rec.parent;;
data_G3 := BuildIntertwinerDataUntwisted(G3);;
Print("E_+(3) order: ", Order(G3), "\n");

H_d8 := d8_rec.subgroup;;
RTSAssertEqual("D_8 order", Order(H_d8), 8);
RTSAssertEqual("D_8 IdGroup = [8, 3]", IdGroup(H_d8), [8, 3]);

restricted_d8 := RestrictTraceOnWToSubgroup(data_G3, H_d8);;
RTSAssertEqual("|classes(D_8)| = 5",
               Length(restricted_d8.idx.classes), 5);

CheckClassToGWellDefined(restricted_d8, "Test 2 (D_8)");
CheckTraceCallable(restricted_d8, "Test 2 (D_8)");
CheckEpsilonTrivial(restricted_d8, "Test 2 (D_8)");

# Print the class_to_G mapping for diagnostic purposes.
Print("  D_8 class_to_G mapping (k_H -> k_G):\n");
for k_H_d8 in [1..Length(restricted_d8.idx.reps)] do
    Print("    k_H=", k_H_d8,
          " (size ", Size(restricted_d8.idx.classes[k_H_d8]), ")",
          " -> k_G=", restricted_d8.class_to_G[k_H_d8].k_G, "\n");
od;

# ---- Test 3: m = 3 maximal elementary abelian restriction -------------
#
# Each call to `*_E_plus(m)` creates a fresh `EPlusGroup(m)`; we use
# this rec's own `.parent` to build the matching intertwiner_data.

Print("\n=================================================================\n");
Print("Test 3: E_+(3) -> max EA(3) ~= Z_2^4, class count = 16\n");
Print("=================================================================\n");

ea_rec := MaximalElementaryAbelian_E_plus(3);;
G3_ea := ea_rec.parent;;
data_G3_ea := BuildIntertwinerDataUntwisted(G3_ea);;
H_ea := ea_rec.subgroup;;
RTSAssertEqual("max EA(3) order", Order(H_ea), 2^4);
RTSAssertTrue("max EA(3) is elementary abelian", IsElementaryAbelian(H_ea));

restricted_ea := RestrictTraceOnWToSubgroup(data_G3_ea, H_ea);;
RTSAssertEqual("|classes(EA(3))| = 16",
               Length(restricted_ea.idx.classes), 16);

CheckClassToGWellDefined(restricted_ea, "Test 3 (EA)");
CheckTraceCallable(restricted_ea, "Test 3 (EA)");
CheckEpsilonTrivial(restricted_ea, "Test 3 (EA)");

# An abelian subgroup: each element is its own class.
all_size1_ea := ForAll(restricted_ea.idx.classes, c -> Size(c) = 1);;
RTSAssertTrue("Test 3: every EA(3) class is a singleton (abelian)",
              all_size1_ea);

# ---- Test 4: m = 3 Q_8 section restriction ----------------------------
#
# Q_8 = E_-(1) section, added by this PR (mirrors D8Section_E_plus).
# Same parent-instance handling as Test 3.

Print("\n=================================================================\n");
Print("Test 4: E_+(3) -> Q8Section_E_plus(3), class count = 5\n");
Print("=================================================================\n");

q8_rec := Q8Section_E_plus(3);;
G3_q8 := q8_rec.parent;;
data_G3_q8 := BuildIntertwinerDataUntwisted(G3_q8);;
H_q8 := q8_rec.subgroup;;
RTSAssertEqual("Q_8 order", Order(H_q8), 8);
RTSAssertEqual("Q_8 IdGroup = [8, 4]", IdGroup(H_q8), [8, 4]);

restricted_q8 := RestrictTraceOnWToSubgroup(data_G3_q8, H_q8);;
RTSAssertEqual("|classes(Q_8)| = 5",
               Length(restricted_q8.idx.classes), 5);

CheckClassToGWellDefined(restricted_q8, "Test 4 (Q_8)");
CheckTraceCallable(restricted_q8, "Test 4 (Q_8)");
CheckEpsilonTrivial(restricted_q8, "Test 4 (Q_8)");

# Print the class_to_G mapping for diagnostic purposes.
Print("  Q_8 class_to_G mapping (k_H -> k_G):\n");
for k_H_q8 in [1..Length(restricted_q8.idx.reps)] do
    Print("    k_H=", k_H_q8,
          " (size ", Size(restricted_q8.idx.classes[k_H_q8]), ")",
          " -> k_G=", restricted_q8.class_to_G[k_H_q8].k_G, "\n");
od;

# ---- Test 5: parent_data round-trip ------------------------------------

Print("\n=================================================================\n");
Print("Test 5: parent_data round-trip\n");
Print("=================================================================\n");

RTSAssertTrue("parent_data preserves the original record",
              IsIdenticalObj(restricted_d8.parent_data, data_G3));
RTSAssertTrue("parent_G matches parent_data.group",
              restricted_d8.parent_G = data_G3.group);

# ---- Final report -----------------------------------------------------

Print("\n=================================================================\n");
Print("  Summary: ", RTS_PASSES, " passes, ",
      Length(RTS_FAILURES), " failures.\n");
Print("=================================================================\n");

if Length(RTS_FAILURES) = 0 then
    Print("\nPASS test_restrict_to_subgroup\n");
else
    Print("\nFAIL test_restrict_to_subgroup:\n");
    for f in RTS_FAILURES do
        Print("  - ", f, "\n");
    od;
fi;

QUIT;
