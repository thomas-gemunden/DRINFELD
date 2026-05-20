# Tests for _DETF_LagrangiansViaWitt (issue #299: D-VAN m=7 Witt
# Lagrangian enumeration). Verifies:
#   1. Count at m = 1, 2, 3, 4 matches the closed-form N_+(m, 2) =
#      prod_{i=0..m-1}(2^i + 1) = 2, 6, 30, 270.
#   2. Each Lagrangian is q-isotropic and B-orthogonal (sanity check).
#   3. No duplicates (RREF basis uniqueness).
#   4. _DETF_AllMaxEAsIn(E_+(m), m) at m <= 5 returns the same count as
#      before (preserve fast paths).
#   5. _DETF_AllMaxEAsIn(E_+(6), 6) returns 151470 max EAs as
#      basis-tuples (full Witt enumeration path).
#
# Run:
#   gap -q -b -c 'Read("tests/test_lagrangians_via_witt.g"); QUIT;'

BreakOnError := false;;

Read("detecting_family_restriction.g");
Read("qforms_f2.g");

Print("\n=== test_lagrangians_via_witt.g ===\n");

testFailures := [];;
If_ := function(c, a, b) if c then return a; else return b; fi; end;;
AssertOrLog := function(label, cond)
    Print("  ", label, ": ", If_(cond, "PASS", "FAIL"), "\n");
    if not cond then Add(testFailures, label); fi;
end;;

# Closed-form count formula.
N_plus := function(m)
    local p, i;
    p := 1;
    for i in [0..(m - 1)] do
        p := p * (2^i + 1);
    od;
    return p;
end;;

# Verify a basis-matrix candidate is a type-+ Lagrangian.
IsTypePlusLagrangian := function(L, m)
    local k, l;
    if Length(L) <> m then return false; fi;
    # Each row q-isotropic.
    for k in [1..m] do
        if _DETF_QForm(L[k]) <> 0 then return false; fi;
    od;
    # All pairs B-orthogonal.
    for k in [1..(m - 1)] do
        for l in [(k + 1)..m] do
            if _DETF_BForm(L[k], L[l]) <> 0 then return false; fi;
        od;
    od;
    # Rank check: rows are linearly independent.
    if RankMat(L * Z(2)^0) <> m then return false; fi;
    return true;
end;;

# Canonical hashable form for a Lagrangian: tuple of all m basis rows
# converted to a string (since we control the RREF form, this should
# uniquely identify the subspace).
LagrangianFingerprint := function(L)
    return String(L);
end;;

Print("\n--- N_+(m, 2) closed-form counts ---\n");
AssertOrLog("N_+(1, 2) = 2",  N_plus(1) = 2);
AssertOrLog("N_+(2, 2) = 6",  N_plus(2) = 6);
AssertOrLog("N_+(3, 2) = 30", N_plus(3) = 30);
AssertOrLog("N_+(4, 2) = 270", N_plus(4) = 270);
AssertOrLog("N_+(5, 2) = 4590", N_plus(5) = 4590);
AssertOrLog("N_+(6, 2) = 151470", N_plus(6) = 151470);
AssertOrLog("N_+(7, 2) = 9845550", N_plus(7) = 9845550);

Print("\n--- _DETF_LagrangiansViaWitt at m = 1 ---\n");
L1 := _DETF_LagrangiansViaWitt(1);;
AssertOrLog("count at m=1 is N_+(1, 2) = 2",
            Length(L1) = N_plus(1));
AssertOrLog("each Lagrangian at m=1 is type-+ valid",
            ForAll(L1, L -> IsTypePlusLagrangian(L, 1)));
AssertOrLog("no duplicates at m=1",
            Length(Set(L1, LagrangianFingerprint)) = Length(L1));

Print("\n--- _DETF_LagrangiansViaWitt at m = 2 ---\n");
L2 := _DETF_LagrangiansViaWitt(2);;
AssertOrLog("count at m=2 is N_+(2, 2) = 6",
            Length(L2) = N_plus(2));
AssertOrLog("each Lagrangian at m=2 is type-+ valid",
            ForAll(L2, L -> IsTypePlusLagrangian(L, 2)));
AssertOrLog("no duplicates at m=2",
            Length(Set(L2, LagrangianFingerprint)) = Length(L2));

Print("\n--- _DETF_LagrangiansViaWitt at m = 3 ---\n");
L3 := _DETF_LagrangiansViaWitt(3);;
AssertOrLog("count at m=3 is N_+(3, 2) = 30",
            Length(L3) = N_plus(3));
AssertOrLog("each Lagrangian at m=3 is type-+ valid",
            ForAll(L3, L -> IsTypePlusLagrangian(L, 3)));
AssertOrLog("no duplicates at m=3",
            Length(Set(L3, LagrangianFingerprint)) = Length(L3));

Print("\n--- _DETF_LagrangiansViaWitt at m = 4 ---\n");
L4 := _DETF_LagrangiansViaWitt(4);;
AssertOrLog("count at m=4 is N_+(4, 2) = 270",
            Length(L4) = N_plus(4));
AssertOrLog("each Lagrangian at m=4 is type-+ valid",
            ForAll(L4, L -> IsTypePlusLagrangian(L, 4)));
AssertOrLog("no duplicates at m=4",
            Length(Set(L4, LagrangianFingerprint)) = Length(L4));

Print("\n--- _DETF_LagrangiansViaWitt at m = 5 (streaming, count only) ---\n");
m5_count := rec(n := 0);;
m5_consumer := function(L) m5_count.n := m5_count.n + 1; end;;
_DETF_LagrangiansViaWitt_streaming(5, m5_consumer);;
AssertOrLog("count at m=5 is N_+(5, 2) = 4590",
            m5_count.n = N_plus(5));

Print("\n--- Streaming variant at m = 3 ---\n");
streamed_count := rec(n := 0);;
consumer_count := function(L)
    streamed_count.n := streamed_count.n + 1;
end;;
streamed_n := _DETF_LagrangiansViaWitt_streaming(3, consumer_count);;
AssertOrLog("streaming variant returns N_+(3, 2) = 30",
            streamed_n = 30);
AssertOrLog("streaming consumer invoked exactly 30 times",
            streamed_count.n = 30);

Print("\n--- m <= 5 fast-path preservation (m=2) ---\n");
# Direct sanity check: _DETF_AllMaxEAsIn(E_+(2), 2) still uses
# ConjugacyClassesSubgroups and returns 6 distinct max EAs (= N_+(2, 2)).
G_m2 := EPlusGroup(2);;
ea_list_m2 := _DETF_AllMaxEAsIn(G_m2, 2);;
AssertOrLog("E_+(2) max EAs count = 6 (= N_+(2, 2))",
            Length(ea_list_m2) = 6);

Print("\n--- m <= 5 fast-path preservation (m=3) ---\n");
G_m3 := EPlusGroup(3);;
ea_list_m3 := _DETF_AllMaxEAsIn(G_m3, 3);;
AssertOrLog("E_+(3) max EAs count = 30 (= N_+(3, 2))",
            Length(ea_list_m3) = 30);

Print("\n--- m=5 fast-path preservation (112 axis+pair-swap) ---\n");
G_m5 := EPlusGroup(5);;
ea_list_m5 := _DETF_AllMaxEAsIn(G_m5, 5);;
AssertOrLog("E_+(5) max EAs count = 112 (axis-aligned + pair-swap)",
            Length(ea_list_m5) = 112);

Print("\n--- m=5 Witt-vs-112: 112 axis+pair-swap is subset of full Witt ---\n");
# Build the full Witt list at m=5 (in F_2 form), then check that each
# of the 112 axis+pair-swap Lagrangians (in F_2 form) appears.
m5_Witt_list := _DETF_LagrangiansViaWitt(5);;
AssertOrLog("Full Witt at m=5 has 4590 Lagrangians",
            Length(m5_Witt_list) = N_plus(5));

# Build the 112 axis+pair-swap Lagrangians directly in F_2 form (mirroring
# _DETF_AllMaxEAsIn's logic but emitting F_2 row matrices).
# Note: these F_2 matrices may not be in RREF; we must canonicalise via
# RREF before set-comparison.
Build112_F2 := function()
    local list, sel_bits, sel, F_a, b, other_pairs, other_sel_bits,
          oj, idx, basis, m, k, vec, mat_to_rref, e;
    m := 5;
    list := [];
    # Helper: convert a list of F_2 vectors to RREF representation.
    mat_to_rref := function(rows)
        local mat, r;
        # Build matrix, RREF over F_2.
        mat := List(rows, ShallowCopy);
        # RREF over F_2 using existing F2RREF if available; else inline.
        return F2RREF(mat).rref;
    end;
    # (a) axis-aligned: 32 = 2^5 selections.
    for sel_bits in [0..(2^m - 1)] do
        basis := [];
        for k in [1..m] do
            vec := List([1..2*m], i -> 0);
            if QuoInt(sel_bits, 2^(k - 1)) mod 2 = 0 then
                vec[2*k - 1] := 1;
            else
                vec[2*k] := 1;
            fi;
            Add(basis, vec);
        od;
        Add(list, mat_to_rref(basis));
    od;
    # (b) diagonal pair-swap: C(5,2) * 2^3 = 10 * 8 = 80.
    for F_a in [1..(m - 1)] do
        for b in [(F_a + 1)..m] do
            other_pairs := Filtered([1..m], c -> c <> F_a and c <> b);
            for other_sel_bits in [0..(2^(m - 2) - 1)] do
                basis := [];
                # d1 = e_{2a-1} + e_{2b}
                vec := List([1..2*m], i -> 0);
                vec[2*F_a - 1] := 1; vec[2*b] := 1;
                Add(basis, vec);
                # d2 = e_{2a} + e_{2b-1}
                vec := List([1..2*m], i -> 0);
                vec[2*F_a] := 1; vec[2*b - 1] := 1;
                Add(basis, vec);
                for oj in [1..(m - 2)] do
                    idx := other_pairs[oj];
                    vec := List([1..2*m], i -> 0);
                    if QuoInt(other_sel_bits, 2^(oj - 1)) mod 2 = 0 then
                        vec[2*idx - 1] := 1;
                    else
                        vec[2*idx] := 1;
                    fi;
                    Add(basis, vec);
                od;
                Add(list, mat_to_rref(basis));
            od;
        od;
    od;
    return list;
end;;

list_112_rref := Build112_F2();;
Print("  112-Lagrangian list size: ", Length(list_112_rref), "\n");
AssertOrLog("Built 112 axis+pair-swap Lagrangians",
            Length(list_112_rref) = 112);

# m5_Witt_list is already in RREF (by construction). Compare as a set of
# string-fingerprints.
witt_fps := Set(m5_Witt_list, LagrangianFingerprint);;
fps_112 := Set(list_112_rref, LagrangianFingerprint);;
AssertOrLog("All 112 axis+pair-swap Lagrangians are in the full Witt list",
            IsSubset(witt_fps, fps_112));
AssertOrLog("Witt-distinct 112-set has 112 unique elements (no internal dups)",
            Length(fps_112) = 112);

Print("\n--- _DETF_AllMaxEAsIn at m=6 (Witt path, basis-tuples) ---\n");
# At m >= 6, _DETF_AllMaxEAsIn dispatches to Witt and returns basis-tuples
# (lists of m+1 group elements), NOT GAP Subgroup objects. Verify count
# and shape; spot-check that wrapping the first basis-tuple gives a max EA.
G_m6 := EPlusGroup(6);;
ea_list_m6 := _DETF_AllMaxEAsIn(G_m6, 6);;
AssertOrLog("E_+(6) Witt-path count = 151470 (= N_+(6, 2))",
            Length(ea_list_m6) = N_plus(6));
AssertOrLog("E_+(6) ea_list[1] is a basis-tuple (list of group elements)",
            IsList(ea_list_m6[1]) and Length(ea_list_m6[1]) = 7);
# Spot-check: first tuple wraps into a max EA of rank m+1 = 7.
spot_sub := Subgroup(G_m6, ea_list_m6[1]);;
AssertOrLog("E_+(6) Subgroup(G, ea_list[1]) is a rank-7 EA (order 128)",
            Order(spot_sub) = 128 and IsElementaryAbelian(spot_sub));

if IsEmpty(testFailures) then
    Print("\n=== test_lagrangians_via_witt: PASS ===\n");
else
    Print("\n=== test_lagrangians_via_witt: FAIL (",
          Length(testFailures), ") ===\n");
    for f in testFailures do Print("  - ", f, "\n"); od;
fi;
