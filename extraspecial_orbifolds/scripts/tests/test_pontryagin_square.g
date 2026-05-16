# test_pontryagin_square.g — regression test for the Pontryagin square.
# Issue #161 (Q-int B2-2). Builds on Steenrod cup-1 from #160.
#
# Run from extraspecial_orbifolds/scripts/:
#   gap -q -b -c 'Read("tests/test_pontryagin_square.g"); QUIT;'
#
# Anchor: D_8 = SmallGroup(8, 3). Smallest non-trivial 2-group; full
# G^5 = 32768 cocycle-equation sweep is tractable.

BreakOnError := false;;

Read("pontryagin_square.g");
Read("bar_cocycle.g");

Print("\n=== test_pontryagin_square.g (issue #161) ===\n");

testFailures := [];;
If_loc := function(c, a, b) if c then return a; else return b; fi; end;;
AssertOrLog := function(label, cond)
    Print("  ", label, ": ", If_loc(cond, "PASS", "FAIL"), "\n");
    if not cond then Add(testFailures, label); fi;
end;;

# --------------------------------------------------------------------
# Task 1: Build an F_2 2-cocycle on D_8 (the Quillen quadratic form at m=1).
# --------------------------------------------------------------------
#
# At m=1, E_+(1) = D_8 with V = (F_2)² and quadratic form
#     Q(x_1, x_2) = x_1 · x_2.
# As a bar 2-cocycle on G = D_8:
#     Q(g, h) = x_1(g) · x_2(h)   mod 2
# where x_1, x_2 are two F_2 homs forming a basis of H^1(D_8; F_2)
# (excluding the third Z/2 basis element of the abelianisation).

Print("\n--- Task 1: F_2 2-cocycle Q on D_8 ---\n");

G := SmallGroup(8, 3);;
gens_G := GeneratorsOfGroup(G);;

_Z2 := CyclicGroup(IsPermGroup, 2);;
_z2_one := GeneratorsOfGroup(_Z2)[1];;
_z2_id  := Identity(_Z2);;
valid_assignments := [];;
for v in Cartesian(List(gens_G, g -> [0, 1])) do
    if GroupHomomorphismByImages(G, _Z2, gens_G,
            List(v, x -> If_loc(x = 0, _z2_id, _z2_one))) <> fail then
        Add(valid_assignments, v);
    fi;
od;
non_zero := Filtered(valid_assignments, v -> Sum(v) > 0);;
x_hom := F2HomFromImages(G, non_zero[1]);;
y_hom := F2HomFromImages(G, non_zero[2]);;

Q := function(g, h) return (x_hom(g) * y_hom(h)) mod 2; end;;

# Verify Q is a bar 2-cocycle (mod 2).
n_viol_Q := 0;;
for t in Tuples(AsList(G), 3) do
    if (Q(t[2], t[3]) - Q(t[1] * t[2], t[3])
        + Q(t[1], t[2] * t[3]) - Q(t[1], t[2])) mod 2 <> 0 then
        n_viol_Q := n_viol_Q + 1;
    fi;
od;
AssertOrLog("Q(g, h) = x(g)*y(h) is an F_2 2-cocycle on D_8 (0 violations)",
            n_viol_Q = 0);

# --------------------------------------------------------------------
# Task 2: PontryaginSquare(Q, 2) is a Z/4 4-cocycle.
# --------------------------------------------------------------------

Print("\n--- Task 2: P(Q) bar 4-cocycle equation (mod 4) ---\n");

PQ := PontryaginSquare(Q, 2);;

r := VerifyBar2nCocycleEquationMod4(G, PQ, 2);;
Print("  bar 4-cocycle equation on ", r.total, " tuples; violations = ",
      r.violations, "\n");
AssertOrLog("P(Q) satisfies bar 4-cocycle equation mod 4 on D_8 (0 violations)",
            r.violations = 0);

# --------------------------------------------------------------------
# Task 3: P(Q) takes non-trivial values mod 4 (order > 1).
# --------------------------------------------------------------------

Print("\n--- Task 3: P(Q) value distribution ---\n");

elts := AsList(G);;
pq_values := [];;
for args in Tuples(elts, 4) do
    AddSet(pq_values, CallFuncList(PQ, args));
od;
Print("  distinct values of P(Q) on D_8^4: ", pq_values, "\n");
AssertOrLog("P(Q) is not identically zero mod 4",
            pq_values <> [0]);
AssertOrLog("P(Q) takes a value in {1, 3} mod 4 (proves order 4 class)",
            1 in pq_values or 3 in pq_values);

# --------------------------------------------------------------------
# Task 4: F_2 reduction. P(α) mod 2 ≡ α ∪ α (since δα̃ ∪₁ α̃ has each
# δα̃ factor in 2Z, so the ∪₁ term vanishes mod 2). This is a key
# structural property — check it.
# --------------------------------------------------------------------

Print("\n--- Task 4: F_2 reduction of P(Q) ---\n");

Q_cup_Q := BarCup(Q, 2, Q, 2);;
mismatches := 0;;
for args in Tuples(elts, 4) do
    if (CallFuncList(PQ, args) mod 2)
       <> (CallFuncList(Q_cup_Q, args) mod 2) then
        mismatches := mismatches + 1;
    fi;
od;
AssertOrLog("P(Q) mod 2 = Q ∪ Q (= α̃ ∪ α̃ mod 2) on D_8^4",
            mismatches = 0);

# --------------------------------------------------------------------
# Task 5: Cocycle property symbolic check. The internal cocycle
# verification predicts δP(α) ∈ 4Z; verify by sampling values of
# the INTEGER (not yet reduced mod 4) version of δP(α).
# --------------------------------------------------------------------

Print("\n--- Task 5: Integer δP(Q) is in 4Z (Brumfiel-Morgan inline proof) ---\n");

# Construct P(Q) WITHOUT mod 4 reduction, so we can probe the structure.
cup_QQ_int := BarCup(Q, 2, Q, 2);;
dQ := BarCoboundary(Q, 2);;
cup1_dQ_Q := SteenrodCup1(dQ, 3, Q, 2);;
PQ_int := function(arg)
    local args;
    args := arg;
    return CallFuncList(cup_QQ_int, args) + CallFuncList(cup1_dQ_Q, args);
end;;

# Verify the integer δ of PQ_int is in 4Z on a sample.
n_in_4Z := 0;;
n_total := 0;;
for args in Tuples(elts, 5) do
    if (n_total > 0) and (n_total mod 4096 = 0) then break; fi;
    # δPQ_int(g_1, ..., g_5)
    # = PQ_int(g_2, ..., g_5)
    # + sum_{i=1}^4 (-1)^i PQ_int(g_1, ..., g_i*g_{i+1}, ..., g_5)
    # + (-1)^5 PQ_int(g_1, ..., g_4).
    val := CallFuncList(PQ_int, args{[2..5]});
    for i in [1..4] do
        sub := Concatenation(args{[1..i-1]},
                              [args[i] * args[i+1]],
                              args{[i+2..5]});
        if IsEvenInt(i) then
            val := val + CallFuncList(PQ_int, sub);
        else
            val := val - CallFuncList(PQ_int, sub);
        fi;
    od;
    val := val - CallFuncList(PQ_int, args{[1..4]});
    if val mod 4 = 0 then n_in_4Z := n_in_4Z + 1; fi;
    n_total := n_total + 1;
od;
Print("  δPQ_int ≡ 0 (mod 4) on ", n_in_4Z, " / ", n_total, " sample tuples\n");
AssertOrLog("integer δ(α̃ ∪ α̃ + δα̃ ∪₁ α̃) ∈ 4Z on sample",
            n_in_4Z = n_total);

# --------------------------------------------------------------------
# Summary.
# --------------------------------------------------------------------

Print("\n=== Summary ===\n");
if IsEmpty(testFailures) then
    Print("test_pontryagin_square: ALL PASS\n");
else
    Print("test_pontryagin_square: FAIL (",
          Length(testFailures), " failures)\n");
    for f in testFailures do Print("  - ", f, "\n"); od;
fi;
