# Test whether Q_8 modular data for cocycles 1 (trivial) and 2 (order 2) are equivalent.
Read("../../src/modular_data.g");

data1 := LoadModularData(8, 4, 1);
data2 := LoadModularData(8, 4, 2);

Print("\n=== Direct equality ===\n");
Print("S1 = S2: ", data1.S = data2.S, "\n");
Print("T1 = T2: ", data1.T = data2.T, "\n");

Print("\n=== T-spectrum comparison ===\n");
t1 := DiagonalOfMat(data1.T);
t2 := DiagonalOfMat(data2.T);
Print("Sorted T1: ", SortedList(t1), "\n");
Print("Sorted T2: ", SortedList(t2), "\n");
Print("Multisets equal: ", SortedList(t1) = SortedList(t2), "\n");

Print("\n=== S-diagonal comparison ===\n");
s1 := DiagonalOfMat(data1.S);
s2 := DiagonalOfMat(data2.S);
Print("Sorted S1 diag: ", SortedList(s1), "\n");
Print("Sorted S2 diag: ", SortedList(s2), "\n");
Print("S-diag multisets equal: ", SortedList(s1) = SortedList(s2), "\n");

Print("\n=== BasicEquivalentModularDataTests ===\n");
result := BasicEquivalentModularDataTests(data1, data2);
Print("Equivalent (heuristic): ", result, "\n");

# Also do a stronger test: see if sorted multiset of (T_i, sorted-row-i-of-S) pairs match
Print("\n=== Pair (T_i, sorted S-row_i) multiset comparison ===\n");
pairs1 := List([1..Length(t1)], i -> [t1[i], SortedList(data1.S[i])]);
pairs2 := List([1..Length(t2)], i -> [t2[i], SortedList(data2.S[i])]);
Sort(pairs1);
Sort(pairs2);
Print("Stronger row-multiset test equal: ", pairs1 = pairs2, "\n");

QUIT;
