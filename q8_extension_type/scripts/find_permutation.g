# Search for an explicit permutation π such that
#     S1[π(i)][π(j)] = S2[i][j]    and    T1[π(i)] = T2[i]
# i.e. (S1, T1) ≡ (S2, T2) under simultaneous row+column permutation.

Read("../../src/modular_data.g");

data1 := LoadModularData(8, 4, 1);
data2 := LoadModularData(8, 4, 2);
S1 := data1.S;; S2 := data2.S;;
T1 := DiagonalOfMat(data1.T);; T2 := DiagonalOfMat(data2.T);;
n := Length(T1);;
Print("Rank: ", n, "\n");

# Step 1. Initial candidates per row from (T_i, sorted S-row_i) signature.
sig1 := List([1..n], i -> [T1[i], SortedList(S1[i])]);;
sig2 := List([1..n], i -> [T2[i], SortedList(S2[i])]);;

candidates := List([1..n], i -> Filtered([1..n], j -> sig2[i] = sig1[j]));;
Print("Candidate counts (S2 row -> S1 rows): ", List(candidates, Length), "\n");
Print("Sum log2 of candidate counts: ", Float(Sum(candidates, c -> Log2(Float(Length(c))))), "\n");

# Step 2. Backtrack.
found := fail;;
search := function(assigned, remaining, used)
    local i, j, ok, k;
    if remaining = [] then
        # Verify the full S equation.
        for i in [1..n] do for j in [1..n] do
            if S2[i][j] <> S1[assigned[i]][assigned[j]] then
                return fail;
            fi;
        od; od;
        return assigned;
    fi;
    i := remaining[1];
    for j in candidates[i] do
        if not j in used then
            assigned[i] := j;
            ok := true;
            # Check consistency with already-assigned rows.
            for k in [1..n] do
                if IsBound(assigned[k]) and S2[i][k] <> S1[j][assigned[k]] then
                    ok := false; break;
                fi;
            od;
            if ok then
                AddSet(used, j);
                found := search(assigned, remaining{[2..Length(remaining)]}, used);
                if found <> fail then return found; fi;
                RemoveSet(used, j);
            fi;
            Unbind(assigned[i]);
        fi;
    od;
    return fail;
end;;

# Order rows by ascending candidate count (fail fast).
orderedRows := SortedList(List([1..n], i -> [Length(candidates[i]), i]));;
orderedRows := List(orderedRows, p -> p[2]);;
Print("Search order (rows of S2): ", orderedRows, "\n");

result := search([], orderedRows, []);;
if result = fail then
    Print("\n*** NO PERMUTATION FOUND -- modular data are NOT equivalent ***\n");
else
    Print("\n=== FOUND PERMUTATION pi : i (in S2) -> pi(i) (in S1) ===\n");
    Print("pi as list (entry i = pi(i)): ", result, "\n");
    pi := PermList(result);
    Print("As GAP permutation: ", pi, "\n");
    Print("Cycle structure: ", CycleStructurePerm(pi), "\n");
    Print("Order: ", Order(pi), "\n");

    # Verify.
    P := PermutationMat(pi^-1, n);
    S2perm := P * S1 * TransposedMat(P);
    T2perm := List([1..n], i -> T1[result[i]]);
    Print("\nVerification: S2 = P S1 P^-1: ", S2perm = S2, "\n");
    Print("Verification: T2[i] = T1[pi(i)]: ", T2perm = T2, "\n");
fi;

QUIT;
