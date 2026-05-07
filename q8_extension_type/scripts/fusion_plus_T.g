# Find permutation pi making BOTH the fusion ring AND the T-vector
# match -- but NOT necessarily S. This is the natural "weakest" modular-data
# equivalence in some physics literature (S is sometimes considered a
# derived object up to fusion-ring automorphism).

Read("../../src/modular_data.g");

data1 := LoadModularData(8, 4, 1);;
data2 := LoadModularData(8, 4, 2);;
S1 := data1.S;; T1 := DiagonalOfMat(data1.T);;
S2 := data2.S;; T2 := DiagonalOfMat(data2.T);;
n := Length(T1);;

Verlinde := function(S)
    local n, N, i, j, k, a, val;
    n := Length(S);
    N := List([1..n], i -> List([1..n], j -> List([1..n], k -> 0)));
    for i in [1..n] do for j in [1..n] do for k in [1..n] do
        val := 0;
        for a in [1..n] do
            if S[1][a] <> 0 then
                val := val + S[i][a]*S[j][a]*ComplexConjugate(S[k][a])/S[1][a];
            fi;
        od;
        N[i][j][k] := val;
    od; od; od;
    return N;
end;;

N1 := Verlinde(S1);;
N2 := Verlinde(S2);;

# Search for pi : i -> pi(i) such that N2[i][j][k] = N1[pi(i)][pi(j)][pi(k)]
# AND T2[i] = T1[pi(i)].
FindFusionTPerm := function(N1, T1, N2, T2)
    local n, sig1, sig2, candidates, search;
    n := Length(N1);
    # Signature combines T value and sorted fusion data
    sig1 := List([1..n], i -> [T1[i], SortedList(List([1..n], j -> SortedList(N1[i][j])))]);
    sig2 := List([1..n], i -> [T2[i], SortedList(List([1..n], j -> SortedList(N2[i][j])))]);
    candidates := List([1..n], i -> Filtered([1..n], j -> sig2[i] = sig1[j]));
    search := function(assigned, remaining, used)
        local i, j, ok, k, l, found;
        if remaining = [] then
            for i in [1..n] do for j in [1..n] do for k in [1..n] do
                if N2[i][j][k] <> N1[assigned[i]][assigned[j]][assigned[k]] then return fail; fi;
            od; od; od;
            return assigned;
        fi;
        i := remaining[1];
        for j in candidates[i] do
            if not j in used then
                assigned[i] := j;
                ok := true;
                for k in [1..n] do for l in [1..n] do
                    if IsBound(assigned[k]) and IsBound(assigned[l]) and
                       N2[i][k][l] <> N1[j][assigned[k]][assigned[l]] then
                        ok := false; break;
                    fi;
                od; if not ok then break; fi; od;
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
    end;
    return search([], List(SortedList(List([1..n], i -> [Length(candidates[i]), i])), p -> p[2]), []);
end;;

Print("=== Fusion + T joint permutation search ===\n");
r := FindFusionTPerm(N1, T1, N2, T2);;
if r = fail then
    Print("  NO permutation aligns both fusion ring and T.\n");
else
    pi := PermList(r);
    Print("  FOUND: ", pi, "\n  list: ", r, "\n");
    Print("  Order: ", Order(pi), ", cycles: ", CycleStructurePerm(pi), "\n");
    # Sanity
    permT := List([1..n], i -> T1[r[i]]);
    permN := List([1..n], i -> List([1..n], j -> List([1..n], k -> N1[r[i]][r[j]][r[k]])));
    Print("  T match: ", permT = T2, "\n");
    Print("  N match: ", permN = N2, "\n");
    permS := List([1..n], i -> List([1..n], j -> S1[r[i]][r[j]]));
    Print("  S match (would be too good): ", permS = S2, "\n");
fi;

# Also: enumerate all permutations satisfying fusion+T to see freedom
Print("\n=== Counting fusion+T permutations ===\n");
count := 0;
search_all := function(assigned, remaining, used)
    local i, j, ok, k, l;
    if remaining = [] then
        for i in [1..n] do for j in [1..n] do for k in [1..n] do
            if N2[i][j][k] <> N1[assigned[i]][assigned[j]][assigned[k]] then return; fi;
        od; od; od;
        count := count + 1;
        return;
    fi;
    i := remaining[1];
    for j in [1..n] do
        if T1[j] = T2[i] and not j in used then
            assigned[i] := j;
            ok := true;
            for k in [1..n] do for l in [1..n] do
                if IsBound(assigned[k]) and IsBound(assigned[l]) and
                   N2[i][k][l] <> N1[j][assigned[k]][assigned[l]] then
                    ok := false; break;
                fi;
            od; if not ok then break; fi; od;
            if ok then
                AddSet(used, j);
                search_all(assigned, remaining{[2..Length(remaining)]}, used);
                RemoveSet(used, j);
            fi;
            Unbind(assigned[i]);
        fi;
    od;
end;;
search_all([], [1..n], []);
Print("  Number of permutations satisfying fusion+T: ", count, "\n");

QUIT;
