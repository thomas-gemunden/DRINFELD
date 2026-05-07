Read("../../src/modular_data.g");
data1 := LoadModularData(8, 4, 1);;
S1 := data1.S;; T1 := DiagonalOfMat(data1.T);;
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

count := 0;
search_all := function(N1, T1, N2, T2, assigned, remaining, used)
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
                search_all(N1, T1, N2, T2, assigned, remaining{[2..Length(remaining)]}, used);
                RemoveSet(used, j);
            fi;
            Unbind(assigned[i]);
        fi;
    od;
end;;

# Sanity 1: data1 vs data1.
count := 0;;
search_all(N1, T1, N1, T1, [], [1..n], []);;
Print("Aut(N1, T1) count = ", count, "\n");

# data2 vs data2.
data2 := LoadModularData(8, 4, 2);;
S2 := data2.S;; T2 := DiagonalOfMat(data2.T);;
N2 := Verlinde(S2);;
count := 0;;
search_all(N2, T2, N2, T2, [], [1..n], []);;
Print("Aut(N2, T2) count = ", count, "\n");

# Confirm: count of data1 -> data2 fusion+T permutations
count := 0;;
search_all(N1, T1, N2, T2, [], [1..n], []);;
Print("(N1,T1) -> (N2,T2) fusion+T permutation count = ", count, "\n");

QUIT;
