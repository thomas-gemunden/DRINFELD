Read("../../src/modular_data.g");

data1 := LoadModularData(8, 4, 1);;
S1 := data1.S;; T1 := DiagonalOfMat(data1.T);;
n := Length(T1);;

# Same backtracking as before, factored into a function.
FindEquivPerm := function(Sa, Ta, Sb, Tb)
    local n, sigA, sigB, candidates, search, found, orderedRows, result;
    n := Length(Ta);
    sigA := List([1..n], i -> [Ta[i], SortedList(Sa[i])]);
    sigB := List([1..n], i -> [Tb[i], SortedList(Sb[i])]);
    # We want: Sb[i][j] = Sa[pi(i)][pi(j)], Tb[i] = Ta[pi(i)]
    candidates := List([1..n], i -> Filtered([1..n], j -> sigB[i] = sigA[j]));
    search := function(assigned, remaining, used)
        local i, j, ok, k;
        if remaining = [] then
            for i in [1..n] do for j in [1..n] do
                if Sb[i][j] <> Sa[assigned[i]][assigned[j]] then return fail; fi;
            od; od;
            return assigned;
        fi;
        i := remaining[1];
        for j in candidates[i] do
            if not j in used then
                assigned[i] := j;
                ok := true;
                for k in [1..n] do
                    if IsBound(assigned[k]) and Sb[i][k] <> Sa[j][assigned[k]] then
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
    end;
    orderedRows := List(SortedList(List([1..n], i -> [Length(candidates[i]), i])), p -> p[2]);
    return search([], orderedRows, []);
end;;

# Test 1: data1 vs itself -> must find identity (or some autom)
Print("\n--- Test 1: data1 vs data1 (should find a permutation, ideally id) ---\n");
r := FindEquivPerm(S1, T1, S1, T1);;
Print("Result: ", r, "\n");
Print("Is identity: ", r = [1..n], "\n");

# Test 2: data1 vs (data1 with random permutation applied)
sigma := (1,5,10)(2,7);;
Print("\n--- Test 2: data1 vs sigma(data1), sigma = ", sigma, " ---\n");
sigmaList := ListPerm(sigma, n);;
Sshuffled := List([1..n], i -> List([1..n], j -> S1[sigmaList[i]][sigmaList[j]]));;
Tshuffled := List([1..n], i -> T1[sigmaList[i]]);;
r := FindEquivPerm(S1, T1, Sshuffled, Tshuffled);;
Print("Result list: ", r, "\n");
Print("Expected (sigma as list): ", sigmaList, "\n");
Print("Matches: ", r = sigmaList, "\n");

# Test 3: re-run real comparison.
data2 := LoadModularData(8, 4, 2);;
S2 := data2.S;; T2 := DiagonalOfMat(data2.T);;
Print("\n--- Test 3: data1 vs data2 (the real question) ---\n");
r := FindEquivPerm(S1, T1, S2, T2);;
Print("Result: ", r, "\n");

QUIT;
