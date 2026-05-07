Read("../../src/modular_data.g");

data1 := LoadModularData(8, 4, 1);;
data2 := LoadModularData(8, 4, 2);;
S1 := data1.S;; T1 := DiagonalOfMat(data1.T);;
S2 := data2.S;; T2 := DiagonalOfMat(data2.T);;
n := Length(T1);;

# === Galois-twisted search ============================================
# Allow simultaneous complex conjugation. Since S is rational here,
# σ(S2) = S2; only T2 changes under σ.
T2bar := List(T2, ComplexConjugate);;

FindEquivPerm := function(Sa, Ta, Sb, Tb)
    local n, sigA, sigB, candidates, search, found;
    n := Length(Ta);
    sigA := List([1..n], i -> [Ta[i], SortedList(Sa[i])]);
    sigB := List([1..n], i -> [Tb[i], SortedList(Sb[i])]);
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
    return search([], List(SortedList(List([1..n], i -> [Length(candidates[i]), i])), p -> p[2]), []);
end;;

Print("=== Plain permutation: (S1,T1) ~ (S2,T2)? ===\n");
r := FindEquivPerm(S1, T1, S2, T2);;
Print("  result: ", r, "\n");

Print("\n=== Galois-twisted: (S1,T1) ~ (S2, σ(T2))? ===\n");
r := FindEquivPerm(S1, T1, S2, T2bar);;
Print("  result: ", r, "\n");

# === Fusion ring comparison via Verlinde =============================
# N_{ij}^k = Σ_a (S[i][a] S[j][a] conj(S[k][a]) / S[1][a])
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

# Sanity: integrality
allInt1 := ForAll(N1, x -> ForAll(x, y -> ForAll(y, z -> IsInt(z) and z >= 0)));;
allInt2 := ForAll(N2, x -> ForAll(x, y -> ForAll(y, z -> IsInt(z) and z >= 0)));;
Print("\n=== Fusion ring sanity ===\n");
Print("  N1 entries are non-neg integers: ", allInt1, "\n");
Print("  N2 entries are non-neg integers: ", allInt2, "\n");

# Compare fusion rings as multisets of fusion-vectors per simple object
# For each i, the multiset {[N[i][j][k]] : j, k} characterises the fusion of i.
fusionSig := function(N, i)
    return SortedList(List([1..Length(N)], j -> SortedList(N[i][j])));
end;;
sigs1 := SortedList(List([1..n], i -> fusionSig(N1, i)));;
sigs2 := SortedList(List([1..n], i -> fusionSig(N2, i)));;
Print("\n=== Fusion-ring per-object signature multisets ===\n");
Print("  Multisets equal: ", sigs1 = sigs2, "\n");

# Try permutation matching fusion rings (ignoring T)
FindFusionPerm := function(N1, N2)
    local n, sig1, sig2, candidates, search, found;
    n := Length(N1);
    sig1 := List([1..n], i -> SortedList(List([1..n], j -> SortedList(N1[i][j]))));
    sig2 := List([1..n], i -> SortedList(List([1..n], j -> SortedList(N2[i][j]))));
    candidates := List([1..n], i -> Filtered([1..n], j -> sig2[i] = sig1[j]));
    search := function(assigned, remaining, used)
        local i, j, ok, k, l;
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

Print("\n=== Fusion-ring permutation search ===\n");
fr := FindFusionPerm(N1, N2);;
Print("  result: ", fr, "\n");
if fr <> fail then
    pi := PermList(fr);
    Print("  As GAP perm: ", pi, "\n");
    Print("  Order: ", Order(pi), ", cycle struct: ", CycleStructurePerm(pi), "\n");
    # Now check whether this same pi also takes T1 to T2
    Tperm := List([1..n], i -> T1[fr[i]]);
    Print("  Does it also align T? T1[pi(i)] = T2[i]: ", Tperm = T2, "\n");
    # And how about S?
    Sperm := List([1..n], i -> List([1..n], j -> S1[fr[i]][fr[j]]));
    Print("  Does it also align S? S1[pi(i)][pi(j)] = S2[i][j]: ", Sperm = S2, "\n");
fi;

QUIT;
