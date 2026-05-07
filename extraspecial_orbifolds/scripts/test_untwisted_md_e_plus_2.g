# Verify the direct untwisted-modular-data library against the
# precomputed Gruen output for E_+(2) = SmallGroup(32, 49).

Read("untwisted_modular_data.g");
Read("../../src/modular_data.g");        # for LoadModularData
Read("predict_e_plus_m.g");

G := SmallGroup(32, 49);;
Print("=== Direct computation of Mod(D^1(E_+(2))) ===\n");
tic := Runtime();;
data := ComputeUntwistedModularData(G);;
toc := Runtime() - tic;;
Print("Time: ", toc / 1000., " s\n");
Print("Rank: ", data.idx.rank, "\n");

# T-spectrum sanity
Tcollect := Collected(data.T);;
Print("\nT-multiset (computed):\n");
for pair in Tcollect do
    Print("  T = ", pair[1], "  multiplicity ", pair[2], "\n");
od;

Print("\nAnalytical prediction (m=2):\n");
pred := PredictE_plus_m(2);;
Print("  T = 1     : ", pred.TMultiset.one, "\n");
Print("  T = -1    : ", pred.TMultiset.minus_one, "\n");
Print("  T = i     : ", pred.TMultiset.i, "\n");
Print("  T = -i    : ", pred.TMultiset.minus_i, "\n");

# Cross-check against precomputed Gruen.
gruen := LoadModularData(32, 49, 1);;
gruenT := DiagonalOfMat(gruen.T);;
Print("\n=== Cross-check vs Gruen modular_data/32/49/1.txt ===\n");
Print("Rank match: ", Length(gruenT) = data.idx.rank, "\n");
Print("T-multiset (computed) = T-multiset (Gruen): ",
      SortedList(data.T) = SortedList(gruenT), "\n");

# Find a permutation aligning (S_direct, T_direct) with (S_gruen, T_gruen).
FindEquivPerm := function(Sa, Ta, Sb, Tb)
    local n, sigA, sigB, candidates, search;
    n := Length(Ta);
    sigA := List([1..n], i -> [Ta[i], SortedList(Sa[i])]);
    sigB := List([1..n], i -> [Tb[i], SortedList(Sb[i])]);
    candidates := List([1..n], i -> Filtered([1..n], j -> sigB[i] = sigA[j]));
    search := function(assigned, remaining, used)
        local i, j, ok, k, found;
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

Print("\nSearching for permutation aligning direct (S,T) with Gruen (S,T)...\n");
tic := Runtime();;
perm := FindEquivPerm(data.S, data.T, gruen.S, gruenT);;
toc := Runtime() - tic;;
Print("Time: ", toc / 1000., " s\n");
Print("Permutation found: ", perm <> fail, "\n");

# Modular consistency: S^2 = (ST)^3 (with T as DiagonalMat).
Tmat := DiagonalMat(data.T);;
LHS := data.S^2;;
RHS := (data.S * Tmat)^3;;
Print("\n=== Modularity / unitarity sanity ===\n");
Print("S^2 = (ST)^3: ", LHS = RHS, "\n");

# Unitarity sample: row 1 norm squared
norm1 := Sum(data.S[1], x -> x * ComplexConjugate(x));;
Print("Sum |S[1][a]|^2 = ", norm1, " (expect 1)\n");

# T order divides exp(G) (= 4 for E_+(m))
Tord := Lcm(List(data.T, t -> Order(t)));;
Print("LCM of T orders: ", Tord, " (expect divides ", Exponent(G), ")\n");

QUIT;
