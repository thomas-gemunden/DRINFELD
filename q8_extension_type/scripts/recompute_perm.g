Read("../../src/modular_data.g");

G := SmallGroup(8, 4);;
R := ResolutionFiniteGroup(G, 4);;
K := TensorWithIntegers(R);;
UCT := UniversalCoefficientsTheorem(K, 3);;
m := UCT.exponent;;

storedCocycles := ReadAsFunction("Modular_Data/8/4/3-cocycles.txt")();;

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

for i in [1, 2] do
    Print("\n=== Cocycle ", i, " ===\n");
    vec := storedCocycles[i];
    val := Gcd(Concatenation([m], Filtered(vec, x -> x <> 0)));
    if Filtered(vec, x -> x <> 0) = [] then val := m; fi;
    exp := m / val;
    omega := StandardCocycle(R, vec, 3, m);
    fresh := ComputeModularData(G, omega, val, exp);
    stored := LoadModularData(8, 4, i);
    Tfresh := DiagonalOfMat(fresh.T);
    Tstored := DiagonalOfMat(stored.T);
    Print("  T-multisets equal: ", SortedList(Tfresh) = SortedList(Tstored), "\n");
    perm := FindEquivPerm(stored.S, Tstored, fresh.S, Tfresh);
    Print("  fresh ≡ stored under permutation: ", perm <> fail, "\n");
od;

# Also: do two FRESH runs of cocycle 2 give equivalent (but possibly different ordering) results?
Print("\n=== Two fresh runs of cocycle 2 ===\n");
vec := storedCocycles[2];;
val := Gcd(Concatenation([m], Filtered(vec, x -> x <> 0)));;
exp := m / val;;
omega := StandardCocycle(R, vec, 3, m);;
fresh1 := ComputeModularData(G, omega, val, exp);;
fresh2 := ComputeModularData(G, omega, val, exp);;
T1 := DiagonalOfMat(fresh1.T);;
T2 := DiagonalOfMat(fresh2.T);;
Print("  Same: ", fresh1.S = fresh2.S and T1 = T2, "\n");
perm := FindEquivPerm(fresh1.S, T1, fresh2.S, T2);;
Print("  Equivalent under permutation: ", perm <> fail, "\n");

# Now the BIG QUESTION: fresh cocycle-1 vs fresh cocycle-2 — are they equivalent?
Print("\n=== Fresh cocycle 1 vs fresh cocycle 2 ===\n");
vec1 := storedCocycles[1];;
val1 := m;; exp1 := 1;;  # trivial cocycle
omega1 := StandardCocycle(R, vec1, 3, m);;
fr1 := ComputeModularData(G, omega1, val1, exp1);;
T1 := DiagonalOfMat(fr1.T);;
Print("  fresh trivial T-multiset: ", SortedList(T1), "\n");

vec2 := storedCocycles[2];;
val2 := Gcd(Concatenation([m], Filtered(vec2, x -> x <> 0)));;
exp2 := m / val2;;
omega2 := StandardCocycle(R, vec2, 3, m);;
fr2 := ComputeModularData(G, omega2, val2, exp2);;
T2 := DiagonalOfMat(fr2.T);;
Print("  fresh order-2 T-multiset: ", SortedList(T2), "\n");
Print("  T-multisets equal: ", SortedList(T1) = SortedList(T2), "\n");
perm := FindEquivPerm(fr1.S, T1, fr2.S, T2);;
Print("  fresh-trivial ≡ fresh-order-2 under permutation: ", perm <> fail, "\n");

QUIT;
