# E_BRW m=3 step 2: build the structural representation of S for
# E_+(3) and verify reconstruction against the dense S.
#
# Strategy:
#   1. Identify canonical pair (i_g, j_g) for each refined group g.
#   2. Save canonical block B_g from the dense S.
#   3. For each (i, j) in group g, find row+col permutations
#      (P_{i,j,g}, Q_{i,j,g}) such that
#          dense_block[i][j][k][l] = B_g[P(k)][Q(l)].
#   4. Verify reconstruction byte-equals the dense S.

Read("untwisted_modular_data.g");

G := SmallGroup(128, 2326);;
idx := BuildSimpleIndex(G);;
n_classes := Length(idx.classes);;

ClassifyTypes := function(idx)
    local types, i, rep, ord, sz;
    types := [];
    for i in [1..Length(idx.classes)] do
        rep := idx.reps[i];
        ord := Order(rep); sz := idx.class_sizes[i];
        if sz = 1 and ord = 1 then Add(types, "id");
        elif sz = 1 and ord = 2 then Add(types, "minus_one");
        elif ord = 2 then Add(types, "sigma2");
        elif ord = 4 then Add(types, "sigma_1sigma_2");
        else Add(types, "UNKNOWN"); fi;
    od;
    return types;
end;;
types := ClassifyTypes(idx);;

ComputeCommute := function(idx)
    local n, M, i, j;
    n := Length(idx.classes); M := NullMat(n, n);
    for i in [1..n] do for j in [1..n] do
        if idx.reps[i] * idx.reps[j] = idx.reps[j] * idx.reps[i] then
            M[i][j] := 1;
        fi;
    od; od;
    return M;
end;;
commute := ComputeCommute(idx);;

If_ := function(cond, a, b) if cond then return a; else return b; fi; end;;

GroupKey := function(i, j)
    return Concatenation(types[i], "/", types[j], "/", String(commute[i][j]),
                         "/", If_(i = j, "diag", "off"));
end;;

GetBlock := function(S, idx, i, j)
    local off_i, off_j;
    off_i := idx.global_offset[i]; off_j := idx.global_offset[j];
    return List([1..idx.num_irreps[i]], k ->
        List([1..idx.num_irreps[j]], l -> S[off_i + k][off_j + l]));
end;;

# --- Find row + col permutation between A and B ---
# Returns rec(P, Q) such that B[k][l] = A[P[k]][Q[l]], or fail.
FindRowColPerm := function(A, B)
    local m, n, candidates_row, k, k0, ok, P, Q, l, match_col, search,
          found_perm;
    m := Length(A); n := Length(A[1]);

    # Quick check: same canonical form.
    if SortedList(TransposedMat(SortedList(A))) <> SortedList(TransposedMat(SortedList(B))) then
        return fail;
    fi;

    # Backtracking search.  We assign P[k] -> row of A.  For each
    # assignment of all P, check if the corresponding column permutation Q
    # exists by matching rows.
    found_perm := fail;
    search := function(P_partial, used_rows, k)
        local row_B, row_A_candidate, sorted, candidates, k0, q_perm,
              col_assigned, l, j, ok, match;
        if k > m then
            # All rows assigned; now find Q.
            # B[k0][l] = A[P[k0]][Q[l]] for all k0, l.
            # Pick first row to determine Q candidates.
            row_B := B[1];
            row_A_candidate := A[P_partial[1]];
            # Q[l] is the position in row_A_candidate of value row_B[l].
            # If duplicates, multiple options; try first that's consistent
            # across all rows.
            q_perm := [];
            col_assigned := List([1..n], i -> false);
            for l in [1..n] do
                # Find a column j of A's row-A_candidate that:
                # - has value = row_B[l]
                # - hasn't been assigned yet
                # - is consistent with all OTHER rows
                ok := false;
                for j in [1..n] do
                    if not col_assigned[j] and row_A_candidate[j] = row_B[l] then
                        # Check consistency
                        match := true;
                        for k0 in [2..m] do
                            if A[P_partial[k0]][j] <> B[k0][l] then
                                match := false; break;
                            fi;
                        od;
                        if match then
                            q_perm[l] := j;
                            col_assigned[j] := true;
                            ok := true; break;
                        fi;
                    fi;
                od;
                if not ok then return; fi;
            od;
            found_perm := rec(P := P_partial, Q := q_perm);
            return;
        fi;
        # Try each unused row of A as P[k].
        sorted := SortedList(B[k]);
        for k0 in [1..m] do
            if not used_rows[k0] and SortedList(A[k0]) = sorted then
                P_partial[k] := k0;
                used_rows[k0] := true;
                search(P_partial, used_rows, k + 1);
                if found_perm <> fail then return; fi;
                P_partial[k] := 0;
                used_rows[k0] := false;
            fi;
        od;
    end;
    search([], List([1..m], i -> false), 1);
    return found_perm;
end;;

# --- Load dense S ---
Print("Loading dense S...\n");
Read("../computed/E_plus_3/S.g");

# --- Build the structural rep ---
Print("\nBuilding structural rep...\n");
tic := Runtime();;
groups := rec();
canonical_blocks := rec();   # group_key -> canonical block
canonical_pairs := rec();    # group_key -> (i_g, j_g)
permutations := [];          # list parallel to all (i, j); permutations[idx] = rec(P, Q)
pair_to_group := rec();      # "i,j" -> group key

for i in [1..n_classes] do
    for j in [1..n_classes] do
        key := GroupKey(i, j);
        if not IsBound(groups.(key)) then
            groups.(key) := [];
            # First pair = canonical
            canonical_pairs.(key) := [i, j];
            canonical_blocks.(key) := GetBlock(S, idx, i, j);
        fi;
        Add(groups.(key), [i, j]);
    od;
od;
Print("  ", Length(RecNames(groups)), " refined groups; ",
      "canonical blocks saved.\n");

# Find permutations for each (i, j) relative to its canonical.
n_pairs := n_classes * n_classes;;
n_done := 0;;
n_failed := 0;;
perms_lookup := List([1..n_classes], i -> List([1..n_classes], j -> 0));;
tic2 := Runtime();;
for i in [1..n_classes] do
    for j in [1..n_classes] do
        key := GroupKey(i, j);
        if [i, j] = canonical_pairs.(key) then
            perms_lookup[i][j] := "canonical";
        else
            B := GetBlock(S, idx, i, j);
            A := canonical_blocks.(key);
            r := FindRowColPerm(A, B);
            if r = fail then
                n_failed := n_failed + 1;
                Print("  FAIL at (", i, ", ", j, ") group ", key, "\n");
            else
                perms_lookup[i][j] := r;
            fi;
        fi;
        n_done := n_done + 1;
    od;
od;
toc2 := Runtime() - tic2;;
Print("  permutation discovery: ", toc2/1000., " s, ", n_failed, " failures\n");

# --- Reconstruct and verify ---
Print("\nReconstructing dense S from structural rep...\n");
tic := Runtime();;
S_reconstructed := List([1..idx.rank], i -> List([1..idx.rank], j -> 0));;
for i in [1..n_classes] do
    for j in [1..n_classes] do
        key := GroupKey(i, j);
        canonical := canonical_blocks.(key);
        off_i := idx.global_offset[i];
        off_j := idx.global_offset[j];
        if perms_lookup[i][j] = "canonical" then
            for k in [1..idx.num_irreps[i]] do
                for l in [1..idx.num_irreps[j]] do
                    S_reconstructed[off_i + k][off_j + l] := canonical[k][l];
                od;
            od;
        else
            P := perms_lookup[i][j].P;
            Q := perms_lookup[i][j].Q;
            for k in [1..idx.num_irreps[i]] do
                for l in [1..idx.num_irreps[j]] do
                    S_reconstructed[off_i + k][off_j + l] := canonical[P[k]][Q[l]];
                od;
            od;
        fi;
    od;
od;
toc := Runtime() - tic;;
Print("  reconstruction: ", toc/1000., " s\n");

Print("\nVerifying reconstruction == original dense S...\n");
match := S_reconstructed = S;;
Print("  EQUAL: ", match, "\n");

if match then
    Print("\n=== STRUCTURAL REP VALIDATED for E_+(3) ===\n");
    # Save structural rep.
    outdir := "../computed/E_plus_3/structural";;
    Exec(Concatenation("mkdir -p ", outdir));
    PrintTo(Concatenation(outdir, "/canonical_blocks.g"),
        "canonical_blocks_data := rec(\n");
    keys := SortedList(RecNames(canonical_blocks));
    for k in keys do
        AppendTo(Concatenation(outdir, "/canonical_blocks.g"),
            "    ",  ReplacedString(k, "/", "_"), " := ",
            canonical_blocks.(k), ",\n");
    od;
    AppendTo(Concatenation(outdir, "/canonical_blocks.g"), ");;\n");
    Print("Wrote ", outdir, "/canonical_blocks.g\n");
fi;

QUIT;
