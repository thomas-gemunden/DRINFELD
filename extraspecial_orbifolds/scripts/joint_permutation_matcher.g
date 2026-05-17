# joint_permutation_matcher.g
#
# K-4a-T1 (issue #192): reusable permutation matcher for two pairs of
# modular data (S, T).
#
# Algorithm (signature-pruned backtracking) extracted from the top-level
# script `q8_extension_type/scripts/find_permutation.g`, which was written
# during the Q_8 extension-type investigation. The original is a
# one-shot stdout-printing script tied to Q_8; this file lifts the body
# into a reusable callable with a structured return value, so downstream
# classifiers (e.g. ClassifyOnQ8 in q8_classifier.g, and an eventual
# ClassifyOnD8) can call it without duplicating the algorithm.
#
# PUBLIC API
# ----------
#   JointPermutationMatcher(S1, T1, S2, T2)
#
# Given two pairs of modular data
#     (S1, T1), (S2, T2)
# for some rank-N modular tensor categories of the same rank, search for
# a permutation pi : {1, ..., N} -> {1, ..., N} such that
#     S2[i][j]  = S1[pi(i)][pi(j)]    for all i, j in {1, ..., N},
#     T2[i]     = T1[pi(i)]           for all i in {1, ..., N}.
# Return value: a record with fields
#     pi      -- the permutation as a list (entry i = pi(i)), or `fail`
#                if no such permutation exists,
#     ok      -- boolean (= (pi <> fail)),
#     reason  -- a short string explaining why ok=false, present only
#                when !ok.
#
# Inputs S1, S2 must be square matrices of cyclotomics of the same
# dimension N >= 1. Inputs T1, T2 may be either a vector (DiagonalOfMat
# applied) or a DiagonalMat; this function normalises both internally to
# a vector form, so callers may freely pass `LoadModularData(...).T`
# (which is a DiagonalMat — see CLAUDE.md) without preprocessing.
#
# ALGORITHM
# ---------
# 1.  Signature pruning. For each row i compute a signature
#         sig[i] = [ T[i], SortedList(S[i]) ].
#     Candidates for pi^-1(i) (i.e. for the value pi(i)) are the rows of
#     S1 whose signature matches sig2[i].
# 2.  Order rows of S2 by ascending |candidates|, so the search tries
#     the most constrained rows first (fail-fast).
# 3.  Backtrack. At each step pick j from candidates[i]; check
#     consistency with already-assigned rows by verifying
#         S2[i][k] = S1[j][assigned[k]]    for all assigned k.
#     This eliminates whole subtrees early without waiting for a full
#     assignment.
# 4.  At the leaf verify the full S equation
#         S2[i][j] = S1[assigned[i]][assigned[j]]   for all i, j.
#     This is largely redundant with the per-step check but cheap and
#     belt-and-braces.
#
# Complexity is exponential in pathological cases but in practice Q_8
# (rank 22) and D_8 (rank 22) run in well under a second.
#
# CONVENTIONS
# -----------
# Uses GAP 1-based indexing throughout. All `local` variables are
# explicitly declared (per CLAUDE.md). Returns a `rec` rather than
# printing to stdout (cf. `find_permutation.g`).

JointPermutationMatcher := function(S1, T1, S2, T2)
    local n, n1, T1vec, T2vec, sig1, sig2, candidates, search, found,
          orderedRows, i, j, ok, S2dim;

    # ---- Normalise T arguments to vector form ----
    # `LoadModularData(...).T` returns a DiagonalMat; the find_permutation
    # script does `DiagonalOfMat(...)` at the call site. We accept either
    # form and convert to a flat list internally.
    if IsMatrix(T1) then
        T1vec := DiagonalOfMat(T1);
    else
        T1vec := T1;
    fi;
    if IsMatrix(T2) then
        T2vec := DiagonalOfMat(T2);
    else
        T2vec := T2;
    fi;

    # ---- Shape checks ----
    n  := Length(T2vec);
    n1 := Length(T1vec);
    if n <> n1 then
        return rec(
            pi     := fail,
            ok     := false,
            reason := Concatenation(
                "rank mismatch: |T1| = ", String(n1),
                ", |T2| = ", String(n))
        );
    fi;
    if n = 0 then
        # Vacuous: the empty permutation matches the empty pair.
        return rec(pi := [], ok := true);
    fi;
    if Length(S1) <> n then
        return rec(
            pi     := fail,
            ok     := false,
            reason := Concatenation(
                "rank mismatch: |T1| = ", String(n),
                ", #rows(S1) = ", String(Length(S1)))
        );
    fi;
    if Length(S2) <> n then
        return rec(
            pi     := fail,
            ok     := false,
            reason := Concatenation(
                "rank mismatch: |T2| = ", String(n),
                ", #rows(S2) = ", String(Length(S2)))
        );
    fi;
    S2dim := Length(S2[1]);
    if S2dim <> n or Length(S1[1]) <> n then
        return rec(
            pi     := fail,
            ok     := false,
            reason := "S1 or S2 is not square of rank |T|."
        );
    fi;

    # ---- Cheap necessary check: T-multisets must agree ----
    if SortedList(T1vec) <> SortedList(T2vec) then
        return rec(
            pi     := fail,
            ok     := false,
            reason := "T-multisets differ; no permutation can match T."
        );
    fi;

    # ---- Step 1: per-row signatures and candidate sets ----
    # sig[i] is the (T_i, sorted S-row_i) fingerprint. The candidate set
    # for "what does row i of S2 map FROM in S1" is the set of rows j of
    # S1 with sig1[j] = sig2[i].
    sig1 := List([1..n], i -> [T1vec[i], SortedList(S1[i])]);
    sig2 := List([1..n], i -> [T2vec[i], SortedList(S2[i])]);
    candidates := List([1..n],
                       i -> Filtered([1..n], j -> sig2[i] = sig1[j]));

    # Per-row necessary condition: at least one candidate.
    for i in [1..n] do
        if candidates[i] = [] then
            return rec(
                pi     := fail,
                ok     := false,
                reason := Concatenation(
                    "no candidate for S2 row ", String(i),
                    " under (T, sorted-S-row) signature.")
            );
        fi;
    od;

    # ---- Step 2: backtracking search ----
    # `assigned[i] = j` means pi(i) = j (row i of S2 corresponds to row j
    # of S1). `remaining` is the order in which we fill in rows of S2;
    # `used` is the set of values already taken in S1 (no two rows of S2
    # may map to the same S1 row).
    search := function(assigned, remaining, used)
        local i, j, ok_local, k, sub;
        if remaining = [] then
            # Leaf: verify full S equation.
            for i in [1..n] do
                for j in [1..n] do
                    if S2[i][j] <> S1[assigned[i]][assigned[j]] then
                        return fail;
                    fi;
                od;
            od;
            return assigned;
        fi;
        i := remaining[1];
        for j in candidates[i] do
            if not j in used then
                assigned[i] := j;
                ok_local := true;
                # Check consistency with already-assigned rows.
                for k in [1..n] do
                    if IsBound(assigned[k])
                       and S2[i][k] <> S1[j][assigned[k]] then
                        ok_local := false;
                        break;
                    fi;
                od;
                if ok_local then
                    AddSet(used, j);
                    sub := search(assigned,
                                  remaining{[2..Length(remaining)]},
                                  used);
                    if sub <> fail then
                        return sub;
                    fi;
                    RemoveSet(used, j);
                fi;
                Unbind(assigned[i]);
            fi;
        od;
        return fail;
    end;

    # Order rows by ascending candidate count (fail-fast).
    orderedRows := List(
        SortedList(List([1..n], i -> [Length(candidates[i]), i])),
        p -> p[2]);

    found := search([], orderedRows, []);

    if found = fail then
        return rec(
            pi     := fail,
            ok     := false,
            reason := "no permutation aligns (S, T)."
        );
    else
        return rec(
            pi := found,
            ok := true
        );
    fi;
end;;
