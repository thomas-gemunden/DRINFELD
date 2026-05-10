# aut_nt_partition.g — initial partition for the Aut(N, T) engine.
#
# Task V-5a (issue #17, task #54).
#
# Background. Computing |Aut(N, T)| for a modular tensor category C with
# fusion ring N and modular T-matrix uses ordered-basis backtracking on
# {1, ..., r} where r is the rank (number of simples). Aut(N, T) consists
# of permutations σ of {1, ..., r} that
#   (a) preserve the T-eigenvalue at each simple, T_{σ(i)} = T_i, and
#   (b) preserve the fusion structure (N_{ij}^k = N_{σ(i),σ(j)}^{σ(k)}).
# Quantum dimension QD_i is an N-invariant (it is the Frobenius–Perron
# eigenvalue of the N_i fusion matrix), so σ also preserves QD.
#
# The cheapest pre-backtracking refinement of {1, ..., r} groups simples
# by their joint (T, QD) value. This file provides:
#
#   InitialPartition(N, T, QD)
#     N  : optional (unused in this initial refinement; passed in for
#          API symmetry — backtracking will need it later). May be
#          `fail`.
#     T  : a list of length r of T-eigenvalues (the diagonal of the
#          T-matrix). Cyclotomic entries; equality is GAP-=.
#     QD : a list of length r of quantum dimensions. May be cyclotomic
#          (golden ratio etc.) or rational.
#     Returns: a list of disjoint subsets of {1, ..., r} whose union is
#     {1, ..., r}, each subset being one (T, QD)-equivalence class. The
#     blocks are listed in a deterministic order (sorted by the string
#     form of their (T, QD) key), and indices inside a block are
#     ascending.
#
# Acceptance criteria.
#   * D(Q_8) — modular_data/8/4/1.txt — has 22 simples and the joint
#     (T, QD) partition has 5 blocks of sizes [8, 4, 4, 3, 3] (one
#     T=1, QD=1 block of size 8, then T-distinguished QD=2 blocks of
#     sizes 4, 4, 3, 3).
#   * D(E_+(2)) = D^1(E_+(2)) — modular_data/32/49/1.txt — has 184
#     simples with T-multiset {1^102, (-1)^70, i^6, (-i)^6}; the joint
#     (T, QD) partition refines this.
#
# Conventions.
#   * QD_i can be computed from S via QD_i = S[i][1] / S[1][1] when
#     simple 1 is the unit (the standard convention in modular_data.g).
#     The helper QuantumDimensionsFromS below performs this division.
#   * We deliberately accept arbitrary cyclotomics as T and QD values:
#     GAP's `=` on cyclotomics is sound, and we key on a stable string
#     form via String([T_i, QD_i]).
#
# This file installs four globals: QuantumDimensionsFromS,
# JointTQDKey, JointTQDClasses (alias of the main routine), and
# InitialPartition.

# ---- Quantum dimensions from the S-matrix ---------------------------
QuantumDimensionsFromS := function(S)
    local r, q1, i, qds;
    r := Length(S);
    if r = 0 then
        return [];
    fi;
    q1 := S[1][1];
    if q1 = 0 then
        Error("QuantumDimensionsFromS: S[1][1] is zero; cannot normalise.");
    fi;
    qds := [];
    for i in [1 .. r] do
        Add(qds, S[i][1] / q1);
    od;
    return qds;
end;

# ---- The joint partition --------------------------------------------
#
# We use a simple "collect-by-key" pass:
#   1. For each i ∈ {1, ..., r}, form key_i := [T_i, QD_i].
#   2. Group {1, ..., r} by equality of key_i. Two keys are considered
#      equal iff GAP-= says so.
#   3. Sort the resulting blocks by their key's string form (stable,
#      deterministic, independent of which simple was seen first).
#   4. Inside each block sort the indices ascending (they already are
#      by construction, but assert).
#
# Complexity: O(r^2) equality probes in the worst case, which is fine
# for r ≤ ~10^4 — the V-5b backtracking will dominate any realistic
# runtime.

InitialPartition := function(N, T, QD)
    local r, classes, i, j, key_i, placed, keys;
    if T = fail or QD = fail then
        Error("InitialPartition: T and QD must both be supplied.");
    fi;
    r := Length(T);
    if Length(QD) <> r then
        Error("InitialPartition: |T| = ", r,
              " but |QD| = ", Length(QD), "; they must agree.");
    fi;
    # `classes` is a list of pairs [key, list_of_indices].
    classes := [];
    for i in [1 .. r] do
        key_i := [T[i], QD[i]];
        placed := false;
        for j in [1 .. Length(classes)] do
            if not placed and classes[j][1] = key_i then
                Add(classes[j][2], i);
                placed := true;
            fi;
        od;
        if not placed then
            Add(classes, [key_i, [i]]);
        fi;
    od;
    # Sort blocks by their key's string form for a deterministic output.
    # Build parallel arrays and use SortParallel (always available).
    keys := List(classes, c -> String(c[1]));
    SortParallel(keys, classes);
    return List(classes, c -> c[2]);
end;

# Convenience alias: caller can pass S instead of pre-computing QD.
JointTQDClasses := function(N, T, S)
    return InitialPartition(N, T, QuantumDimensionsFromS(S));
end;

JointTQDKey := function(T_i, QD_i)
    return String([T_i, QD_i]);
end;

Print("Loaded aut_nt_partition.g (InitialPartition, ",
      "QuantumDimensionsFromS, JointTQDClasses, JointTQDKey).\n");
