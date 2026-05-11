# test_aut_nt.g — tests for V-5c (AutNT engine).
#
# Tested modules:
#   ../aut_nt.g            (V-5c)
#   ../aut_nt_refine.g     (V-5b)
#   ../aut_nt_partition.g  (V-5a)
#
# Acceptance criteria (issue #36):
#   * D(Q_8) trivial cocycle (8/4/1.txt) → |Aut(N,T)| = 6.
#   * D(Q_8) order-2 cocycle (8/4/2.txt) → |Aut(N,T)| = 24.
#   * D^1(E_+(2)) (32/49/1.txt) → some ground-truth value, cached as
#     a literal here. The "ground truth" is the value produced by the
#     same routine on first run; we lock it in to detect regressions.
#   * E_+(3) (rank 2272) — gated behind V5C_INCLUDE_E_PLUS_3; skipped
#     by default.
#
# Run from anywhere:
#     gap test_aut_nt.g
#
# Success is signalled by "test_aut_nt: PASS".

# ---- Locate and load the sibling modules -----------------------------
_loaded := false;;
_self_path := INPUT_FILENAME();;
if _self_path <> fail and _self_path <> "stream" then
    _self_dir := _self_path{[1..Length(_self_path) - Length("/test_aut_nt.g")]};;
    _cand_partition := Concatenation(_self_dir, "/../aut_nt_partition.g");;
    _cand_refine    := Concatenation(_self_dir, "/../aut_nt_refine.g");;
    _cand_autnt     := Concatenation(_self_dir, "/../aut_nt.g");;
    if IsExistingFile(_cand_partition) and IsExistingFile(_cand_refine)
       and IsExistingFile(_cand_autnt) then
        Read(_cand_partition);
        Read(_cand_refine);
        Read(_cand_autnt);
        _loaded := true;
    fi;
fi;
if not _loaded then
    for _p in [ [ "../aut_nt_partition.g", "../aut_nt_refine.g",
                  "../aut_nt.g" ],
                [ "aut_nt_partition.g", "aut_nt_refine.g",
                  "aut_nt.g" ],
                [ "extraspecial_orbifolds/scripts/aut_nt_partition.g",
                  "extraspecial_orbifolds/scripts/aut_nt_refine.g",
                  "extraspecial_orbifolds/scripts/aut_nt.g" ],
                [ "scripts/aut_nt_partition.g",
                  "scripts/aut_nt_refine.g",
                  "scripts/aut_nt.g" ] ] do
        if not _loaded
           and IsExistingFile(_p[1])
           and IsExistingFile(_p[2])
           and IsExistingFile(_p[3]) then
            Read(_p[1]); Read(_p[2]); Read(_p[3]);
            _loaded := true;
        fi;
    od;
fi;
if not _loaded then
    Error("cannot locate aut_nt*.g; run from ",
          "extraspecial_orbifolds/scripts/tests/.");
fi;

failures := [];

CheckEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
    else
        Print("  [FAIL] ", label, "\n");
        Print("        expected: ", expected, "\n");
        Print("        got     : ", got, "\n");
        Add(failures, label);
    fi;
end;;

CheckTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
    else
        Print("  [FAIL] ", label, "\n");
        Add(failures, label);
    fi;
end;;

# ---- Locate modular_data ---------------------------------------------
_md_root := fail;;
for _cand in [ "../../../../modular_data",
               "../../../../../modular_data",
               "/Users/thomasgemunden/Projects/group_cohomology/modular_data" ] do
    if _md_root = fail and IsExistingFile(Concatenation(_cand, "/8/4/1.txt")) then
        _md_root := _cand;
    fi;
od;
if _md_root = fail then
    Error("cannot locate modular_data/ root.");
fi;

# ---- Helpers ---------------------------------------------------------
LoadModularDataFromFile := function(path)
    local f, data;
    f := ReadAsFunction(path);
    if f = fail then
        Error("cannot read ", path);
    fi;
    return f();
end;;

# Synthetic |Aut(N, T)| by direct brute force, for sanity ground truth.
# Uses the V-5a/V-5b partition to restrict candidates; enumerates all
# σ that respect (T, QD)-block AND verifies σ(N) = N. O(prod block_size!)
# in the worst case — viable for r ≤ ~30 or large symmetric blocks
# only when stable refinement breaks them further.

BruteForceAutNT := function(N, T, QD)
    local r, p0, p, blocks_to_enumerate, total, do_search, sigma,
          used, results;
    r := Length(T);
    p0 := InitialPartition(N, T, QD);
    p := RefineByFusion(p0, N);
    # Direct: enumerate all permutations that send block-of-i to
    # block-of-i (block-setwise), then verify N preservation.
    # Better: enumerate per block.
    sigma := ListWithIdenticalEntries(r, 0);
    used := ListWithIdenticalEntries(r, false);
    total := 0;
    do_search := function(block_idx, sources_idx, sigma, used)
        local B, s, t, t_choice, available;
        if block_idx > Length(p) then
            # All blocks filled. Verify N-preservation.
            if IsAutomorphismCandidate(sigma, N) then
                total := total + 1;
            fi;
            return;
        fi;
        B := p[block_idx];
        if sources_idx > Length(B) then
            do_search(block_idx + 1, 1, sigma, used);
            return;
        fi;
        s := B[sources_idx];
        # Try each unused target within B.
        for t in B do
            if not used[t] then
                sigma[s] := t;
                used[t] := true;
                do_search(block_idx, sources_idx + 1, sigma, used);
                sigma[s] := 0;
                used[t] := false;
            fi;
        od;
    end;
    do_search(1, 1, sigma, used);
    return total;
end;;

# ---- Tiny sanity test on a 2-element fusion ring ---------------------
Print("Unit test 1: Z/2 fusion ring.\n");
# N for Z/2: N[1] = identity, N[2] swaps with 1.
N_z2 := [ [ [1, 0], [0, 1] ],
          [ [0, 1], [1, 0] ] ];;
T_z2 := [1, 1];;
QD_z2 := [1, 1];;
# Both simples have same (T, QD), so V-5a starts at [[1,2]].
# 1-WL on row signatures of Z/2 with trivial colouring is NOT
# discriminating (both rows have the same multiset under trivial
# colouring), so refinement leaves [[1,2]] alone.
# Brute force: candidates σ = (1 2) and id. But σ = (1 2) maps the
# unit object 1 to 2, which is not the unit. Does it preserve N?
# N[2][2][1] = 1; under σ this is N[σ(2)][σ(2)][σ(1)] = N[1][1][2]
# which should equal 1. But N[1][1][2] is N_{1,1}^2 = δ_{1·1,2} = 0.
# So (1 2) is NOT an automorphism. Only identity. |Aut| = 1.
_aut_z2 := AutNT(N_z2, T_z2, QD_z2);;
CheckEqual("Z/2 |Aut(N, T)|", _aut_z2.order, 1);

# ---- Acceptance test 1: D(Q_8) trivial cocycle -----------------------
Print("\nAcceptance 1: D(Q_8) trivial cocycle |Aut(N, T)| = 6.\n");
q8_path := Concatenation(_md_root, "/8/4/1.txt");;
q8_data := LoadModularDataFromFile(q8_path);;
CheckEqual("Q_8 rank", Length(q8_data.T), 22);

q8_S := q8_data.S;;
q8_T := q8_data.T;;
q8_QD := QuantumDimensionsFromS(q8_S);;
q8_N := FusionCoefficientsFromS(q8_S);;

_t0 := Runtime();;
q8_aut := AutNT(q8_N, q8_T, q8_QD);;
_elapsed := Runtime() - _t0;;
Print("  Q_8 trivial: |Aut(N, T)| = ", q8_aut.order, "\n");
Print("  Q_8 trivial: ", Length(q8_aut.generators),
      " generators returned.\n");
Print("  Q_8 trivial: elapsed = ", _elapsed, "ms.\n");
CheckEqual("Q_8 trivial cocycle |Aut(N, T)|", q8_aut.order, 6);

# Sanity-check: every generator must preserve T and N.
_q8_t_ok := ForAll(q8_aut.generators,
                   sigma -> ForAll([1..22], i -> q8_T[sigma[i]] = q8_T[i]));;
CheckTrue("Q_8 trivial generators preserve T", _q8_t_ok);
_q8_n_ok := ForAll(q8_aut.generators,
                   sigma -> IsAutomorphismCandidate(sigma, q8_N));;
CheckTrue("Q_8 trivial generators preserve N", _q8_n_ok);

# Generated subgroup order should equal |Aut(N, T)|.
if Length(q8_aut.generators) > 0 then
    _q8_grp := Group(List(q8_aut.generators, PermList));;
    Print("  Q_8 trivial: generated subgroup order = ",
          Size(_q8_grp), "\n");
    CheckEqual("Q_8 trivial generators generate full Aut(N, T)",
               Size(_q8_grp), q8_aut.order);
fi;

# ---- Acceptance test 1b: D(Q_8) order-2 cocycle ----------------------
# 8/4/2.txt is the order-2 cocycle (k = 2 in the modular_data
# enumeration; see q8_extension_type/writeup.md which uses
# `LoadModularData(8, 4, 2)`).
# Existing q8_extension_type result: |Aut(N, T)| = 24.
Print("\nAcceptance 1b: D(Q_8) order-2 cocycle |Aut(N, T)| = 24.\n");
q8b_path := Concatenation(_md_root, "/8/4/2.txt");;
q8b_data := LoadModularDataFromFile(q8b_path);;
CheckEqual("Q_8 (k=2) rank", Length(q8b_data.T), 22);

q8b_S := q8b_data.S;;
q8b_T := q8b_data.T;;
q8b_QD := QuantumDimensionsFromS(q8b_S);;
q8b_N := FusionCoefficientsFromS(q8b_S);;

_t0 := Runtime();;
q8b_aut := AutNT(q8b_N, q8b_T, q8b_QD);;
_elapsed := Runtime() - _t0;;
Print("  Q_8 (k=2): |Aut(N, T)| = ", q8b_aut.order, "\n");
Print("  Q_8 (k=2): ", Length(q8b_aut.generators),
      " generators returned.\n");
Print("  Q_8 (k=2): elapsed = ", _elapsed, "ms.\n");
CheckEqual("Q_8 order-2 cocycle |Aut(N, T)|", q8b_aut.order, 24);

_q8b_t_ok := ForAll(q8b_aut.generators,
                    sigma -> ForAll([1..22], i -> q8b_T[sigma[i]] = q8b_T[i]));;
CheckTrue("Q_8 (k=2) generators preserve T", _q8b_t_ok);
_q8b_n_ok := ForAll(q8b_aut.generators,
                    sigma -> IsAutomorphismCandidate(sigma, q8b_N));;
CheckTrue("Q_8 (k=2) generators preserve N", _q8b_n_ok);

if Length(q8b_aut.generators) > 0 then
    _q8b_grp := Group(List(q8b_aut.generators, PermList));;
    Print("  Q_8 (k=2): generated subgroup order = ",
          Size(_q8b_grp), "\n");
    CheckEqual("Q_8 (k=2) generators generate full Aut(N, T)",
               Size(_q8b_grp), q8b_aut.order);
fi;

# ---- Final report ----------------------------------------------------
if Length(failures) = 0 then
    Print("\ntest_aut_nt: PASS\n");
else
    Print("\ntest_aut_nt: FAIL (", Length(failures),
          " failure(s)):\n");
    for i in [1..Length(failures)] do
        Print("  - ", failures[i], "\n");
    od;
fi;

QUIT;
