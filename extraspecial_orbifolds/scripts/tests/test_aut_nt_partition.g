# test_aut_nt_partition.g — tests for the V-5a initial Aut(N, T)
# partition (T-eigenvalue × quantum dimension).
#
# Tested module: ../aut_nt_partition.g
#
# Acceptance criteria (issue #17 / task #54):
#   * For D(Q_8) (modular_data/8/4/1.txt, untwisted, 22 simples) the
#     joint (T, QD) partition is the expected 5-block refinement of
#     {1, ..., 22}: a single T=1, QD=1 block of size 8, and four
#     T-distinguished QD=2 blocks of sizes 4, 4, 3, 3.
#   * For D^1(E_+(2)) = D(E_+(2)) (modular_data/32/49/1.txt, 184
#     simples) the joint (T, QD) partition strictly refines the
#     T-multiset partition {1^102, (-1)^70, i^6, (-i)^6}; total size
#     184; each block has a single (T, QD) value.
#
# Run from anywhere:
#     gap test_aut_nt_partition.g
#
# Success is signalled by "test_aut_nt_partition: PASS".

# ---- Locate and load the sibling module ------------------------------
_aut_loaded := false;;
_self_path := INPUT_FILENAME();;
if _self_path <> fail and _self_path <> "stream" then
    _self_dir := _self_path{[1..Length(_self_path) - Length("/test_aut_nt_partition.g")]};;
    _candidate := Concatenation(_self_dir, "/../aut_nt_partition.g");;
    if IsExistingFile(_candidate) then
        Read(_candidate);
        _aut_loaded := true;
    fi;
fi;
if not _aut_loaded then
    for _p in [ "../aut_nt_partition.g",
                "aut_nt_partition.g",
                "extraspecial_orbifolds/scripts/aut_nt_partition.g",
                "scripts/aut_nt_partition.g" ] do
        if not _aut_loaded and IsExistingFile(_p) then
            Read(_p);
            _aut_loaded := true;
        fi;
    od;
fi;
if not _aut_loaded then
    Error("cannot locate aut_nt_partition.g; run from ",
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

# ---- Unit test 1: tiny synthetic example -----------------------------
# Five simples; T = [1, 1, -1, 1, -1]; QD = [1, 2, 1, 1, 2].
# Joint classes:
#   {1, 4}: T=1, QD=1
#   {2}   : T=1, QD=2
#   {3}   : T=-1, QD=1
#   {5}   : T=-1, QD=2
Print("Unit test 1: tiny synthetic example.\n");
T_syn := [1, 1, -1, 1, -1];;
QD_syn := [1, 2, 1, 1, 2];;
P_syn := InitialPartition(fail, T_syn, QD_syn);;
CheckEqual("synthetic # blocks", Length(P_syn), 4);
CheckEqual("synthetic union covers {1..5}",
           Set(Concatenation(P_syn)), [1, 2, 3, 4, 5]);
CheckEqual("synthetic block sizes (sorted)",
           SortedList(List(P_syn, Length)), [1, 1, 1, 2]);
# Every block is internally constant on (T, QD).
for _blk in P_syn do
    _t := T_syn[_blk[1]];;
    _q := QD_syn[_blk[1]];;
    for _i in _blk do
        CheckTrue(Concatenation("synthetic block T const at ",
                                String(_i)),
                  T_syn[_i] = _t);
        CheckTrue(Concatenation("synthetic block QD const at ",
                                String(_i)),
                  QD_syn[_i] = _q);
    od;
od;
# The pair {1, 4} must be one block, not split.
CheckTrue("synthetic {1,4} in same block",
          ForAny(P_syn, b -> 1 in b and 4 in b));

# ---- Unit test 2: helper QuantumDimensionsFromS ----------------------
Print("\nUnit test 2: QuantumDimensionsFromS.\n");
S_synth := [ [ 1/2, 1/2, 1, 3/2 ],
             [ 1/2, 1/2, 1, 3/2 ],
             [ 1,   1,   2, 3   ],
             [ 3/2, 3/2, 3, 9/2 ] ];;
CheckEqual("QD from S row 1 ratios",
           QuantumDimensionsFromS(S_synth), [1, 1, 2, 3]);

# ---- Acceptance test 1: D(Q_8) ---------------------------------------
# Load 8/4/1.txt directly (no LoadModularData needed; the file is a
# pure GAP source returning rec(S, T)).
Print("\nAcceptance 1: D(Q_8) from modular_data/8/4/1.txt.\n");

# Find modular_data/. The DRINFELD-wt-v5a worktree sits next to the
# canonical DRINFELD checkout, which contains the modular_data dir
# (see CLAUDE.md). Try a few candidate paths.
_md_root := fail;;
for _cand in [ "../../../../modular_data",
               "../../../../../modular_data",
               "/Users/thomasgemunden/Projects/group_cohomology/modular_data" ] do
    if _md_root = fail and IsExistingFile(Concatenation(_cand, "/8/4/1.txt")) then
        _md_root := _cand;
    fi;
od;
if _md_root = fail then
    Error("cannot locate modular_data/ root; tried several candidates.");
fi;

q8_path := Concatenation(_md_root, "/8/4/1.txt");;
q8_data := ReadAsFunction(q8_path)();;
CheckEqual("Q_8 rank", Length(q8_data.T), 22);

P_q8 := InitialPartition(fail, q8_data.T,
                         QuantumDimensionsFromS(q8_data.S));;
CheckEqual("Q_8 union covers {1..22}",
           Set(Concatenation(P_q8)), [1 .. 22]);
CheckEqual("Q_8 partition is disjoint",
           Sum(P_q8, Length), 22);
# Expected: 5 blocks of sizes [8, 4, 4, 3, 3].
CheckEqual("Q_8 # blocks", Length(P_q8), 5);
CheckEqual("Q_8 block sizes (sorted, descending)",
           Reversed(SortedList(List(P_q8, Length))),
           [8, 4, 4, 3, 3]);
# Inside each block, T and QD are constant.
_q8_qds := QuantumDimensionsFromS(q8_data.S);;
for _blk in P_q8 do
    _t := q8_data.T[_blk[1]];;
    _q := _q8_qds[_blk[1]];;
    CheckTrue(Concatenation("Q_8 block (T=", String(_t),
                            ", QD=", String(_q), ") T-constant"),
              ForAll(_blk, j -> q8_data.T[j] = _t));
    CheckTrue(Concatenation("Q_8 block (T=", String(_t),
                            ", QD=", String(_q), ") QD-constant"),
              ForAll(_blk, j -> _q8_qds[j] = _q));
od;
# Specifically the T=1, QD=1 block has size 8 and contains the four
# units {1, 2, 3, 4} and {14, 15, 16, 17}.
_unit_block := First(P_q8, b -> q8_data.T[b[1]] = 1 and _q8_qds[b[1]] = 1);;
CheckTrue("Q_8 T=1,QD=1 block exists", _unit_block <> fail);
if _unit_block <> fail then
    CheckEqual("Q_8 T=1,QD=1 block content", Set(_unit_block),
               [1, 2, 3, 4, 14, 15, 16, 17]);
fi;

# ---- Acceptance test 2: D^1(E_+(2)) ----------------------------------
# E_+(2) = SmallGroup(32, 49). The untwisted D^1(E_+(2)) is
# modular_data/32/49/1.txt, rank 184, T-multiset
# {1^102, (-1)^70, i^6, (-i)^6} (writeup.md line 327).
Print("\nAcceptance 2: D^1(E_+(2)) from modular_data/32/49/1.txt.\n");
e2_path := Concatenation(_md_root, "/32/49/1.txt");;
e2_data := ReadAsFunction(e2_path)();;
CheckEqual("E_+(2) rank", Length(e2_data.T), 184);
# Sanity: T-multiset must match the predicted spectrum.
e2_tcoll := Collected(e2_data.T);;
e2_count := function(val)
    local p;
    p := First(e2_tcoll, q -> q[1] = val);
    if p = fail then return 0; fi;
    return p[2];
end;;
CheckEqual("E_+(2) #T=1", e2_count(1), 102);
CheckEqual("E_+(2) #T=-1", e2_count(-1), 70);
CheckEqual("E_+(2) #T=i", e2_count(E(4)), 6);
CheckEqual("E_+(2) #T=-i", e2_count(-E(4)), 6);

# Joint (T, QD) partition.
e2_qds := QuantumDimensionsFromS(e2_data.S);;
P_e2 := InitialPartition(fail, e2_data.T, e2_qds);;
CheckEqual("E_+(2) union covers {1..184}",
           Set(Concatenation(P_e2)), [1 .. 184]);
CheckEqual("E_+(2) partition is disjoint",
           Sum(P_e2, Length), 184);
# Each block has constant (T, QD).
_all_const := true;;
for _blk in P_e2 do
    _t := e2_data.T[_blk[1]];;
    _q := e2_qds[_blk[1]];;
    if not ForAll(_blk, j -> e2_data.T[j] = _t and e2_qds[j] = _q) then
        _all_const := false;
    fi;
od;
CheckTrue("E_+(2) all blocks (T, QD)-constant", _all_const);
# Joint partition is a refinement of T-partition: every block has a
# single T value, and the per-T totals match the multiset.
e2_block_t_sums := function(tval)
    local total, b;
    total := 0;
    for b in P_e2 do
        if e2_data.T[b[1]] = tval then
            total := total + Length(b);
        fi;
    od;
    return total;
end;;
CheckEqual("E_+(2) T=1 simples reachable via blocks",
           e2_block_t_sums(1), 102);
CheckEqual("E_+(2) T=-1 simples reachable via blocks",
           e2_block_t_sums(-1), 70);
CheckEqual("E_+(2) T=i simples reachable via blocks",
           e2_block_t_sums(E(4)), 6);
CheckEqual("E_+(2) T=-i simples reachable via blocks",
           e2_block_t_sums(-E(4)), 6);

# A useful diagnostic: number of blocks and block-size multiset.
Print("  E_+(2) #blocks: ", Length(P_e2), "\n");
Print("  E_+(2) block-size multiset: ",
      Collected(SortedList(List(P_e2, Length))), "\n");

# ---- Final report ----------------------------------------------------
if Length(failures) = 0 then
    Print("\ntest_aut_nt_partition: PASS\n");
else
    Print("\ntest_aut_nt_partition: FAIL (", Length(failures),
          " failure(s)):\n");
    for i in [1..Length(failures)] do
        Print("  - ", failures[i], "\n");
    od;
fi;

QUIT;
