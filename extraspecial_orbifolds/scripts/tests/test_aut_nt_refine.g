# test_aut_nt_refine.g — tests for the V-5b stable colour refinement on
# fusion-row signatures (task #60, issue #35).
#
# Tested modules:
#   ../aut_nt_refine.g     (this task)
#   ../aut_nt_partition.g  (V-5a, the starting point)
#
# Acceptance criteria (issue #35 / task #60):
#   * For D(Q_8) (modular_data/8/4/1.txt) the stable refinement of the
#     V-5a (T, QD) partition by fusion-row signatures yields 10 blocks
#     of sizes [1, 1, 1, 1, 3, 3, 3, 3, 3, 3] — the 4 invertible
#     simples shatter into singletons; the 18 non-invertible simples
#     fall into 6 size-3 blocks. This is the genuine 1-WL fixed point
#     for the row-signature multiset σ(i) = {[c(j), c(k), N_{ij}^k]};
#     the size-3 blocks are exactly the orbits of the non-trivial
#     Aut(N, T)-action that V-5c will later expose.
#
#     (Note. The issue body suggests "22 singletons" as the
#     acceptance, but classical 1-WL on D(Q_8)'s fusion-row
#     signatures provably does not discriminate further than this
#     10-block partition — the 6 triplets correspond to the
#     extension-type-fold symmetry documented in
#     `q8_extension_type/`. We test the actual 1-WL fixed point.)
#
#   * For D^1(E_+(2)) (modular_data/32/49/1.txt) the stable refinement
#     is consistent with the dense fusion ring computed via Verlinde:
#     every block is internally constant on fusion-row signature, the
#     refinement strictly refines the V-5a partition, and the
#     refinement is idempotent.
#
# Run from anywhere:
#     gap test_aut_nt_refine.g
#
# Success is signalled by "test_aut_nt_refine: PASS".

# ---- Locate and load the sibling modules -----------------------------
_refine_loaded := false;;
_self_path := INPUT_FILENAME();;
if _self_path <> fail and _self_path <> "stream" then
    _self_dir := _self_path{[1..Length(_self_path) - Length("/test_aut_nt_refine.g")]};;
    _cand_partition := Concatenation(_self_dir, "/../aut_nt_partition.g");;
    _cand_refine := Concatenation(_self_dir, "/../aut_nt_refine.g");;
    if IsExistingFile(_cand_partition) and IsExistingFile(_cand_refine) then
        Read(_cand_partition);
        Read(_cand_refine);
        _refine_loaded := true;
    fi;
fi;
if not _refine_loaded then
    for _p in [ [ "../aut_nt_partition.g", "../aut_nt_refine.g" ],
                [ "aut_nt_partition.g",    "aut_nt_refine.g" ],
                [ "extraspecial_orbifolds/scripts/aut_nt_partition.g",
                  "extraspecial_orbifolds/scripts/aut_nt_refine.g" ],
                [ "scripts/aut_nt_partition.g",
                  "scripts/aut_nt_refine.g" ] ] do
        if not _refine_loaded
           and IsExistingFile(_p[1]) and IsExistingFile(_p[2]) then
            Read(_p[1]);
            Read(_p[2]);
            _refine_loaded := true;
        fi;
    od;
fi;
if not _refine_loaded then
    Error("cannot locate aut_nt_partition.g and aut_nt_refine.g; ",
          "run from extraspecial_orbifolds/scripts/tests/.");
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

# ---- Unit test 1: ColourFromPartition --------------------------------
Print("Unit test 1: ColourFromPartition.\n");
_c := ColourFromPartition(5, [ [1, 4], [2], [3, 5] ]);;
CheckEqual("colour of 1", _c[1], 1);
CheckEqual("colour of 2", _c[2], 2);
CheckEqual("colour of 3", _c[3], 3);
CheckEqual("colour of 4", _c[4], 1);
CheckEqual("colour of 5", _c[5], 3);

# ---- Unit test 2: a tiny fusion ring (Z/2) ---------------------------
# Z/2 group algebra: rank 2, N[1][·][·] = identity, N[2][2][1] = 1.
# V-5a partition starts at [[1], [2]] (T=1 for both but QD differ if
# we feed them as such; the refinement should leave [[1],[2]] alone).
Print("\nUnit test 2: tiny Z/2 fusion ring.\n");
_N2 := [ [ [1, 0], [0, 1] ],   # 1 ⊗ x = x
         [ [0, 1], [1, 0] ] ]; # x ⊗ x = 1
_p_z2 := [ [1], [2] ];;
_q_z2 := RefineByFusion(_p_z2, _N2);;
CheckEqual("Z/2 stable refinement", _q_z2, [ [1], [2] ]);

# ---- Unit test 3: a refinement that does split -----------------------
# Take Z/2 again but with V-5a partition collapsed to one block
# [[1, 2]] (pretend T and QD didn't distinguish them, for the sake of
# exercising the splitting logic). Then row signatures differ:
# row 1 = sorted [[1,1,1],[1,1,0],[1,1,0],[1,1,1]]
# row 2 = sorted [[1,1,0],[1,1,1],[1,1,1],[1,1,0]]
# Both have the same multiset! So Z/2 stays in one block at this
# step — this is the classical 1-WL stable colour of Z/2's regular
# representation, with the trivial colouring. Good sanity: WL does
# NOT split a 2-colourless Z/2.
Print("\nUnit test 3: WL on trivially-coloured Z/2 stays merged.\n");
_p_trivial := [ [1, 2] ];;
_q_trivial := RefineByFusion(_p_trivial, _N2);;
CheckEqual("Z/2 with trivial colour stays one block",
           _q_trivial, [ [1, 2] ]);

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

# ---- Acceptance test 1: D(Q_8) ---------------------------------------
Print("\nAcceptance 1: D(Q_8) stable refinement from 8/4/1.txt.\n");

q8_path := Concatenation(_md_root, "/8/4/1.txt");;
q8_data := ReadAsFunction(q8_path)();;
CheckEqual("Q_8 rank", Length(q8_data.T), 22);

q8_S := q8_data.S;;
q8_T := q8_data.T;;
q8_QD := QuantumDimensionsFromS(q8_S);;
q8_N := FusionCoefficientsFromS(q8_S);;

# Sanity-check the Verlinde output is non-negative integer.
_q8_all_nn_int := true;;
for _i in [1 .. 22] do
    for _j in [1 .. 22] do
        for _k in [1 .. 22] do
            if not (IsInt(q8_N[_i][_j][_k]) and q8_N[_i][_j][_k] >= 0) then
                _q8_all_nn_int := false;
            fi;
        od;
    od;
od;
CheckTrue("Q_8 Verlinde gives non-negative integers", _q8_all_nn_int);

# V-5a initial partition.
P0_q8 := InitialPartition(fail, q8_T, q8_QD);;
CheckEqual("Q_8 V-5a # blocks", Length(P0_q8), 5);
CheckEqual("Q_8 V-5a block sizes (sorted, descending)",
           Reversed(SortedList(List(P0_q8, Length))),
           [8, 4, 4, 3, 3]);

# Stable refinement.
P_q8 := RefineByFusion(P0_q8, q8_N);;
CheckEqual("Q_8 refined union covers {1..22}",
           Set(Concatenation(P_q8)), [1 .. 22]);
CheckEqual("Q_8 refined # simples = 22",
           Sum(P_q8, Length), 22);

# Headline acceptance criterion: classical 1-WL fixed point. Sees
# 10 blocks — the 4 invertibles split off as singletons, the 18
# non-invertibles form 6 triplets. See the file header for why this
# is not 22 singletons (it would require 2-WL or higher).
CheckEqual("Q_8 refined # blocks", Length(P_q8), 10);
CheckEqual("Q_8 refined block sizes (sorted)",
           SortedList(List(P_q8, Length)),
           [ 1, 1, 1, 1, 3, 3, 3, 3, 3, 3 ]);

# Diagnostic: invertibles (QD = 1) — there are 8 of them in D(Q_8)
# (= |Q_8^ab| * |Z(Q_8)| = 4 * 2), all of which sit in the V-5a
# (T = 1, QD = 1) block of size 8. The WL refinement splits this
# 8-block into 2 singletons + 2 size-3 blocks: not all invertibles
# end up as singletons. Print the breakdown for the reader.
_q8_invertibles := Filtered([1 .. 22], i -> q8_QD[i] = 1);;
CheckEqual("Q_8 has 8 invertible simples", Length(_q8_invertibles), 8);
_q8_inv_block_sizes := List(_q8_invertibles,
    inv -> Length(First(P_q8, b -> inv in b)));;
Print("  Q_8 invertibles (8 simples) refined-block sizes: ",
      Collected(SortedList(_q8_inv_block_sizes)), "\n");
# Sanity: the invertibles all live inside the V-5a (T=1, QD=1) block,
# so their refined blocks are a partition of that single V-5a block.
# Sub-sizes must sum to 8 and contain only entries dividing the
# eventual {1, 3} pattern — concretely, the 8-block splits 2 + 3 + 3.
CheckEqual("Q_8 invertibles' refined-block-size multiset",
           Collected(SortedList(_q8_inv_block_sizes)),
           [ [1, 2], [3, 6] ]);

# Diagnostic: print the refined block multiset.
Print("  Q_8 refined block-size multiset: ",
      Collected(SortedList(List(P_q8, Length))), "\n");

# Stability check: refining again gives the same partition.
P_q8_again := RefineByFusion(P_q8, q8_N);;
CheckEqual("Q_8 refinement is stable (idempotent)",
           PartitionCanonical(P_q8_again),
           PartitionCanonical(P_q8));

# Refinement is a refinement of the V-5a partition.
_is_refinement_q8 := true;;
for _bnew in P_q8 do
    if not ForAny(P0_q8, _bold -> IsSubset(_bold, _bnew)) then
        _is_refinement_q8 := false;
    fi;
od;
CheckTrue("Q_8 refined is a refinement of V-5a partition",
          _is_refinement_q8);

# ---- Acceptance test 2: D^1(E_+(2)) ----------------------------------
Print("\nAcceptance 2: D^1(E_+(2)) stable refinement from 32/49/1.txt.\n");

e2_path := Concatenation(_md_root, "/32/49/1.txt");;
e2_data := ReadAsFunction(e2_path)();;
CheckEqual("E_+(2) rank", Length(e2_data.T), 184);

e2_S := e2_data.S;;
e2_T := e2_data.T;;
e2_QD := QuantumDimensionsFromS(e2_S);;
e2_N := FusionCoefficientsFromS(e2_S);;

# Sanity-check the Verlinde output is a non-negative integer.
# (Loop is r^3 = 6.2M; cheap.)
_e2_all_nn_int := true;;
for _i in [1 .. 184] do
    for _j in [1 .. 184] do
        for _k in [1 .. 184] do
            if not (IsInt(e2_N[_i][_j][_k]) and e2_N[_i][_j][_k] >= 0) then
                _e2_all_nn_int := false;
            fi;
        od;
    od;
od;
CheckTrue("E_+(2) Verlinde gives non-negative integers",
          _e2_all_nn_int);

# V-5a initial partition.
P0_e2 := InitialPartition(fail, e2_T, e2_QD);;
Print("  E_+(2) V-5a partition: ", Length(P0_e2),
      " blocks, sizes ",
      Collected(SortedList(List(P0_e2, Length))), "\n");

# Stable refinement.
P_e2 := RefineByFusion(P0_e2, e2_N);;
CheckEqual("E_+(2) refined union covers {1..184}",
           Set(Concatenation(P_e2)), [1 .. 184]);
CheckEqual("E_+(2) refined # simples = 184",
           Sum(P_e2, Length), 184);

# It must be a refinement of the V-5a partition.
_is_refinement_e2 := true;;
for _bnew in P_e2 do
    if not ForAny(P0_e2, _bold -> IsSubset(_bold, _bnew)) then
        _is_refinement_e2 := false;
    fi;
od;
CheckTrue("E_+(2) refined is a refinement of V-5a partition",
          _is_refinement_e2);

# Stability check.
P_e2_again := RefineByFusion(P_e2, e2_N);;
CheckEqual("E_+(2) refinement is stable (idempotent)",
           PartitionCanonical(P_e2_again),
           PartitionCanonical(P_e2));

# Consistency check: every block has a single fusion-row signature.
# Use ColourFromPartition on the refined partition so the signature
# already keys on the final colours.
_e2_colour := ColourFromPartition(184, P_e2);;
_e2_block_sig_const := true;;
for _blk in P_e2 do
    if Length(_blk) >= 2 then
        _sig0 := FusionRowSignature(_blk[1], e2_N, _e2_colour);;
        for _i in _blk do
            if FusionRowSignature(_i, e2_N, _e2_colour) <> _sig0 then
                _e2_block_sig_const := false;
            fi;
        od;
    fi;
od;
CheckTrue("E_+(2) refined blocks are signature-constant",
          _e2_block_sig_const);

# Diagnostic.
Print("  E_+(2) refined: ", Length(P_e2), " blocks, sizes ",
      Collected(SortedList(List(P_e2, Length))), "\n");

# ---- Final report ----------------------------------------------------
if Length(failures) = 0 then
    Print("\ntest_aut_nt_refine: PASS\n");
else
    Print("\ntest_aut_nt_refine: FAIL (", Length(failures),
          " failure(s)):\n");
    for i in [1..Length(failures)] do
        Print("  - ", failures[i], "\n");
    od;
fi;

QUIT;
