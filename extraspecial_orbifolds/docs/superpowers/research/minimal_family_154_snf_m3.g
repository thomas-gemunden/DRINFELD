# minimal_family_154_snf_m3.g
#
# SNF-based search for the minimal detecting family at m=3.
# Brute force sizes 1..4, then if no injective family found, switch to
# greedy growth for an upper bound on the minimum.

ChangeDirectoryCurrent(
  "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-dvan-math-154/extraspecial_orbifolds/scripts");

Read("detecting_family_restriction.g");

BuildFamilyM := function(data, ea_indices, include_D8, include_Q8)
    local M_blocks, T_blocks, j, M, T_H;
    M_blocks := [];
    T_blocks := [];
    for j in ea_indices do
        Add(M_blocks, data.res_EA_list[j]);
        Append(T_blocks, data.torsion_EA_list[j]);
    od;
    if include_D8 then
        Add(M_blocks, data.res_D8);
        Append(T_blocks, data.torsion_D8);
    fi;
    if include_Q8 and data.res_Q8 <> fail then
        Add(M_blocks, data.res_Q8);
        Append(T_blocks, data.torsion_Q8);
    fi;
    M := TransposedMat(Concatenation(List(M_blocks, TransposedMat)));
    T_H := T_blocks;
    return rec(M := M, T_H := T_H);
end;;

ImageOrder := function(M, T_H)
    local N, D_H, B, snf, factors, k;
    N := Length(T_H);
    D_H := List([1..N], i -> List([1..N], j ->
                If_(i = j, T_H[i], 0)));
    B := Concatenation(M, D_H);
    snf := SmithNormalFormIntegerMat(B);
    factors := [];
    for k in [1..Minimum(Length(snf), N)] do
        if snf[k][k] = 0 then
            Error("ImageOrder: zero invariant factor; bug");
        fi;
        Add(factors, snf[k][k]);
    od;
    return Product(T_H) / Product(factors);
end;;

KernelOrder := function(data, ea_indices, include_D8, include_Q8)
    local rec_M, image_order, group_order;
    rec_M := BuildFamilyM(data, ea_indices, include_D8, include_Q8);
    image_order := ImageOrder(rec_M.M, rec_M.T_H);
    group_order := Product(data.torsion_G);
    return group_order / image_order;
end;;

_outfile := "/tmp/minimal_family_154_snf_m3.out";;
_stream  := OutputTextFile(_outfile, false);;
SetPrintFormattingStatus(_stream, false);;

PrintTo(_stream, "# m=3 minimal-family SNF search\n");
PrintTo(_stream, "# Date: 2026-05-20\n\n");

Print("Loading m=3 restriction matrices...\n");
_data3 := BuildRestrictionMatrices(3, "hap");;
_k_G  := Length(_data3.torsion_G);
_n_EA := Length(_data3.H_EA_list);

PrintTo(_stream, "# k_G = ", _k_G,
        ",  n_EA = ", _n_EA,
        ",  |H^3(G; U(1))| = ", Product(_data3.torsion_G), "\n\n");

# Baseline: full 30 EAs + D8 + Q8
PrintTo(_stream, "## Baseline {30 EAs + D8 + Q8}: ker = ",
        KernelOrder(_data3, [1..30], true, true), "\n\n");

# ---- BRUTE FORCE search at sizes 1, 2, 3, 4 ----
# Try with and without {D_8, Q_8}.
Print("Brute-force search at m=3, size 1..4 (with D8 + Q8)...\n");
PrintTo(_stream, "## Brute-force EA subset search WITH D_8 + Q_8 included\n");
_done := false;
for _k in [0..4] do
    _examples := [];
    for _S in Combinations([1.._n_EA], _k) do
        if KernelOrder(_data3, _S, true, true) = 1 then
            Add(_examples, _S);
            if Length(_examples) >= 5 then break; fi;
        fi;
    od;
    if Length(_examples) > 0 then
        PrintTo(_stream, "  size ", _k,
                ": found ", Length(_examples), " (showing up to 5):\n");
        for _S in _examples do
            PrintTo(_stream, "    ", _S, "\n");
        od;
        _done := true;
        break;
    else
        PrintTo(_stream, "  size ", _k, ": none\n");
    fi;
od;
PrintTo(_stream, "\n");

if not _done then
    Print("Brute force up to size 4 did not find min with D8+Q8.\n");
    Print("Switching to greedy growth heuristic...\n");
    # Greedy: start empty (+D_8, +Q_8 in family), add EA that
    # maximally reduces ker order at each step.
    _chosen := [];
    _curr_ker := KernelOrder(_data3, [], true, true);
    PrintTo(_stream, "## Greedy growth (start ker = ", _curr_ker, "):\n");
    while _curr_ker > 1 do
        _best := fail;
        _best_ker := _curr_ker;
        for _j in [1.._n_EA] do
            if _j in _chosen then continue; fi;
            _k_try := KernelOrder(_data3,
                                  Concatenation(_chosen, [_j]),
                                  true, true);
            if _k_try < _best_ker then
                _best := _j;
                _best_ker := _k_try;
            fi;
        od;
        if _best = fail then
            PrintTo(_stream, "  STUCK at ker = ", _curr_ker, ".\n");
            break;
        fi;
        Add(_chosen, _best);
        _curr_ker := _best_ker;
        PrintTo(_stream, "  add EA[", _best, "] -> ker = ", _curr_ker, "\n");
    od;
    PrintTo(_stream, "# Greedy result: |F_EA| <= ", Length(_chosen),
            " with witness ", _chosen, "\n");
fi;

# Same with EA-only (no D8, no Q8). At m=2, NO EA-only works.
# Test whether EA-only ever works at m=3.
PrintTo(_stream, "\n## Brute-force EA-only search (no D_8, no Q_8)\n");
_done_ea := false;
for _k in [1..4] do
    _examples := [];
    for _S in Combinations([1.._n_EA], _k) do
        if KernelOrder(_data3, _S, false, false) = 1 then
            Add(_examples, _S);
            if Length(_examples) >= 5 then break; fi;
        fi;
    od;
    if Length(_examples) > 0 then
        PrintTo(_stream, "  size ", _k,
                ": found ", Length(_examples), " (showing up to 5):\n");
        for _S in _examples do
            PrintTo(_stream, "    ", _S, "\n");
        od;
        _done_ea := true;
        break;
    else
        PrintTo(_stream, "  size ", _k, ": none\n");
    fi;
od;
if not _done_ea then
    Print("EA-only up to size 4 did not yield injectivity.\n");
    # Greedy growth for EA-only too.
    _chosen := [];
    _curr_ker := KernelOrder(_data3, [], false, false);
    PrintTo(_stream, "## Greedy EA-only growth (start ker = ", _curr_ker, "):\n");
    _step := 0;
    while _curr_ker > 1 and _step < 15 do
        _best := fail;
        _best_ker := _curr_ker;
        for _j in [1.._n_EA] do
            if _j in _chosen then continue; fi;
            _k_try := KernelOrder(_data3,
                                  Concatenation(_chosen, [_j]),
                                  false, false);
            if _k_try < _best_ker then
                _best := _j;
                _best_ker := _k_try;
            fi;
        od;
        if _best = fail then
            PrintTo(_stream, "  STUCK at ker = ", _curr_ker, ".\n");
            break;
        fi;
        Add(_chosen, _best);
        _curr_ker := _best_ker;
        _step := _step + 1;
        PrintTo(_stream, "  step ", _step, ": add EA[", _best,
                "] -> ker = ", _curr_ker, "\n");
    od;
    PrintTo(_stream, "# EA-only greedy result: |F_EA| ~ ", Length(_chosen),
            " with witness ", _chosen,
            " (final ker = ", _curr_ker, ")\n");
fi;

CloseStream(_stream);
Print("Wrote ", _outfile, "\n");
QUIT_GAP(0);
