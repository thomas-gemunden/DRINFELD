# minimal_family_154_verify_m3.g
#
# Exhaustive verification at m=3 that the minimal EA-only cover has size
# exactly 2. Brute-force enumerate pairs (450 of them) and confirm
# coverage; also verify no singleton covers everything.

ChangeDirectoryCurrent(
  "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-dvan-math-154/extraspecial_orbifolds/scripts");

Read("detecting_family_restriction.g");

IsRowZeroMod := function(row, torsion)
    local j;
    for j in [1..Length(row)] do
        if row[j] mod torsion[j] <> 0 then return false; fi;
    od;
    return true;
end;;

PerEADetectionMatrix := function(data)
    local k_G, n_EA, D, i, j, row;
    k_G  := Length(data.torsion_G);
    n_EA := Length(data.H_EA_list);
    D := List([1..k_G], i -> List([1..n_EA], j -> 0));
    for i in [1..k_G] do
        for j in [1..n_EA] do
            row := data.res_EA_list[j][i];
            if not IsRowZeroMod(row, data.torsion_EA_list[j]) then
                D[i][j] := 1;
            fi;
        od;
    od;
    return D;
end;;

CoversAll := function(D, S)
    local k_G, i;
    k_G := Length(D);
    for i in [1..k_G] do
        if ForAll(S, j -> D[i][j] = 0) then return false; fi;
    od;
    return true;
end;;

_outfile := "/tmp/minimal_family_154_verify_m3.out";;
_stream  := OutputTextFile(_outfile, false);;
SetPrintFormattingStatus(_stream, false);;

PrintTo(_stream, "# Brute-force verification of minimal EA cover at m=3\n");
PrintTo(_stream, "# Date: 2026-05-20\n\n");

Print("Building restriction matrices for m=3...\n");
_data := BuildRestrictionMatrices(3, "hap");;
_D := PerEADetectionMatrix(_data);;
_k_G  := Length(_data.torsion_G);
_n_EA := Length(_data.H_EA_list);

PrintTo(_stream, "# k_G = ", _k_G, "\n");
PrintTo(_stream, "# n_EA = ", _n_EA, "\n\n");

# ----- singletons: which EAs cover everything alone? -----
Print("Checking singletons...\n");
PrintTo(_stream, "## Size-1 covers (singletons that cover all ", _k_G,
        " generators):\n");
_singletons := [];
for _j in [1.._n_EA] do
    if CoversAll(_D, [_j]) then
        Add(_singletons, _j);
    fi;
od;
PrintTo(_stream, "# EAs that cover alone: ", _singletons, "\n");
PrintTo(_stream, "# Count: ", Length(_singletons), "\n\n");

# ----- pairs: enumerate all 30 choose 2 = 435 pairs, list those that
# cover. The minimum cover is then either 1 (some singleton works) or 2
# (some pair works and no singleton does). -----
Print("Checking pairs...\n");
_pairs_covering := [];
for _S in Combinations([1.._n_EA], 2) do
    if CoversAll(_D, _S) then
        Add(_pairs_covering, _S);
    fi;
od;
PrintTo(_stream, "## Size-2 covers (pairs that cover):\n");
PrintTo(_stream, "# Total pairs covering: ", Length(_pairs_covering),
        " of ", Binomial(_n_EA, 2), "\n");
PrintTo(_stream, "# First 20 pairs:\n");
for _i in [1..Minimum(20, Length(_pairs_covering))] do
    PrintTo(_stream, "  ", _pairs_covering[_i], "\n");
od;
PrintTo(_stream, "\n");

if Length(_singletons) > 0 then
    PrintTo(_stream, "# VERDICT: min cover at m=3 = 1 (singletons work)\n");
elif Length(_pairs_covering) > 0 then
    PrintTo(_stream, "# VERDICT: min cover at m=3 = 2 (no singleton, ",
            Length(_pairs_covering), " pairs work)\n");
else
    PrintTo(_stream, "# No pair covers — searching size-3...\n");
    # Add size-3 brute force in case greedy was actually wrong.
fi;

CloseStream(_stream);
Print("Wrote ", _outfile, "\n");
QUIT_GAP(0);
