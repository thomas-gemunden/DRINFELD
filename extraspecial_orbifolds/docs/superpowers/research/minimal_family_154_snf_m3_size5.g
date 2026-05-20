# minimal_family_154_snf_m3_size5.g
#
# Brute-force size-5 EA subsets at m=3 (with D_8 + Q_8 always included)
# to determine the exact minimum.
#
# C(30, 5) = 142506; each SNF on a ~50x35 matrix takes ~10-30 ms,
# so the full sweep is ~30-60 minutes. We exit early once we find
# 5 injective examples (or 0 after exhaustive search).

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
            Error("zero invariant factor");
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

_outfile := "/tmp/minimal_family_154_snf_m3_size5.out";;
_stream  := OutputTextFile(_outfile, false);;
SetPrintFormattingStatus(_stream, false);;

PrintTo(_stream, "# Brute-force size-5 EA + D8 + Q8 search at m=3\n");
PrintTo(_stream, "# Date: 2026-05-20\n\n");

Print("Loading m=3 data...\n");
_data3 := BuildRestrictionMatrices(3, "hap");;
PrintTo(_stream, "# k_G = ", Length(_data3.torsion_G),
        ",  n_EA = ", Length(_data3.H_EA_list), "\n\n");

Print("Brute-force size-5 search (C(30,5) = 142506)...\n");
_found := [];
_count := 0;
_start := Runtime();
for _S in Combinations([1..30], 5) do
    _count := _count + 1;
    if KernelOrder(_data3, _S, true, true) = 1 then
        Add(_found, _S);
        Print("  found: ", _S, "  (n=", _count, ", wall=",
              (Runtime() - _start) / 1000.0, "s)\n");
        if Length(_found) >= 10 then break; fi;
    fi;
    if _count mod 5000 = 0 then
        Print("  ... progress: ", _count, " of 142506 (",
              (Runtime() - _start) / 1000.0, "s wall)\n");
    fi;
od;

PrintTo(_stream, "## Size 5 EA + D8 + Q8 results\n");
PrintTo(_stream, "# tested: ", _count, "\n");
PrintTo(_stream, "# Injective subsets found: ", Length(_found), "\n");
for _S in _found do
    PrintTo(_stream, "  ", _S, "\n");
od;

if Length(_found) > 0 then
    PrintTo(_stream, "\n# VERDICT m=3: min |F_EA| with D_8 + Q_8 = 5\n");
    PrintTo(_stream, "# Total family size (D_8 + Q_8 + EAs) = 5 + 2 = 7\n");
else
    PrintTo(_stream, "\n# VERDICT m=3: size 5 also fails. Min |F_EA| = 6.\n");
fi;

CloseStream(_stream);
Print("Wrote ", _outfile, "\n");
QUIT_GAP(0);
