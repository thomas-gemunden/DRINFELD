# minimal_family_154_snf_m3_5subsets.g
#
# Test the 5-element subsets of greedy-witness {4, 6, 11, 22, 7, 16} at
# m=3: are any of these 6 size-5 subfamilies also injective?
#
# If yes: there's hope of size 5 being achievable. If no: greedy
# witness is locally tight at size 6.

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
        if snf[k][k] = 0 then Error("zero invariant factor"); fi;
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

_outfile := "/tmp/minimal_family_154_snf_m3_5subsets.out";;
_stream  := OutputTextFile(_outfile, false);;
SetPrintFormattingStatus(_stream, false);;

PrintTo(_stream, "# m=3: 5-element subsets of greedy witness ",
        "{4, 6, 11, 22, 7, 16}\n");
PrintTo(_stream, "# Date: 2026-05-20\n\n");

Print("Loading m=3 data...\n");
_data3 := BuildRestrictionMatrices(3, "hap");;

_witness := [4, 6, 11, 22, 7, 16];;
PrintTo(_stream, "# Greedy witness (size 6): ", _witness, "\n\n");

# Test removing each one (size 5 subsets).
for _i in [1..6] do
    _sub := Concatenation(_witness{[1.._i-1]}, _witness{[_i+1..6]});
    _k := KernelOrder(_data3, _sub, true, true);
    PrintTo(_stream, "  remove EA[", _witness[_i], "] -> ", _sub,
            "  ker = ", _k, "\n");
od;

CloseStream(_stream);
Print("Wrote ", _outfile, "\n");
QUIT_GAP(0);
