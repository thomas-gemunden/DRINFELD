# minimal_family_154_subsets_m2.g
#
# Enumerate ALL 2^6 - 1 = 63 non-empty subsets of {EA_1, ..., EA_6} at
# m=2 and for each, test true injectivity of res: H^3(G; U(1)) ->
# oplus_{H in F} H^3(H; U(1)) by counting elements of the kernel
# (= elements of (Z/2)^9 × Z/8 that restrict to 0 in every H in F).
#
# Reports:
#   - smallest |F| with kernel = 0 (pure EA-only).
#   - smallest |F| with kernel = 0 when D_8 + Q_8 are also in the family.
#
# Also tests one specific reference family: {EA_1, EA_3, EA_5} (a
# putative "diagonal" subset spanning the 3 distinct EA orbits, if
# such structure exists at m=2).

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

RestrictToH := function(omega, M, torsion_H)
    local k_G, k_H, out, j, i;
    k_G := Length(omega);
    k_H := Length(torsion_H);
    out := List([1..k_H], j -> 0);
    for j in [1..k_H] do
        out[j] := Sum([1..k_G], i -> omega[i] * M[i][j]) mod torsion_H[j];
    od;
    return out;
end;;

VanishesEverywhere := function(omega, data, ea_indices, include_D8, include_Q8)
    local j;
    for j in ea_indices do
        if not IsRowZeroMod(
              RestrictToH(omega, data.res_EA_list[j],
                          data.torsion_EA_list[j]),
              data.torsion_EA_list[j]) then
            return false;
        fi;
    od;
    if include_D8 then
        if not IsRowZeroMod(
              RestrictToH(omega, data.res_D8, data.torsion_D8),
              data.torsion_D8) then
            return false;
        fi;
    fi;
    if include_Q8 and data.res_Q8 <> fail then
        if not IsRowZeroMod(
              RestrictToH(omega, data.res_Q8, data.torsion_Q8),
              data.torsion_Q8) then
            return false;
        fi;
    fi;
    return true;
end;;

SocleAt2Power := function(torsion_G, level)
    local k_G, ranges, i, sz, count, elements, idx, vec, ar, base;
    k_G := Length(torsion_G);
    ranges := [];
    for i in [1..k_G] do
        sz := Minimum(torsion_G[i], 2^level);
        Add(ranges, List([0..(sz - 1)], k -> k * (torsion_G[i] / sz)));
    od;
    count := Product(ranges, r -> Length(r));
    elements := [];
    for idx in [0..(count - 1)] do
        vec := List([1..k_G], i -> 0);
        ar := idx;
        for i in [1..k_G] do
            base := Length(ranges[i]);
            vec[i] := ranges[i][(ar mod base) + 1];
            ar := QuoInt(ar, base);
        od;
        if ForAny(vec, x -> x <> 0) then
            Add(elements, vec);
        fi;
    od;
    return elements;
end;;

KernelSize := function(data, full_group, ea_indices, include_D8, include_Q8)
    local count, omega;
    count := 0;
    for omega in full_group do
        if VanishesEverywhere(omega, data, ea_indices, include_D8, include_Q8)
        then
            count := count + 1;
        fi;
    od;
    return count;
end;;

# ---------------------------------------------------------------------
_outfile := "/tmp/minimal_family_154_subsets_m2.out";;
_stream  := OutputTextFile(_outfile, false);;
SetPrintFormattingStatus(_stream, false);;

PrintTo(_stream, "# Subset enumeration for minimal family at m=2 (full ",
        "injectivity test)\n");
PrintTo(_stream, "# Date: 2026-05-20\n\n");

Print("Loading m=2 restriction matrices...\n");
_data := BuildRestrictionMatrices(2, "hap");;
_full_group := SocleAt2Power(_data.torsion_G, 3);;  # 4095 elements

PrintTo(_stream, "# torsion_G = ", _data.torsion_G, "\n");
PrintTo(_stream, "# H^3 - 1 = ", Length(_full_group), " elements to test\n\n");

# Enumerate all 2^6 - 1 = 63 non-empty subsets of EAs.
# For each, test EA-only injectivity, and also EA + D_8 + Q_8 injectivity.

PrintTo(_stream, "## EA-only test (no D_8, no Q_8)\n");
PrintTo(_stream, "## subset | |F| | |ker|\n");
_ea_only_injective := [];
for _k in [1..6] do
    for _S in Combinations([1..6], _k) do
        _ks := KernelSize(_data, _full_group, _S, false, false);
        if _ks = 0 then
            PrintTo(_stream, "  ", _S, "  ", _k, "  ", _ks,
                    "  INJECTIVE\n");
            Add(_ea_only_injective, _S);
        fi;
    od;
od;
if Length(_ea_only_injective) = 0 then
    PrintTo(_stream, "  (no EA-only subset of any size yields ker=0)\n");
fi;
PrintTo(_stream, "\n");

PrintTo(_stream, "## EA + D_8 + Q_8 test\n");
PrintTo(_stream, "## subset | |F_EA| | |ker|\n");
_with_dq_injective := [];
# Include empty subset of EAs (just D_8 + Q_8).
_ks := KernelSize(_data, _full_group, [], true, true);
if _ks = 0 then
    PrintTo(_stream, "  []  0  0  INJECTIVE\n");
    Add(_with_dq_injective, []);
else
    PrintTo(_stream, "  []  0  ", _ks, "\n");
fi;
for _k in [1..6] do
    for _S in Combinations([1..6], _k) do
        _ks := KernelSize(_data, _full_group, _S, true, true);
        if _ks = 0 then
            PrintTo(_stream, "  ", _S, "  ", _k, "  ", _ks,
                    "  INJECTIVE\n");
            Add(_with_dq_injective, _S);
        fi;
    od;
od;
PrintTo(_stream, "\n");

# Smallest EA-only family that gives injectivity:
if Length(_ea_only_injective) > 0 then
    _min_ea_size := Minimum(List(_ea_only_injective, Length));
    PrintTo(_stream, "# Smallest EA-only injective family: |F| = ",
            _min_ea_size, "\n");
    PrintTo(_stream, "# Examples: ",
            Filtered(_ea_only_injective,
                     S -> Length(S) = _min_ea_size), "\n");
else
    PrintTo(_stream, "# No EA-only subset of any size yields injectivity.\n");
fi;
PrintTo(_stream, "\n");

# Smallest EA family with D_8 + Q_8:
if Length(_with_dq_injective) > 0 then
    _min_dq_size := Minimum(List(_with_dq_injective, Length));
    PrintTo(_stream, "# Smallest EA family (with D_8, Q_8 included) ",
            "giving injectivity: |F_EA| = ", _min_dq_size, "\n");
    PrintTo(_stream, "# Examples: ",
            Filtered(_with_dq_injective,
                     S -> Length(S) = _min_dq_size), "\n");
else
    PrintTo(_stream, "# Even all 6 EAs + D_8 + Q_8 not injective?? (bug)\n");
fi;
PrintTo(_stream, "\n");

CloseStream(_stream);
Print("Wrote ", _outfile, "\n");
QUIT_GAP(0);
