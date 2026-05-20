# minimal_family_154_strong_test.g
#
# STRONG injectivity test for candidate detecting families at m=2.
# Per-unit-generator detection is NECESSARY but not SUFFICIENT for
# injectivity of res: H^3(G; U(1)) -> oplus H^3(H_i; U(1)) — the map
# could still kill a linear combination omega = sum c_i e_i.
#
# This script tests true injectivity at m=2 by enumerating the
# 2-SOCLE of H^3(E_+(2); U(1)) = (Z/2)^9 × Z/8. The 2-socle is
# (Z/2)^9 × {0, 4} ≅ (Z/2)^10 (1024 elements). Every order-2 element
# of H^3(G; U(1)) lies in the 2-socle; if a candidate family F detects
# the 2-socle non-trivially (i.e., no nonzero socle elt restricts to 0
# in every H_i in F), then F detects the entire 2-torsion. Combined
# with the (separate) Z/4 / Z/8 detection (which is checked by the
# behaviour on the higher-order generators), this is the genuine
# injectivity test.
#
# We then ALSO do the full 4-socle check: enumerate (Z/2)^9 × {0, 2, 4, 6}
# = 4096 elements (the 4-torsion subgroup), and check no nonzero one
# is in the kernel.
#
# At m=3 the H^3 is (Z/2)^34 × Z/4; 2-socle = (Z/2)^34 × {0,2}, size
# 2^35 ≈ 3.4e10 elements — infeasible to enumerate. We instead compute
# the kernel via Smith Normal Form on the augmented restriction matrix.

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

# Apply restriction matrix M (k_G x k_H) to coefficient vector omega
# (length k_G); returns the H-side coord vector mod torsion_H.
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

# Test: does omega vanish under every H in the family?
VanishesEverywhere := function(omega, data, ea_indices, include_D8, include_Q8)
    local j, row, M, t;
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

# Enumerate elements of a sub-bilattice of Z^{k_G} mod torsion_G.
# `level` = which 2-torsion-power "shell" to enumerate: level=1 is
# 2-socle (each generator scaled to its order-2 element); level=2 is
# 4-socle (each generator scaled to its order-4 element if it exists);
# etc. Returns coefficient vectors WITHOUT (0,...,0).
SocleAt2Power := function(torsion_G, level)
    local k_G, allowed, i, elements, ranges, ar, base, idx, vec, sz, count;
    k_G := Length(torsion_G);
    # For each coord i, the order-2^level subgroup of Z/torsion_G[i]
    # has size min(torsion_G[i], 2^level), with step = torsion_G[i] /
    # min(torsion_G[i], 2^level).
    ranges := [];
    for i in [1..k_G] do
        sz := Minimum(torsion_G[i], 2^level);
        Add(ranges, List([0..(sz - 1)], k -> k * (torsion_G[i] / sz)));
    od;
    # Cartesian product of ranges.
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
        # Skip the zero vector.
        if ForAny(vec, x -> x <> 0) then
            Add(elements, vec);
        fi;
    od;
    return elements;
end;;

# ---------------------------------------------------------------------
_outfile := "/tmp/minimal_family_154_strong_test_m2.out";;
_stream  := OutputTextFile(_outfile, false);;
SetPrintFormattingStatus(_stream, false);;

PrintTo(_stream, "# Strong injectivity test for minimal family at m=2\n");
PrintTo(_stream, "# Date: 2026-05-20\n\n");

Print("Loading m=2 restriction matrices...\n");
_data := BuildRestrictionMatrices(2, "hap");;
PrintTo(_stream, "# torsion_G = ", _data.torsion_G, "\n");
PrintTo(_stream, "# k_G = ", Length(_data.torsion_G), "\n");
PrintTo(_stream, "# n_EA = ", Length(_data.H_EA_list), "\n\n");

# Enumerate the 8-socle = full H^3 (=4096 elements at m=2).
# torsion_G = [2,2,...,2,8] so socle level 3 (= 2^3 = 8) gives full group.
_full_torsion_group := SocleAt2Power(_data.torsion_G, 3);;
_socle_2 := SocleAt2Power(_data.torsion_G, 1);;
_socle_4 := SocleAt2Power(_data.torsion_G, 2);;
PrintTo(_stream, "# 2-socle size (nonzero): ", Length(_socle_2), "\n");
PrintTo(_stream, "# 4-socle size (nonzero): ", Length(_socle_4), "\n");
PrintTo(_stream, "# full group size (nonzero): ", Length(_full_torsion_group), "\n\n");

# Candidate families to test.
# We test:
#   1. {EA[3]} alone — was the singleton claim.
#   2. {EA[6]} alone — second singleton candidate.
#   3. {EA[3], D_8, Q_8}.
#   4. {EA[6], D_8, Q_8}.
#   5. {EA[3], EA[6]} — pair.
#   6. {D_8, Q_8} alone (no EAs).
#   7. Full N_+(2, 2) = all 6 EAs + D_8 + Q_8 (the production baseline).

TestFamily := function(name, ea_indices, include_D8, include_Q8)
    local killed_full, killed_socle2, killed_socle4, omega, w;
    killed_full   := [];
    killed_socle2 := [];
    killed_socle4 := [];
    for omega in _full_torsion_group do
        if VanishesEverywhere(omega, _data, ea_indices, include_D8, include_Q8) then
            Add(killed_full, omega);
        fi;
    od;
    for omega in _socle_2 do
        if VanishesEverywhere(omega, _data, ea_indices, include_D8, include_Q8) then
            Add(killed_socle2, omega);
        fi;
    od;
    for omega in _socle_4 do
        if VanishesEverywhere(omega, _data, ea_indices, include_D8, include_Q8) then
            Add(killed_socle4, omega);
        fi;
    od;
    PrintTo(_stream, "## Family ", name, " : EA=", ea_indices,
            " D8=", include_D8, " Q8=", include_Q8, "\n");
    PrintTo(_stream, "  killed in 2-socle (1023 total):  ",
            Length(killed_socle2), "\n");
    PrintTo(_stream, "  killed in 4-socle (4095 total):  ",
            Length(killed_socle4), "\n");
    PrintTo(_stream, "  killed in full H^3 (4095 total): ",
            Length(killed_full), "\n");
    PrintTo(_stream, "  INJECTIVE = ", Length(killed_full) = 0, "\n");
    if Length(killed_full) > 0 and Length(killed_full) <= 10 then
        PrintTo(_stream, "  killed elements: ", killed_full, "\n");
    fi;
    PrintTo(_stream, "\n");
end;;

Print("Testing candidate families at m=2...\n");
TestFamily("{EA[3]} only",       [3], false, false);
TestFamily("{EA[6]} only",       [6], false, false);
TestFamily("{EA[3], D8, Q8}",    [3], true,  true);
TestFamily("{EA[6], D8, Q8}",    [6], true,  true);
TestFamily("{EA[3], EA[6]}",     [3, 6], false, false);
TestFamily("{D8, Q8} only",      [], true,  true);
TestFamily("Full 6 EAs + D8 + Q8", [1, 2, 3, 4, 5, 6], true, true);

CloseStream(_stream);
Print("Wrote ", _outfile, "\n");
QUIT_GAP(0);
