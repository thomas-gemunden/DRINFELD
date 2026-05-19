# dvan_math_audit_m2_anomaly.g
# Probe the m=2 single-(EA, D_8, Q_8) anomaly to confirm whether the
# restriction is injective at degree 3, modulo Aut(G).
#
# Strategy:
# 1. Build the 6 max EAs in E_+(2), and the {D_8, Q_8} sections.
# 2. Construct the 10 unit-class generators of H^3(E_+(2); U(1)) via
#    HAP + UCT (UCT.hombasis).
# 3. For each unit generator: compute its restriction to the single
#    "first" max EA, to D_8, to Q_8. Check which classes have ZERO
#    restriction at H = (EA_1, D_8, Q_8), and whether they vanish at
#    the OTHER EAs too.
# 4. Confirm: a class is "globally trivial" iff it has zero restriction
#    to ALL 6 max EAs ∪ D_8 ∪ Q_8.

# Use scripts/detecting_family_restriction.g for the matrix-building.

ChangeDirectoryCurrent(
  "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-dvan-math/extraspecial_orbifolds/scripts");

Read("detecting_family_restriction.g");

# This loads HAP + transgression_kernel + quillen_detecting_subgroup.

_outfile := "/tmp/dvan_math_audit_m2_anomaly.out";;
_stream := OutputTextFile(_outfile, false);;
SetPrintFormattingStatus(_stream, false);;

EmitLine := function(s)
    AppendTo(_stream, s);
    AppendTo(_stream, "\n");
    Print(s, "\n");
end;;

EmitLine("# D-VAN m=2 anomaly probe (issue #289)");
EmitLine("# Confirming whether 1-EA + D_8 + Q_8 misses 2/10 unit generators.");
EmitLine("");

# Build restriction matrices for m=2 via the canonical HAP path.
data := BuildRestrictionMatrices(2, "hap");
G    := data.G;

EmitLine(Concatenation("# m=2: |G| = ", String(Order(G))));
EmitLine(Concatenation("# H^3(G; U(1)) torsion = ", String(data.torsion_G)));
EmitLine(Concatenation("# Number of unit generators (k_G): ",
    String(Length(data.torsion_G))));
EmitLine(Concatenation("# G-conj classes of max EA: ",
    String(Length(data.H_EA_list))));
EmitLine(Concatenation("# Torsion of one max EA: ", String(data.torsion_E)));
EmitLine(Concatenation("# Torsion of D_8: ", String(data.torsion_D8)));
EmitLine(Concatenation("# Torsion of Q_8: ", String(data.torsion_Q8)));
EmitLine("");

# For each of the k_G unit generators e_i (= unit row vector with 1 in
# position i, 0 elsewhere in Z/torsion_G[i]), compute restrictions and
# check vanishing under the "minimal" family {EA_1, D_8, Q_8} and the
# "full" family {EA_1, ..., EA_6, D_8, Q_8}.

k_G := Length(data.torsion_G);
n_EA := Length(data.H_EA_list);
EmitLine("# Per-generator restriction summary:");
EmitLine(Concatenation(
    "# col 1 = gen index, col 2 = ord, col 3 = (res to EA_1 zero?), ",
    "col 4 = (res to D_8 zero?), col 5 = (res to Q_8 zero?), ",
    "col 6 = (res to ANY of EA_2..EA_6 nonzero?)"));

both_zero_minimal_count := 0;
both_zero_full_count := 0;
single_minimal_missed := [];
for i in [1..k_G] do
    # e_i = unit vector at coordinate i, scaled so it's a generator of the
    # i-th Z/torsion_G[i] factor (i.e. coordinate is 1).
    # Restriction is left-multiplication by res_{H} (a k_G x k_H matrix);
    # so the i-th row of res_H is the image of the i-th G-side generator.

    # EA_1 row:
    row_EA1 := data.res_EA_list[1][i];
    zero_EA1 := ForAll(row_EA1, x -> x mod data.torsion_E[Position(row_EA1, x)] = 0);
    # Better: row is already reduced mod torsion_E; check all-zero:
    zero_EA1 := ForAll([1..Length(row_EA1)],
        j -> row_EA1[j] mod data.torsion_E[j] = 0);

    # D_8 row:
    row_D8 := data.res_D8[i];
    zero_D8 := ForAll([1..Length(row_D8)],
        j -> row_D8[j] mod data.torsion_D8[j] = 0);

    # Q_8 row:
    if data.res_Q8 = fail then
        zero_Q8 := true;  # no constraint
    else
        row_Q8 := data.res_Q8[i];
        zero_Q8 := ForAll([1..Length(row_Q8)],
            j -> row_Q8[j] mod data.torsion_Q8[j] = 0);
    fi;

    # All EAs (EA_2..EA_n_EA):
    any_nonzero_other_EA := false;
    for k in [2..n_EA] do
        row_k := data.res_EA_list[k][i];
        is_zero_k := ForAll([1..Length(row_k)],
            j -> row_k[j] mod data.torsion_EA_list[k][j] = 0);
        if not is_zero_k then
            any_nonzero_other_EA := true;
            break;
        fi;
    od;

    # Decisions:
    minimal_trivial := zero_EA1 and zero_D8 and zero_Q8;
    full_trivial    := minimal_trivial and (not any_nonzero_other_EA);

    if minimal_trivial then
        both_zero_minimal_count := both_zero_minimal_count + 1;
        if not full_trivial then
            Add(single_minimal_missed, i);
        fi;
    fi;
    if full_trivial then
        both_zero_full_count := both_zero_full_count + 1;
    fi;

    EmitLine(Concatenation(
        "gen ", String(i),
        "  ord=", String(data.torsion_G[i]),
        "  EA_1=", String(zero_EA1),
        "  D_8=", String(zero_D8),
        "  Q_8=", String(zero_Q8),
        "  other_EA_nonzero=", String(any_nonzero_other_EA),
        "  minimal_triv=", String(minimal_trivial),
        "  full_triv=", String(full_trivial)));
od;

EmitLine("");
EmitLine(Concatenation(
    "# Minimal family (EA_1+D_8+Q_8) reports trivial for: ",
    String(both_zero_minimal_count), " generators"));
EmitLine(Concatenation(
    "# Full family (6 EAs + D_8 + Q_8) reports trivial for: ",
    String(both_zero_full_count), " generators"));
EmitLine(Concatenation(
    "# Generators marked 'minimal-trivial but full-non-trivial' (= ",
    "the 'erroneous trivials' if we used minimal only): ",
    String(single_minimal_missed)));

CloseStream(_stream);
QUIT_GAP(0);
