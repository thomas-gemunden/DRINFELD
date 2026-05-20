# dvan_math_audit_orbits.g
# Light GAP probe (m=2, m=3) for the D-VAN math audit (issue #289).
#
# Computes Aut(E_+(m))-orbit count of maximal elementary abelian
# subgroups, plus the G-conjugacy class count. Cap = 1 GAP process.
# Writes results to /tmp/dvan_math_audit_orbits.out.

LoadPackage("hap");;

_outfile := "/tmp/dvan_math_audit_orbits.out";;
_stream := OutputTextFile(_outfile, false);;
SetPrintFormattingStatus(_stream, false);;

EmitLine := function(s)
    AppendTo(_stream, s);
    AppendTo(_stream, "\n");
    Print(s, "\n");
end;;

EmitLine("# D-VAN math audit (issue #289) — Aut(G)-orbit counts of max EAs");
EmitLine("# Date: 2026-05-19");
EmitLine("");

# ---------------------------------------------------------------------
# Helper: get max EA subgroups + count Aut(G) orbits
# ---------------------------------------------------------------------

AnalyseMaxEAsInExtraspecial := function(m)
    local G, expected_order, classes_subs, reps, max_eas,
          num_classes, Aut_G, AutGens, ImagesOfAuts, action_on_subgroups,
          orbits_subs, num_aut_orbits, info, sub, idx, i, j, found_class;
    G := ExtraspecialGroup(2^(2*m+1), "+");
    expected_order := 2^(m+1);

    classes_subs := ConjugacyClassesSubgroups(G);
    reps := List(classes_subs, Representative);
    max_eas := Filtered(reps,
        S -> IsElementaryAbelian(S) and Order(S) = expected_order);
    num_classes := Length(max_eas);

    EmitLine(Concatenation("=== m = ", String(m),
        ", |G| = ", String(Order(G)), " ==="));
    EmitLine(Concatenation("Total conjugacy classes of subgroups: ",
        String(Length(classes_subs))));
    EmitLine(Concatenation(
        "Conjugacy classes of maximal EA (rank ", String(m+1), "): ",
        String(num_classes)));

    if num_classes = 0 then return; fi;

    # Build Aut(G) and act on the set of conjugacy-class reps of max EAs.
    # Each automorphism phi sends max EA subgroup S to phi(S), which is
    # itself a max EA. We can identify the resulting subgroup with one of
    # the existing G-conj-class reps by checking conjugacy.
    Aut_G := AutomorphismGroup(G);
    EmitLine(Concatenation("|Aut(G)| = ", String(Order(Aut_G))));

    # Action of Aut(G) on the *set* of max-EA G-conjugacy-class reps.
    # Two G-conj-classes are in the same Aut-orbit if there exists an
    # automorphism sending one rep into the other class.
    # Note: inner automorphisms map a class to itself (since classes are
    # G-conjugacy invariant). So the action factors through Out(G).
    action_on_subgroups := function(S, phi)
        local imgS, k;
        imgS := Image(phi, S);
        # Find which conj class imgS belongs to: it must be conjugate in G
        # to one of the existing reps.
        for k in [1..Length(max_eas)] do
            if IsConjugate(G, imgS, max_eas[k]) then
                return max_eas[k];
            fi;
        od;
        # Shouldn't happen if the class list is complete.
        Error("AnalyseMaxEAsInExtraspecial: image of S not conjugate to ",
              "any listed max EA representative — class list incomplete");
    end;

    orbits_subs := OrbitsDomain(Aut_G, max_eas, action_on_subgroups);
    num_aut_orbits := Length(orbits_subs);

    EmitLine(Concatenation(
        "Aut(G)-orbits on max-EA G-conj-class reps: ",
        String(num_aut_orbits)));
    EmitLine(Concatenation(
        "Orbit sizes: ", String(List(orbits_subs, Length))));
    EmitLine("");
end;;

# m = 2 and m = 3 (E_+(3) has |G|=128, lattice ~700 subgroups — fast).
AnalyseMaxEAsInExtraspecial(2);
AnalyseMaxEAsInExtraspecial(3);

# ---------------------------------------------------------------------
# Bonus: count Q_8 and D_8 G-conjugacy-class reps inside E_+(2) and E_+(3)
# ---------------------------------------------------------------------

CountSubgroupKinds := function(m)
    local G, classes_subs, reps, d8s, q8s, eas;
    G := ExtraspecialGroup(2^(2*m+1), "+");
    classes_subs := ConjugacyClassesSubgroups(G);
    reps := List(classes_subs, Representative);
    d8s := Filtered(reps, S -> Order(S) = 8 and IdGroup(S) = [8, 3]);
    q8s := Filtered(reps, S -> Order(S) = 8 and IdGroup(S) = [8, 4]);
    eas := Filtered(reps,
        S -> IsElementaryAbelian(S) and Order(S) = 2^(m+1));
    EmitLine(Concatenation("--- m = ", String(m), " kind counts ---"));
    EmitLine(Concatenation("  D_8 G-conj classes: ", String(Length(d8s))));
    EmitLine(Concatenation("  Q_8 G-conj classes: ", String(Length(q8s))));
    EmitLine(Concatenation("  max-EA G-conj classes (rank ",
        String(m+1), "): ", String(Length(eas))));
end;;

CountSubgroupKinds(2);
CountSubgroupKinds(3);

CloseStream(_stream);
QUIT_GAP(0);
