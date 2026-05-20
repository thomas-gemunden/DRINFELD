# minimal_family_154_spike.g
#
# Spike for issue #154 ("minimal detecting family for H^3(E_+(m); U(1))").
# Builds restriction matrices for E_+(2) and E_+(3), then asks at each m:
#
#   (a) Per-generator coverage: which max EAs detect which unit generator?
#   (b) Set-cover: what is the smallest subset of max EAs that jointly
#       detects every unit generator?
#   (c) Coverage with the {D_8, Q_8} sections always included (since the
#       current production family includes them for the A(4) cyclic
#       summand).
#   (d) Per-EA "essentiality": for each EA, are there generators it is the
#       SOLE detector of? (If yes, that EA must be in the minimal family.)
#
# Writes a detailed table to /tmp/minimal_family_154_spike_m{m}.out and
# a compact verdict to /tmp/minimal_family_154_spike_summary.out.
#
# Run via: gap -q -b minimal_family_154_spike.g
# (CWD = extraspecial_orbifolds/scripts/).

# We need the per-EA restriction matrices, the D_8 / Q_8 restriction
# matrices, and the unit-generator structure. All in BuildRestrictionMatrices.

ChangeDirectoryCurrent(
  "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-dvan-math-154/extraspecial_orbifolds/scripts");

Read("detecting_family_restriction.g");

# ---------------------------------------------------------------------
# Utility: row of a restriction matrix is the image of the i-th G-side
# unit generator. So we ask "is row[i] zero mod torsion_H?" to decide
# if EA_j detects the i-th generator.
# ---------------------------------------------------------------------

IsRowZeroMod := function(row, torsion)
    local j;
    for j in [1..Length(row)] do
        if row[j] mod torsion[j] <> 0 then
            return false;
        fi;
    od;
    return true;
end;;

# For a given m, build the (k_G x n_EA) "detect" matrix D where
#   D[i][j] = 1  iff  res_{EA_j}(e_i) is non-zero.
# Each column is the "detection footprint" of EA_j.

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

# Greedy set-cover and brute-force minimal-cover (for small m).
# We want the smallest collection of EA indices J s.t. for each row i,
# there exists j in J with D[i][j] = 1.

# Greedy: at each step pick the column covering most as-yet-uncovered
# rows. Returns the chosen index set (sorted).
GreedySetCover := function(D, mandatory)
    local k_G, n_EA, covered, chosen, i, j, best, best_cnt, cnt, c;
    k_G  := Length(D);
    n_EA := Length(D[1]);
    covered := List([1..k_G], i -> false);
    chosen := ShallowCopy(mandatory);
    for j in mandatory do
        for i in [1..k_G] do
            if D[i][j] = 1 then covered[i] := true; fi;
        od;
    od;
    while not ForAll(covered, x -> x) do
        best := fail;
        best_cnt := 0;
        for j in [1..n_EA] do
            if j in chosen then continue; fi;
            cnt := 0;
            for i in [1..k_G] do
                if not covered[i] and D[i][j] = 1 then cnt := cnt + 1; fi;
            od;
            if cnt > best_cnt then
                best := j;
                best_cnt := cnt;
            fi;
        od;
        if best = fail then
            # Some rows uncovered by ANY column - means no detecting subset.
            return rec(chosen := chosen, complete := false,
                       uncovered := Filtered([1..k_G], i -> not covered[i]));
        fi;
        AddSet(chosen, best);
        for i in [1..k_G] do
            if D[i][best] = 1 then covered[i] := true; fi;
        od;
    od;
    return rec(chosen := chosen, complete := true,
               uncovered := []);
end;;

# Brute-force: enumerate all subsets of [1..n_EA] and pick the smallest
# that covers every row.
BruteForceMinCover := function(D)
    local k_G, n_EA, best_size, best_set, k, S, covered, i, j, ok, mask;
    k_G  := Length(D);
    n_EA := Length(D[1]);
    best_size := n_EA + 1;
    best_set := fail;
    for k in [0..n_EA] do
        if k >= best_size then break; fi;
        for S in Combinations([1..n_EA], k) do
            # Check coverage.
            ok := true;
            for i in [1..k_G] do
                if ForAll(S, j -> D[i][j] = 0) then
                    ok := false;
                    break;
                fi;
            od;
            if ok then
                best_size := k;
                best_set := S;
                break;  # smallest at this size; no need to look at larger.
            fi;
        od;
        if best_set <> fail then break; fi;
    od;
    return rec(size := best_size, set := best_set);
end;;

# Identify EAs that are "essential" — there exists at least one
# generator detected ONLY by that EA (column-unique 1).
EssentialEAs := function(D)
    local k_G, n_EA, ess, i, j, ones;
    k_G  := Length(D);
    n_EA := Length(D[1]);
    ess := [];
    for i in [1..k_G] do
        ones := Filtered([1..n_EA], j -> D[i][j] = 1);
        if Length(ones) = 1 then
            AddSet(ess, ones[1]);
        fi;
    od;
    return ess;
end;;

# Distinct columns (= EAs with same detection footprint are merged).
DistinctFootprints := function(D)
    local k_G, n_EA, sigs, sig, j, i, eq, idx;
    k_G  := Length(D);
    n_EA := Length(D[1]);
    sigs := [];   # list of [column-as-list, representative-index]
    for j in [1..n_EA] do
        sig := List([1..k_G], i -> D[i][j]);
        eq := fail;
        for idx in [1..Length(sigs)] do
            if sigs[idx][1] = sig then eq := idx; break; fi;
        od;
        if eq = fail then
            Add(sigs, [sig, j]);
        fi;
    od;
    return sigs;
end;;

# Coverage WITH D_8 and Q_8 included as fixed family members.
PerGenDQDetection := function(data)
    local k_G, det_D8, det_Q8, i, row;
    k_G  := Length(data.torsion_G);
    det_D8 := List([1..k_G], i -> 0);
    det_Q8 := List([1..k_G], i -> 0);
    for i in [1..k_G] do
        row := data.res_D8[i];
        if not IsRowZeroMod(row, data.torsion_D8) then det_D8[i] := 1; fi;
        if data.res_Q8 <> fail then
            row := data.res_Q8[i];
            if not IsRowZeroMod(row, data.torsion_Q8) then det_Q8[i] := 1; fi;
        fi;
    od;
    return rec(D8 := det_D8, Q8 := det_Q8);
end;;

# ---------------------------------------------------------------------
# Main driver for one m. Writes to /tmp/minimal_family_154_spike_m<m>.out
# and returns a summary rec.
# ---------------------------------------------------------------------

AnalyseMinimalFamily := function(m)
    local out, stream, data, k_G, n_EA, D, dq, det_D8, det_Q8,
          dq_cov_idx, brute_EA, brute_EA_D8Q8, greedy_EA, greedy_EA_D8Q8,
          ess, sigs, i, j, row, summary;

    out := Concatenation("/tmp/minimal_family_154_spike_m", String(m), ".out");
    stream := OutputTextFile(out, false);
    SetPrintFormattingStatus(stream, false);

    PrintTo(stream, "# Minimal-family spike (issue #154) — m = ", m, "\n");
    PrintTo(stream, "# Date stamp: 2026-05-20\n\n");

    Print("[m=", m, "] Building restriction matrices...\n");
    data := BuildRestrictionMatrices(m, "hap");
    k_G  := Length(data.torsion_G);
    n_EA := Length(data.H_EA_list);

    PrintTo(stream, "# |G| = ", Order(data.G), "\n");
    PrintTo(stream, "# H^3(G; U(1)) torsion = ", data.torsion_G, "\n");
    PrintTo(stream, "# k_G = ", k_G, "  (number of unit generators)\n");
    PrintTo(stream, "# n_EA = ", n_EA,
            "  (G-conj classes of max EA; equals N_+(m,2))\n");
    PrintTo(stream, "# D_8 torsion = ", data.torsion_D8, "\n");
    if data.res_Q8 = fail then
        PrintTo(stream, "# Q_8 section: NONE (m=1 only)\n");
    else
        PrintTo(stream, "# Q_8 torsion = ", data.torsion_Q8, "\n");
    fi;
    PrintTo(stream, "\n");

    Print("[m=", m, "] Computing detection matrix...\n");
    D := PerEADetectionMatrix(data);
    dq := PerGenDQDetection(data);

    # ----- per-generator coverage table -----
    PrintTo(stream, "## Per-generator detection table\n");
    PrintTo(stream,
        "# Row i = gen i; columns = EA_1..EA_n_EA, then D_8, then Q_8.\n");
    PrintTo(stream,
        "# Entry: 1 = detected (res != 0), 0 = killed (res = 0).\n");
    PrintTo(stream, "# Also: ord_i = torsion_G[i].\n\n");
    for i in [1..k_G] do
        PrintTo(stream, "gen[", i, "] ord=", data.torsion_G[i],
                " EA=", D[i],
                " D8=", dq.D8[i],
                " Q8=", dq.Q8[i],
                " EA_count=", Sum(D[i]), "\n");
    od;
    PrintTo(stream, "\n");

    # ----- column (EA) footprints — which gens each EA detects -----
    PrintTo(stream, "## Per-EA footprint (which generators it detects)\n");
    for j in [1..n_EA] do
        PrintTo(stream, "EA[", j, "] detects ",
            Filtered([1..k_G], i -> D[i][j] = 1),
            "  (count=", Sum(List([1..k_G], i -> D[i][j])), ")\n");
    od;
    PrintTo(stream, "\n");

    # ----- distinct EA footprints -----
    sigs := DistinctFootprints(D);
    PrintTo(stream, "## Distinct EA footprints\n");
    PrintTo(stream, "# n_EA = ", n_EA,
            "; distinct = ", Length(sigs), "\n");
    for i in [1..Length(sigs)] do
        PrintTo(stream, "  footprint ", i, ": EA index ", sigs[i][2],
                " detects ", Sum(sigs[i][1]), " gens\n");
    od;
    PrintTo(stream, "\n");

    # ----- essential EAs (sole detectors) -----
    ess := EssentialEAs(D);
    PrintTo(stream, "## Essential EAs (sole detector for some generator)\n");
    PrintTo(stream, "# Essential EA indices: ", ess, "\n");
    PrintTo(stream, "# Count: ", Length(ess), "/", n_EA, "\n\n");

    # ----- which generators are covered by D_8 ∪ Q_8 alone? -----
    dq_cov_idx := Filtered([1..k_G],
        i -> dq.D8[i] = 1 or dq.Q8[i] = 1);
    PrintTo(stream, "## D_8 ∪ Q_8 coverage\n");
    PrintTo(stream, "# Generators detected by D_8 alone: ",
        Filtered([1..k_G], i -> dq.D8[i] = 1 and dq.Q8[i] = 0), "\n");
    PrintTo(stream, "# Generators detected by Q_8 alone: ",
        Filtered([1..k_G], i -> dq.Q8[i] = 1 and dq.D8[i] = 0), "\n");
    PrintTo(stream, "# Generators detected by both: ",
        Filtered([1..k_G], i -> dq.Q8[i] = 1 and dq.D8[i] = 1), "\n");
    PrintTo(stream, "# Generators not detected by D_8 or Q_8: ",
        Filtered([1..k_G],
            i -> dq.D8[i] = 0 and (data.res_Q8 = fail or dq.Q8[i] = 0)),
        "\n\n");

    # ----- minimal EA-only cover (brute force for small n_EA) -----
    if n_EA <= 12 then
        Print("[m=", m, "] Brute-force minimal EA-only cover...\n");
        brute_EA := BruteForceMinCover(D);
        PrintTo(stream, "## Minimal EA-only cover (brute force)\n");
        PrintTo(stream, "# Min |F_EA| = ", brute_EA.size, "\n");
        PrintTo(stream, "# Witness: EA indices ", brute_EA.set, "\n\n");
    else
        Print("[m=", m, "] n_EA=", n_EA,
              " too large for brute force; using greedy heuristic.\n");
        PrintTo(stream, "## Minimal EA-only cover (greedy heuristic; ",
                "n_EA=", n_EA, " too big for brute force)\n");
        greedy_EA := GreedySetCover(D, []);
        if greedy_EA.complete then
            PrintTo(stream, "# Greedy |F_EA| <= ", Length(greedy_EA.chosen),
                    "\n");
            PrintTo(stream, "# Greedy witness: ", greedy_EA.chosen, "\n\n");
        else
            PrintTo(stream, "# Greedy could NOT cover; uncovered gens: ",
                    greedy_EA.uncovered, "\n\n");
        fi;
    fi;

    # ----- minimal EA cover ASSUMING D_8 and Q_8 are always in the family
    # (production scenario). Then we only need to cover gens that D_8 ∪ Q_8
    # miss. -----
    PrintTo(stream, "## Minimal EA cover assuming {D_8, Q_8} always included\n");
    PrintTo(stream, "# (D_8 + Q_8 alone cover ", Length(dq_cov_idx),
            " of ", k_G, " gens.)\n");
    if Length(dq_cov_idx) = k_G then
        PrintTo(stream, "# D_8 + Q_8 ALREADY suffice — zero EAs needed.\n\n");
    else
        # Build sub-detection matrix on uncovered rows.
        # Actually simpler: run brute force on the full D again, but the
        # constraint is "cover all rows", and we treat D_8 ∪ Q_8 coverage
        # as a virtual extra column — equivalently, just check coverage on
        # rows NOT in dq_cov_idx and require EA cover on those.
        Print("[m=", m, "] Minimal EA cover w/ {D_8, Q_8} included...\n");
        if n_EA <= 12 then
            # Replace covered rows by a dummy 1 in every column - simpler:
            # build subD that is D with covered rows stripped.
            brute_EA_D8Q8 := BruteForceMinCover(
                List(Filtered([1..k_G], i -> not (i in dq_cov_idx)),
                     i -> D[i]));
            PrintTo(stream, "# Min |F_EA| above D_8 ∪ Q_8 = ",
                    brute_EA_D8Q8.size, "\n");
            PrintTo(stream, "# Witness: EA indices ", brute_EA_D8Q8.set, "\n");
        else
            greedy_EA_D8Q8 := GreedySetCover(
                List(Filtered([1..k_G], i -> not (i in dq_cov_idx)),
                     i -> D[i]),
                []);
            if greedy_EA_D8Q8.complete then
                PrintTo(stream, "# Greedy |F_EA| above D_8 ∪ Q_8 <= ",
                        Length(greedy_EA_D8Q8.chosen), "\n");
                PrintTo(stream, "# Greedy witness: ", greedy_EA_D8Q8.chosen,
                        "\n");
            else
                PrintTo(stream, "# Greedy could not cover gens ",
                        greedy_EA_D8Q8.uncovered,
                        " — D_8/Q_8 plus EAs insufficient?\n");
            fi;
        fi;
        PrintTo(stream, "\n");
    fi;

    CloseStream(stream);
    Print("[m=", m, "] Wrote ", out, "\n");
    summary := rec(
        m         := m,
        k_G       := k_G,
        n_EA      := n_EA,
        torsion_G := data.torsion_G,
        D         := D,
        detD8     := dq.D8,
        detQ8     := dq.Q8,
        essential := ess,
        distinct  := Length(sigs)
    );
    return summary;
end;;

# ---------------------------------------------------------------------
# Top-level. Summary file aggregates verdicts for m=2 (and m=3 if it
# fits in the wall-clock budget).
# ---------------------------------------------------------------------

_summary_path := "/tmp/minimal_family_154_spike_summary.out";;
_summary_stream := OutputTextFile(_summary_path, false);;
SetPrintFormattingStatus(_summary_stream, false);;

Emit := function(s)
    PrintTo(_summary_stream, s, "\n");
    Print(s, "\n");
end;;

Emit("# Minimal-family spike summary (issue #154)");
Emit("# Date: 2026-05-20");
Emit("");

_sm2 := AnalyseMinimalFamily(2);;
Emit(Concatenation("m=2: k_G=", String(_sm2.k_G),
    "  n_EA=", String(_sm2.n_EA),
    "  distinct_footprints=", String(_sm2.distinct),
    "  essential_EAs=", String(Length(_sm2.essential))));
Emit(Concatenation("    essential EA indices = ", String(_sm2.essential)));
Emit(Concatenation("    D_8 detects = ",
    String(Filtered([1.._sm2.k_G], i -> _sm2.detD8[i] = 1))));
Emit(Concatenation("    Q_8 detects = ",
    String(Filtered([1.._sm2.k_G], i -> _sm2.detQ8[i] = 1))));

_sm3 := AnalyseMinimalFamily(3);;
Emit(Concatenation("m=3: k_G=", String(_sm3.k_G),
    "  n_EA=", String(_sm3.n_EA),
    "  distinct_footprints=", String(_sm3.distinct),
    "  essential_EAs=", String(Length(_sm3.essential))));
Emit(Concatenation("    essential EA indices = ", String(_sm3.essential)));
Emit(Concatenation("    D_8 detects (count) = ",
    String(Length(Filtered([1.._sm3.k_G], i -> _sm3.detD8[i] = 1)))));
Emit(Concatenation("    Q_8 detects (count) = ",
    String(Length(Filtered([1.._sm3.k_G], i -> _sm3.detQ8[i] = 1)))));

CloseStream(_summary_stream);
Print("Summary written to ", _summary_path, "\n");
QUIT_GAP(0);
