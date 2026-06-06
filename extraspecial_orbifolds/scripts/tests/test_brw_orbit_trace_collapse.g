# test_brw_orbit_trace_collapse.g  --  math finding for issue #447 Change B.
#
# Tests the math claim of issue #447 Change B:
#
#   > TraceOnOmega0(h, m) = Tr(T_h) is BRW-EQUIVARIANT:
#   > for y in BRW(m) and h in E_+(m),
#   > Tr(T_{y h y^{-1}}) = Tr(T_h).
#   > Combined with the fact that BRW(m) has 4 orbits on E_+(m)-conjugacy
#   > classes, Tr(T_h) takes only 4 distinct values.
#
# EMPIRICAL FINDING (run on 2026-06-06 against the spectral builder at
# main commit bcbbd92):
#
#   * At m=3, `TraceOnOmega0` IS a class function on E_+(m)
#     (verified: it agrees on every element of every conjugacy class).
#
#   * The BRW(m) action on E_+(m)-conjugacy classes does have exactly
#     4 orbits (= 4 orbit-types `id`, `minus_one`, `sigma2`,
#     `sigma_1sigma_2`), and BRW(m) acts TRANSITIVELY on each type.
#
#   * However, `Tr(T_h)` is NOT BRW-invariant.  Within a single BRW orbit
#     it takes multiple values:
#       - sigma2 (35 classes):           Tr in {0, 8}
#       - sigma_1sigma_2 (28 classes):   Tr in {-4, 0, 4}
#     So `Tr(T_h)` takes 5 distinct values overall (16, 8, 4, 0, -4)
#     across the 65 classes at m=3, NOT 4.
#
#   * The math intuition behind the claim — "T_h is BRW-equivariant" —
#     does not hold for the intertwiner constructed in
#     `defect_rep_minus_id_optim.g`.  T_h is built in a basis tied to a
#     specific Witt / symplectic decomposition; conjugating h by a BRW
#     element produces a new h' for which T_{h'} is the intertwiner in
#     the SAME basis, not in a basis transformed by y.  The two traces
#     are not equal in general.
#
# Consequence: implementing Change B as written would inject WRONG
# trace values for ~30 / 35 sigma2 classes (the ones whose true Tr=0
# would be replaced by 8) and ~25 / 28 sigma_1sigma_2 classes — that is,
# `CharacterMultiplicities` would return wrong multiplicities, and the
# downstream K-4b verdict would be incorrect.
#
# This test therefore documents the math finding (PASS = finding
# reproduces) and is itself a regression guard: if a future refactor
# *makes* TraceOnOmega0 BRW-equivariant (e.g., by adding a basis-change
# wrapper), the corresponding "4 distinct values" assertion will start
# holding and we'll want to revisit the spec.
#
# Run from the scripts/ directory:
#   gap -q -b -c 'Read("tests/test_brw_orbit_trace_collapse.g");'

SetInfoLevel(InfoWarning, 1);

# ---- Locate and load sibling modules ---------------------------------
_loaded := false;;
_self_path := INPUT_FILENAME();;
if _self_path <> fail and _self_path <> "stream" then
    _self_dir := _self_path{[1..Length(_self_path)
                          - Length("/test_brw_orbit_trace_collapse.g")]};;
    _scripts_dir := Concatenation(_self_dir, "/..");
    _cand := Concatenation(_scripts_dir,
                            "/krr_spectral_characters_sparse.g");
    if IsExistingFile(_cand) then
        ChangeDirectoryCurrent(_scripts_dir);
        Read("bw_lattice.g");
        Read("em_construction.g");
        Read("twisted_group_algebra.g");
        Read("qforms_f2.g");
        Read("defect_rep_minus_id.g");
        Read("defect_rep_minus_id_optim.g");
        Read("untwisted_modular_data.g");
        Read("krr_spectral_characters.g");
        Read("krr_spectral_characters_sparse.g");
        _loaded := true;
    fi;
fi;;
if not _loaded then
    Error("cannot locate krr_spectral_characters_sparse.g; ",
          "run from extraspecial_orbifolds/scripts/tests/.");
fi;

failures := [];;

AssertOrLog := function(label, cond)
    if cond then
        Print("  PASS: ", label, "\n");
    else
        Print("  FAIL: ", label, "\n");
        Add(failures, label);
    fi;
end;;

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

# ---------------------------------------------------------------------
# Setup at m = 3.
# ---------------------------------------------------------------------
Print("\n================================================================\n");
Print("  Test: BRW-orbit Tr collapse math finding at m = 3\n");
Print("================================================================\n");

m := 3;;
n := 2^m;;
z := -IdentityMat(n);;

ResetSparseTraceCache();;
G := EmUnimodGroup(m);;
idx := BuildSimpleIndex(G);;
i_central := PositionProperty(idx.reps, r -> r = z);;
if i_central = fail then
    Error("could not find central class -I");
fi;
cls_data := CentraliserClassData(idx, i_central);;
num_classes_C := cls_data.num;
Print("\nCentral class i = ", i_central,
      "; C_G(-I) has ", num_classes_C, " conjugacy classes ",
      "(expected 2^(2m)+1 = ", 2^(2*m) + 1, ")\n");
CheckEqual("(0) num_classes_C = 2^(2m) + 1",
           num_classes_C, 2^(2*m) + 1);

# ---------------------------------------------------------------------
# Compute the per-class traces (one trace per E_+(m)-conjugacy class).
# ---------------------------------------------------------------------
Print("\nComputing ", num_classes_C, " per-class traces ...\n");
t0 := Runtime();;
traces_per_class := [];;
for j in [1..num_classes_C] do
    h := cls_data.reps[j];
    Add(traces_per_class, TraceOnOmega0(h, m));
od;;
t_per_class := (Runtime() - t0) / 1000.0;
Print("Per-class traces wall: ", t_per_class, " s (",
      num_classes_C, " trace calls).\n");

# ---------------------------------------------------------------------
# Classify classes into BRW-orbit types.
# ---------------------------------------------------------------------
class_types := _SparseClassifyEmBRWTypes(cls_data.classes);;

type_counts := rec();;
for t in class_types do
    if IsBound(type_counts.(t)) then
        type_counts.(t) := type_counts.(t) + 1;
    else
        type_counts.(t) := 1;
    fi;
od;;

expected_sigma2 := 2^(2*m - 1) + 2^(m - 1) - 1;;
expected_sigma1sigma2 := 2^(2*m - 1) - 2^(m - 1);;
Print("\nPer-type class counts:\n");
for t in SortedList(RecNames(type_counts)) do
    Print("  ", t, " : ", type_counts.(t), "\n");
od;
Print("Expected at m=", m, ": id=1, minus_one=1, sigma2=",
      expected_sigma2, ", sigma_1sigma_2=", expected_sigma1sigma2,
      " (total ", 1 + 1 + expected_sigma2 + expected_sigma1sigma2,
      ")\n");

CheckEqual("(1a) per-type count: id = 1",
           type_counts.id, 1);
CheckEqual("(1b) per-type count: minus_one = 1",
           type_counts.minus_one, 1);
CheckEqual("(1c) per-type count: sigma2 matches closed-form",
           type_counts.sigma2, expected_sigma2);
CheckEqual("(1d) per-type count: sigma_1sigma_2 matches closed-form",
           type_counts.sigma_1sigma_2, expected_sigma1sigma2);
CheckEqual("(1e) per-type counts sum to num_classes_C",
           Sum(List(RecNames(type_counts), nm -> type_counts.(nm))),
           num_classes_C);

# ---------------------------------------------------------------------
# (2) Math claim of issue #447 Change B: Tr(T_h) is BRW-invariant,
# i.e., within each BRW-orbit type all class traces equal.
# Empirically: this is FALSE.  We document the finding here.
# ---------------------------------------------------------------------
Print("\nPer-type Tr values seen (one entry per class, grouped):\n");
type_values := rec();;
for j in [1..Length(class_types)] do
    t := class_types[j];
    tr := traces_per_class[j];
    if not IsBound(type_values.(t)) then
        type_values.(t) := [];
    fi;
    Add(type_values.(t), tr);
od;;
for t in SortedList(RecNames(type_values)) do
    Print("  ", t, " : Set = ",
          AsSet(type_values.(t)), "\n");
od;

# Total distinct trace values across all classes.
distinct_traces := AsSet(traces_per_class);;
Print("\nDistinct trace values overall: ", distinct_traces, "\n");
Print("|Distinct trace values| = ", Length(distinct_traces), "\n");

# Issue #447 Change B claim: |Distinct trace values| should be 4.
brw_invariant_holds :=
    Length(AsSet(type_values.id)) = 1
    and Length(AsSet(type_values.minus_one)) = 1
    and Length(AsSet(type_values.sigma2)) = 1
    and Length(AsSet(type_values.sigma_1sigma_2)) = 1;
Print("\nIssue #447 Change B claim 'Tr(T_h) is BRW-invariant': ",
      brw_invariant_holds, "\n");

# This SHOULD be `false` per the empirical finding. The test PASSES
# if this finding REPRODUCES (i.e., the claim does NOT hold), which
# documents the math correctly.  If a future refactor restores BRW
# invariance, this assertion will start failing and the spec should
# be revisited.
AssertOrLog(
    "(2) issue #447 Change B math claim 'Tr(T_h) is BRW-invariant' reproduces FALSE",
    not brw_invariant_holds);

# ---------------------------------------------------------------------
# (3) Diagnostic: count distinct Tr values per type.
# Expected per the empirical finding at m=3:
#     id : 1 distinct  (Tr=16)
#     minus_one : 1 distinct  (Tr=16)
#     sigma2 : 2 distinct  (Tr in {0, 8})
#     sigma_1sigma_2 : 2 distinct  (Tr in {-4, 4})
# Total distinct across all classes: 5 (16, 8, 4, 0, -4)
# ---------------------------------------------------------------------
Print("\nDistinct trace count per BRW-orbit type (empirical 2026-06-06):\n");
expected_per_type := rec(
    id := 1,
    minus_one := 1,
    sigma2 := 2,
    sigma_1sigma_2 := 2
);
for t in SortedList(RecNames(type_values)) do
    n_distinct := Length(AsSet(type_values.(t)));
    Print("  ", t, " : ", n_distinct, " distinct (expected ",
          expected_per_type.(t), ")\n");
    CheckEqual(Concatenation("(3) distinct Tr count: ", t),
               n_distinct, expected_per_type.(t));
od;

# Total distinct trace count (across all classes).
CheckEqual("(3.total) total distinct trace count at m=3",
           Length(distinct_traces), 5);

# ---------------------------------------------------------------------
# (4) Wall comparison: per-class trace loop vs the (incorrect) 4-eval
# collapse.  We report the wall but do NOT use the collapsed traces
# downstream (they're known wrong).
# ---------------------------------------------------------------------
Print("\nWall: per-class (correct) vs 4-eval (incorrect math) collapse:\n");
ResetSparseTraceCache();;
t0 := Runtime();;
collapsed_4_traces := rec();;
seen_types := [];;
for j in [1..Length(class_types)] do
    t := class_types[j];
    if not IsBound(collapsed_4_traces.(t)) then
        collapsed_4_traces.(t) := TraceOnOmega0(cls_data.reps[j], m);
        Add(seen_types, t);
    fi;
od;;
t_collapsed := (Runtime() - t0) / 1000.0;
Print("  per-class (correct)         : ", t_per_class, " s (",
      num_classes_C, " trace calls)\n");
Print("  4-eval collapse (incorrect) : ", t_collapsed, " s (",
      Length(seen_types), " trace calls)\n");
if t_collapsed > 0.0 then
    Print("  ratio (per-class / collapsed): ",
          t_per_class / t_collapsed,
          " (at m=3 the per-call cost dominates; at m=7\n",
          "   the ratio would be ~", 2^14 / 4,
          ":1 IF the math were correct, which it is NOT)\n");
else
    Print("  ratio: collapsed wall < 1ms; per-class wall = ",
          t_per_class, " s\n");
fi;

# Construct what the (wrong) collapsed traces would look like, for
# diagnostic comparison.
traces_collapsed_wrong := List(class_types, t -> collapsed_4_traces.(t));;

# Count mismatches between correct and wrong.
mismatch_count := 0;;
for j in [1..Length(traces_per_class)] do
    if traces_per_class[j] <> traces_collapsed_wrong[j] then
        mismatch_count := mismatch_count + 1;
    fi;
od;;
Print("\nMismatch count (per-class vs 4-eval): ", mismatch_count,
      " / ", num_classes_C,
      " classes would have been given a WRONG trace by Change B.\n");

# ---------------------------------------------------------------------
# Summary.
# ---------------------------------------------------------------------
Print("\n================================================================\n");
if Length(failures) = 0 then
    Print("test_brw_orbit_trace_collapse: PASS\n");
    Print("  (the empirical math finding reproduces: Tr(T_h) is\n");
    Print("   NOT BRW-invariant at m=3; issue #447 Change B is\n");
    Print("   mathematically incorrect as written.)\n");
else
    Print("test_brw_orbit_trace_collapse: FAIL (", Length(failures),
          " checks failed)\n");
    for f in failures do
        Print("  - ", f, "\n");
    od;
fi;
Print("================================================================\n");

QUIT_GAP(Length(failures));
