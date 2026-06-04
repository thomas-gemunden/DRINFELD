# salvage_dvan_m7_result.g — one-off recovery from PR #429 driver's
# broken pc-element serialisation (issue #427 follow-up).
#
# The PR #429 driver's run (2026-06-04) successfully computed
# `_DETF_TrimmedFamily(7)` and wrote result.g — but in the agent #427
# worktree (path drift; CWD-at-launch issue) AND with pc-elements
# serialised by symbolic name (`f15, f1*f8*f10*f11, ...`) which GAP
# can't Read back without setting up the f1..f15 bindings.
#
# This script:
#   1. Loads E_+(7) via _DETF_BuildSetupG_LHS(7).
#   2. Binds f1..f15 globally to the pc-generators.
#   3. Reads the broken result.g.
#   4. Persists a new result.g at the correct location using
#      EXPONENT VECTORS for ea_generators (portable, round-trips).
#
# Usage:
#   cd extraspecial_orbifolds/scripts
#   gap -q -b -c 'Read("salvage_dvan_m7_result.g"); QUIT;'

Read("solver/logging_util.g");
Read("detecting_family_restriction.g");

_LogPhase("salvage", "=== salvage_dvan_m7_result.g ===");

source_path := Concatenation(
    "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD/",
    ".claude/worktrees/agent-a1f84fc77d7b2d283/",
    "extraspecial_orbifolds/computed/dvan_min_family/m7/result.g");;
target_path := "../computed/dvan_min_family/m7/result.g";;

if not IsExistingFile(source_path) then
    Error("salvage: source ", source_path, " not found");
fi;

_LogPhase("salvage", "Building setup_G via _DETF_BuildSetupG_LHS(7) ...");
setup_G := _DETF_BuildSetupG_LHS(7);;
G := setup_G.group;;
fam_pcgs := FamilyPcgs(G);;

_LogPhase("salvage", "|FamilyPcgs| = ", Length(fam_pcgs),
          " (expect 15 for E_+(7))");

if Length(fam_pcgs) <> 15 then
    Error("salvage: expected 15 pc-generators, got ", Length(fam_pcgs));
fi;

# Bind f1..f15 globally so the Read of source result.g resolves them.
for f_idx in [1..15] do
    name := Concatenation("f", String(f_idx));
    if IsBoundGlobal(name) then
        UnbindGlobal(name);
    fi;
    BindGlobal(name, fam_pcgs[f_idx]);
od;
_LogPhase("salvage", "Bound f1..f15 to pc generators");

if IsBoundGlobal("dvan_m7_result") then
    UnbindGlobal("dvan_m7_result");
fi;
Read(source_path);
if not IsBoundGlobal("dvan_m7_result") then
    Error("salvage: post-Read dvan_m7_result not bound");
fi;
_LogPhase("salvage", "Source Read OK. ea_count = ", dvan_m7_result.ea_count,
          ", final_ker = ", dvan_m7_result.final_ker,
          ", locally_tight = ", dvan_m7_result.locally_tight);

# Convert ea_generators from pc-elements to integer exponent vectors.
ea_gens_exp := List(dvan_m7_result.ea_generators,
    gen_tuple -> List(gen_tuple, e -> ExponentsOfPcElement(fam_pcgs, e)));;
ea_gens_sorted_exp := List(dvan_m7_result.ea_generators_sorted,
    gen_tuple -> List(gen_tuple, e -> ExponentsOfPcElement(fam_pcgs, e)));;

_LogPhase("salvage", "Converted ea_generators to exponent vectors. ",
          "First EA's first elt exponents: ", ea_gens_exp[1][1]);

result_portable := rec(
    m := dvan_m7_result.m,
    source := dvan_m7_result.source,
    ea_indices_chosen := dvan_m7_result.ea_indices_chosen,
    ea_indices_chosen_sorted := dvan_m7_result.ea_indices_chosen_sorted,
    ea_generators_exp := ea_gens_exp,
    ea_generators_sorted_exp := ea_gens_sorted_exp,
    include_D8 := dvan_m7_result.include_D8,
    include_Q8 := dvan_m7_result.include_Q8,
    final_ker := dvan_m7_result.final_ker,
    ea_count := dvan_m7_result.ea_count,
    family_size := dvan_m7_result.family_size,
    greedy_log := dvan_m7_result.greedy_log,
    locally_tight := dvan_m7_result.locally_tight,
    drop_one_kers := dvan_m7_result.drop_one_kers,
    walltime_ms := dvan_m7_result.walltime_ms,
    sample_size := dvan_m7_result.sample_size,
    total_lagrangians := dvan_m7_result.total_lagrangians,
    salvaged_from := source_path,
    salvage_note := "ea_generators_exp replaces ea_generators (exponent vectors round-trip cleanly via Read)"
);;

stream := OutputTextFile(target_path, false);;
SetPrintFormattingStatus(stream, false);
PrintTo(stream, "# D-VAN m=7 minimum detecting family.\n");
PrintTo(stream, "# Salvaged from PR #429 driver run via ",
        "salvage_dvan_m7_result.g.\n");
PrintTo(stream, "# Original f1..f15 pc-element serialisation replaced ",
        "by ea_generators_exp (integer exponent vectors).\n");
PrintTo(stream, "dvan_m7_result := ", result_portable, ";;\n");
CloseStream(stream);
_LogPhase("salvage", "Wrote ", target_path);

# Verify post-write Read.
UnbindGlobal("dvan_m7_result");
Read(target_path);
if not IsBoundGlobal("dvan_m7_result")
   or not IsBound(dvan_m7_result.ea_generators_exp) then
    Error("salvage: post-write Read failed");
fi;
_LogPhase("salvage", "Post-write Read PASS. |ea_generators_exp| = ",
          Length(dvan_m7_result.ea_generators_exp),
          ", each of size ", Length(dvan_m7_result.ea_generators_exp[1]));
_LogPhase("salvage", "=== SALVAGE DONE ===");
