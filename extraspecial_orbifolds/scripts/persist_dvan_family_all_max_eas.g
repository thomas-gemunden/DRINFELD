# Persist a D-VAN-compatible result.g for m ∈ {2, 3, 5} using the
# "all maximal EAs" set (NOT the D-VAN trimmed minimum family). This
# provides a unified `LoadDVANEAFamily(m)` for all m without depending
# on a prior D-VAN production run.
#
# The persisted family is in the `ea_generators_exp` schema (exponent
# vectors against `FamilyPcgs(ExtraspecialGroup(2^(2m+1), "+"))`), so
# `LoadDVANEAFamily(m)` reconstructs subgroups deterministically.
#
# Driver usage:
#   gap -q -b -c 'MPARAM := 3; Read("persist_dvan_family_all_max_eas.g"); QUIT;'
#
# Output: extraspecial_orbifolds/computed/dvan_min_family/m<m>/result.g
#
# Note: this is the "all max EAs" set, which is detecting (the full
# union covers all 1-dim cohomology classes via Quillen). The K-4a
# unified dispatch uses it for multi-EA classification; performance is
# worse than the D-VAN trimmed minimum but the dispatch path is the
# same as m=7. Replace with the trimmed family when D-VAN production
# at m ∈ {3, 5} is run.

if not IsBound(MPARAM) then
    Error("persist_dvan_family_all_max_eas.g: set MPARAM (m value) before Read");
fi;

Read("solver/logging_util.g");
Read("detecting_family_restriction.g");

_LogPhase("persist-dvan-family", "MPARAM = ", MPARAM, " starting ...");

# At m = 7 there's an existing trimmed family on disk; don't overwrite.
if MPARAM = 7 then
    Error("persist_dvan_family_all_max_eas.g: m = 7 already has a ",
          "persisted file (D-VAN trimmed minimum); this driver is for ",
          "m ∈ {2, 3, 5} (all max EAs).");
fi;

_LogPhase("persist-dvan-family", "Building restriction matrices for m = ",
          MPARAM, " (HAP source) ...");
t0 := Runtime();
brm := BuildRestrictionMatrices(MPARAM, "hap");;
_LogPhase("persist-dvan-family", "BuildRestrictionMatrices done in ",
          (Runtime() - t0) / 1000., " s; |H_EA_list| = ",
          Length(brm.H_EA_list));

# Build a fresh ExtraspecialGroup(2^(2m+1), "+") and translate each H_EA
# subgroup's generators to PC-element exponent vectors against its
# FamilyPcgs.
G_target := ExtraspecialGroup(2^(2*MPARAM + 1), "+");;
fam_pcgs_target := FamilyPcgs(G_target);;

# brm.H_EA_list lives inside G_source = brm.setup_G.group. We need an
# isomorphism G_source -> G_target. Both are presentations of the
# extraspecial group 2^(2m+1)_+; IsomorphismGroups picks one up.
G_source := Parent(brm.H_EA_list[1]);;
_LogPhase("persist-dvan-family",
          "G_source = ", StructureDescription(G_source),
          "; G_target = ", StructureDescription(G_target));

iso := IsomorphismGroups(G_source, G_target);;
if iso = fail then
    Error("persist-dvan-family: no isomorphism G_source -> G_target");
fi;

ea_generators_exp := [];
for H in brm.H_EA_list do
    gens_src := GeneratorsOfGroup(H);
    gens_tgt := List(gens_src, g -> Image(iso, g));
    exp_tuple := List(gens_tgt, g -> ExponentsOfPcElement(fam_pcgs_target, g));
    Add(ea_generators_exp, exp_tuple);
od;
_LogPhase("persist-dvan-family", "Translated ", Length(ea_generators_exp),
          " EAs to PC-exp schema");

# Persist
out_dir := Concatenation(
    "../computed/dvan_min_family/m", String(MPARAM));
result_path := Concatenation(out_dir, "/result.g");
Exec(Concatenation("mkdir -p ", out_dir));

stream := OutputTextFile(result_path, false);;
SetPrintFormattingStatus(stream, false);

dvan_result := rec(
    m := MPARAM,
    ea_count := Length(ea_generators_exp),
    family_size := Length(ea_generators_exp),
    include_D8 := true,
    include_Q8 := true,
    source := "hap-all-max-eas",
    notes := Concatenation(
        "All maximal elementary abelian subgroups of E_+(", String(MPARAM),
        ") of rank m+1. This is NOT the D-VAN trimmed minimum family; it's ",
        "the union over all max EAs. Detection is by Quillen + ",
        "AM04 (every nonzero class of H^3(E_+(m); U(1)) restricts ",
        "non-trivially to at least one of {max EA, D_8, Q_8}). ",
        "Provides a unified `LoadDVANEAFamily(m)` for m < 7 without ",
        "requiring a prior D-VAN trim production run."),
    ea_generators_exp := ea_generators_exp);

PrintTo(stream, "# All max EAs of E_+(", MPARAM,
        "); persisted by persist_dvan_family_all_max_eas.g\n");
PrintTo(stream, "# Schema: dvan_m", MPARAM,
        "_result.ea_generators_exp = list of exponent-vector tuples\n");
PrintTo(stream, "# against FamilyPcgs(ExtraspecialGroup(2^(2*", MPARAM,
        "+1), \"+\")).\n");
PrintTo(stream, "dvan_m", MPARAM, "_result := ", dvan_result, ";;\n");
CloseStream(stream);

_LogPhase("persist-dvan-family", "Wrote ", result_path,
          "; ea_count = ", Length(ea_generators_exp));
