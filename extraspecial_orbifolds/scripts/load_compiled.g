# load_compiled.g — load gac-compiled hot-path .so modules in place of
# their interpreted .g siblings (issue #286).
#
# Usage: Read("load_compiled.g") at the top of a driver/test. Each file
# is loaded compiled (via LoadDynamicModule) if a corresponding .so
# exists in compiled/, else falls back to the interpreted .g.
#
# Re-compile artefacts via `./compile_codebase.sh`.
#
# Modules are loaded in dependency order (top-of-tree first).

if not IsBoundGlobal("_LOAD_COMPILED_DIR") then
    _LOAD_COMPILED_DIR := Filename(
        DirectoryCurrent(), "compiled");
fi;

_LoadCompiledOrInterpreted := function(base, g_path)
    local so_path;
    so_path := Concatenation(_LOAD_COMPILED_DIR, "/", base, ".so");
    if IsExistingFile(so_path) then
        LoadDynamicModule(so_path);
    else
        Read(g_path);
    fi;
end;;

# Tier 1 — leaf modules (no DRINFELD-internal deps).
_LoadCompiledOrInterpreted("mod2_solver", "solver/mod2_solver.g");
_LoadCompiledOrInterpreted("transgression_kernel", "transgression_kernel.g");
_LoadCompiledOrInterpreted("abelian_branch_fast", "abelian_branch_fast.g");
# Issue #487: load abelian_modular_data_closed_form before
# untwisted_modular_data so the latter's IsAbelian-dispatch fast path
# is bound before ComputeUntwistedModularData fires for an abelian G.
_LoadCompiledOrInterpreted("abelian_modular_data_closed_form",
                           "abelian_modular_data_closed_form.g");
_LoadCompiledOrInterpreted("joint_permutation_matcher", "joint_permutation_matcher.g");
_LoadCompiledOrInterpreted("untwisted_modular_data", "untwisted_modular_data.g");
_LoadCompiledOrInterpreted("em_construction", "em_construction.g");
_LoadCompiledOrInterpreted("bw_lattice", "bw_lattice.g");
_LoadCompiledOrInterpreted("quillen_detecting_subgroup", "quillen_detecting_subgroup.g");
_LoadCompiledOrInterpreted("fsi_wrapper", "fsi_wrapper.g");

# Tier 2 — depend on tier 1.
_LoadCompiledOrInterpreted("z4_fallback", "solver/z4_fallback.g");
_LoadCompiledOrInterpreted("iterated_bockstein", "solver/iterated_bockstein.g");
_LoadCompiledOrInterpreted("krr_projector", "krr_projector.g");
_LoadCompiledOrInterpreted("d8_classifier", "d8_classifier.g");
_LoadCompiledOrInterpreted("q8_classifier", "q8_classifier.g");
_LoadCompiledOrInterpreted("restrict_to_subgroup", "restrict_to_subgroup.g");
_LoadCompiledOrInterpreted("brw_construction", "brw_construction.g");

# Tier 3 — depend on tier 1 + 2.
_LoadCompiledOrInterpreted("iscoboundary2_split", "solver/iscoboundary2_split.g");
_LoadCompiledOrInterpreted("ct_modular_data", "ct_modular_data.g");
_LoadCompiledOrInterpreted("brw_h3_action", "brw_h3_action.g");
_LoadCompiledOrInterpreted("brw_simples_action", "brw_simples_action.g");
_LoadCompiledOrInterpreted("keller_twist_is_trivial", "keller/keller_twist_is_trivial.g");

# Tier 4 — depend on all of the above.
_LoadCompiledOrInterpreted("detecting_family_restriction", "detecting_family_restriction.g");
_LoadCompiledOrInterpreted("keller_s_entry", "keller/keller_s_entry.g");

# Tier 5 — K-4b m=7 #449 hot-path additions, including transitive deps
# so that K4aClassify's `_K4A_LoadSibling` checks find every symbol it
# expects (UnimodSigma, EmUnimodGroup, BuildKRRSpectralCharactersSparse,
# TranslateSpectralDataToEPlus, etc.).
_LoadCompiledOrInterpreted("twisted_group_algebra", "twisted_group_algebra.g");
_LoadCompiledOrInterpreted("qforms_f2", "qforms_f2.g");
_LoadCompiledOrInterpreted("defect_rep_minus_id", "defect_rep_minus_id.g");
_LoadCompiledOrInterpreted("defect_rep_minus_id_optim", "defect_rep_minus_id_optim.g");
_LoadCompiledOrInterpreted("krr_spectral_characters", "krr_spectral_characters.g");
_LoadCompiledOrInterpreted("krr_spectral_characters_sparse", "krr_spectral_characters_sparse.g");
_LoadCompiledOrInterpreted("eplus_classes_closed_form", "eplus_classes_closed_form.g");
_LoadCompiledOrInterpreted("eplus_irreps_closed_form", "eplus_irreps_closed_form.g");
_LoadCompiledOrInterpreted("em_eplus_translate", "em_eplus_translate.g");
