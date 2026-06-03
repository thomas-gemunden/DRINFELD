# load_compiled.g — load gac-compiled hot-path .so modules in place of
# their interpreted .g siblings (issue #286).
#
# Usage: Read("load_compiled.g") at the top of a driver/test. Each file
# is loaded compiled (via LoadDynamicModule) if a corresponding .so
# exists in compiled/, else falls back to the interpreted .g.
#
# Re-compile artefacts via `./compile_codebase.sh`.

if not IsBoundGlobal("_LOAD_COMPILED_DIR") then
    _LOAD_COMPILED_DIR := Filename(
        DirectoryCurrent(), "compiled");
fi;

_LoadCompiledOrInterpreted := function(base)
    local so_path, g_path;
    so_path := Concatenation(_LOAD_COMPILED_DIR, "/", base, ".so");
    g_path := Concatenation(base, ".g");
    if IsExistingFile(so_path) then
        LoadDynamicModule(so_path);
        Print("[load_compiled] LOADED compiled ", so_path, "\n");
    else
        Read(g_path);
        Print("[load_compiled] FALLBACK to interpreted ", g_path,
              " (no compiled .so at ", so_path, ")\n");
    fi;
end;;

_LoadCompiledOrInterpreted("abelian_branch_fast");
