# orbit_cache_persist.g — disk persistence for per-BRW-orbit cocycle-basis
# caches (issue #336).
#
# A-5b at m=5 spends ~15 h building 5 orbit-rep cocycle-basis caches (one
# per BRW-conjugacy orbit). The caches are kept in module-level GAP state
# (`_basis_cache_by_class` in solver/snf_wrapper.g, plus the driver's
# local `orbit_caches` list in run_e_plus_m_kernel_hap.g). When the GAP
# process crashes — as it did at m=5 on 2026-05-20 — all that work is
# lost on restart.
#
# This file adds disk persistence so a relaunch reads the on-disk caches
# (< 1 min for m=5 totals) and skips the rebuild.
#
# ---------------------------------------------------------------------
# On-disk format
# ---------------------------------------------------------------------
#
# Each orbit's cache is saved as a GAP source file at
#
#   <out_dir>/orbit_<orbit_idx>_cache.g
#
# The file body is a single `return rec(...);` expression suitable for
# `ReadAsFunction(path)()`. Fields:
#
#   version         : integer, currently 1. Bumped on format change.
#   fingerprint     : record (see _OrbitCacheFingerprint below) used to
#                     detect mismatched inputs (different G, different
#                     UCT.exponent, different cohomology torsion, etc.).
#   rep_exps        : pc-exponent vector of the orbit representative
#                     (relative to FamilyPcgs of the group).
#   elts_exps       : list of pc-exponent vectors for each centraliser
#                     element, in `AsList(C)` order. Length n.
#   n               : Length(elts_exps). Redundant with the length above,
#                     stored for fast sanity check.
#   table_rows      : nested list of integers, shape (n*n) x k. Each row
#                     is the cocycle-basis c_g table for one (a, b) pair.
#                     Entries in [0..exp-1].
#
# Notes:
#   * `C` (centralizer subgroup) is REBUILT on load as `Centralizer(G, rep)`.
#     The driver has G in scope.
#   * `idx_map` (NewDictionary) is REBUILT on load from `elts`. Cheap.
#   * `table_gf2` is REBUILT on load from `table` via the same formula
#     BuildPerClassCocycleBasis uses (`(QuoInt(x, r_half) mod 2) * one_gf2`).
#     This halves the on-disk size vs persisting both views; verified
#     bit-for-bit equivalent by reconstruction.
#
# Why a GAP source file rather than IO_Pickle? Matches the convention
# used by computed/transgression/<m>/kernel.g and the rest of the repo.
# All persisted state in this codebase is human-readable GAP source.
#
# Auto-wrap hazard (per CLAUDE.md guidance): GAP's `PrintTo` and
# `AppendTo` wrap long lines at ~80 chars with "\\\n". For cache tables
# with thousands of integers per row, this produces unreadable files
# that fail to re-parse. We use OutputTextFile + SetPrintFormattingStatus
# on the stream so output is emitted verbatim.
#
# ---------------------------------------------------------------------
# Fingerprint
# ---------------------------------------------------------------------
#
# Goal: detect when the on-disk cache was built against a *different*
# input setup than the current run, so we rebuild rather than silently
# return a wrong answer.
#
# Captured fields:
#   - m              : the extraspecial parameter (so a stale m=3 cache
#                      doesn't get accidentally loaded for an m=5 run
#                      via the same path).
#   - group_order    : |G| (matches IsomorphismPcGroup(EmGroup(m))).
#   - centraliser_order : |C_G(rep)| (n).
#   - torsion        : the H^3(G; U(1)) torsion vector. Catches UCT
#                      basis changes if the resolution / SmallGroups
#                      library shifts.
#   - exponent       : the H^3 exponent (LCM of torsion).
#   - k              : Length(setup.UCT.hombasis), the number of H^3
#                      generators. Redundant with Length(torsion); we
#                      store it to make the table-row shape check
#                      explicit on load.
#   - rep_exps       : pc-exponent vector of the rep. Strong per-orbit
#                      discriminator inside a single (m, G) setup.
#   - gap_version    : GAPInfo.Version. Catches major GAP bumps that
#                      could change Pcgs / SmallGroups numbering.
#
# Equality is checked field-by-field. Any mismatch -> rebuild.
#
# ---------------------------------------------------------------------
# Functions exported
# ---------------------------------------------------------------------
#
# _OrbitCacheFingerprint(setup, rep, m_param)
#   Returns the fingerprint record described above.
#
# SaveOrbitCache(path, orbit_idx, m_param, setup, rep, cache)
#   Persists `cache` (the cocycle-basis cache record from
#   BuildPerClassCocycleBasis or the inline identity-class builder) to
#   `path`. Writes atomically: first to `path.tmp`, then RenameFile.
#
# LoadOrbitCache(path, expected_fp, G)
#   Reads the file at `path`, validates the fingerprint against
#   `expected_fp`, and reconstructs the cache record. Returns the cache
#   on success, `fail` on missing file, fingerprint mismatch, version
#   mismatch, or parse error.
#
# ---------------------------------------------------------------------
# Atomicity
# ---------------------------------------------------------------------
#
# The save path writes to `<path>.tmp` and renames on success. A crash
# during the write leaves a `.tmp` file that the loader ignores. The
# rename is atomic on POSIX, so a reader never sees a half-written
# cache file at `<path>`.


# ---------------------------------------------------------------------
# Internal: shell-quote a file path for use inside Exec("mv ...").
# Wraps in single quotes and escapes any embedded single quotes via the
# '\'' shell idiom. Paths in this repo are tame (no quote chars), but
# we still handle them safely.
# ---------------------------------------------------------------------
_OCP_ShellQuote := function(s)
    local result, c;
    result := "'";
    for c in s do
        if c = '\'' then
            Append(result, "'\\''");
        else
            Add(result, c);
        fi;
    od;
    Add(result, '\'');
    return result;
end;;


# ---------------------------------------------------------------------
# Fingerprint
# ---------------------------------------------------------------------

_OrbitCacheFingerprint := function(setup, rep, m_param)
    local G, pcgs, rep_exps;
    G := setup.group;
    if not IsPcGroup(G) then
        Error("_OrbitCacheFingerprint: setup.group must be a PcGroup");
    fi;
    pcgs := FamilyPcgs(G);
    rep_exps := ExponentsOfPcElement(pcgs, rep);
    return rec(
        m := m_param,
        group_order := Order(G),
        centraliser_order := Order(Centralizer(G, rep)),
        torsion := ShallowCopy(setup.torsion),
        exponent := setup.exponent,
        k := setup.num_generators,
        rep_exps := rep_exps,
        gap_version := GAPInfo.Version
    );
end;;


# Compare two fingerprint records field-by-field. Returns true iff all
# captured fields match. We compare lists element-wise (GAP's `=` on
# lists is element-wise, which is what we want).
_OrbitCacheFingerprintEqual := function(fp1, fp2)
    local fields, f;
    if not IsRecord(fp1) or not IsRecord(fp2) then
        return false;
    fi;
    fields := ["m", "group_order", "centraliser_order", "torsion",
               "exponent", "k", "rep_exps", "gap_version"];
    for f in fields do
        if not IsBound(fp1.(f)) or not IsBound(fp2.(f)) then
            return false;
        fi;
        if fp1.(f) <> fp2.(f) then
            return false;
        fi;
    od;
    return true;
end;;


# ---------------------------------------------------------------------
# Save
# ---------------------------------------------------------------------

_ORBIT_CACHE_FORMAT_VERSION := 1;;

# Write a single orbit cache to disk.
#
# Arguments:
#   path        : absolute or relative path to the cache file.
#                 Convention: <out_dir>/orbit_<i>_cache.g.
#   orbit_idx   : integer, the orbit index in `orbits_data` (1-based).
#                 Stored as a top-level field for human inspection;
#                 NOT part of the fingerprint match.
#   m_param     : the extraspecial parameter.
#   setup       : the cohomology setup record (group, UCT, etc.).
#   rep         : the orbit-rep group element.
#   cache       : the cache record returned by BuildPerClassCocycleBasis
#                 (or the inline identity-class builder), with fields
#                 (C, table, table_gf2, elts, n, idx_map).
#
# Writes <path>.tmp first, then renames to <path> on completion.
SaveOrbitCache := function(path, orbit_idx, m_param, setup, rep, cache)
    local tmp_path, stream, fp, pcgs, G, elts_exps, a, k, n, rep_exps;
    G := setup.group;
    pcgs := FamilyPcgs(G);
    n := cache.n;
    k := setup.num_generators;
    fp := _OrbitCacheFingerprint(setup, rep, m_param);
    rep_exps := fp.rep_exps;
    elts_exps := List(cache.elts, x -> ExponentsOfPcElement(pcgs, x));

    tmp_path := Concatenation(path, ".tmp");
    # Pre-delete any leftover .tmp from a prior failed save.
    if IsExistingFile(tmp_path) then
        RemoveFile(tmp_path);
    fi;

    stream := OutputTextFile(tmp_path, false);
    if stream = fail then
        Error("SaveOrbitCache: could not open ", tmp_path, " for writing");
    fi;
    # Disable GAP's 80-col line-wrap. Critical: table rows can be
    # thousands of integers wide; a backslash-newline mid-row would
    # produce a malformed source file.
    SetPrintFormattingStatus(stream, false);

    PrintTo(stream,
        "# Orbit cocycle-basis cache (issues #336, #365) — auto-generated.\n",
        "# Orbit index: ", orbit_idx, "\n",
        "# m: ", m_param, "\n",
        "# |C(rep)| = n = ", n, ", k = ", k, "\n",
        "# Format version: ", _ORBIT_CACHE_FORMAT_VERSION, "\n",
        "#\n",
        "# Re-populate via:\n",
        "#   _ORBIT_CACHE_DATA := fail;;\n",
        "#   Read(\"", path, "\");;\n",
        "#   # _ORBIT_CACHE_DATA now holds the cache record.\n",
        "#   LoadOrbitCache wraps this and reconstructs C, elts, idx_map, table_gf2.\n",
        "#\n",
        "# The leading top-level assignment (instead of `return rec(...)` ",
        "with\n",
        "# ReadAsFunction) is required because at m=5 the table_rows literal ",
        "has\n",
        "# 4.2M rows, which exceeds GAP's per-function bytecode size limit ",
        "in\n",
        "# the function created by ReadAsFunction. Read() of a top-level ",
        "# statement bypasses that limit.\n",
        "_ORBIT_CACHE_DATA := rec(\n",
        "    version := ", _ORBIT_CACHE_FORMAT_VERSION, ",\n",
        "    orbit_idx := ", orbit_idx, ",\n",
        "    fingerprint := rec(\n",
        "        m := ", fp.m, ",\n",
        "        group_order := ", fp.group_order, ",\n",
        "        centraliser_order := ", fp.centraliser_order, ",\n",
        "        torsion := ", fp.torsion, ",\n",
        "        exponent := ", fp.exponent, ",\n",
        "        k := ", fp.k, ",\n",
        "        rep_exps := ", fp.rep_exps, ",\n",
        "        gap_version := \"", fp.gap_version, "\"\n",
        "    ),\n",
        "    rep_exps := ", rep_exps, ",\n",
        "    n := ", n, ",\n",
        "    elts_exps := [\n");
    # Emit elements one per line for readability; each is a small list.
    for a in [1..n] do
        if a < n then
            PrintTo(stream, "        ", elts_exps[a], ",\n");
        else
            PrintTo(stream, "        ", elts_exps[a], "\n");
        fi;
    od;
    PrintTo(stream,
        "    ],\n",
        "    table_rows := [\n");
    # Table has n*n rows; we emit each row inline. Each row is k integers
    # in [0..exp-1]. GAP's Print of a small integer list is the canonical
    # source representation.
    for a in [1..n * n] do
        if a < n * n then
            PrintTo(stream, "        ", cache.table[a], ",\n");
        else
            PrintTo(stream, "        ", cache.table[a], "\n");
        fi;
    od;
    PrintTo(stream,
        "    ]\n",
        ");;\n");
    CloseStream(stream);
    # Atomic rename: only happens if the above PrintTo + CloseStream
    # completes without error. A mid-write crash leaves <path>.tmp,
    # which LoadOrbitCache does not look at. We shell out to `mv`
    # because GAP 4.15.1 does not expose a top-level RenameFile;
    # `mv` is atomic on POSIX (rename(2)) when both paths are on
    # the same filesystem, which is the case here (both under
    # OutDir / TEST_DIR).
    Exec(Concatenation("mv -f ",
                       _OCP_ShellQuote(tmp_path),
                       " ",
                       _OCP_ShellQuote(path)));
end;;


# ---------------------------------------------------------------------
# Load
# ---------------------------------------------------------------------
#
# Try to load an orbit cache from disk and reconstruct the live record.
#
# Returns `fail` (with a Print message) if:
#   - the file does not exist, OR
#   - the file's `version` field is unknown, OR
#   - the file's fingerprint does not match `expected_fp`, OR
#   - the file's stored n / k / table shape is inconsistent with the
#     fingerprint, OR
#   - reading the file raises an error (caught via CALL_WITH_CATCH).
#
# Returns the reconstructed cache record on success, with fields:
#   (C, table, table_gf2, elts, n, idx_map)
# matching the shape produced by BuildPerClassCocycleBasis.
LoadOrbitCache := function(path, expected_fp, G)
    local catch, data, n, k, rep_exps, rep, C, pcgs, elts, idx_map,
          table, exp_val, r_half, one_gf2, table_gf2, table_gf2_bot,
          table_gf2_top_T, a, t_phase;
    if not IsExistingFile(path) then
        return fail;
    fi;
    if not IsPcGroup(G) then
        Error("LoadOrbitCache: G must be a PcGroup");
    fi;
    # Issue #383: per-phase logging so the on-disk codepath is visible.
    # Issue #384: switch to _LogPhase (timestamped) if available so each
    # phase line shows wall-clock time and a `[load-cache]` tag.
    t_phase := Runtime();
    if IsBoundGlobal("_LogPhase") then
        _LogPhase("load-cache", "Read() ", path, " ...");
    else
        Print("      LoadOrbitCache: Read() ", path, " ...\n");
    fi;

    # Issue #365: prefer Read() on the new top-level-assignment file
    # format. ReadAsFunction wraps the file in a function whose
    # bytecode hits GAP's per-function size limit at m=5 (the
    # table_rows literal alone is ~692M cells). Read() processes
    # top-level statements directly without that limit.
    _ORBIT_CACHE_DATA := fail;
    catch := CALL_WITH_CATCH(Read, [path]);
    if catch[1] = true and IsRecord(_ORBIT_CACHE_DATA) then
        data := _ORBIT_CACHE_DATA;
        _ORBIT_CACHE_DATA := fail;  # release reference for GC.
    else
        # Fallback for the legacy `return rec(...);;` format (any cache
        # written before issue #365 landed). The Read() above failed
        # because top-level `return` is a syntax error; CALL_WITH_CATCH
        # caught it. ReadAsFunction works on files small enough to fit
        # under the per-function bytecode limit (m=2/3 caches).
        _ORBIT_CACHE_DATA := fail;
        catch := CALL_WITH_CATCH(ReadAsFunction, [path]);
        if catch[1] = false then
            Print("LoadOrbitCache: failed to load(", path, "); ",
                  "treating as missing.\n");
            return fail;
        fi;
        # ReadAsFunction returns `fail` (not throws) when the parser
        # hits the per-function size limit. Detect this explicitly so
        # we don't propagate the "no method for CallFuncList on fail"
        # crash that was issue #365.
        if catch[2] = fail then
            Print("LoadOrbitCache: ReadAsFunction returned fail at ",
                  path, " (likely parser size limit); treating as ",
                  "missing.\n");
            return fail;
        fi;
        data := catch[2]();
        if not IsRecord(data) then
            Print("LoadOrbitCache: file ", path, " did not return a record.\n");
            return fail;
        fi;
    fi;

    if not IsBound(data.version) or data.version <> _ORBIT_CACHE_FORMAT_VERSION then
        Print("LoadOrbitCache: file ", path, " has version ",
              data.version, " (current = ", _ORBIT_CACHE_FORMAT_VERSION,
              "); rebuilding.\n");
        return fail;
    fi;

    if not IsBound(data.fingerprint)
            or not _OrbitCacheFingerprintEqual(data.fingerprint, expected_fp) then
        Print("LoadOrbitCache: fingerprint mismatch at ", path,
              "; rebuilding.\n");
        return fail;
    fi;

    # Shape sanity.
    n := data.n;
    k := expected_fp.k;
    if not IsBound(data.elts_exps) or Length(data.elts_exps) <> n then
        Print("LoadOrbitCache: elts_exps length mismatch at ", path,
              "; rebuilding.\n");
        return fail;
    fi;
    if not IsBound(data.table_rows) or Length(data.table_rows) <> n * n then
        Print("LoadOrbitCache: table_rows length mismatch (got ",
              Length(data.table_rows), ", want ", n * n, ") at ", path,
              "; rebuilding.\n");
        return fail;
    fi;
    if not IsBound(data.rep_exps) then
        Print("LoadOrbitCache: missing rep_exps at ", path,
              "; rebuilding.\n");
        return fail;
    fi;

    if IsBoundGlobal("_LogPhase") then
        _LogPhase("load-cache", "Read() done in ",
                  (Runtime() - t_phase) / 1000.,
                  " s; reconstructing live record ...");
    else
        Print("      LoadOrbitCache: Read() done in ",
              (Runtime() - t_phase) / 1000.,
              " s; reconstructing live record ...\n");
    fi;
    t_phase := Runtime();
    # Reconstruct the live record.
    pcgs := FamilyPcgs(G);
    rep_exps := data.rep_exps;
    rep := PcElementByExponents(pcgs, rep_exps);
    C := Centralizer(G, rep);
    if Order(C) <> n then
        Print("LoadOrbitCache: rebuilt Centralizer has order ",
              Order(C), " but cache n = ", n,
              "; rebuilding.\n");
        return fail;
    fi;

    elts := List(data.elts_exps, e -> PcElementByExponents(pcgs, e));
    # Build idx_map (matches BuildPerClassCocycleBasis exactly).
    idx_map := NewDictionary(elts[1], true, elts);
    for a in [1..n] do
        AddDictionary(idx_map, elts[a], a);
    od;

    if IsBoundGlobal("_LogPhase") then
        _LogPhase("load-cache", "live record done in ",
                  (Runtime() - t_phase) / 1000.,
                  " s; promoting table to IsMatrixRep + ",
                  "rebuilding table_gf2 ...");
    else
        Print("      LoadOrbitCache: live record done in ",
              (Runtime() - t_phase) / 1000.,
              " s; promoting table to IsMatrixRep + ",
              "rebuilding table_gf2 ...\n");
    fi;
    t_phase := Runtime();
    # Issue #387 audit-tier3 P16: the comment below was the original
    # intent but the call IS a no-op for integer matrices (see
    # `docs/superpowers/research/2026-06-02-perf-audit-full.md` — TNUM
    # unchanged, matvec wall unchanged). Left as a marker; the
    # downstream `table * vec_target` stays on the interpreted path
    # until a structural fix (e.g. batched GF(2)) lands.
    # Original intent: promote table to GAP's matrix rep so downstream
    # `table * vec_target` would hit the compiled integer matvec.
    table := List(data.table_rows, ShallowCopy);
    ConvertToMatrixRep(table);

    # Rebuild table_gf2 from table via the same formula
    # BuildPerClassCocycleBasis uses.
    exp_val := expected_fp.exponent;
    r_half := exp_val / 2;
    one_gf2 := One(GF(2));
    table_gf2 := List(table, row ->
        List(row, x -> (QuoInt(x, r_half) mod 2) * one_gf2));
    ConvertToMatrixRep(table_gf2, GF(2));
    # Issue #391 (Approach B): also derive bit_0(table) packed-GF(2) view.
    # On-disk format is unchanged (table_rows holds the integer entries);
    # table_gf2_bot is derived on load, same as table_gf2_top.
    table_gf2_bot := List(table, row ->
        List(row, x -> (x mod 2) * one_gf2));
    ConvertToMatrixRep(table_gf2_bot, GF(2));
    # Issue #391 (A+B combine, PR #394): derive column-major view of
    # table_gf2_top for the sparsity-aware GF(2) column-XOR path in
    # the Path Z bit-pack dispatcher. On-disk format unchanged.
    table_gf2_top_T := TransposedMat(table_gf2);
    ConvertToMatrixRep(table_gf2_top_T, GF(2));
    if IsBoundGlobal("_LogPhase") then
        _LogPhase("load-cache", "table promotion + table_gf2 / ",
                  "table_gf2_bot / table_gf2_top_T rebuild done in ",
                  (Runtime() - t_phase) / 1000., " s");
    else
        Print("      LoadOrbitCache: table promotion + table_gf2 / ",
              "table_gf2_bot / table_gf2_top_T rebuild done in ",
              (Runtime() - t_phase) / 1000., " s\n");
    fi;

    return rec(C := C, table := table,
               table_gf2 := table_gf2,           # back-compat alias
               table_gf2_top := table_gf2,
               table_gf2_top_T := table_gf2_top_T,
               table_gf2_bot := table_gf2_bot,
               elts := elts, n := n, idx_map := idx_map);
end;;


# Convenience: also populate the module-level `_basis_cache_by_class`
# cache (in solver/snf_wrapper.g) so that any downstream
# BuildPerClassCocycleBasis(setup, rep, C) calls within the same GAP
# session hit the loaded result and skip the rebuild.
#
# Only call this after a successful LoadOrbitCache.
PopulateBasisCacheFromLoaded := function(setup, rep, cache)
    local key;
    if not IsBound(_basis_cache_by_class) then
        # snf_wrapper.g not loaded — caller is in a context where the
        # downstream BuildPerClassCocycleBasis flow isn't active, so
        # there is nothing to pre-populate.
        return;
    fi;
    if not IsBound(_SafeIdString) then
        return;
    fi;
    key := Concatenation("G", _SafeIdString(setup.group),
                         "_g", String(rep),
                         "_C", _SafeIdString(cache.C),
                         "_n", String(Size(cache.C)));
    _basis_cache_by_class.(key) := cache;
end;;
