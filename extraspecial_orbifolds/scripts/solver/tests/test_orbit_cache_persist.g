# test_orbit_cache_persist.g — verify the issue #336 orbit-cache disk
# persistence: save + reload round-trip preserves the cache structure.
#
# Strategy (CHEAP, m=2): build one orbit's cocycle-basis cache via
# BuildPerClassCocycleBasis, persist it via SaveOrbitCache, then load
# via LoadOrbitCache. Check:
#
#   1. Loaded cache.n == original cache.n.
#   2. Loaded cache.table is element-for-element equal to original.
#   3. Loaded cache.table_gf2 is element-for-element equal to original.
#   4. Loaded cache.elts has the same group elements (by equality).
#   5. Loaded cache.idx_map looks up to the same indices.
#   6. Loaded cache.C has the same Order as original.
#   7. Re-saving (with a different orbit_idx label) followed by
#      LoadOrbitCache with a MISMATCHED fingerprint returns `fail`.
#
# Usage:
#   gap -q -b -o 4g /path/to/test_orbit_cache_persist.g
#
# This script Reads the persistence module + snf_wrapper.g and runs
# entirely at m=2 so it finishes in seconds.

LoadPackage("hap");;
LoadPackage("IO");;

# CWD-independent path resolution (matches test_orbit_checkpoint_resume.g).
_SCRIPT_DIR := "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-336/extraspecial_orbifolds/scripts";;
ChangeDirectoryCurrent(_SCRIPT_DIR);;

Read("transgression_per_generator_brw.g");
Read("solver/orbit_cache_persist.g");
ChangeDirectoryCurrent(_SCRIPT_DIR);;

# Per-test workspace (clean each run).
TEST_DIR := "/tmp/test_orbit_cache_persist";;
Exec(Concatenation("rm -rf ", TEST_DIR));
Exec(Concatenation("mkdir -p ", TEST_DIR));

m := 2;;
Print("=== test_orbit_cache_persist (m=", m, ") ===\n");

# Build minimal setup.
conj_action := BRWConjugacyAction(m);;
G := conj_action.em;;
setup := SetupCohomology3(G);;
k := setup.num_generators;;
classes := conj_action.classes;;
Print("|G| = ", Order(G), ", k = ", k, "\n");

# Pick an orbit rep that is NOT identity (so we get a non-trivial table).
# At m=2 the first non-identity class will do.
rep := fail;;
chosen_class_idx := fail;;
for i in [1..Length(classes)] do
    candidate := Representative(classes[i]);
    if not IsOne(candidate) and Order(Centralizer(G, candidate)) < Order(G) then
        rep := candidate;
        chosen_class_idx := i;
        break;
    fi;
od;
# Fall back to the first non-identity if none has proper centralizer.
if rep = fail then
    for i in [1..Length(classes)] do
        candidate := Representative(classes[i]);
        if not IsOne(candidate) then
            rep := candidate;
            chosen_class_idx := i;
            break;
        fi;
    od;
fi;
if rep = fail then
    Error("No non-identity class found in m=", m);
fi;
C := Centralizer(G, rep);;
Print("Chose class ", chosen_class_idx, ": rep = ", rep,
      ", |C(rep)| = ", Order(C), "\n");

# Build the cache (this is fast at m=2).
Print("Building cache via BuildPerClassCocycleBasis... ");
t0 := Runtime();;
cache_orig := BuildPerClassCocycleBasis(setup, rep, C);;
Print((Runtime() - t0) / 1000., " s\n");

Print("Cache shape: n = ", cache_orig.n,
      ", table rows = ", Length(cache_orig.table),
      ", table[1] cols = ", Length(cache_orig.table[1]), "\n");

# Save the cache.
cache_path := Concatenation(TEST_DIR, "/orbit_", String(chosen_class_idx),
                             "_cache.g");;
Print("Saving cache to ", cache_path, "... ");
t0 := Runtime();;
SaveOrbitCache(cache_path, chosen_class_idx, m, setup, rep, cache_orig);;
Print((Runtime() - t0) / 1000., " s\n");
Print("File size: ", Length(StringFile(cache_path)), " bytes\n");

# Load it back.
Print("Loading cache via LoadOrbitCache... ");
expected_fp := _OrbitCacheFingerprint(setup, rep, m);;
t0 := Runtime();;
cache_loaded := LoadOrbitCache(cache_path, expected_fp, G);;
Print((Runtime() - t0) / 1000., " s\n");

if cache_loaded = fail then
    Print("FAIL: LoadOrbitCache returned fail.\n");
    QUIT;
fi;

# Verify equality field-by-field.
n_pass := 0;;
n_fail := 0;;

CheckEq := function(label, lhs, rhs)
    if lhs = rhs then
        n_pass := n_pass + 1;
        Print("  [ OK ] ", label, "\n");
    else
        n_fail := n_fail + 1;
        Print("  [FAIL] ", label, ": got ", lhs, " vs ", rhs, "\n");
    fi;
end;;

CheckEq("n", cache_loaded.n, cache_orig.n);
CheckEq("Order(C)", Order(cache_loaded.C), Order(cache_orig.C));
CheckEq("table length", Length(cache_loaded.table), Length(cache_orig.table));
CheckEq("table_gf2 length", Length(cache_loaded.table_gf2),
        Length(cache_orig.table_gf2));
CheckEq("elts length", Length(cache_loaded.elts), Length(cache_orig.elts));

# Table contents — element-wise.
mismatches_table := 0;;
for a in [1..Length(cache_orig.table)] do
    for b in [1..Length(cache_orig.table[a])] do
        if cache_loaded.table[a][b] <> cache_orig.table[a][b] then
            mismatches_table := mismatches_table + 1;
        fi;
    od;
od;
if mismatches_table = 0 then
    n_pass := n_pass + 1;
    Print("  [ OK ] table contents (", Length(cache_orig.table), " rows × ",
          Length(cache_orig.table[1]), " cols) byte-identical\n");
else
    n_fail := n_fail + 1;
    Print("  [FAIL] table contents: ", mismatches_table, " mismatches\n");
fi;

# table_gf2 contents.
mismatches_gf2 := 0;;
for a in [1..Length(cache_orig.table_gf2)] do
    for b in [1..Length(cache_orig.table_gf2[a])] do
        if cache_loaded.table_gf2[a][b] <> cache_orig.table_gf2[a][b] then
            mismatches_gf2 := mismatches_gf2 + 1;
        fi;
    od;
od;
if mismatches_gf2 = 0 then
    n_pass := n_pass + 1;
    Print("  [ OK ] table_gf2 contents byte-identical\n");
else
    n_fail := n_fail + 1;
    Print("  [FAIL] table_gf2: ", mismatches_gf2, " mismatches\n");
fi;

# elts: each element should be equal (== not necessarily IsIdenticalObj).
mismatches_elts := 0;;
for a in [1..Length(cache_orig.elts)] do
    if cache_loaded.elts[a] <> cache_orig.elts[a] then
        mismatches_elts := mismatches_elts + 1;
    fi;
od;
if mismatches_elts = 0 then
    n_pass := n_pass + 1;
    Print("  [ OK ] elts byte-identical (n=", Length(cache_orig.elts), ")\n");
else
    n_fail := n_fail + 1;
    Print("  [FAIL] elts: ", mismatches_elts, " mismatches\n");
fi;

# idx_map: round-trip lookup. For each element e_a, both maps should
# return the same index a.
mismatches_idx := 0;;
for a in [1..cache_orig.n] do
    e_a := cache_orig.elts[a];
    idx_orig := LookupDictionary(cache_orig.idx_map, e_a);
    idx_loaded := LookupDictionary(cache_loaded.idx_map, e_a);
    if idx_orig <> idx_loaded or idx_loaded <> a then
        mismatches_idx := mismatches_idx + 1;
    fi;
od;
if mismatches_idx = 0 then
    n_pass := n_pass + 1;
    Print("  [ OK ] idx_map lookups agree\n");
else
    n_fail := n_fail + 1;
    Print("  [FAIL] idx_map: ", mismatches_idx, " lookup mismatches\n");
fi;

# Fingerprint mismatch should return fail.
bogus_fp := ShallowCopy(expected_fp);;
bogus_fp.m := 99;;
bogus_loaded := LoadOrbitCache(cache_path, bogus_fp, G);;
if bogus_loaded = fail then
    n_pass := n_pass + 1;
    Print("  [ OK ] fingerprint-mismatch returns fail\n");
else
    n_fail := n_fail + 1;
    Print("  [FAIL] fingerprint-mismatch did NOT return fail\n");
fi;

# Missing file should return fail.
absent_loaded := LoadOrbitCache("/tmp/does-not-exist.g", expected_fp, G);;
if absent_loaded = fail then
    n_pass := n_pass + 1;
    Print("  [ OK ] missing-file returns fail\n");
else
    n_fail := n_fail + 1;
    Print("  [FAIL] missing-file did NOT return fail\n");
fi;

# Critical: AsList(cache_loaded.C) inside IsCoboundary2SplitVec must agree
# with cache_loaded.elts (which we restored from disk). Verify the live
# AsList(C) call on the freshly-reconstructed Centralizer matches our
# saved order — this is what makes the c_g_vec indexing valid downstream.
live_elts := AsList(cache_loaded.C);;
if Length(live_elts) <> cache_loaded.n then
    n_fail := n_fail + 1;
    Print("  [FAIL] AsList(C_loaded) has length ", Length(live_elts),
          ", want ", cache_loaded.n, "\n");
else
    mismatches_live := 0;
    for a in [1..cache_loaded.n] do
        if live_elts[a] <> cache_loaded.elts[a] then
            mismatches_live := mismatches_live + 1;
        fi;
    od;
    if mismatches_live = 0 then
        n_pass := n_pass + 1;
        Print("  [ OK ] AsList(C_loaded) order matches saved elts ",
              "(critical for IsCoboundary2SplitVec)\n");
    else
        n_fail := n_fail + 1;
        Print("  [FAIL] AsList(C_loaded) order DIFFERS at ",
              mismatches_live, " positions\n");
    fi;
fi;

Print("\nSummary: ", n_pass, " pass, ", n_fail, " fail\n");
if n_fail = 0 then
    Print("=== test_orbit_cache_persist: PASS ===\n");
else
    Print("=== test_orbit_cache_persist: FAIL ===\n");
fi;
QUIT;
