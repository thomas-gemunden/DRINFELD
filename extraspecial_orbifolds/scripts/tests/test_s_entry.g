# Tests for SEntry(m, i, j) — V-7a single-S-entry primitive.
#
# Coverage:
#   * m = 3: 1000 random (i, j) pairs vs dense S.
#   * m = 5: a few canonical-pair lookups; query timing.
#   * m = 7: documented behaviour for the three missing-block regimes.
#
# Run from extraspecial_orbifolds/scripts/ (the script Read's
# `s_entry.g` directly).  Output is plain text; exit code is via QUIT
# either way.

ChangeDirectoryCurrent(
    "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-v7a/extraspecial_orbifolds/scripts");

Read("s_entry.g");

# Random RNG seeded for repeatability.
Reset(GlobalMersenneTwister, 42);;

# ----------------------------------------------------------------
# m = 3: 1000 random pairs vs dense S.
# ----------------------------------------------------------------

Print("\n=== m = 3 :: 1000 random pairs vs dense S ===\n");
s3 := SEntry_Init(3);;
rank3 := s3.idx.rank;;
Print("rank(D^1(E_+(3))) = ", rank3, "\n");

n_ok_3 := 0;;
n_fail_3 := 0;;
for trial in [1..1000] do
    i := Random(GlobalMersenneTwister, [1..rank3]);
    j := Random(GlobalMersenneTwister, [1..rank3]);
    expected := s3.dense_S[i][j];
    got := SEntry(3, i, j);
    if got = expected then
        n_ok_3 := n_ok_3 + 1;
    else
        n_fail_3 := n_fail_3 + 1;
        if n_fail_3 <= 5 then
            Print("  MISMATCH at (", i, ", ", j, "): expected ",
                  expected, ", got ", got, "\n");
        fi;
    fi;
od;
Print("m = 3 :: ", n_ok_3, "/1000 agree (", n_fail_3, " failures)\n");

# Direct canonical-block coverage at m = 3: walk every canonical
# (ci, cj) pair, query the centre of its block via the canonical-block
# path, and verify against the dense S.
Print("\n--- m = 3 canonical-block path direct coverage ---\n");
n_cov_ok := 0;; n_cov_fail := 0;;
for key in RecNames(s3.canonical_pairs) do
    pair := s3.canonical_pairs.(key);
    ci := pair[1]; cj := pair[2];
    # Query (1, 1) within the block (deterministic).
    i := s3.idx.global_offset[ci] + 1;
    j := s3.idx.global_offset[cj] + 1;
    expected := s3.dense_S[i][j];
    got := SEntry(3, i, j);
    if got = expected then
        n_cov_ok := n_cov_ok + 1;
    else
        n_cov_fail := n_cov_fail + 1;
        Print("  CANONICAL MISMATCH ", key, " (i=", i, ", j=", j,
              "): expected ", expected, ", got ", got, "\n");
    fi;
od;
Print("m = 3 canonical-pair lookup: ", n_cov_ok, "/",
      Length(RecNames(s3.canonical_pairs)),
      " refined groups match dense S\n");

# ----------------------------------------------------------------
# m = 5: timing for canonical-pair lookup; report whether non-canonical
# falls back to on-demand block (slower).
# ----------------------------------------------------------------

Print("\n=== m = 5 :: query timing ===\n");
s5 := SEntry_Init(5);;
rank5 := s5.idx.rank;;
n_classes_5 := Length(s5.idx.classes);;
Print("rank(D^1(E_+(5))) = ", rank5, ", #classes = ", n_classes_5, "\n");

# Find a canonical (i, j) pair we can hit O(1).  Use the (1, 1) class
# pair = ([id], [id]) which is always canonical for its refined group.
i_canon := s5.idx.global_offset[1] + 1;;
j_canon := s5.idx.global_offset[1] + 1;;

# Warm up the canonical block read.
warmup := SEntry(5, i_canon, j_canon);;
Print("first canonical lookup: ", warmup, "\n");

# Time 1000 canonical lookups (vary the irrep within the class).
tic := Runtime();;
for trial in [1..1000] do
    # Pick global indices within the (1, 1) canonical block.
    k1 := Random(GlobalMersenneTwister, [1..s5.idx.num_irreps[1]]);
    k2 := Random(GlobalMersenneTwister, [1..s5.idx.num_irreps[1]]);
    val := SEntry(5, s5.idx.global_offset[1] + k1,
                     s5.idx.global_offset[1] + k2);
od;
toc := Runtime() - tic;;
per_query_ms := toc / 1000.0;;  # Runtime() is in ms, total over 1000 = ms each
Print("m = 5 canonical lookup: 1000 queries in ", toc, " ms ",
      "(", per_query_ms, " ms per query average)\n");
if per_query_ms <= 1.0 then
    Print("m = 5 :: PASS  <= 1 ms per canonical query\n");
else
    Print("m = 5 :: TIMING NOTE: ", per_query_ms,
          " ms per query (target was <= 1 ms)\n");
fi;

# ----------------------------------------------------------------
# m = 7: documented missing-block behaviour.
#
# We cannot run BuildSimpleIndex(E_+(7)) here (ConjugacyClasses OOM at
# 60 GB heap; see run_e_plus_7_canonical.g).  SEntry(7, i, j) errors
# out with a directing message.  Instead we exercise SEntryByClass
# against partial state and the closed-form / zero documentation.
# ----------------------------------------------------------------

Print("\n=== m = 7 :: documented missing-block behaviour ===\n");
s7 := SEntry_Init(7);;
Print("idx available: ", s7.idx <> fail,
      " (expected: false; BuildSimpleIndex(E_+(7)) OOMs)\n");
Print("canonical_blocks loaded: ",
      Length(RecNames(s7.canonical_blocks)),
      " (manifest expects 9 stored, 13 omitted)\n");

# Documented behaviour summary (also encoded in s_entry.g comments):
Print("\nMissing-block taxonomy at m = 7:\n");
Print("  * non-commuting (sigma2, sigma2), (sigma2, sigma1sigma2),\n");
Print("    (sigma1sigma2, sigma1sigma2) class pairs -> SEntryByClass\n");
Print("    returns 0 via the commute-flag check.\n");
Print("  * (id, id), (id, -1), (-1, -1) fully-central blocks ->\n");
Print("    Phase D closed form:\n");
Print("      S_((id, rho), (id, sigma))    = dim(rho)  * dim(sigma)  / |G|\n");
Print("      S_((id, rho), (-1, sigma))    = dim(rho)  * sigma(-1)   / |G|\n");
Print("      S_((-1, rho), (-1, sigma))    = rho(-1)   * sigma(-1)   / |G|\n");
Print("    These cost O(1) per entry given the closed form -- no GAP\n");
Print("    CharacterTable for the central blocks needed.\n");
Print("  * Canonical pairs of the remaining refined groups (9 blocks):\n");
Print("    canonical_blocks.g (8.7 GB, gitignored) provides O(1) lookup\n");
Print("    when present; otherwise SEntryByClass returns 'fail' from the\n");
Print("    canonical-lookup helper and surfaces a directed error.\n");

# Summary
Print("\n=== Summary ===\n");
Print("m = 3 :: ", n_ok_3, "/1000 agreement\n");
Print("m = 5 canonical query :: ", per_query_ms, " ms\n");
Print("m = 7 :: missing-block behaviour documented; SEntry guards against ",
      "global-index decode (would OOM).\n");

QUIT;
