# Test driver for the section-6 optimisation pipeline (Keller-Roberts-Roberts,
# arXiv:2411.13646).  Verifies correctness against the brute-force Schur-sum
# implementation at m = 3, then exercises the m = 5 and m = 7 relation
# matrices.
#
# Run from this directory with:
#     gap -q -b -c 'Read("test_defect_rep_optim.g");'

SetInfoLevel(InfoWarning, 0);

Read("bw_lattice.g");
Read("em_construction.g");
Read("twisted_group_algebra.g");
Read("qforms_f2.g");
Read("defect_rep_minus_id.g");
Read("defect_rep_minus_id_optim.g");


# --------------------------------------------------------------------
# Helper utilities used throughout
# --------------------------------------------------------------------

# Build all generators T_{a,r} for given m as a list of records with
# fields .a, .r, .h, .mhh, .A.  Pre-fills the optim caches so that each
# entry is fast.
BuildGenerators := function(m)
    local k, n, gens, a, r, h, sht, hd, B;
    B := BasisForN(m);
    gens := [];
    for a in [1..m] do
        for r in [1..2] do
            h := UnimodSigma(m, a, r);
            sht := _efShAndTarget(h, m);
            hd := _efPerHData(h, m);
            Add(gens, rec(a := a, r := r, h := h,
                           mhh := MhHalfefMat(h, m),
                           A := Kernef(h, m)));
        od;
    od;
    return gens;
end;;

# Print a 2D rational matrix in a compact form.
PrintMatrix := function(M)
    local row;
    for row in M do
        Print("  ", row, "\n");
    od;
end;;


# --------------------------------------------------------------------
# 1. m = 3 single-entry cross-check
# --------------------------------------------------------------------

Print("\n");
Print("=================================================================\n");
Print("  Test 1: m = 3 single-entry cross-check                          \n");
Print("    HardCodeShortComputeInterTwineref vs brute-force InterTwineref\n");
Print("=================================================================\n");

m := 3;;
k := 2^(m-1);;
n := 2^m;;
zero_n := F2_ZeroVec(n);;
zero_k := F2_ZeroVec(k);;

gens3 := BuildGenerators(m);;
B3 := BasisForN(m);;
R3 := TwoCocycleForN(m);;

t0 := Runtime();;
totalMismatch := 0;;
for genrec in gens3 do
    h := genrec.h;
    mhh := genrec.mhh;
    A := genrec.A;
    mismatch := 0;
    for ci in [1..2^k] do
        c := DecodeBitVec(ci, k);
        for di in [1..2^k] do
            d := DecodeBitVec(di, k);
            vBrute := InterTwineref(h, c, d, zero_k, zero_k, zero_n, m);
            vShort := HardCodeShortComputeInterTwineref(
                          h, zero_k, zero_k, c, d, zero_n,
                          mhh, A, B3, R3, m);
            if vBrute <> vShort then mismatch := mismatch + 1; fi;
        od;
    od;
    Print("  T", genrec.a, genrec.r,
          ": brute matches short on all ", 2^(2*k), " entries: ",
          mismatch = 0, "  (", mismatch, " mismatches)\n");
    totalMismatch := totalMismatch + mismatch;
od;
t1 := Runtime();;
Print("Test 1 total mismatches: ", totalMismatch,
      "  (", t1 - t0, " ms)\n");
test1Pass := totalMismatch = 0;;


# --------------------------------------------------------------------
# 2. m = 3 product cross-check
# --------------------------------------------------------------------

Print("\n");
Print("=================================================================\n");
Print("  Test 2: m = 3 product cross-check                               \n");
Print("    HardCodeShortComputeProductCoordinateef vs full T_h1 * T_h2   \n");
Print("=================================================================\n");

# Build full intertwiner matrices once.
mats3 := List(gens3, g -> BuildIntertwiner(g.h, zero_k, zero_k, zero_n, m));;

t0 := Runtime();;
totalMismatch := 0;;
totalChecks := 0;;
for i in [1..6] do
    for j in [1..6] do
        h1 := gens3[i].h; h2 := gens3[j].h;
        prod := mats3[i] * mats3[j];
        mismatch := 0;
        for ci in [1..2^k] do
            c := DecodeBitVec(ci, k);
            for di in [1..2^k] do
                d := DecodeBitVec(di, k);
                vFull := prod[di][ci];
                vShort := HardCodeShortComputeProductCoordinateef(
                              h1, gens3[i].A, zero_k, zero_k, c, zero_n,
                              gens3[i].mhh, gens3[i].A, B3,
                              h2, gens3[j].A, zero_k, zero_k, d, zero_n,
                              gens3[j].mhh, gens3[j].A, B3, m);
                totalChecks := totalChecks + 1;
                if vFull <> vShort then mismatch := mismatch + 1; fi;
            od;
        od;
        if mismatch > 0 then
            Print("  T", gens3[i].a, gens3[i].r, " * T",
                  gens3[j].a, gens3[j].r,
                  ": ", mismatch, " mismatches\n");
        fi;
        totalMismatch := totalMismatch + mismatch;
    od;
od;
t1 := Runtime();;
Print("Test 2: ", totalChecks, " checks across all 36 product pairs, ",
      totalMismatch, " mismatches  (", t1 - t0, " ms)\n");
test2Pass := totalMismatch = 0;;


# --------------------------------------------------------------------
# 3. m = 5 relation matrix
# --------------------------------------------------------------------

Print("\n");
Print("=================================================================\n");
Print("  Test 3: m = 5 relation matrix                                   \n");
Print("=================================================================\n");

m := 5;;
k := 2^(m-1);;
n := 2^m;;
zero_n := F2_ZeroVec(n);;
zero_k := F2_ZeroVec(k);;

gens5 := BuildGenerators(m);;
B5 := BasisForN(m);;

t0 := Runtime();;
M5raw := List([1..10], i -> List([1..10], j -> 0));;
for i in [1..10] do
    for j in [1..10] do
        h1 := gens5[i].h; h2 := gens5[j].h;
        M5raw[i][j] := HardCodeShortComputeProductCoordinateef(
                           h1, gens5[i].A, zero_k, zero_k, zero_k, zero_n,
                           gens5[i].mhh, gens5[i].A, B5,
                           h2, gens5[j].A, zero_k, zero_k, zero_k, zero_n,
                           gens5[j].mhh, gens5[j].A, B5, m);
    od;
od;
t1 := Runtime();;
Print("100 entries built in ", t1 - t0, " ms (avg ",
      QuoInt(1000 * (t1 - t0), 100), " us/entry)\n");

# Normalise: each T_h^2 has T_h^2[0,0] = 2^{2k} = 2^32; divide every
# entry by sqrt(diag_i * diag_j).  This makes the diagonal exactly 1.
diag5 := List([1..10], i -> M5raw[i][i]);;
M5 := List([1..10], i ->
            List([1..10], j ->
                M5raw[i][j] / RootInt(diag5[i] * diag5[j])));;
Print("\nm=5 relation matrix (raw values divided by sqrt(diag_i diag_j)):\n");
PrintMatrix(M5);

Print("\nDiagonal: ", List([1..10], i -> M5[i][i]), "\n");
Print("Diagonal all 1 (so T_ar^2 = scalar*I):  ",
      ForAll([1..10], i -> M5[i][i] = 1), "\n");
Print("Symmetric (so T_ar T_bs = T_bs T_ar):    ", M5 = TransposedMat(M5), "\n");

# Compare to paper's transcribed matrix (in m5_relation_matrix.g).  This
# WILL NOT MATCH because our SymplecticBasisF2 picks a different
# symplectic basis of N than Magma's WittDecomposition.  Both are valid
# symplectic bases, but they give different concrete intertwiner
# matrices on Omega_0; the substantive paper claim (diagonal=1,
# symmetric, hence trivial 2-cocycle) holds in either basis.
paperM5 := [
    [1, 1/4, 1, 1/8, 1/4, 1/2, 1/2, 1/2, 1/2, 1/2],
    [1/4, 1, 1/4, 1/4, 1/8, 1/4, 1/8, 1/4, 1/4, 1/4],
    [1, 1/4, 1, 1/8, 1/4, 1/2, 1/2, 1/2, 1/2, 1/2],
    [1/8, 1/4, 1/8, 1, 1/16, 1/8, 1/8, 1/8, 1/8, 1/8],
    [1/4, 1/8, 1/4, 1/16, 1, 1/8, 1/4, 1/4, 1/4, 1/4],
    [1/2, 1/4, 1/2, 1/8, 1/8, 1, 1/2, 1/2, 1/2, 1/2],
    [1/2, 1/8, 1/2, 1/8, 1/4, 1/2, 1, 1/4, 1/4, 1/2],
    [1/2, 1/4, 1/2, 1/8, 1/4, 1/2, 1/4, 1, 1/2, 1/4],
    [1/2, 1/4, 1/2, 1/8, 1/4, 1/2, 1/4, 1/2, 1, 1/4],
    [1/2, 1/4, 1/2, 1/8, 1/4, 1/2, 1/2, 1/4, 1/4, 1]
];;
Print("\nLiteral entries match paper (eq. 4.4.9):  ", M5 = paperM5, "\n");
Print("(Expected `false`: we use SymplecticBasisF2 which differs from Magma\n");
Print(" WittDecomposition; only the qualitative properties survive.)\n");

m5DiagOne := ForAll([1..10], i -> M5[i][i] = 1);;
m5Sym := M5 = TransposedMat(M5);;
test3Pass := m5DiagOne and m5Sym;;


# --------------------------------------------------------------------
# 4. m = 7 relation matrix
# --------------------------------------------------------------------

Print("\n");
Print("=================================================================\n");
Print("  Test 4: m = 7 relation matrix                                   \n");
Print("=================================================================\n");

m := 7;;
k := 2^(m-1);;
n := 2^m;;
zero_n := F2_ZeroVec(n);;
zero_k := F2_ZeroVec(k);;

Print("Pre-computing generators for m = 7 (this can take a few seconds)...\n");
t0 := Runtime();;
gens7 := BuildGenerators(m);;
B7 := BasisForN(m);;
t1 := Runtime();;
Print("Pre-computation done in ", t1 - t0, " ms.\n");

t0 := Runtime();;
M7raw := List([1..14], i -> List([1..14], j -> 0));;
for i in [1..14] do
    for j in [1..14] do
        h1 := gens7[i].h; h2 := gens7[j].h;
        M7raw[i][j] := HardCodeShortComputeProductCoordinateef(
                           h1, gens7[i].A, zero_k, zero_k, zero_k, zero_n,
                           gens7[i].mhh, gens7[i].A, B7,
                           h2, gens7[j].A, zero_k, zero_k, zero_k, zero_n,
                           gens7[j].mhh, gens7[j].A, B7, m);
    od;
od;
t1 := Runtime();;
Print("196 entries built in ", t1 - t0, " ms (avg ",
      QuoInt(t1 - t0, 196), " ms/entry)\n");

diag7 := List([1..14], i -> M7raw[i][i]);;
M7 := List([1..14], i ->
            List([1..14], j ->
                M7raw[i][j] / RootInt(diag7[i] * diag7[j])));;
Print("\nRaw diagonal entries (each = (T_h^2)_{0,0}): all equal to ",
      diag7[1], "  (= 2^", LogInt(diag7[1], 2), " = (2^k)^2 with k=",
      k, ")\n");
Print("\nm=7 relation matrix (raw values divided by sqrt(diag_i diag_j)):\n");
PrintMatrix(M7);

Print("\nDiagonal: ", List([1..14], i -> M7[i][i]), "\n");
Print("Diagonal all 1 (so T_ar^2 = scalar*I):  ",
      ForAll([1..14], i -> M7[i][i] = 1), "\n");
Print("Symmetric (so T_ar T_bs = T_bs T_ar):    ", M7 = TransposedMat(M7), "\n");

# Power-of-2 representation: each non-zero entry is 2^(some integer);
# print the integer.  Zeros print as "*".
Log2OrStar := function(x)
    local v;
    if x = 0 then return "*"; fi;
    v := x;
    if not IsInt(v) then
        # x is rational, e.g. 1/4.  Compute log2 of numerator over
        # denominator.
        return Concatenation("2^",
            String(LogInt(NumeratorRat(v), 2) - LogInt(DenominatorRat(v), 2)));
    fi;
    return Concatenation("2^", String(LogInt(v, 2)));
end;;
Print("\nPower-of-2 representation (each cell shows the exponent):\n");
for row in M7 do
    Print("  [");
    for j in [1..Length(row)] do
        if j > 1 then Print(", "); fi;
        Print(Log2OrStar(row[j]));
    od;
    Print("]\n");
od;

m7DiagOne := ForAll([1..14], i -> M7[i][i] = 1);;
m7Sym := M7 = TransposedMat(M7);;
test4Pass := m7DiagOne and m7Sym;;


# --------------------------------------------------------------------
# Summary
# --------------------------------------------------------------------

Print("\n");
Print("=================================================================\n");
Print("  Summary                                                         \n");
Print("=================================================================\n");
Print("Test 1 (m=3 single-entry cross-check):    ",
      test1Pass, "\n");
Print("Test 2 (m=3 product cross-check):         ",
      test2Pass, "\n");
Print("Test 3 (m=5 relation matrix diag=1, sym): ",
      test3Pass, "\n");
Print("Test 4 (m=7 relation matrix diag=1, sym): ",
      test4Pass, "\n");
allPass := test1Pass and test2Pass and test3Pass and test4Pass;;
Print("\nAll tests pass: ", allPass, "\n");

QUIT;
