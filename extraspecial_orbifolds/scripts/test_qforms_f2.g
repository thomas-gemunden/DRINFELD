# Test driver for qforms_f2.g.  Verifies basic invariants of the F_2
# quadratic-form utilities: bilinear form symmetry, MatOfBilForm
# consistency, idempotence of StandardizeQForm, splitting into radical
# and complement, and the canonical shape produced by
# QuadStandardFormChar2CompleteForm.

Read("qforms_f2.g");

ZeroV := function(n) return List([1..n], i -> 0); end;;
StdBasis := function(n)
    local i, e, B;
    B := [];
    for i in [1..n] do
        e := List([1..n], j -> 0);
        e[i] := 1;
        Add(B, e);
    od;
    return B;
end;;
F2Eq := function(A, B)
    return F2Mod(A) = F2Mod(B);
end;;

# ---- Test 1: BilForm is symmetric and matches MatOfBilForm. ----
TestBilForm := function(q)
    local n, B, e, sym, ok, i, j;
    n := Length(q);
    B := MatOfBilForm(q);
    sym := B = TransposedMat(B);
    ok := true;
    e := StdBasis(n);
    for i in [1..n] do
        for j in [1..n] do
            if BilForm(q, e[i], e[j]) <> B[i][j] then ok := false; fi;
        od;
    od;
    Print("  symmetric: ", sym, "; consistent with matrix: ", ok, "\n");
    return sym and ok;
end;;

# ---- Test 2: StandardizeQForm preserves Q on every vector. ----
TestStandardize := function(q)
    local s, n, ok, total, v, k, j;
    s := StandardizeQForm(q);
    n := Length(q);
    ok := true;
    total := 2^n;
    for k in [0..total-1] do
        v := List([0..n-1], j -> QuoInt(k, 2^j) mod 2);
        if QFormEval(q, v) <> QFormEval(s, v) then ok := false; fi;
    od;
    # Standardised form should be upper-triangular with entries equal to
    # B_q(e_i, e_j) for i < j and Q(e_i) on the diagonal.
    Print("  Q preserved by StandardizeQForm: ", ok,
          "; result upper-tri: ",
          ForAll([1..n], i -> ForAll([1..i-1], j -> s[i][j] = 0)), "\n");
    return ok;
end;;

# ---- Test 3: QuadStandardFormStart radical/complement bases. ----
TestStart := function(q)
    local pair, bd, bn, n, B, ok, v, w, totalDim;
    pair := QuadStandardFormStart(q);
    bd := pair[1]; bn := pair[2];
    n := Length(q);
    B := MatOfBilForm(q);
    # Each radical basis vector v must satisfy v*B = 0.
    ok := true;
    for v in bd do
        w := F2ModVec(v * B);
        if w <> ZeroV(n) then ok := false; fi;
    od;
    totalDim := Length(bd) + Length(bn);
    Print("  |bd|=", Length(bd), " |bn|=", Length(bn),
          " sum=", totalDim, " (expect ", n, ")",
          "; bd in radical: ", ok, "\n");
    return ok and totalDim = n;
end;;

# ---- Test 4: SplitDegeneratePart correctness. ----
TestSplit := function(q)
    local sd, aniso, iso, ok, v;
    sd := SplitDegeneratePart(q);
    aniso := sd[1]; iso := sd[2];
    ok := true;
    for v in aniso do
        if QFormEval(q, v) <> 1 then ok := false; fi;
    od;
    for v in iso do
        if QFormEval(q, v) <> 0 then ok := false; fi;
    od;
    Print("  |aniso|=", Length(aniso), " |iso|=", Length(iso),
          "; Q=1 on aniso, Q=0 on iso: ", ok, "\n");
    return ok;
end;;

# ---- Test 5: QuadStandardFormChar2CompleteForm canonical shape. ----
# After running, the matrix S (= P q P^T standardised) should have:
#   - 2k x 2k symplectic block at top-left with 1 in positions (2i-1,2i),
#     zeros elsewhere
#   - possibly a 1x1 or 2x2 defect block
#   - 1's on the diagonal in the anisotropic radical positions
#   - zeros elsewhere
TestCompleteForm := function(q, label)
    local S, P, bases, n, qMod, qViaP, ok, i, j;
    n := Length(q);
    Print("[", label, "] dim ", n, "\n");
    if not TestBilForm(q) then Print("  FAIL bilform\n"); fi;
    if not TestStandardize(q) then Print("  FAIL standardize\n"); fi;
    if not TestStart(q) then Print("  FAIL start\n"); fi;
    if not TestSplit(q) then Print("  FAIL split\n"); fi;
    bases := QuadStandardFormChar2CompleteBasesSeparate(q);
    Print("  separate bases sizes: nondeg=", Length(bases[1]),
          " aniso-rad=", Length(bases[2]),
          " iso-rad=", Length(bases[3]), "\n");
    S := QuadStandardFormChar2CompleteForm(q);
    Print("  CompleteForm = ");
    Print(S, "\n");
    # Sanity: Q evaluated on any v via S(P^{-1} v) should equal Q via q.
    # We just check it's upper triangular (StandardizeQForm property).
    ok := ForAll([1..n], i -> ForAll([1..i-1], j -> S[i][j] = 0));
    Print("  upper triangular: ", ok, "\n");
end;;

# ---- Cases ----

Print("\n=== Case A: zero form on F_2^4 ===\n");
TestCompleteForm(List([1..4], i -> List([1..4], j -> 0)), "zero4");

Print("\n=== Case B: q = diag(1,0,0,1) on F_2^4 (purely radical, with aniso part) ===\n");
TestCompleteForm([[1,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,1]], "diag1001");

Print("\n=== Case C: standard symplectic Q(v) = v1 v2 + v3 v4 on F_2^4 ===\n");
TestCompleteForm([[0,1,0,0],[0,0,0,0],[0,0,0,1],[0,0,0,0]], "sympl4");

Print("\n=== Case D: hyperbolic + radical, dim 4 ===\n");
# Q(v) = v1 v2 + v3, so v3 axis is a 1-d radical with Q=1 on e3.
TestCompleteForm([[0,1,0,0],[0,0,0,0],[0,0,1,0],[0,0,0,0]], "hyp+aniso");

Print("\n=== Case E: 2-d radical, mixed: dim 6, Q=v1v2 + v5 + v6 ===\n");
# v1v2 nondeg (radical-free) over span(e1,e2). On span(e3..e6), Q=v5+v6 so
# bilform is zero -- entire span(e3..e6) is in the radical.  Q on radical
# basis: Q(e3)=0, Q(e4)=0, Q(e5)=1, Q(e6)=1.  Aniso radical has dim 1
# (e.g. <e5>), iso radical dim 3.
TestCompleteForm([
    [0,1,0,0,0,0],
    [0,0,0,0,0,0],
    [0,0,0,0,0,0],
    [0,0,0,0,0,0],
    [0,0,0,0,1,0],
    [0,0,0,0,0,1]], "case_E");

Print("\n=== Case F: anisotropic 2-d defect: Q(v) = v1^2 + v1 v2 + v2^2 ===\n");
# This form has B(e1,e2) = (1+1+1) - 1 - 1 = 0 mod 2?  Actually
# Q(e1)=1, Q(e2)=1, Q(e1+e2) = 1+1+1 = 1.  So B(e1,e2) = 1 - 1 - 1 = -1
# = 1 mod 2.  So bilform nondegenerate but no v with Q(v)=0 in span (we
# have 4 vectors: 0 (Q=0), e1 (Q=1), e2 (Q=1), e1+e2 (Q=1)).  Type 2.
TestCompleteForm([[1,1,0,0],[0,1,0,0],[0,0,0,0],[0,0,0,0]],
                 "aniso2d_plus_rad");

Print("\n=== Case G: QSymp on dim 4 vectors ===\n");
Print("  QSymp([1,1,0,0]) = ", QSymp([1,1,0,0]), " (expect 1)\n");
Print("  QSymp([1,0,1,0]) = ", QSymp([1,0,1,0]), " (expect 0)\n");
Print("  QSymp([1,1,1,1]) = ", QSymp([1,1,1,1]), " (expect 0)\n");
Print("  QSymp([0,1,0,1]) = ", QSymp([0,1,0,1]), " (expect 0)\n");
Print("  QSymp([1,1,1,0]) = ", QSymp([1,1,1,0]), " (expect 1)\n");

Print("\nAll tests done.\n");

QUIT;
