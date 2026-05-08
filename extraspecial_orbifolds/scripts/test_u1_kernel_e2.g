# Compute the EXACT U(1)-cohomology kernel of Tr for E_+(2), and
# verify that the per-generator yes/no test (mod-exp IsCoboundary2)
# already gives the right answer at U(1) level (no Bockstein "false
# negatives" empirically on E_+(2)).
#
# Math: c_g class in H^2(C; U(1)) is 0 iff
#   either (1) c_g is a mod-exp coboundary on C, OR
#          (2) the integer Bockstein u = δ(lift c_g) / exp is an
#              integer 3-coboundary on C.
#
# Reason: short exact sequence 0 → Z → Z → Z/exp → 0 induces a
# Bockstein β: H^2(C; Z/exp) → H^3(C; Z).  Composing with the natural
# map H^2(C; Z/exp) → H^2(C; U(1)) gives the long exact sequence
# whose kernel-of-projection is exactly im(β).
#
# So: e_i in U(1) ker Tr  iff  for every conjugacy class g, c_g is
# either a mod-exp coboundary OR its Bockstein image vanishes in
# H^3(C; Z).
#
# Strategy: for each generator e_i, for each class g, test (1) first
# (IsCoboundary2); if it fails, test (2) (Bockstein-image-coboundary).
# Both pass -> e_i in U(1) kernel.

LogPath := "/tmp/test_u1_e2.log";;
PrintTo(LogPath, "");

Read("transgression_kernel.g");

# IsBoundary3: given an integer 3-cocycle u: C^3 -> Z, decide if u
# is an integer 3-coboundary on C.  Augmented integer system:
#   u(h1,h2,h3) = (δβ)(h1,h2,h3) over Z, β: C^2 -> Z.
# (No mod-exp slack -- looking for INTEGER coboundary.)
IsBoundary3 := function(H, u_func)
    local elts, n, A, b, i, j, k, idx, ij, jk, row, sol;
    elts := AsList(H);
    n := Length(elts);
    idx := function(h) return Position(elts, h); end;

    A := NullMat(n*n*n, n*n);
    b := List([1..n*n*n], i -> 0);
    for i in [1..n] do for j in [1..n] do for k in [1..n] do
        row := (i-1)*n*n + (j-1)*n + k;
        ij := idx(elts[i] * elts[j]);
        jk := idx(elts[j] * elts[k]);
        # δβ(h1, h2, h3) = β(h2, h3) - β(h1 h2, h3) + β(h1, h2 h3) - β(h1, h2)
        A[row][(j-1)*n + k] := A[row][(j-1)*n + k] + 1;
        A[row][(ij-1)*n + k] := A[row][(ij-1)*n + k] - 1;
        A[row][(i-1)*n + jk] := A[row][(i-1)*n + jk] + 1;
        A[row][(i-1)*n + j] := A[row][(i-1)*n + j] - 1;
        b[row] := u_func(elts[i], elts[j], elts[k]);
    od; od; od;
    sol := SolutionIntMat(TransposedMat(A), b);
    return sol <> fail;
end;;

# Bockstein image: u(h1,h2,h3) = δc_g(h1,h2,h3) / exp, integer-valued.
BocksteinFunc := function(c_g, exp)
    return function(h1, h2, h3)
        local d;
        # Lift c_g values to [0, exp), then compute δ.
        d := (c_g(h2, h3) mod exp)
             - (c_g(h1*h2, h3) mod exp)
             + (c_g(h1, h2*h3) mod exp)
             - (c_g(h1, h2) mod exp);
        # d should be a multiple of exp (since c_g is a mod-exp cocycle)
        return d / exp;
    end;
end;;

# Test: for each generator e_i, check whether every c_g is U(1)-trivial.
G := SmallGroup(32, 49);;
setup_G := SetupCohomology3(G);;
classes := ConjugacyClasses(G);;
n_classes := Length(classes);;
k := setup_G.num_generators;;
exp := setup_G.exponent;;

AppendTo(LogPath, "E_+(2): k = ", k, " generators, ", n_classes, " classes, exp = ", exp, "\n\n");

TestVecU1 := function(vec)
    local omega, j, gRep, c_g, isCob, u, isBdy, all_in;
    omega := StandardCocycleOf(setup_G, vec);
    all_in := true;
    for j in [1..n_classes] do
        gRep := Representative(classes[j]);
        c_g := CGCocycleFunc(omega, gRep);
        isCob := IsCoboundary2(Centralizer(G, gRep), c_g, exp);
        if isCob then
            # Mod-exp coboundary -- automatically U(1)-trivial.
            continue;
        fi;
        # Mod-exp non-trivial; check Bockstein.
        u := BocksteinFunc(c_g, exp);
        isBdy := IsBoundary3(Centralizer(G, gRep), u);
        if not isBdy then
            all_in := false; break;
        fi;
    od;
    return all_in;
end;;

# Per-generator U(1) test
AppendTo(LogPath, "--- U(1)-cohomology per-generator test ---\n");
in_kernel := [];;
for i in [1..k] do
    vec := List([1..k], j -> 0);
    vec[i] := 1;
    t := Runtime();
    res := TestVecU1(vec);
    AppendTo(LogPath, "  e_", i, " (order ", setup_G.torsion[i], "): ",
             If_(res, "IN", "NOT"), " U(1) kernel  (",
             (Runtime() - t)/1000., " s)\n");
    if res then Add(in_kernel, i); fi;
od;
AppendTo(LogPath, "\nTotal U(1) ker generators: ", Length(in_kernel),
         " / ", k, "\n");
AppendTo(LogPath, "in_kernel = ", in_kernel, "\n");

# Brute-force the e_10 axis (Z/8) under U(1) test
if not 10 in in_kernel then
    AppendTo(LogPath, "\n--- Brute-force on <e_10> = Z/8 (U(1) test) ---\n");
    e10_kernel := [];;
    for k_e10 in [0..7] do
        vec := List([1..k], j -> 0);
        vec[k] := k_e10;
        in_ker := TestVecU1(vec);
        AppendTo(LogPath, "  ", k_e10, "*e_10: ",
                 If_(in_ker, "IN", "NOT"), " U(1) ker\n");
        if in_ker then Add(e10_kernel, k_e10); fi;
    od;
    AppendTo(LogPath, "\nU(1) ker on <e_10>: ", e10_kernel, "\n");
    if Length(e10_kernel) > 1 then
        order_killer := Minimum(Filtered(e10_kernel, k -> k > 0));
        e10_size := 8 / order_killer;
    else
        e10_size := 1;
    fi;
    total_kernel := 2^Length(in_kernel) * e10_size;
    AppendTo(LogPath, "\n|U(1) ker Tr| = 2^", Length(in_kernel),
             " * ", e10_size, " = ", total_kernel, "\n");
    AppendTo(LogPath, "|H^3(E_+(2); U(1))| = ", Product(setup_G.torsion), "\n");
fi;

QUIT;
