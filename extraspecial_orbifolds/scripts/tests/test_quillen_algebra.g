# test_quillen_algebra.g — regression tests for the polynomial-times-
# exterior algebra defined in scripts/quillen_algebra.g.
#
# Smoke tests required by issue Q-1:
#   1. Λ(y) ⊗ F_2[x] (deg(x) = deg(y) = 1, no relations) has dimensions
#      (1, 2, 2, 2, ...) in degrees 0, 1, 2, 3, ....
#   2. Λ(y_1, y_2) ⊗ F_2[c] with one relation: take deg(c) = 2,
#      deg(y_1) = deg(y_2) = 1, and the relation y_1 y_2 + c = 0
#      (i.e. y_1 y_2 = c in characteristic 2). The expected dimensions
#      are (1, 2, 1, 2, 1, 2, ...) starting from degree 0.
#
# Additional sanity checks:
#   * monomial multiplication agrees with the algebra Multiply on
#     individual generators.
#   * Multiply is bilinear (distributive, commutativity-with-sym).
#   * y_i^2 = 0 (exterior square zero).
#
# Run from this directory:
#     gap test_quillen_algebra.g
# or from inside GAP:
#     ChangeDirectoryCurrent(Directory("...scripts/tests"));
#     Read("test_quillen_algebra.g");
# The test driver ends with QUIT; success is signalled by
# "test_quillen_algebra: PASS".

# Locate the parent module. Use INPUT_FILENAME() so the test runs from
# any working directory: when GAP reads this file by absolute path,
# the module is at "../quillen_algebra.g" relative to that absolute
# directory. Fall back to a few CWD-relative paths for users who
# `cd` into scripts/tests/ first.
_quillen_loaded := false;;
_self_path := INPUT_FILENAME();;
if _self_path <> fail and _self_path <> "stream" then
    # strip the trailing "/test_quillen_algebra.g"
    _self_dir := _self_path{[1..Length(_self_path) - Length("/test_quillen_algebra.g")]};;
    _candidate := Concatenation(_self_dir, "/../quillen_algebra.g");;
    if IsExistingFile(_candidate) then
        Read(_candidate);
        _quillen_loaded := true;
    fi;
fi;
if not _quillen_loaded then
    for _p in [ "../quillen_algebra.g",
                "quillen_algebra.g",
                "extraspecial_orbifolds/scripts/quillen_algebra.g",
                "scripts/quillen_algebra.g" ] do
        if not _quillen_loaded and IsExistingFile(_p) then
            Read(_p);
            _quillen_loaded := true;
        fi;
    od;
fi;
if not _quillen_loaded then
    Error("cannot locate quillen_algebra.g; run from ",
          "extraspecial_orbifolds/scripts/tests/.");
fi;

failures := [];

CheckEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
    else
        Print("  [FAIL] ", label, "\n");
        Print("        expected: ", expected, "\n");
        Print("        got     : ", got, "\n");
        Add(failures, label);
    fi;
end;;

CheckTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
    else
        Print("  [FAIL] ", label, "\n");
        Add(failures, label);
    fi;
end;;

# ---- Smoke test 1: Λ(y) ⊗ F_2[x], deg(x) = deg(y) = 1 ---------------

Print("Smoke 1: Lambda(y) tensor F_2[x] with deg(x)=deg(y)=1, no relations.\n");
A1 := PolynomialTimesExterior(
    [rec(name := "x", deg := 1)],
    [rec(name := "y", deg := 1)],
    []);

# Expected: dim 1 in deg 0; dim 2 in deg 1, 2, 3, 4, 5.
CheckEqual("dim deg 0", DimensionInDegree(A1, 0), 1);
CheckEqual("dim deg 1", DimensionInDegree(A1, 1), 2);
CheckEqual("dim deg 2", DimensionInDegree(A1, 2), 2);
CheckEqual("dim deg 3", DimensionInDegree(A1, 3), 2);
CheckEqual("dim deg 4", DimensionInDegree(A1, 4), 2);
CheckEqual("dim deg 5", DimensionInDegree(A1, 5), 2);

# Inspect the basis in degree 2: should be {x^2, x y}.
B1_2 := BasisInDegree(A1, 2);
Print("  basis deg 2: [");
for i in [1..Length(B1_2)] do
    if i > 1 then Print(", "); fi;
    Print(QuillenElementToString(A1, B1_2[i]));
od;
Print("]\n");

# y_1^2 = 0 inside A1 (the ext square).
y := QuillenExtGenerator(A1, 1);;
yy := QuillenMultiply(A1, y, y);;
CheckEqual("y*y = 0", yy, []);

# x * y = monomial xy, well-formed.
x := QuillenSymGenerator(A1, 1);;
xy := QuillenMultiply(A1, x, y);;
CheckTrue("x*y has length 1", Length(xy) = 1);
CheckEqual("x*y has degree 2",
           QuillenMonomialDegree(A1, xy[1]), 2);

# Distributive: (x + y) * x = x^2 + xy.
sum_xy := QuillenAddElements(A1, x, y);;
prod := QuillenMultiply(A1, sum_xy, x);;
expected := QuillenAddElements(A1,
    QuillenMultiply(A1, x, x),
    QuillenMultiply(A1, y, x));;
CheckEqual("distributive (x+y)*x", prod, expected);

# ---- Smoke test 2: Λ(y_1, y_2) ⊗ F_2[c], deg(c)=2, relation y1 y2 = c
#
# We pick the canonical Quillen-style "y_i y_j is a Bockstein" relation
# y_1 y_2 = c. Over F_2, this is the relation y_1 y_2 + c = 0.
# Expected dimensions:
#   deg 0: {1}                 dim 1
#   deg 1: {y_1, y_2}          dim 2
#   deg 2: {y_1 y_2, c}; with relation y_1 y_2 = c, basis = {c}, dim 1.
#   deg 3: {c y_1, c y_2}; (y_1 y_2 y_1 = 0 since y_1^2 = 0; same for
#          y_1 y_2 y_2)          dim 2
#   deg 4: {c^2, c y_1 y_2}; with y_1 y_2 = c, c y_1 y_2 = c^2; basis
#          = {c^2}              dim 1
#   deg 5: {c^2 y_1, c^2 y_2}; (c y_1 y_2 y_1 = 0 etc.) dim 2
#   pattern: 1, 2, 1, 2, 1, 2, ...

Print("\nSmoke 2: Lambda(y1, y2) tensor F_2[c] with deg(c)=2, ");
Print("relation y1 y2 = c.\n");

A2 := PolynomialTimesExterior(
    [rec(name := "c", deg := 2)],
    [rec(name := "y1", deg := 1), rec(name := "y2", deg := 1)],
    # Relation y_1 y_2 + c (= 0). The element is the F_2 sum of the
    # two monomials y_1 y_2 and c.
    [[rec(sym := [1], ext := []),
      rec(sym := [0], ext := [1, 2])]]);

CheckEqual("smoke2 dim 0", DimensionInDegree(A2, 0), 1);
CheckEqual("smoke2 dim 1", DimensionInDegree(A2, 1), 2);
CheckEqual("smoke2 dim 2", DimensionInDegree(A2, 2), 1);
CheckEqual("smoke2 dim 3", DimensionInDegree(A2, 3), 2);
CheckEqual("smoke2 dim 4", DimensionInDegree(A2, 4), 1);
CheckEqual("smoke2 dim 5", DimensionInDegree(A2, 5), 2);
CheckEqual("smoke2 dim 6", DimensionInDegree(A2, 6), 1);

# Basis in deg 2 should be a 1-element list whose element reduces to c.
B2_2 := BasisInDegree(A2, 2);;
Print("  basis deg 2: [");
for i in [1..Length(B2_2)] do
    if i > 1 then Print(", "); fi;
    Print(QuillenElementToString(A2, B2_2[i]));
od;
Print("]\n");

# Multiplication checks inside A2. y1 * y2 should reduce to c.
y1 := QuillenExtGenerator(A2, 1);;
y2 := QuillenExtGenerator(A2, 2);;
c  := QuillenSymGenerator(A2, 1);;
prod_y1y2 := QuillenMultiply(A2, y1, y2);;
CheckEqual("y1*y2 reduces to c", prod_y1y2, c);

# c * y1 - some non-zero thing. Test that c*y1*y2 = c*c = c^2 in A2.
cy1y2 := QuillenMultiply(A2, c, prod_y1y2);;        # c * c
cc := QuillenMultiply(A2, c, c);;                    # c * c
CheckEqual("c*(y1*y2) = c*c", cy1y2, cc);

# Symmetry of the polynomial part: c * c is one monomial of degree 4.
CheckTrue("c*c has length 1", Length(cc) = 1);
CheckEqual("c*c has degree 4",
           QuillenMonomialDegree(A2, cc[1]), 4);

# y1 * y1 = 0 in any case.
y1y1 := QuillenMultiply(A2, y1, y1);;
CheckEqual("y1*y1 = 0", y1y1, []);

# ---- Sanity test: associativity on a triple ---------------------------
Print("\nSanity: associativity on (c * y1) * y2 = c * (y1 * y2).\n");
left  := QuillenMultiply(A2, QuillenMultiply(A2, c, y1), y2);;
right := QuillenMultiply(A2, c, QuillenMultiply(A2, y1, y2));;
CheckEqual("associativity c*y1*y2", left, right);

# ---- Edge case: pure polynomial ring F_2[x] (no exterior) --------------
Print("\nEdge: F_2[x] with deg(x)=1, no exterior, no relations.\n");
A_poly := PolynomialTimesExterior(
    [rec(name := "x", deg := 1)], [], []);
# dim = 1 in every degree.
CheckEqual("F_2[x] dim 0", DimensionInDegree(A_poly, 0), 1);
CheckEqual("F_2[x] dim 3", DimensionInDegree(A_poly, 3), 1);
CheckEqual("F_2[x] dim 7", DimensionInDegree(A_poly, 7), 1);

# ---- Edge case: pure exterior algebra Λ(y_1, y_2, y_3) ----------------
Print("\nEdge: Lambda(y1, y2, y3) with deg(y_i)=1, no polynomial part.\n");
A_ext := PolynomialTimesExterior(
    [], [rec(name := "y1", deg := 1),
         rec(name := "y2", deg := 1),
         rec(name := "y3", deg := 1)], []);
# Hilbert series 1 + 3t + 3t^2 + t^3 (binomial coefficients of 3).
CheckEqual("Lambda^3 dim 0", DimensionInDegree(A_ext, 0), 1);
CheckEqual("Lambda^3 dim 1", DimensionInDegree(A_ext, 1), 3);
CheckEqual("Lambda^3 dim 2", DimensionInDegree(A_ext, 2), 3);
CheckEqual("Lambda^3 dim 3", DimensionInDegree(A_ext, 3), 1);
CheckEqual("Lambda^3 dim 4", DimensionInDegree(A_ext, 4), 0);

# ---- Mixed degrees: F_2[c, x] with deg(c)=2, deg(x)=1, no relations ---
#
# Hilbert series of F_2[c, x] with these degrees: 1/((1-t)(1-t^2))
#   = 1 + t + 2 t^2 + 2 t^3 + 3 t^4 + 3 t^5 + 4 t^6 + ...
Print("\nMixed: F_2[c, x] with deg(c)=2, deg(x)=1.\n");
A_mix := PolynomialTimesExterior(
    [rec(name := "c", deg := 2), rec(name := "x", deg := 1)], [], []);
expected_dims := [1, 1, 2, 2, 3, 3, 4, 4];
for i in [0..Length(expected_dims) - 1] do
    CheckEqual(Concatenation("F_2[c,x] dim ", String(i)),
               DimensionInDegree(A_mix, i), expected_dims[i + 1]);
od;

# Multiplication: c * c = c^2, x * x = x^2, c * x = c x.
ccc := QuillenMultiply(A_mix, QuillenSymGenerator(A_mix, 1),
                              QuillenSymGenerator(A_mix, 1));;
CheckEqual("c^2 has degree 4", QuillenMonomialDegree(A_mix, ccc[1]), 4);

# ---- Hilbert series sanity: Smoke 1 dimensions match closed form -----
# Λ(y) ⊗ F_2[x] has Hilbert series (1 + t) / (1 - t) = 1 + 2t + 2t^2 +
# 2t^3 + ..., so dim_n = 2 for n >= 1, and dim_0 = 1.
Print("\nHilbert: Lambda(y) tensor F_2[x] dimensions deg 0..10.\n");
for d in [0..10] do
    if d = 0 then
        CheckEqual(Concatenation("smoke1 deg ", String(d)),
                   DimensionInDegree(A1, d), 1);
    else
        CheckEqual(Concatenation("smoke1 deg ", String(d)),
                   DimensionInDegree(A1, d), 2);
    fi;
od;

# ---- Final report ----------------------------------------------------

if Length(failures) = 0 then
    Print("\ntest_quillen_algebra: PASS\n");
else
    Print("\ntest_quillen_algebra: FAIL (", Length(failures),
          " failure(s)):\n");
    for i in [1..Length(failures)] do
        Print("  - ", failures[i], "\n");
    od;
fi;

QUIT;
