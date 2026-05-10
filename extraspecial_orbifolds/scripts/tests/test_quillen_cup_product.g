# test_quillen_cup_product.g — Smoke tests for the bar-resolution cup
# product over F_2.
#
# Q-3 / Task #49. See scripts/quillen_cup_product.g for the implementation.
#
# Stage-1 tests:
#   1.  CupProductBarResolution(G, 1, 1) returns a function whose value
#       on a 2-tuple [g, h] is a(g) * b(h) in F_2.
#   2.  For G = D_8, Deg1CochainBasis(G) returns 2 cochains (since
#       D_8^{ab} = (Z/2)^2). Their cup-products form a 2-symmetric system
#       agreeing with the obvious projection onto coordinates.
#
# Stage-2 tests (best-effort):
#   * Associativity on three deg-1 cochains.
#   * Graded commutativity (cup is symmetric in F_2 = char 2): a ∪ b = b ∪ a
#     as cochains (NB this is at the cochain level, NOT just cohomology;
#     for deg-1 ∪ deg-1 on the bar resolution, the sign is +1 in char 2).
#
# Run:
#     gap test_quillen_cup_product.g
# from this directory, or via Read("...") with an absolute path.

_qcup_loaded := false;;
_self_path := INPUT_FILENAME();;
if _self_path <> fail and _self_path <> "stream" then
    _self_dir := _self_path{[1..Length(_self_path) - Length("/test_quillen_cup_product.g")]};;
    _candidate := Concatenation(_self_dir, "/../quillen_cup_product.g");;
    if IsExistingFile(_candidate) then
        Read(_candidate);
        _qcup_loaded := true;
    fi;
fi;
if not _qcup_loaded then
    for _p in [ "../quillen_cup_product.g",
                "quillen_cup_product.g",
                "extraspecial_orbifolds/scripts/quillen_cup_product.g",
                "scripts/quillen_cup_product.g" ] do
        if not _qcup_loaded and IsExistingFile(_p) then
            Read(_p);
            _qcup_loaded := true;
        fi;
    od;
fi;
if not _qcup_loaded then
    Error("cannot locate quillen_cup_product.g; run from ",
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

# ---- Stage 1: basic functional check on a tiny abelian group ---------

Print("Stage 1a: cup product on (Z/2)^2 -- evaluator works.\n");

G := SmallGroup(4, 2);;   # Z/2 x Z/2 (Klein four)
basis := Deg1CochainBasis(G);;
CheckEqual("dim H^1((Z/2)^2; F_2)", basis.dim, 2);

# basis.cochains contains 2 evaluators. Let a, b = cochains[1], [2].
a := basis.cochains[1];;
b := basis.cochains[2];;

# Make sure each evaluates to 0 or 1.
elts := Elements(G);;
for g in elts do
    CheckTrue(Concatenation("a([g]) is F_2 for g=", String(g)),
              a([g]) in GF(2));
    CheckTrue(Concatenation("b([g]) is F_2 for g=", String(g)),
              b([g]) in GF(2));
od;

# Distinct cochains: there exist g, h with a(g) != b(g) somewhere.
diff := false;;
for g in elts do
    if a([g]) <> b([g]) then diff := true; break; fi;
od;
CheckTrue("basis.cochains[1] != basis.cochains[2] on some g", diff);

# Build the cup product a ∪ b.
cup11 := CupProductBarResolution(G, 1, 1);;
ab := cup11(a, b);;

# Stage 1: check the bar formula directly: (a ∪ b)([g, h]) = a([g]) * b([h]).
Print("\nStage 1b: cup-product formula (a u b)([g,h]) = a(g) * b(h).\n");
all_ok := true;;
for g in elts do
    for h in elts do
        val_cup     := ab([g, h]);
        val_formula := a([g]) * b([h]);
        if val_cup <> val_formula then
            Print("  [FAIL] (a u b)([",g,",",h,"]) = ", val_cup,
                  " but a(g)*b(h) = ", val_formula, "\n");
            all_ok := false;
        fi;
    od;
od;
CheckTrue("cup formula matches a(g)*b(h) on all (g, h) pairs", all_ok);

# ---- Stage 2: graded commutativity and associativity -----------------

Print("\nStage 2a: cup is symmetric on the cochain level (char 2).\n");
ba := cup11(b, a);;
sym_ok := true;;
for g in elts do
    for h in elts do
        if ab([g, h]) <> ba([h, g]) then
            sym_ok := false;
            Print("  [FAIL] (a u b)([",g,",",h,"]) != (b u a)([",h,",",g,"])\n");
        fi;
    od;
od;
CheckTrue("(a u b)([g,h]) = (b u a)([h,g])", sym_ok);

# Associativity on three deg-1 cochains: ((a u a) u a)([g,h,k]) = (a u (a u a))([g,h,k]).
# We use 'a' three times for simplicity.
Print("\nStage 2b: associativity on deg-1+1+1 (with cochain a thrice).\n");
cup21 := CupProductBarResolution(G, 2, 1);;
cup12 := CupProductBarResolution(G, 1, 2);;
aa  := cup11(a, a);;
aaa_left  := cup21(aa, a);;
aaa_right := cup12(a, aa);;
assoc_ok := true;;
for g in elts do
    for h in elts do
        for k in elts do
            if aaa_left([g, h, k]) <> aaa_right([g, h, k]) then
                assoc_ok := false;
                Print("  [FAIL] assoc at ([",g,",",h,",",k,"])\n");
            fi;
        od;
    od;
od;
CheckTrue("associativity (a u a) u a = a u (a u a)", assoc_ok);

# Stage 2c: distinct ordered triples — pick (a, b, a).
Print("\nStage 2c: associativity on (a, b, a).\n");
ab1 := cup11(a, b);;
ba1 := cup11(b, a);;
aba_left  := cup21(ab1, a);;
aba_right := cup12(a, ba1);;
assoc_ab_ok := true;;
for g in elts do
    for h in elts do
        for k in elts do
            if aba_left([g, h, k]) <> aba_right([g, h, k]) then
                assoc_ab_ok := false;
                Print("  [FAIL] (a u b) u a != a u (b u a) at ([",g,",",h,",",k,"])\n");
            fi;
        od;
    od;
od;
CheckTrue("associativity (a u b) u a = a u (b u a)", assoc_ab_ok);

# ---- Stage 2d: test on D_8 -------------------------------------------

Print("\nStage 2d: cup product on D_8.\n");
D8 := DihedralGroup(8);;
basis_d8 := Deg1CochainBasis(D8);;
CheckEqual("dim H^1(D_8; F_2)", basis_d8.dim, 2);

# Check cup formula on D8.
a_d8 := basis_d8.cochains[1];;
b_d8 := basis_d8.cochains[2];;
cup11_d8 := CupProductBarResolution(D8, 1, 1);;
ab_d8 := cup11_d8(a_d8, b_d8);;
elts_d8 := Elements(D8);;
d8_ok := true;;
for g in elts_d8 do
    for h in elts_d8 do
        if ab_d8([g, h]) <> a_d8([g]) * b_d8([h]) then
            d8_ok := false;
        fi;
    od;
od;
CheckTrue("D_8 cup formula", d8_ok);

# ---- Summary ---------------------------------------------------------

Print("\n");
if Length(failures) = 0 then
    Print("test_quillen_cup_product: PASS\n");
else
    Print("test_quillen_cup_product: FAIL (", Length(failures), " test(s))\n");
    for _f in failures do
        Print("  - ", _f, "\n");
    od;
fi;
