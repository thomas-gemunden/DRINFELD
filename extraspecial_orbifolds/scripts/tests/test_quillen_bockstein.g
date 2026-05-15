# test_quillen_bockstein.g — tests for the Quillen Bockstein action
# infrastructure (Stage A1, issue #136).
#
# Anchors: the Cohen-Quillen presentation of H*(D_8; F_2)
# (= QuillenCanonicalPresentation(1)) provides explicit formulas:
#   * β(x_i) = x_i^2 for i in {1, 2}.
#   * β(w) = (x_1 + x_2) w.
# Plus the Leibniz rule β(uv) = β(u)v + uβ(v) over F_2.
# Plus the ideal relation x_1 x_2 = 0.
#
# Run from extraspecial_orbifolds/scripts/:
#   gap -q -b -c 'Read("tests/test_quillen_bockstein.g");'

BreakOnError := false;;

Read("quillen_algebra.g");
Read("quillen_canonical_presentation.g");
Read("quillen_bockstein.g");

Print("\n=== test_quillen_bockstein.g ===\n");

testFailures := [];;
If_ := function(c, a, b) if c then return a; else return b; fi; end;;
AssertOrLog := function(label, cond)
    Print("  ", label, ": ", If_(cond, "PASS", "FAIL"), "\n");
    if not cond then Add(testFailures, label); fi;
end;;

# --------------------------------------------------------------------
# Setup: D_8 (m = 1) canonical Quillen presentation.
# --------------------------------------------------------------------
R := QuillenCanonicalPresentation(1);;
Print("\n--- D_8 canonical: n_sym = ", R.n_sym, ", ",
      Length(R.relations), " relation(s) ---\n");

# Helper: build a sym-only monomial from an exponent list.
SymMon := function(exps)
    return rec(sym := exps, ext := []);
end;;

# Convenience: x_1, x_2, w as elements.
x1 := QuillenSymGenerator(R, 1);;
x2 := QuillenSymGenerator(R, 2);;
w  := QuillenSymGenerator(R, 3);;

# --------------------------------------------------------------------
# Test 1: β on generators.
# --------------------------------------------------------------------
Print("\n--- Test 1: BocksteinOnGenerator(R, i) ---\n");

beta_x1 := BocksteinOnGenerator(R, 1);;
beta_x2 := BocksteinOnGenerator(R, 2);;
beta_w  := BocksteinOnGenerator(R, 3);;

AssertOrLog("β(x_1) = x_1^2 (singleton with sym=[2,0,0])",
            beta_x1 = [SymMon([2, 0, 0])]);
AssertOrLog("β(x_2) = x_2^2 (singleton with sym=[0,2,0])",
            beta_x2 = [SymMon([0, 2, 0])]);

# β(w) = x_1 w + x_2 w; in our graded lex with the QCP defaults, x_1 w
# comes before x_2 w (lex on sym). Build the expected element directly
# via QuillenAddElements to be order-agnostic.
expected_beta_w := QuillenAddElements(R,
    [SymMon([1, 0, 1])],     # x_1 * w
    [SymMon([0, 1, 1])]);;   # x_2 * w
AssertOrLog("β(w) = x_1 w + x_2 w (Cohen-Quillen for D_8)",
            beta_w = expected_beta_w);

# --------------------------------------------------------------------
# Test 2: β on individual monomials (no reduction — raw Leibniz form).
# --------------------------------------------------------------------
Print("\n--- Test 2: BocksteinOnMonomial(R, mon) ---\n");

# β(1) = 0.
b_one := BocksteinOnMonomial(R, SymMon([0, 0, 0]));;
AssertOrLog("β(1) = 0", b_one = []);

# β(x_1^2) = 0 (even exponent kills the Leibniz term).
b_x1sq := BocksteinOnMonomial(R, SymMon([2, 0, 0]));;
AssertOrLog("β(x_1^2) = 0 (even exponent)", b_x1sq = []);

# β(x_1) = x_1^2.
b_x1 := BocksteinOnMonomial(R, SymMon([1, 0, 0]));;
AssertOrLog("β(x_1) = x_1^2 monomial-form",
            b_x1 = [SymMon([2, 0, 0])]);

# β(x_1 * w) — Leibniz: β(x_1) * w + x_1 * β(w) =
#   x_1^2 * w + x_1 * (x_1 w + x_2 w) =
#   x_1^2 w + x_1^2 w + x_1 x_2 w =
#   x_1 x_2 w   (after F_2 cancellation; NOT yet reduced mod (x_1 x_2)).
b_x1w := BocksteinOnMonomial(R, SymMon([1, 0, 1]));;
AssertOrLog("β(x_1 w) raw = x_1 x_2 w (monomial sym=[1,1,1])",
            b_x1w = [SymMon([1, 1, 1])]);

# β(x_2 * w) symmetric: x_1 x_2 w by the same calculation.
b_x2w := BocksteinOnMonomial(R, SymMon([0, 1, 1]));;
AssertOrLog("β(x_2 w) raw = x_1 x_2 w (monomial sym=[1,1,1])",
            b_x2w = [SymMon([1, 1, 1])]);

# β(x_1 x_2 w) — Leibniz:
#   β(x_1) x_2 w + x_1 β(x_2) w + x_1 x_2 β(w)
# = x_1^2 x_2 w + x_1 x_2^2 w + x_1 x_2 (x_1 w + x_2 w)
# = x_1^2 x_2 w + x_1 x_2^2 w + x_1^2 x_2 w + x_1 x_2^2 w
# = 0  (mod 2).
b_x1x2w := BocksteinOnMonomial(R, SymMon([1, 1, 1]));;
AssertOrLog("β(x_1 x_2 w) raw = 0 (F_2 cancellation)",
            b_x1x2w = []);

# --------------------------------------------------------------------
# Test 3: β on whole elements (reduction mod the ideal applied).
# --------------------------------------------------------------------
Print("\n--- Test 3: BocksteinOnElement(R, e) with reduction ---\n");

# β(x_1 w) reduced mod (x_1 x_2) is 0.
be_x1w := BocksteinOnElement(R, [SymMon([1, 0, 1])]);;
AssertOrLog("β(x_1 w) reduced = 0 (x_1 x_2 w lives in the ideal)",
            be_x1w = []);

# β(x_1 + x_2) = x_1^2 + x_2^2.
be_x1_plus_x2 := BocksteinOnElement(R,
    QuillenAddElements(R, [SymMon([1, 0, 0])], [SymMon([0, 1, 0])]));;
expected := QuillenAddElements(R,
    [SymMon([2, 0, 0])], [SymMon([0, 2, 0])]);;
AssertOrLog("β(x_1 + x_2) = x_1^2 + x_2^2",
            be_x1_plus_x2 = expected);

# Property: β o β = 0. (Standard for the cochain Bockstein.) Test on a
# small spread of elements.
test_elements := [
    [SymMon([1, 0, 0])],            # x_1
    [SymMon([0, 1, 0])],            # x_2
    [SymMon([1, 0, 1])],            # x_1 w
    [SymMon([2, 1, 0])],            # x_1^2 x_2
    QuillenAddElements(R, [SymMon([1, 0, 1])], [SymMon([0, 1, 1])]),
                                    # x_1 w + x_2 w  (= β(w) itself!)
    [SymMon([3, 0, 0])]             # x_1^3
];;
for elt in test_elements do
    b1 := BocksteinOnElement(R, elt);
    if b1 = fail then
        AssertOrLog(
            Concatenation("β o β on element with leading sym ",
                          String(elt[Length(elt)].sym),
                          " — β returned fail"),
            false);
        continue;
    fi;
    b2 := BocksteinOnElement(R, b1);
    AssertOrLog(
        Concatenation("β o β = 0 on element with leading sym ",
                      String(elt[Length(elt)].sym)),
        b2 = []);
od;

# --------------------------------------------------------------------
# Test 4: BocksteinAvailableOnW predicate.
# --------------------------------------------------------------------
Print("\n--- Test 4: BocksteinAvailableOnW(m) ---\n");
AssertOrLog("m = 1 available", BocksteinAvailableOnW(1) = true);
AssertOrLog("m = 2 NOT available (Stage A2)",
            BocksteinAvailableOnW(2) = false);
AssertOrLog("m = 3 NOT available (Stage A2)",
            BocksteinAvailableOnW(3) = false);

# --------------------------------------------------------------------
# Test 5: m = 2 gracefully returns fail when w is involved.
# --------------------------------------------------------------------
Print("\n--- Test 5: m = 2 fail-mode for w-involving terms ---\n");
R2 := QuillenCanonicalPresentation(2);;
# n_sym = 5: x_1..x_4, w (deg 4).
beta_w2 := BocksteinOnGenerator(R2, 5);;
AssertOrLog("β(w) at m = 2 returns fail", beta_w2 = fail);

# β on x_1 (no w term) succeeds.
b_x1_m2 := BocksteinOnGenerator(R2, 1);;
AssertOrLog("β(x_1) at m = 2 = x_1^2 succeeds",
            b_x1_m2 = [rec(sym := [2, 0, 0, 0, 0], ext := [])]);

# β on a w-involving monomial (x_1 * w at m=2 has sym=[1,0,0,0,1]) is fail.
b_x1w_m2 := BocksteinOnMonomial(R2, rec(sym := [1, 0, 0, 0, 1], ext := []));;
AssertOrLog("β(x_1 w) at m = 2 = fail (β(w) unknown, e_w = 1 odd)",
            b_x1w_m2 = fail);

# β on a w^2 term IS computable even at m=2, because exponent 2 is even
# and Leibniz drops the β(w) contribution. β(x_1 w^2) = β(x_1) w^2 =
# x_1^2 w^2 (sym=[2,0,0,0,2]).
b_x1w2_m2 := BocksteinOnMonomial(R2,
    rec(sym := [1, 0, 0, 0, 2], ext := []));;
AssertOrLog("β(x_1 w^2) at m = 2 = x_1^2 w^2 (even w-exponent skips β(w))",
            b_x1w2_m2 = [rec(sym := [2, 0, 0, 0, 2], ext := [])]);

# --------------------------------------------------------------------
# Summary
# --------------------------------------------------------------------
Print("\n=== Summary ===\n");
if IsEmpty(testFailures) then
    Print("test_quillen_bockstein: ALL PASS\n");
else
    Print("test_quillen_bockstein: FAIL (", Length(testFailures), " failures)\n");
    for f in testFailures do Print("  - ", f, "\n"); od;
fi;
