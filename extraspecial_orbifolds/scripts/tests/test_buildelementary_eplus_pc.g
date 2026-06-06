# test_buildelementary_eplus_pc.g — regression test for audit C1.
#
# Closed-form maximal elementary abelian construction in
# `quillen_detecting_subgroup.g` using the canonical
# `ExtraspecialGroup(2^(2m+1), "+")` PC presentation.
#
# Strategy:
#   1. For m in {2, 3, 5, 7}: the closed-form path produces a subgroup
#      of order 2^{m+1} that is elementary abelian and contains the
#      centre Z.
#   2. For m in {2, 3, 5}: the closed-form subgroup is "equivalent" to
#      the greedy fallback in the sense that both have the same order,
#      both are elementary abelian, both contain z. (They need not be
#      equal as subgroups — both are maximal elementary abelians of
#      rank m+1, and there are many such.)
#   3. m=1 is special (ExtraspecialGroup(8, "+") has first generator
#      of order 4); the closed-form path is m >= 2 only and should
#      delegate (or no-op) at m=1.
#
# Run from this directory:
#     gap test_buildelementary_eplus_pc.g

# ---- Locate the parent module -----------------------------------------

_btpc_loaded := false;;
_btpc_self_path := INPUT_FILENAME();;
if _btpc_self_path <> fail and _btpc_self_path <> "stream" then
    _btpc_self_dir := _btpc_self_path{[1..Length(_btpc_self_path) -
                                       Length("/test_buildelementary_eplus_pc.g")]};;
    _btpc_candidate := Concatenation(_btpc_self_dir,
                                     "/../quillen_detecting_subgroup.g");;
    if IsExistingFile(_btpc_candidate) then
        Read(_btpc_candidate);
        _btpc_loaded := true;
    fi;
fi;
if not _btpc_loaded then
    for _btpc_p in [ "../quillen_detecting_subgroup.g",
                     "quillen_detecting_subgroup.g",
                     "extraspecial_orbifolds/scripts/quillen_detecting_subgroup.g",
                     "scripts/quillen_detecting_subgroup.g" ] do
        if not _btpc_loaded and IsExistingFile(_btpc_p) then
            Read(_btpc_p);
            _btpc_loaded := true;
        fi;
    od;
fi;
if not _btpc_loaded then
    Error("cannot locate quillen_detecting_subgroup.g; ",
          "run from extraspecial_orbifolds/scripts/tests/.");
fi;

# ---- Harness ----------------------------------------------------------

btpc_failures := [];

CheckTrueBTPC := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
    else
        Print("  [FAIL] ", label, "\n");
        Add(btpc_failures, label);
    fi;
end;;

CheckEqualBTPC := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
    else
        Print("  [FAIL] ", label, "\n");
        Print("        expected: ", expected, "\n");
        Print("        got     : ", got, "\n");
        Add(btpc_failures, label);
    fi;
end;;

# ---- Test 1: closed-form helper exists --------------------------------

Print("Test 1: closed-form PC helper bound.\n");

CheckTrueBTPC("_TryPCClosedFormEA_EPlus bound",
              IsBoundGlobal("_TryPCClosedFormEA_EPlus"));

# ---- Test 2: closed-form produces a rank-(m+1) elementary abelian -----

Print("\nTest 2: closed-form path m in {2, 3, 5, 7}.\n");

for m in [2, 3, 5, 7] do
    Print("  m = ", m, ":\n");
    G_m := EPlusGroup(m);
    Z_G := Centre(G_m);
    z := First(AsList(Z_G), x -> not IsOne(x));
    t0 := Runtime();
    H_cf := _TryPCClosedFormEA_EPlus(G_m, m);
    t1 := Runtime();
    Print("    closed-form construction: ", (t1 - t0) / 1000.0, " s\n");
    CheckTrueBTPC(
        Concatenation("closed-form returns a subgroup for m=", String(m)),
        H_cf <> fail);
    if H_cf <> fail then
        CheckEqualBTPC(
            Concatenation("closed-form |H| = 2^(m+1) for m=", String(m)),
            Order(H_cf), 2^(m+1));
        CheckTrueBTPC(
            Concatenation("closed-form IsElementaryAbelian for m=",
                          String(m)),
            IsElementaryAbelian(H_cf));
        CheckTrueBTPC(
            Concatenation("closed-form contains centre z for m=",
                          String(m)),
            z in H_cf);
    fi;
od;

# ---- Test 3: BuildElementaryAbelianDirect_E_plus uses the closed-form -

Print("\nTest 3: BuildElementaryAbelianDirect_E_plus at m in {2, 3, 5, 7}.\n");

for m in [2, 3, 5, 7] do
    Print("  m = ", m, ":\n");
    G_m := EPlusGroup(m);
    Z_G := Centre(G_m);
    z := First(AsList(Z_G), x -> not IsOne(x));
    t0 := Runtime();
    H_direct := BuildElementaryAbelianDirect_E_plus(G_m, m);
    t1 := Runtime();
    Print("    direct build: ", (t1 - t0) / 1000.0, " s\n");
    CheckEqualBTPC(
        Concatenation("BEAD: |H| = 2^(m+1) for m=", String(m)),
        Order(H_direct), 2^(m+1));
    CheckTrueBTPC(
        Concatenation("BEAD: IsElementaryAbelian for m=", String(m)),
        IsElementaryAbelian(H_direct));
    CheckTrueBTPC(
        Concatenation("BEAD: contains centre z for m=", String(m)),
        z in H_direct);
od;

# ---- Test 4: MaximalElementaryAbelian_E_plus end-to-end (m=2,3,5,7) ---

Print("\nTest 4: MaximalElementaryAbelian_E_plus(m) end-to-end.\n");

for m in [2, 3, 5, 7] do
    Print("  m = ", m, ":\n");
    t0 := Runtime();
    rec_E := MaximalElementaryAbelian_E_plus(m);
    t1 := Runtime();
    Print("    MaximalElementaryAbelian_E_plus(", m, "): ",
          (t1 - t0) / 1000.0, " s\n");
    CheckEqualBTPC(
        Concatenation("MEA: rank for m=", String(m)),
        rec_E.rank, m + 1);
    CheckEqualBTPC(
        Concatenation("MEA: order for m=", String(m)),
        rec_E.order, 2^(m + 1));
    CheckTrueBTPC(
        Concatenation("MEA: IsElementaryAbelian for m=", String(m)),
        IsElementaryAbelian(rec_E.subgroup));
od;

# ---- Test 5: at m=2,3 closed-form and (legacy) greedy agree as
#               elementary abelians (same order, both contain z) -------

Print("\nTest 5: closed-form vs legacy greedy fallback (m in {2, 3, 5}).\n");

for m in [2, 3, 5] do
    Print("  m = ", m, ":\n");
    G_m := EPlusGroup(m);
    Z_G := Centre(G_m);
    z := First(AsList(Z_G), x -> not IsOne(x));
    H_cf := _TryPCClosedFormEA_EPlus(G_m, m);
    H_greedy := _LegacyGreedyEA_EPlus(G_m, m);
    CheckTrueBTPC(
        Concatenation("closed-form non-fail at m=", String(m)),
        H_cf <> fail);
    if H_cf <> fail then
        CheckEqualBTPC(
            Concatenation("closed-form / greedy same order at m=",
                          String(m)),
            Order(H_cf), Order(H_greedy));
        CheckTrueBTPC(
            Concatenation("both elementary abelian at m=", String(m)),
            IsElementaryAbelian(H_cf) and IsElementaryAbelian(H_greedy));
        CheckTrueBTPC(
            Concatenation("both contain z at m=", String(m)),
            (z in H_cf) and (z in H_greedy));
    fi;
od;

# ---- Test 6: m = 1 is special (a_1 has order 4 in D_8) — closed-form
#               should not assert on m=1 ---------------------------------
#
# For m=1, ExtraspecialGroup(8, "+") = D_8. The first PC generator is
# the order-4 rotation, NOT a non-central involution. The closed-form
# helper should return fail at m=1 so the legacy path handles it.

Print("\nTest 6: m = 1 special case.\n");

G1 := EPlusGroup(1);
H_cf_m1 := _TryPCClosedFormEA_EPlus(G1, 1);
# Either fail (preferred) or a genuine rank-2 elementary abelian.
if H_cf_m1 = fail then
    Print("  [ok] m=1 closed-form correctly returns fail (D_8 quirk)\n");
else
    CheckEqualBTPC("m=1 closed-form |H| = 4", Order(H_cf_m1), 4);
    CheckTrueBTPC("m=1 closed-form IsElementaryAbelian",
                  IsElementaryAbelian(H_cf_m1));
fi;

# ---- Test 7: MaximalElementaryAbelian_E_plus(1) still works ----------

Print("\nTest 7: MaximalElementaryAbelian_E_plus(1) backward compat.\n");

rec_E1 := MaximalElementaryAbelian_E_plus(1);
CheckEqualBTPC("MEA(1): rank", rec_E1.rank, 2);
CheckEqualBTPC("MEA(1): order", rec_E1.order, 4);
CheckTrueBTPC("MEA(1): IsElementaryAbelian",
              IsElementaryAbelian(rec_E1.subgroup));

# ---- Summary ---------------------------------------------------------

Print("\n");
if Length(btpc_failures) = 0 then
    Print("All ", "test_buildelementary_eplus_pc",
          " tests passed.\n");
else
    Print(Length(btpc_failures), " FAILURE(S) in ",
          "test_buildelementary_eplus_pc:\n");
    for f in btpc_failures do Print("  - ", f, "\n"); od;
fi;
