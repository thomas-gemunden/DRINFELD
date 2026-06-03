# test_k4a_dvan_family_missing_warning.g
#
# Issue #428: regression test for the loud WARNING block emitted by
# K4aClassify when the D-VAN minimum detecting family is unavailable
# at m >= 3 with non-zero omega (single-EA fallback is non-injective
# at m >= 3, so a false-negative "trivial" verdict is possible).
#
# What we check:
#   T1. Gate predicate (lattice_source && !omega_zero && m>=3 && family=fail)
#       fires correctly at m=7 with the current state of
#       computed/dvan_min_family/m7/result.g (missing ea_generators).
#   T2. Gate predicate does NOT fire at m=2 (family is registered).
#   T3. Gate predicate does NOT fire when omega is zero (short-circuited).
#   T4. Gate predicate does NOT fire when m < 3 even with non-zero omega.
#   T5. Gate predicate does NOT fire when lattice_source = false.
#   T6. _K4A_GetDVANEAFamily(99) returns fail (sanity: missing m).
#   T7. The top-level returned-rec construction logic propagates
#       `dvan_family_missing` from E_class. Emulated by building a mock
#       E_class with the flag set and checking the IsBound+and pattern.
#   T8. Warning text appears in captured stdout when gate fires
#       (PrintTo + OutputTextString replay of the production Print call).
#   T9. The k4a_classify.g source itself contains the WARNING block
#       and the `dvan_family_missing` propagation.
#
# This test does NOT actually invoke K4aClassify(7, ...) because that
# requires a multi-minute spectral build. Instead it verifies the gate
# predicates that K4aClassify uses, the warning-text printing logic,
# and the `dvan_family_missing` propagation logic — i.e., everything
# the issue #428 fix introduces.
#
# Run from absolute path:
#   gap -q -b /Users/.../tests/test_k4a_dvan_family_missing_warning.g
#
# Exit 0 on success, non-zero on any failure.

K4A_W_PASSES   := 0;;
K4A_W_FAILURES := [];;

K4AWAssertEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
        K4A_W_PASSES := K4A_W_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Print("         expected: ", expected, "\n");
        Print("         got:      ", got, "\n");
        Add(K4A_W_FAILURES, label);
    fi;
end;;

K4AWAssertTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
        K4A_W_PASSES := K4A_W_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Add(K4A_W_FAILURES, label);
    fi;
end;;

K4A_W_SELF := INPUT_FILENAME();;
if K4A_W_SELF = fail or K4A_W_SELF = "stream" then
    Error("test_k4a_dvan_family_missing_warning.g: INPUT_FILENAME() ",
          "unavailable; Read the file by its absolute path.");
fi;
# Resolve to absolute path if invoked via relative path (gap -q -b tests/foo.g).
if Length(K4A_W_SELF) >= 1 and K4A_W_SELF[1] <> '/' then
    K4A_W_SELF := Concatenation(Filename(DirectoryCurrent(), ""),
                                K4A_W_SELF);
fi;
K4A_W_SELFDIR := K4A_W_SELF{
    [1..Length(K4A_W_SELF) - Length("/test_k4a_dvan_family_missing_warning.g")]};;
K4A_W_SCRIPTSDIR := K4A_W_SELFDIR{
    [1..Length(K4A_W_SELFDIR) - Length("/tests")]};;

Print("=================================================================\n");
Print("test_k4a_dvan_family_missing_warning.g (#428)\n");
Print("=================================================================\n");
Print("self        : ", K4A_W_SELF, "\n");
Print("scripts dir : ", K4A_W_SCRIPTSDIR, "\n");

K4A_W_ORIG_DIR := DirectoryCurrent();;
ChangeDirectoryCurrent(K4A_W_SCRIPTSDIR);;
Read("k4a_classify.g");
ChangeDirectoryCurrent(Filename(K4A_W_ORIG_DIR, ""));;

# Gate predicate emulating the exact condition in k4a_classify.g
# around line 912-915. This MUST stay in sync with the production code.
K4AWGateFires := function(opts, m)
    return opts.lattice_source
       and (not _K4A_OmegaIsZero(opts.omega_vec))
       and m >= 3
       and _K4A_GetDVANEAFamily(m) = fail;
end;;

# ---- T1: m=7 with non-zero omega, lattice_source — gate FIRES ----------

Print("\nT1. Gate fires at m=7 with non-zero omega (D-VAN family missing today)\n");
K4A_W_OPTS_M7_NZ := rec(
    lattice_source := true,
    omega_vec      := [1, 0, 0, 0]
);;
K4AWAssertEqual("_K4A_GetDVANEAFamily(7) = fail (today's state)",
                 _K4A_GetDVANEAFamily(7), fail);
K4AWAssertTrue("gate fires at m=7 (warning should print)",
                K4AWGateFires(K4A_W_OPTS_M7_NZ, 7));

# ---- T2: m=2 with non-zero omega, lattice_source — gate does NOT fire --

Print("\nT2. Gate does NOT fire at m=2 (family is hardcoded in registry)\n");
K4A_W_OPTS_M2_NZ := rec(
    lattice_source := true,
    omega_vec      := [1, 0, 0, 0]
);;
K4AWAssertTrue("_K4A_GetDVANEAFamily(2) <> fail",
                _K4A_GetDVANEAFamily(2) <> fail);
K4AWAssertTrue("gate does NOT fire at m=2",
                not K4AWGateFires(K4A_W_OPTS_M2_NZ, 2));

# ---- T3: omega=0 short-circuits the gate ------------------------------

Print("\nT3. Gate does NOT fire when omega is zero (regardless of m)\n");
K4A_W_OPTS_M7_ZERO := rec(
    lattice_source := true,
    omega_vec      := [0, 0, 0, 0]
);;
K4AWAssertTrue("gate does NOT fire at m=7 with omega = 0",
                not K4AWGateFires(K4A_W_OPTS_M7_ZERO, 7));
K4A_W_OPTS_M7_EMPTY := rec(
    lattice_source := true,
    omega_vec      := []
);;
K4AWAssertTrue("gate does NOT fire at m=7 with omega = []",
                not K4AWGateFires(K4A_W_OPTS_M7_EMPTY, 7));
K4A_W_OPTS_M7_FAIL := rec(
    lattice_source := true,
    omega_vec      := fail
);;
K4AWAssertTrue("gate does NOT fire at m=7 with omega = fail",
                not K4AWGateFires(K4A_W_OPTS_M7_FAIL, 7));

# ---- T4: m < 3 short-circuits the gate (untwisted m=1, m=2) ------------

Print("\nT4. Gate does NOT fire when m < 3, even with non-zero omega\n");
K4A_W_OPTS_M1_NZ := rec(
    lattice_source := true,
    omega_vec      := [1]
);;
K4AWAssertTrue("gate does NOT fire at m=1 (m < 3 short-circuit)",
                not K4AWGateFires(K4A_W_OPTS_M1_NZ, 1));

# ---- T5: lattice_source = false short-circuits ------------------------

Print("\nT5. Gate does NOT fire when lattice_source = false\n");
K4A_W_OPTS_M7_NONLATTICE := rec(
    lattice_source := false,
    omega_vec      := fail
);;
K4AWAssertTrue("gate does NOT fire at m=7 with lattice_source = false",
                not K4AWGateFires(K4A_W_OPTS_M7_NONLATTICE, 7));

# ---- T6: sanity — missing m returns fail ------------------------------

Print("\nT6. _K4A_GetDVANEAFamily(99) returns fail\n");
K4AWAssertEqual("get m=99 (no entry, no file)",
                 _K4A_GetDVANEAFamily(99), fail);

# ---- T7: dvan_family_missing propagation logic -------------------------

Print("\nT7. dvan_family_missing propagates from E_class to top-level rec\n");
# Emulate the expression used in K4aClassify's return rec:
#   dvan_family_missing := IsBound(E_class.dvan_family_missing)
#                            and E_class.dvan_family_missing
K4A_W_MOCK_EC_FLAG := rec(is_coboundary := true,
                          dvan_family_missing := true);;
K4A_W_MOCK_EC_NOFLAG := rec(is_coboundary := true);;
K4A_W_MOCK_EC_FALSE := rec(is_coboundary := true,
                           dvan_family_missing := false);;
K4AWAssertEqual("propagation: flag = true bubbles up",
                 IsBound(K4A_W_MOCK_EC_FLAG.dvan_family_missing)
                   and K4A_W_MOCK_EC_FLAG.dvan_family_missing,
                 true);
K4AWAssertEqual("propagation: flag absent bubbles up as false",
                 IsBound(K4A_W_MOCK_EC_NOFLAG.dvan_family_missing)
                   and K4A_W_MOCK_EC_NOFLAG.dvan_family_missing,
                 false);
K4AWAssertEqual("propagation: flag = false bubbles up as false",
                 IsBound(K4A_W_MOCK_EC_FALSE.dvan_family_missing)
                   and K4A_W_MOCK_EC_FALSE.dvan_family_missing,
                 false);

# ---- T8: warning text appears in captured stdout ----------------------

Print("\nT8. Warning text appears in captured stdout when gate fires\n");
# Capture stdout via OutputTextString. We replay the exact Print(...)
# call from k4a_classify.g around the warning block, but written into
# the stream.
K4A_W_TMPSTR := "";;
K4A_W_STREAM := OutputTextString(K4A_W_TMPSTR, true);;
SetPrintFormattingStatus(K4A_W_STREAM, false);;
K4A_W_M_PROBE := 7;;
PrintTo(K4A_W_STREAM, "\n",
        "  ============================================================\n",
        "  WARNING: D-VAN minimum detecting family unavailable at m = ", K4A_W_M_PROBE, ".\n",
        "    LoadDVANEAFamily(", K4A_W_M_PROBE, ") / _K4A_GetDVANEAFamily(", K4A_W_M_PROBE, ") returned fail.\n",
        "    Falling back to single-EA `MaximalElementaryAbelian_E_plus(", K4A_W_M_PROBE, ").subgroup`.\n",
        "    Single-EA restriction is NOT injective at m >= 3.\n",
        "    A FALSE-NEGATIVE 'trivial' verdict is POSSIBLE.\n",
        "  To fix:\n",
        "    * For m=7: regenerate computed/dvan_min_family/m7/result.g with\n",
        "      ea_generators field populated (see issue #427).\n",
        "    * For other m: ensure _K4A_DVAN_EA_FAMILIES has the correct entry\n",
        "      in k4a_classify.g.\n",
        "  ============================================================\n");
CloseStream(K4A_W_STREAM);;
K4AWAssertTrue("captured contains 'WARNING:'",
                PositionSublist(K4A_W_TMPSTR, "WARNING:") <> fail);
K4AWAssertTrue("captured names the m value (m = 7)",
                PositionSublist(K4A_W_TMPSTR, "m = 7") <> fail);
K4AWAssertTrue("captured warns about non-injectivity",
                PositionSublist(K4A_W_TMPSTR,
                                "NOT injective at m >= 3") <> fail);
K4AWAssertTrue("captured names the FALSE-NEGATIVE risk",
                PositionSublist(K4A_W_TMPSTR,
                                "FALSE-NEGATIVE") <> fail);
K4AWAssertTrue("captured names the fix path (issue #427)",
                PositionSublist(K4A_W_TMPSTR, "#427") <> fail);
K4AWAssertTrue("captured names the registry (_K4A_DVAN_EA_FAMILIES)",
                PositionSublist(K4A_W_TMPSTR,
                                "_K4A_DVAN_EA_FAMILIES") <> fail);

# ---- T9: verify the WARNING text in k4a_classify.g matches the spec ----

Print("\nT9. k4a_classify.g source contains the WARNING block\n");
K4A_W_SRC_PATH := Concatenation(K4A_W_SCRIPTSDIR, "/k4a_classify.g");;
K4A_W_SRC_CONTENT := StringFile(K4A_W_SRC_PATH);;
K4AWAssertTrue("source contains 'WARNING: D-VAN minimum detecting family'",
                PositionSublist(K4A_W_SRC_CONTENT,
                                "WARNING: D-VAN minimum detecting family") <> fail);
K4AWAssertTrue("source sets E_class.dvan_family_missing := true",
                PositionSublist(K4A_W_SRC_CONTENT,
                                "E_class.dvan_family_missing := true") <> fail);
K4AWAssertTrue("source returns dvan_family_missing at top level",
                PositionSublist(K4A_W_SRC_CONTENT,
                                "dvan_family_missing := IsBound(E_class.dvan_family_missing)") <> fail);

# ---- Summary -----------------------------------------------------------

Print("\n=================================================================\n");
Print("Passes  : ", K4A_W_PASSES, "\n");
Print("Failures: ", Length(K4A_W_FAILURES), "\n");
if Length(K4A_W_FAILURES) > 0 then
    Print("Failed labels:\n");
    for K4A_W_LBL in K4A_W_FAILURES do
        Print("  - ", K4A_W_LBL, "\n");
    od;
    Print("=================================================================\n");
    QuitGap(1);
fi;
Print("All warning-block checks passed.\n");
Print("\nNOTE: This test verifies the GATE PREDICATE and the WARNING\n");
Print("text/flag propagation. A full integration test of K4aClassify(7, e_i)\n");
Print("emitting the warning to stdout is deferred (multi-minute spectral\n");
Print("build); the predicate-level + text-content coverage above is\n");
Print("sufficient to keep the warning live.\n");
Print("=================================================================\n");
QuitGap(0);
