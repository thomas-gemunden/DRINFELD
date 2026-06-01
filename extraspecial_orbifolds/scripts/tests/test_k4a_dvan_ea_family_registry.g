# test_k4a_dvan_ea_family_registry.g
#
# Issue #334 cleanup: regression test for the multi-EA E-branch routing
# registry (`_K4A_DVAN_EA_FAMILIES` + `_K4A_GetDVANEAFamily`) in
# k4a_classify.g.
#
# Context: PR #338 landed the multi-EA E-branch classifier
# (`_K4A_ClassifyEBranchMulti`) and the per-m hardcoded D-VAN minimum
# family. `K4aClassify` routes through the multi-EA path when
# `opts.lattice_source = true` and `opts.omega_vec` is non-zero and a
# hardcoded family for that m exists. This test cheaply verifies the
# registry shape and the helper predicates; it does NOT run the full
# K4aClassify pipeline (that's ~30-40 min wall at m=5 — see
# test_k4a_classify_m5_smoke.g).
#
# What we check:
#   T1. `_K4A_DVAN_EA_FAMILIES` is bound and has keys for m = 2, 3, 5.
#   T2. The per-m families match the published PR #320 anchors.
#   T3. `_K4A_GetDVANEAFamily(m)` returns the right list for m in {2, 3, 5}.
#   T4. `_K4A_GetDVANEAFamily(m)` returns `fail` for m where no family is
#       hardcoded (m=4, m=7).
#   T5. `_K4A_OmegaIsZero` returns true on the canonical zero vector
#       and false on a non-zero vector.
#
# Run from absolute path:
#   gap -q -b /Users/.../tests/test_k4a_dvan_ea_family_registry.g
#
# Exit 0 on success, non-zero on any failure.

# ---- Test bookkeeping --------------------------------------------------

K4A_REG_PASSES   := 0;;
K4A_REG_FAILURES := [];;

K4ARegAssertEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
        K4A_REG_PASSES := K4A_REG_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Print("         expected: ", expected, "\n");
        Print("         got:      ", got, "\n");
        Add(K4A_REG_FAILURES, label);
    fi;
end;;

K4ARegAssertTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
        K4A_REG_PASSES := K4A_REG_PASSES + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Add(K4A_REG_FAILURES, label);
    fi;
end;;

# ---- Locate the script + load k4a_classify.g ---------------------------

K4A_REG_SELF := INPUT_FILENAME();;
if K4A_REG_SELF = fail or K4A_REG_SELF = "stream" then
    Error("test_k4a_dvan_ea_family_registry.g: INPUT_FILENAME() ",
          "unavailable; Read the file by its absolute path.");
fi;
K4A_REG_SELFDIR := K4A_REG_SELF{
    [1..Length(K4A_REG_SELF) - Length("/test_k4a_dvan_ea_family_registry.g")]};;
K4A_REG_SCRIPTSDIR := K4A_REG_SELFDIR{
    [1..Length(K4A_REG_SELFDIR) - Length("/tests")]};;

Print("=================================================================\n");
Print("test_k4a_dvan_ea_family_registry.g (#334 cleanup)\n");
Print("=================================================================\n");
Print("self        : ", K4A_REG_SELF, "\n");
Print("scripts dir : ", K4A_REG_SCRIPTSDIR, "\n");

# Load k4a_classify.g from the scripts directory. We need
# ChangeDirectoryCurrent because k4a_classify.g uses relative `Read`s
# for sibling files.
K4A_REG_ORIG_DIR := DirectoryCurrent();;
ChangeDirectoryCurrent(K4A_REG_SCRIPTSDIR);;
Read("k4a_classify.g");
ChangeDirectoryCurrent(Filename(K4A_REG_ORIG_DIR, ""));;

# ---- T1: registry is bound + has the expected keys ---------------------

Print("\nT1. _K4A_DVAN_EA_FAMILIES is bound + has expected keys\n");
K4ARegAssertTrue("registry is bound",
                  IsBoundGlobal("_K4A_DVAN_EA_FAMILIES"));
K4ARegAssertTrue("registry is a record",
                  IsRecord(_K4A_DVAN_EA_FAMILIES));
K4ARegAssertTrue("m=2 family key present",
                  IsBound(_K4A_DVAN_EA_FAMILIES.("2")));
K4ARegAssertTrue("m=3 family key present",
                  IsBound(_K4A_DVAN_EA_FAMILIES.("3")));
K4ARegAssertTrue("m=5 family key present",
                  IsBound(_K4A_DVAN_EA_FAMILIES.("5")));

# ---- T2: family values match PR #320 anchors --------------------------

Print("\nT2. Per-m families match PR #320 anchors\n");
K4ARegAssertEqual("m=2 family value",
                   _K4A_DVAN_EA_FAMILIES.("2"),
                   [3, 2, 5]);
K4ARegAssertEqual("m=3 family value",
                   _K4A_DVAN_EA_FAMILIES.("3"),
                   [4, 6, 7, 11, 16, 22]);
K4ARegAssertEqual("m=5 family value",
                   _K4A_DVAN_EA_FAMILIES.("5"),
                   [33, 48, 54, 57, 70, 76, 88, 89, 109]);

# ---- T3: _K4A_GetDVANEAFamily returns the lists ------------------------

Print("\nT3. _K4A_GetDVANEAFamily(m) returns the lists\n");
K4ARegAssertEqual("get m=2", _K4A_GetDVANEAFamily(2), [3, 2, 5]);
K4ARegAssertEqual("get m=3",
                   _K4A_GetDVANEAFamily(3),
                   [4, 6, 7, 11, 16, 22]);
K4ARegAssertEqual("get m=5",
                   _K4A_GetDVANEAFamily(5),
                   [33, 48, 54, 57, 70, 76, 88, 89, 109]);

# ---- T4: missing m returns fail ----------------------------------------

Print("\nT4. _K4A_GetDVANEAFamily(m) returns fail for unhardcoded m\n");
K4ARegAssertEqual("get m=4 (out-of-scope)",
                   _K4A_GetDVANEAFamily(4), fail);
# Issue #377: m=7 falls through to LoadDVANEAFamily(7). Until a
# regenerated result.g containing `ea_generators` lands, the loader
# returns fail, which propagates as the `_K4A_GetDVANEAFamily(7)`
# return value. After the next D-VAN m=7 production rerun (with
# `ea_generators` persisted), this assertion changes — the registry
# will return a list of subgroups instead.
K4ARegAssertEqual("get m=7 (loader returns fail when ea_generators absent)",
                   _K4A_GetDVANEAFamily(7), fail);

# ---- T5: _K4A_OmegaIsZero ----------------------------------------------

Print("\nT5. _K4A_OmegaIsZero predicate\n");
K4ARegAssertTrue("zero vec is zero",
                  _K4A_OmegaIsZero([0, 0, 0, 0, 0]));
K4ARegAssertTrue("empty vec is zero",
                  _K4A_OmegaIsZero([]));
K4ARegAssertTrue("fail is zero",
                  _K4A_OmegaIsZero(fail));
K4ARegAssertTrue("non-zero vec is NOT zero",
                  not _K4A_OmegaIsZero([0, 0, 1, 0]));
K4ARegAssertTrue("single non-zero entry is NOT zero",
                  not _K4A_OmegaIsZero([0, 0, 0, 0, 2]));

# ---- Summary -----------------------------------------------------------

Print("\n=================================================================\n");
Print("Passes : ", K4A_REG_PASSES, "\n");
Print("Failures: ", Length(K4A_REG_FAILURES), "\n");
if Length(K4A_REG_FAILURES) > 0 then
    Print("Failed labels:\n");
    for K4A_REG_LBL in K4A_REG_FAILURES do
        Print("  - ", K4A_REG_LBL, "\n");
    od;
    QuitGap(1);
fi;
Print("All registry checks passed.\n");
Print("=================================================================\n");
QuitGap(0);
