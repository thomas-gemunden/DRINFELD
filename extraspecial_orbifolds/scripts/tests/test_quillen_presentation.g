# test_quillen_presentation.g -- regression test for Q-2 Path P
# (issue #22 / task #37).
#
# Acceptance: for m in {1, 2, 3} and d in 0..4, the F_2 dimension of
# the degree-d component of QuillenPresentation(m) must equal
# dim H^d(E_+(m); F_2) computed live by HAP.
#
# The test computes HAP dimensions itself (using
# `ResolutionPrimePowerGroup`, which is minimal over F_2 -- so the
# module ranks equal the F_2 homology dimensions; this is dramatically
# faster than `ResolutionFiniteGroup` for E_+(3)). Then it compares
# against `QuillenPresentation(m)`.
#
# Run from inside GAP (any CWD):
#     gap test_quillen_presentation.g
# or:
#     ChangeDirectoryCurrent("...DRINFELD-wt-q2/extraspecial_orbifolds/scripts/tests");
#     Read("test_quillen_presentation.g");
# Success is signalled by "test_quillen_presentation: PASS".

# ---- Locate the parent module -----------------------------------------

_qpt_loaded := false;;
_qpt_self_path := INPUT_FILENAME();;
if _qpt_self_path <> fail and _qpt_self_path <> "stream" then
    _qpt_self_dir := _qpt_self_path{[1..Length(_qpt_self_path) - Length("/test_quillen_presentation.g")]};;
    _qpt_candidate := Concatenation(_qpt_self_dir, "/../quillen_presentation.g");;
    if IsExistingFile(_qpt_candidate) then
        Read(_qpt_candidate);
        _qpt_loaded := true;
    fi;
fi;
if not _qpt_loaded then
    for _qpt_p in [ "../quillen_presentation.g",
                    "quillen_presentation.g",
                    "extraspecial_orbifolds/scripts/quillen_presentation.g",
                    "scripts/quillen_presentation.g" ] do
        if not _qpt_loaded and IsExistingFile(_qpt_p) then
            Read(_qpt_p);
            _qpt_loaded := true;
        fi;
    od;
fi;
if not _qpt_loaded then
    Error("cannot locate quillen_presentation.g; run from ",
          "extraspecial_orbifolds/scripts/tests/.");
fi;

# ---- HAP --------------------------------------------------------------

LoadPackage("hap");

# Compute dim H^d(SmallGroup(n, mid); F_2) for d in 0..max_deg using a
# minimal F_p resolution (p = 2). For p-groups in characteristic p,
# `ResolutionPrimePowerGroup` builds a MINIMAL resolution, so after
# tensoring with F_p all boundary maps are zero and Homology(K, d)
# equals the module rank R!.dimension(d). We use Homology(K, d)
# directly (rather than the rank shortcut) so the test exercises the
# real HAP API path used in production code.
QuillenPresentationHAPDimsLive := function(n, mid, max_deg)
    local G, R, K, d, dims;
    G := SmallGroup(n, mid);
    R := ResolutionPrimePowerGroup(G, max_deg + 1);
    K := TensorWithIntegersModP(R, 2);
    dims := [];
    for d in [0..max_deg] do
        Add(dims, Homology(K, d));
    od;
    return dims;
end;;

# ---- Test harness -----------------------------------------------------

failures := [];

CheckEqualQP := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
    else
        Print("  [FAIL] ", label, "\n");
        Print("        expected: ", expected, "\n");
        Print("        got     : ", got, "\n");
        Add(failures, label);
    fi;
end;;

# ---- Test 1: HAP-cached dims match HAP-live dims for m = 1, 2, 3 ------
#
# Cross-check: the hard-coded `QuillenPresentationHAPDims(m)` table
# inside `quillen_presentation.g` should agree with what HAP computes
# live (via the minimal resolution).

Print("Test 1: cached HAP dims agree with live HAP computation.\n");

for m in [1, 2, 3] do
    Print("  m = ", m, " (SmallGroup", QuillenPresentationGroupID(m), "):\n");
    cached := QuillenPresentationHAPDims(m);
    Print("    cached = ", cached, "\n");
    live := QuillenPresentationHAPDimsLive(
                QuillenPresentationGroupID(m)[1],
                QuillenPresentationGroupID(m)[2],
                4);
    Print("    live   = ", live, "\n");
    CheckEqualQP(Concatenation("HAP dims agree for m = ", String(m)),
                 cached, live);
od;

# ---- Test 2: QuillenPresentation(m) basis sizes match HAP dims --------
#
# THE acceptance test. For m in {1, 2, 3} and d in 0..4,
#     Length(BasisInDegree(QuillenPresentation(m), d))
#         == dim H^d(E_+(m); F_2).

Print("\nTest 2: BasisInDegree(QuillenPresentation(m), d) matches HAP for d=0..4.\n");

for m in [1, 2, 3] do
    Print("  m = ", m, ":\n");
    A := QuillenPresentation(m);
    dims_target := QuillenPresentationHAPDims(m);
    for d in [0..4] do
        got := Length(BasisInDegree(A, d));
        CheckEqualQP(
            Concatenation("m = ", String(m), ", d = ", String(d)),
            got, dims_target[d + 1]);
    od;
od;

# ---- Test 3: provenance fields are present ----------------------------

Print("\nTest 3: provenance fields (.path, .m, .group_id, .target_dims).\n");

for m in [1, 2, 3] do
    A := QuillenPresentation(m);
    CheckEqualQP(Concatenation(".path for m=", String(m)),  A.path,    "P");
    CheckEqualQP(Concatenation(".m for m=", String(m)),     A.m,       m);
    CheckEqualQP(Concatenation(".group_id for m=", String(m)),
                 A.group_id, QuillenPresentationGroupID(m));
    CheckEqualQP(Concatenation(".target_dims for m=", String(m)),
                 A.target_dims, QuillenPresentationHAPDims(m));
    CheckEqualQP(Concatenation(".is_quillen_algebra for m=", String(m)),
                 A.is_quillen_algebra, true);
od;

# ---- Test 4: convenience function QuillenPresentationDimensions -------

Print("\nTest 4: QuillenPresentationDimensions(A) == target_dims.\n");

for m in [1, 2, 3] do
    A := QuillenPresentation(m);
    CheckEqualQP(Concatenation("dims vector m=", String(m)),
                 QuillenPresentationDimensions(A),
                 QuillenPresentationHAPDims(m));
od;

# ---- Test 5: error path for m out of range ----------------------------
#
# Verify QuillenPresentation rejects m outside {1, 2, 3}. We use
# `CALL_WITH_CATCH` combined with `BreakOnError := false` to capture
# the error without dropping into the break loop. CALL_WITH_CATCH
# returns [true, result] on success and [false, ...] on caught error.

Print("\nTest 5: error path for m not in {1, 2, 3}.\n");

_qpt_save_break_on_error := BreakOnError;;
BreakOnError := false;;
trap_4 := function()
    local A;
    A := QuillenPresentation(4);
end;;
ok := CALL_WITH_CATCH(trap_4, []);;
BreakOnError := _qpt_save_break_on_error;;

err_caught := IsList(ok) and Length(ok) >= 1 and ok[1] = false;;
CheckEqualQP("m = 4 raises error", err_caught, true);

# ---- Final report -----------------------------------------------------

if Length(failures) = 0 then
    Print("\ntest_quillen_presentation: PASS\n");
else
    Print("\ntest_quillen_presentation: FAIL (", Length(failures),
          " failure(s)):\n");
    for i in [1..Length(failures)] do
        Print("  - ", failures[i], "\n");
    od;
fi;

QUIT;
