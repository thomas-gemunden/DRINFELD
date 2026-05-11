# test_quillen_h3_callable.g — Q-7 / issue #27 acceptance tests.
#
# Tests for `StandardCocycleQuillen(class_alg)` in
# `extraspecial_orbifolds/scripts/quillen_h3_callable.g`.
#
# Acceptance per Q-7:
#   (1) Cocycle condition: for every generator's callable f and a
#       random sample of |G|^4 tuples, delta(f) = 0 mod m.
#   (2) HAP cross-check at m=2 (G = E_+(2) = SmallGroup(32, 49)): each
#       generator's callable agrees with a directly-constructed HAP
#       StandardCocycle on a sample of G^3.
#   (3) Performance gate at m=7 (E_+(7), 32768 elements): SKIPPED by
#       default — set Q7_INCLUDE_PERF := true before reading to opt in.
#
# Run from this directory:
#   gap -q -b ./test_quillen_h3_callable.g
# or from anywhere:
#   gap -q -b /path/to/test_quillen_h3_callable.g

# ---- Locate the module ------------------------------------------------

_q7t_loaded := false;;
_q7t_self_path := INPUT_FILENAME();;
if _q7t_self_path <> fail and _q7t_self_path <> "stream" then
    _q7t_self_dir := _q7t_self_path{[1..Length(_q7t_self_path)
                                     - Length("/test_quillen_h3_callable.g")]};;
    _q7t_candidate := Concatenation(_q7t_self_dir,
                                    "/../quillen_h3_callable.g");;
    if IsExistingFile(_q7t_candidate) then
        Read(_q7t_candidate);
        _q7t_loaded := true;
    fi;
    _q7t_qp := Concatenation(_q7t_self_dir,
                             "/../quillen_presentation.g");;
    if IsExistingFile(_q7t_qp) then
        Read(_q7t_qp);
    fi;
fi;
if not _q7t_loaded then
    for _q7t_p in [ "../quillen_h3_callable.g",
                    "quillen_h3_callable.g",
                    "extraspecial_orbifolds/scripts/quillen_h3_callable.g" ] do
        if not _q7t_loaded and IsExistingFile(_q7t_p) then
            Read(_q7t_p);
            _q7t_loaded := true;
        fi;
    od;
    for _q7t_p in [ "../quillen_presentation.g",
                    "quillen_presentation.g",
                    "extraspecial_orbifolds/scripts/quillen_presentation.g" ] do
        if IsExistingFile(_q7t_p) then
            Read(_q7t_p);
        fi;
    od;
fi;
if not _q7t_loaded then
    Error("test_quillen_h3_callable.g: cannot find quillen_h3_callable.g; ",
          "run from extraspecial_orbifolds/scripts/tests/.");
fi;

# Default: do NOT run the perf gate (E_+(7) is huge — 32768 elements
# — and we don't have a construction for it yet anyway).
if not IsBoundGlobal("Q7_INCLUDE_PERF") then
    BindGlobal("Q7_INCLUDE_PERF", false);
fi;


# ---- Harness ----------------------------------------------------------

_q7t_pass := 0;;
_q7t_fail := 0;;
_q7t_failures := [];;

_q7t_assert := function(label, cond)
    if cond then
        Print("  OK   ", label, "\n");
        _q7t_pass := _q7t_pass + 1;
    else
        Print("  FAIL ", label, "\n");
        _q7t_fail := _q7t_fail + 1;
        Add(_q7t_failures, label);
    fi;
end;;


# ---- Test 1: m=1 (D_8) sanity check ----------------------------------
#
# Smallest case: G = D_8 = E_+(1), |G| = 8. The Q-7 wrapper should
# return a record with one callable per H^3(D_8; U(1)) generator.
# Verify shape + cocycle property + per-generator HAP agreement.

Print("\n=== Test 1: m=1 (D_8 = E_+(1)) wrapper shape + cocycle + HAP agreement ===\n");

_q7t_calg1 := QuillenPresentation(1);;
_q7t_r1    := StandardCocycleQuillen(_q7t_calg1);;
Print("  D_8 torsion = ", _q7t_r1.torsion, "\n");
Print("  D_8 exponent = ", _q7t_r1.exponent, "\n");
Print("  # callables = ", Length(_q7t_r1.callables), "\n");
_q7t_assert("D_8 wrapper has .G, .setup, .callables, .moduli, .torsion",
            IsBound(_q7t_r1.G)
            and IsBound(_q7t_r1.setup)
            and IsBound(_q7t_r1.callables)
            and IsBound(_q7t_r1.moduli)
            and IsBound(_q7t_r1.torsion));
_q7t_assert("D_8 wrapper .path = \"A\"",
            _q7t_r1.path = "A");
_q7t_assert("D_8 wrapper #callables = #hombasis",
            Length(_q7t_r1.callables) = Length(_q7t_r1.setup.UCT.hombasis));
_q7t_assert("D_8 wrapper #moduli = #callables",
            Length(_q7t_r1.moduli) = Length(_q7t_r1.callables));
_q7t_assert("D_8 wrapper .G has |G| = 8",
            Size(_q7t_r1.G) = 8);

# Cocycle property: for each generator, sample 50 random G^4 tuples and
# verify delta(f) = 0 mod m.
_q7t_check_cocycle_random := function(f, G, m, n_samples)
    local elts, violations, k, a, b, c, d, lhs;
    elts := Elements(G);
    violations := 0;
    for k in [1..n_samples] do
        a := Random(elts);
        b := Random(elts);
        c := Random(elts);
        d := Random(elts);
        lhs := CoboundaryOf3Cochain(f, a, b, c, d, m);
        if lhs <> 0 then violations := violations + 1; fi;
    od;
    return rec(checked := n_samples, violations := violations);
end;;

Print("  --- D_8 cocycle condition: 50 random samples per generator ---\n");
for _q7t_i in [1..Length(_q7t_r1.callables)] do
    _q7t_f   := _q7t_r1.callables[_q7t_i];
    _q7t_m   := _q7t_r1.moduli[_q7t_i];
    _q7t_res := _q7t_check_cocycle_random(_q7t_f, _q7t_r1.G, _q7t_m, 50);
    Print("    gen ", _q7t_i, ": delta-violations = ",
          _q7t_res.violations, " / ", _q7t_res.checked, "\n");
    _q7t_assert(Concatenation("D_8 gen ", String(_q7t_i),
                              " is a cocycle on 50 random samples"),
                _q7t_res.violations = 0);
od;

# HAP cross-check: build the HAP cocycle directly and compare on a
# sample of G^3 tuples. Path A IS the HAP path so this should be
# byte-for-byte identical, including all torsion classes.
Print("  --- D_8 HAP cross-check: per-generator agreement on 50 G^3 samples ---\n");
_q7t_R1 := _q7t_r1.setup.R;;
_q7t_m1 := _q7t_r1.exponent;;
for _q7t_i in [1..Length(_q7t_r1.callables)] do
    _q7t_hom_i := _q7t_r1.setup.UCT.hombasis[_q7t_i];
    _q7t_vec_i := (_q7t_r1.setup.UCT.lift * _q7t_hom_i) mod _q7t_m1;
    _q7t_f_hap := StandardCocycle(_q7t_R1, _q7t_vec_i, 3, _q7t_m1);
    _q7t_f_wr  := _q7t_r1.callables[_q7t_i];
    _q7t_agree := 0;
    _q7t_dis   := 0;
    for _q7t_k in [1..50] do
        _q7t_g1 := Random(_q7t_r1.G);
        _q7t_g2 := Random(_q7t_r1.G);
        _q7t_g3 := Random(_q7t_r1.G);
        if _q7t_f_wr(_q7t_g1, _q7t_g2, _q7t_g3) =
           _q7t_f_hap(_q7t_g1, _q7t_g2, _q7t_g3) then
            _q7t_agree := _q7t_agree + 1;
        else
            _q7t_dis := _q7t_dis + 1;
        fi;
    od;
    Print("    gen ", _q7t_i, ": agree = ", _q7t_agree, " / 50",
          ", disagree = ", _q7t_dis, "\n");
    _q7t_assert(Concatenation("D_8 gen ", String(_q7t_i),
                              " wrapper agrees with HAP on 50 samples"),
                _q7t_dis = 0);
od;


# ---- Test 2: m=2 (E_+(2) = SmallGroup(32, 49)) — primary acceptance --
#
# The Q-7 acceptance criterion: at m=2 the wrapper agrees with HAP's
# StandardCocycle on every generator and the cocycle property holds
# on a random G^4 sample.

Print("\n=== Test 2: m=2 (E_+(2) = SmallGroup(32, 49)) ===\n");

_q7t_calg2 := QuillenPresentation(2);;
_q7t_r2    := StandardCocycleQuillen(_q7t_calg2);;
Print("  E_+(2) torsion = ", _q7t_r2.torsion, "\n");
Print("  E_+(2) exponent = ", _q7t_r2.exponent, "\n");
Print("  # callables = ", Length(_q7t_r2.callables), "\n");
_q7t_assert("E_+(2) wrapper #callables = 10",
            Length(_q7t_r2.callables) = 10);
_q7t_assert("E_+(2) exponent = 8",
            _q7t_r2.exponent = 8);

# Cocycle property: 30 random tuples per generator (G has 32 elements,
# so |G|^4 = 1048576 — sampling is the only realistic check).
Print("  --- E_+(2) cocycle condition: 30 random G^4 samples per generator ---\n");
for _q7t_i in [1..Length(_q7t_r2.callables)] do
    _q7t_f   := _q7t_r2.callables[_q7t_i];
    _q7t_m   := _q7t_r2.moduli[_q7t_i];
    _q7t_res := _q7t_check_cocycle_random(_q7t_f, _q7t_r2.G, _q7t_m, 30);
    Print("    gen ", _q7t_i, ": delta-violations = ",
          _q7t_res.violations, " / ", _q7t_res.checked, "\n");
    _q7t_assert(Concatenation("E_+(2) gen ", String(_q7t_i),
                              " is a cocycle on 30 random samples"),
                _q7t_res.violations = 0);
od;

# HAP cross-check on E_+(2): 20 random G^3 samples per generator.
Print("  --- E_+(2) HAP cross-check: per-generator on 20 G^3 samples ---\n");
_q7t_R2 := _q7t_r2.setup.R;;
_q7t_m2 := _q7t_r2.exponent;;
for _q7t_i in [1..Length(_q7t_r2.callables)] do
    _q7t_hom_i := _q7t_r2.setup.UCT.hombasis[_q7t_i];
    _q7t_vec_i := (_q7t_r2.setup.UCT.lift * _q7t_hom_i) mod _q7t_m2;
    _q7t_f_hap := StandardCocycle(_q7t_R2, _q7t_vec_i, 3, _q7t_m2);
    _q7t_f_wr  := _q7t_r2.callables[_q7t_i];
    _q7t_dis   := 0;
    for _q7t_k in [1..20] do
        _q7t_g1 := Random(_q7t_r2.G);
        _q7t_g2 := Random(_q7t_r2.G);
        _q7t_g3 := Random(_q7t_r2.G);
        if _q7t_f_wr(_q7t_g1, _q7t_g2, _q7t_g3) <>
           _q7t_f_hap(_q7t_g1, _q7t_g2, _q7t_g3) then
            _q7t_dis := _q7t_dis + 1;
        fi;
    od;
    Print("    gen ", _q7t_i, ": disagree = ", _q7t_dis, " / 20\n");
    _q7t_assert(Concatenation("E_+(2) gen ", String(_q7t_i),
                              " wrapper agrees with HAP on 20 samples"),
                _q7t_dis = 0);
od;


# ---- Test 3: input validation ----------------------------------------
#
# Verify the wrapper errors loudly on non-records and on records
# without a usable group identifier.

Print("\n=== Test 3: input validation ===\n");

_q7t_save_bok := BreakOnError;;
BreakOnError := false;;

# Non-record input.
_q7t_caught1 := CALL_WITH_CATCH(StandardCocycleQuillen, [42]);;
_q7t_assert("non-record input rejected",
            IsList(_q7t_caught1) and _q7t_caught1[1] = false);

# Record with no group_id and no m.
_q7t_caught2 := CALL_WITH_CATCH(StandardCocycleQuillen,
                                [rec(foo := "bar")]);;
_q7t_assert("record without .group_id or .m rejected",
            IsList(_q7t_caught2) and _q7t_caught2[1] = false);

# Record with malformed group_id.
_q7t_caught3 := CALL_WITH_CATCH(StandardCocycleQuillen,
                                [rec(group_id := "nope")]);;
_q7t_assert("record with bad .group_id rejected",
            IsList(_q7t_caught3) and _q7t_caught3[1] = false);

BreakOnError := _q7t_save_bok;;


# ---- Test 4 (optional, gated): performance at m=7 ---------------------
#
# Q-7 acceptance asked for 1000 random evals/sec/generator on E_+(7).
# E_+(7) is SmallGroup of order 2^15 = 32768; we don't even have a
# canonical construction wired up yet. Gate this behind an explicit
# opt-in.

if Q7_INCLUDE_PERF then
    Print("\n=== Test 4: performance gate at m=7 (E_+(7)) ===\n");
    Print("  (NOT IMPLEMENTED: E_+(7) construction not wired up in Q-2 yet)\n");
    _q7t_assert("perf gate placeholder (intentionally fails until E_+(7) wired up)",
                false);
else
    Print("\n=== Test 4: performance gate at m=7 (SKIPPED — set Q7_INCLUDE_PERF := true to enable) ===\n");
fi;


# ---- Summary ----------------------------------------------------------

Print("\n=== summary ===\n");
Print("  passed: ", _q7t_pass, "    failed: ", _q7t_fail, "\n");
if _q7t_fail > 0 then
    Print("  STATUS: FAIL\n");
    for _q7t_lab in _q7t_failures do
        Print("    - ", _q7t_lab, "\n");
    od;
    QUIT_GAP(1);
else
    Print("  STATUS: PASS\n");
    QUIT_GAP(0);
fi;
