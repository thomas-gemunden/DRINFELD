# test_cocyclebasis_quillen_bridge.g — Q-int A4 / issue #285 acceptance.
#
# Acceptance criteria (per #285):
#   1. Function: QuillenPolynomialOf(setup, i) returns a symbolic
#      polynomial.
#   2. Correctness: random-sample evaluation match between the polynomial
#      and StandardCocycleOf(setup, e_i) — 0 mismatches across 100+
#      G^3 triples.
#   3. m=2: works for all 10 generators.
#   4. m=3: works for all 35 generators (gated on QA4_INCLUDE_M3).
#   5. Diagnostic: pretty-print each generator's polynomial form.
#
# Run from extraspecial_orbifolds/scripts/:
#   gap -q -b ./tests/test_cocyclebasis_quillen_bridge.g
# or from anywhere:
#   gap -q -b /abs/path/to/test_cocyclebasis_quillen_bridge.g
#
# Default: m=2 only. Set QA4_INCLUDE_M3 := true to enable m=3 (slow:
# ~10-20 minutes for the heavy SolutionMat on |G|^2 = 16384 rows).

BreakOnError := false;;
LoadPackage("hap");

# Locate cocyclebasis_quillen_bridge.g via INPUT_FILENAME, falling back
# to CWD-relative paths (same shim pattern as other tests).
_qa4t_loaded := false;;
_qa4t_self := INPUT_FILENAME();;
if _qa4t_self <> fail and _qa4t_self <> "stream" then
    _qa4t_dir := _qa4t_self{[1..Length(_qa4t_self) -
                          Length("/test_cocyclebasis_quillen_bridge.g")]};;
    _qa4t_cand := Concatenation(_qa4t_dir, "/../cocyclebasis_quillen_bridge.g");;
    if IsExistingFile(_qa4t_cand) then
        Read(_qa4t_cand);
        _qa4t_loaded := true;
    fi;
fi;
if not _qa4t_loaded then
    for _qa4t_p in [ "../cocyclebasis_quillen_bridge.g",
                     "cocyclebasis_quillen_bridge.g",
                     "extraspecial_orbifolds/scripts/cocyclebasis_quillen_bridge.g" ] do
        if not _qa4t_loaded and IsExistingFile(_qa4t_p) then
            Read(_qa4t_p);
            _qa4t_loaded := true;
        fi;
    od;
fi;
if not _qa4t_loaded then
    Error("test_cocyclebasis_quillen_bridge.g: cannot locate ",
          "cocyclebasis_quillen_bridge.g; run from scripts/ or tests/");
fi;

# Default flags.
if not IsBoundGlobal("QA4_INCLUDE_M3") then
    BindGlobal("QA4_INCLUDE_M3", false);
fi;
if not IsBoundGlobal("QA4_SAMPLE_SIZE") then
    BindGlobal("QA4_SAMPLE_SIZE", 100);
fi;

_qa4_pass := 0;;
_qa4_fail := 0;;
_qa4_failures := [];;

_qa4_assert := function(label, cond)
    if cond then
        Print("  OK   ", label, "\n");
        _qa4_pass := _qa4_pass + 1;
    else
        Print("  FAIL ", label, "\n");
        _qa4_fail := _qa4_fail + 1;
        Add(_qa4_failures, label);
    fi;
end;;

_qa4_run_for_m := function(m, sample_n)
    local G, setup, i, r, n_mismatch, gen_label;
    Print("\n=== m = ", m, " (E_+(", m, ")) ===\n");
    G := EPlusGroup(m);
    Print("  |G| = ", Order(G), "\n");
    setup := SetupCohomology3(G);
    Print("  torsion        = ", setup.torsion, "\n");
    Print("  exponent       = ", setup.exponent, "\n");
    Print("  num_generators = ", setup.num_generators, "\n");

    for i in [1..setup.num_generators] do
        gen_label := Concatenation("m=", String(m), " e_", String(i),
                                   " (order ", String(setup.torsion[i]), ")");
        r := QuillenPolynomialOf(setup, i);
        Print("    ", gen_label, ": ", r.poly_str, "\n");
        # Reuse the bridge result to avoid re-solving the linear system.
        n_mismatch := VerifyQuillenBridgeOf(r, setup, i, sample_n);
        _qa4_assert(Concatenation(gen_label, " mismatch = 0 on ",
                                  String(sample_n), " triples"),
                    n_mismatch = 0);
    od;
end;;

# --- m = 2 (always run) ---
_qa4_run_for_m(2, QA4_SAMPLE_SIZE);

# --- m = 3 (gated) ---
if QA4_INCLUDE_M3 then
    _qa4_run_for_m(3, QA4_SAMPLE_SIZE);
else
    Print("\n=== m = 3 SKIPPED (set QA4_INCLUDE_M3 := true to enable) ===\n");
fi;

# --- Summary ---
Print("\n=== summary ===\n");
Print("  passed: ", _qa4_pass, "    failed: ", _qa4_fail, "\n");
if _qa4_fail > 0 then
    Print("  STATUS: FAIL\n");
    for _qa4_lab in _qa4_failures do Print("    - ", _qa4_lab, "\n"); od;
    QUIT_GAP(1);
else
    Print("  STATUS: PASS\n");
    QUIT_GAP(0);
fi;
