# test_quillen_vs_hap.g — Q-8 / issue #28 regression suite.
#
# Quillen-vs-HAP end-to-end cross-check at m = 2 (E_+(2)) and m = 3
# (E_+(3), gated).
#
# Acceptance criteria from issue #28:
#   * Torsion vector at m = 2 matches the HAP anchor [2^9, 8].
#   * Torsion vector at m = 3 matches [2^34, 4] (gated by Q8_INCLUDE_M3).
#   * For each H^3 generator, >= 95% of 100 random G^3 evaluations agree
#     between the Quillen wrapper and the directly-built HAP standard
#     cocycle (same generator).
#   * Document any sign / section convention differences.
#
# Status of the cross-check
# -------------------------
# `StandardCocycleQuillen` in `quillen_h3_callable.g` (Q-7) ships ONLY
# Path A — a thin wrapper around HAP's `StandardCocycle`. Concretely:
#
#     setup.StandardCocycle(hom_vec) :=
#         StandardCocycle(R, UCT.lift * hom_vec, 3, UCT.exponent).
#
# So the wrapper callables ARE HAP standard cocycles (just constructed
# via `UCT.hombasis[i]`). The cocycle-level cross-check is therefore an
# identity by construction and the agreement is 100%, not >= 95%. The
# >= 95% threshold becomes a meaningful gate only after Path B
# (Quillen-from-class-algebra cocycles) lands.
#
# The substantive cross-check at this stage is the TORSION-LEVEL one:
#
#   HAP route   : IntegralCohomologyTorsion(SmallGroup(...), 4)
#                 -> elementary divisors of H^4(G; Z)_tors
#                 -> equals H^3(G; U(1)) torsion via 0 -> Z -> R -> U(1) -> 0
#   Quillen route : setup.torsion from UnitCircleCohomology(G, 3),
#                   where setup.UCT = UniversalCoefficientsTheorem(K, 3)
#                   and K = TensorWithIntegers(ResolutionFiniteGroup(G, 4))
#
# Both should produce [2^9, 8] for m = 2 and [2^34, 4] for m = 3. They
# use distinct code paths (HAP's `GroupCohomology` versus Gruen's
# `UniversalCoefficientsTheorem`), so equality of multisets is a
# non-trivial cross-check even though both ultimately rest on HAP
# resolutions.
#
# Convention notes (sign / section)
# ---------------------------------
# Both routes anchor on HAP `ResolutionFiniteGroup`. The Path-A wrapper
# uses `UCT.lift * hom_vec` to lift a hombasis row into a cocycle in
# Z/exp before calling HAP. There are no sign or section choices that
# diverge between wrapper and HAP at this stage; Path B (when it lands)
# will introduce a section choice for the polynomial-to-cocycle
# evaluation map, at which point convention differences become possible.
#
# Run from this directory (`extraspecial_orbifolds/scripts/tests/`):
#     /opt/homebrew/bin/gap -q -b ./test_quillen_vs_hap.g
# or from anywhere:
#     /opt/homebrew/bin/gap -q -b /abs/path/to/test_quillen_vs_hap.g
#
# Set `Q8_INCLUDE_M3 := true` BEFORE Read()-ing to enable the m = 3
# block (default true; takes a few minutes — HAP's GroupCohomology on
# SmallGroup(128, 2326) at degree 4 is the slow step).
# Set `Q8_SAMPLE_SIZE` to override the per-generator sample count
# (default 100, per the issue body).

# ---- Locate the modules we depend on ---------------------------------
#
# We need:
#   * quillen_h3_callable.g  (StandardCocycleQuillen)
#   * quillen_presentation.g (QuillenPresentation)
#   * integral_cohomology.g  (IntegralCohomologyTorsion)
#
# Shim pattern matches `test_quillen_h3_callable.g`.

_q8t_loaded_callable := false;;
_q8t_loaded_pres     := false;;
_q8t_loaded_intcoh   := false;;
_q8t_self_path       := INPUT_FILENAME();;
if _q8t_self_path <> fail and _q8t_self_path <> "stream" then
    _q8t_self_dir := _q8t_self_path{[1..Length(_q8t_self_path)
                                     - Length("/test_quillen_vs_hap.g")]};;
    _q8t_cand_callable := Concatenation(_q8t_self_dir,
                                        "/../quillen_h3_callable.g");;
    if IsExistingFile(_q8t_cand_callable) then
        Read(_q8t_cand_callable);
        _q8t_loaded_callable := true;
    fi;
    _q8t_cand_pres := Concatenation(_q8t_self_dir,
                                    "/../quillen_presentation.g");;
    if IsExistingFile(_q8t_cand_pres) then
        Read(_q8t_cand_pres);
        _q8t_loaded_pres := true;
    fi;
    _q8t_cand_int := Concatenation(_q8t_self_dir,
                                   "/../integral_cohomology.g");;
    if IsExistingFile(_q8t_cand_int) then
        Read(_q8t_cand_int);
        _q8t_loaded_intcoh := true;
    fi;
fi;
if not _q8t_loaded_callable then
    for _q8t_p in [ "../quillen_h3_callable.g",
                    "quillen_h3_callable.g",
                    "extraspecial_orbifolds/scripts/quillen_h3_callable.g" ] do
        if not _q8t_loaded_callable and IsExistingFile(_q8t_p) then
            Read(_q8t_p);
            _q8t_loaded_callable := true;
        fi;
    od;
fi;
if not _q8t_loaded_pres then
    for _q8t_p in [ "../quillen_presentation.g",
                    "quillen_presentation.g",
                    "extraspecial_orbifolds/scripts/quillen_presentation.g" ] do
        if not _q8t_loaded_pres and IsExistingFile(_q8t_p) then
            Read(_q8t_p);
            _q8t_loaded_pres := true;
        fi;
    od;
fi;
if not _q8t_loaded_intcoh then
    for _q8t_p in [ "../integral_cohomology.g",
                    "integral_cohomology.g",
                    "extraspecial_orbifolds/scripts/integral_cohomology.g" ] do
        if not _q8t_loaded_intcoh and IsExistingFile(_q8t_p) then
            Read(_q8t_p);
            _q8t_loaded_intcoh := true;
        fi;
    od;
fi;
if not _q8t_loaded_callable then
    Error("test_quillen_vs_hap.g: cannot locate quillen_h3_callable.g");
fi;
if not _q8t_loaded_pres then
    Error("test_quillen_vs_hap.g: cannot locate quillen_presentation.g");
fi;
if not _q8t_loaded_intcoh then
    Error("test_quillen_vs_hap.g: cannot locate integral_cohomology.g");
fi;

# Default: do run the m = 3 block (the brief says "default true, takes
# some minutes but should fit"). The big cost is HAP's
# GroupCohomology(SmallGroup(128, 2326), 4).
if not IsBoundGlobal("Q8_INCLUDE_M3") then
    BindGlobal("Q8_INCLUDE_M3", true);
fi;
if not IsBoundGlobal("Q8_SAMPLE_SIZE") then
    BindGlobal("Q8_SAMPLE_SIZE", 100);
fi;
# >= 95% agreement threshold from the issue body. Path A trivially
# achieves 100%; the threshold becomes a non-trivial gate only when
# Path B lands.
if not IsBoundGlobal("Q8_AGREEMENT_PCT_MIN") then
    BindGlobal("Q8_AGREEMENT_PCT_MIN", 95);
fi;


# ---- Test harness ----------------------------------------------------

_q8t_pass := 0;;
_q8t_fail := 0;;
_q8t_failures := [];;

_q8t_assert := function(label, cond)
    if cond then
        Print("  OK   ", label, "\n");
        _q8t_pass := _q8t_pass + 1;
    else
        Print("  FAIL ", label, "\n");
        _q8t_fail := _q8t_fail + 1;
        Add(_q8t_failures, label);
    fi;
end;;

# Sorted copy and multiset equality for comparing torsion vectors
# (HAP and UCT may return them in different orders).
_q8t_sortedcopy := function(v)
    local w;
    w := ShallowCopy(v);
    Sort(w);
    return w;
end;;
_q8t_samemultiset := function(a, b)
    return _q8t_sortedcopy(a) = _q8t_sortedcopy(b);
end;;

# Per-generator sample agreement: returns the agreement count between
# the wrapper callable `f_wrap` and the directly-built HAP standard
# cocycle `f_hap` on `n_samples` random G^3 tuples.
_q8t_sample_agreement := function(f_wrap, f_hap, G, n_samples)
    local agree, k, g1, g2, g3, vw, vh;
    agree := 0;
    for k in [1..n_samples] do
        g1 := Random(G);
        g2 := Random(G);
        g3 := Random(G);
        vw := f_wrap(g1, g2, g3);
        vh := f_hap(g1, g2, g3);
        if vw = vh then
            agree := agree + 1;
        fi;
    od;
    return agree;
end;;

# Run the full cross-check for one value of m. Returns nothing — uses
# _q8t_assert for side-effecting test reporting.
_q8t_run_for_m := function(m, expected_torsion, expected_count, sample_n)
    local calg, r, G, hap_torsion, qu_torsion, R, mod_exp,
          n_gens, i, hom_i, vec_i, f_hap, f_wrap, agree, pct;

    Print("\n=== Tests for m = ", m, " (E_+(", m,
          ") = SmallGroup", QuillenPresentationGroupID(m), ") ===\n");

    # --- Step 1: build the Quillen-side setup ---------------------------
    Print("  Building QuillenPresentation(", m, ")...\n");
    calg := QuillenPresentation(m);

    Print("  Building StandardCocycleQuillen wrapper (this calls HAP ",
          "ResolutionFiniteGroup + UCT)...\n");
    r := StandardCocycleQuillen(calg);
    G := r.G;

    Print("  Wrapper torsion         = ", r.torsion, "\n");
    Print("  Wrapper exponent        = ", r.exponent, "\n");
    Print("  Wrapper #callables     = ", Length(r.callables), "\n");

    # --- Step 2: HAP-route torsion (via IntegralCohomologyTorsion at n=4) -
    #
    # H^3(G; U(1)) = H^4(G; Z)_tors under the SES iso. Compute the HAP
    # side independently (this uses HAP's GroupCohomology, NOT the
    # UniversalCoefficientsTheorem path the wrapper uses).
    Print("  Computing IntegralCohomologyTorsion(G, 4) [HAP route]...\n");
    hap_torsion := IntegralCohomologyTorsion(G, 4);
    Print("  HAP torsion (sorted)   = ", _q8t_sortedcopy(hap_torsion), "\n");

    # --- Step 3: Quillen-route torsion (from the wrapper) ---------------
    qu_torsion := r.torsion;
    Print("  Quillen torsion (sorted) = ", _q8t_sortedcopy(qu_torsion), "\n");

    # --- Step 4: torsion assertions -------------------------------------
    _q8t_assert(Concatenation("m=", String(m),
                              " HAP torsion has ",
                              String(expected_count),
                              " elementary divisors"),
                Length(hap_torsion) = expected_count);
    _q8t_assert(Concatenation("m=", String(m),
                              " HAP torsion multiset matches expected ",
                              String(expected_torsion)),
                _q8t_samemultiset(hap_torsion, expected_torsion));
    _q8t_assert(Concatenation("m=", String(m),
                              " Quillen torsion has ",
                              String(expected_count),
                              " elementary divisors"),
                Length(qu_torsion) = expected_count);
    _q8t_assert(Concatenation("m=", String(m),
                              " Quillen torsion multiset matches expected ",
                              String(expected_torsion)),
                _q8t_samemultiset(qu_torsion, expected_torsion));
    _q8t_assert(Concatenation("m=", String(m),
                              " HAP and Quillen torsion multisets agree"),
                _q8t_samemultiset(hap_torsion, qu_torsion));

    # --- Step 5: per-generator sample agreement vs HAP ------------------
    #
    # For each H^3 generator (one per UCT.hombasis row) build the HAP
    # standard cocycle directly with UCT.lift * hom_vec and compare it
    # to the wrapper callable on `sample_n` random G^3 tuples.
    #
    # Path A: wrapper IS HAP, so this is 100% by construction. The >=
    # 95% threshold becomes meaningful only when Path B lands.

    R := r.setup.R;
    mod_exp := r.exponent;
    n_gens := Length(r.callables);

    Print("  --- Per-generator sample agreement vs HAP (",
          sample_n, " random G^3 tuples each) ---\n");
    for i in [1..n_gens] do
        hom_i  := r.setup.UCT.hombasis[i];
        vec_i  := (r.setup.UCT.lift * hom_i) mod mod_exp;
        f_hap  := StandardCocycle(R, vec_i, 3, mod_exp);
        f_wrap := r.callables[i];

        agree := _q8t_sample_agreement(f_wrap, f_hap, G, sample_n);
        pct   := QuoInt(100 * agree, sample_n);
        Print("    gen ", i, ": agreement = ", agree, " / ", sample_n,
              "  (", pct, "%)\n");
        _q8t_assert(Concatenation("m=", String(m),
                                  " gen ", String(i),
                                  " agreement >= ",
                                  String(Q8_AGREEMENT_PCT_MIN),
                                  "% (Path A: 100% by construction)"),
                    pct >= Q8_AGREEMENT_PCT_MIN);
    od;
end;;


# ---- Test A + B: m = 2 (E_+(2)) --------------------------------------
#
# Acceptance: torsion = [2^9, 8] (i.e. 9 copies of 2 and one 8 = 10
# elementary divisors). 100 random G^3 evaluations per generator should
# all agree with HAP (Path A is a HAP wrapper).

_q8t_m2_expected := Concatenation(ListWithIdenticalEntries(9, 2), [8]);;
_q8t_run_for_m(2, _q8t_m2_expected, 10, Q8_SAMPLE_SIZE);


# ---- Test C + D: m = 3 (E_+(3)) — gated ------------------------------
#
# Acceptance: torsion = [2^34, 4] (34 copies of 2 and one 4 = 35
# elementary divisors). 100 random G^3 evaluations per generator should
# all agree with HAP.
#
# Slow: HAP's GroupCohomology(SmallGroup(128, 2326), 4) and
# UniversalCoefficientsTheorem(K, 3) for E_+(3) both take a few
# minutes. Gated on Q8_INCLUDE_M3 (default true).

if Q8_INCLUDE_M3 then
    _q8t_m3_expected := Concatenation(ListWithIdenticalEntries(34, 2), [4]);;
    _q8t_run_for_m(3, _q8t_m3_expected, 35, Q8_SAMPLE_SIZE);
else
    Print("\n=== Tests for m = 3 SKIPPED (set Q8_INCLUDE_M3 := true to enable) ===\n");
fi;


# ---- Summary ---------------------------------------------------------

Print("\n=== summary ===\n");
Print("  passed: ", _q8t_pass, "    failed: ", _q8t_fail, "\n");
if _q8t_fail > 0 then
    Print("  STATUS: FAIL\n");
    for _q8t_lab in _q8t_failures do
        Print("    - ", _q8t_lab, "\n");
    od;
    QUIT_GAP(1);
else
    Print("  STATUS: PASS\n");
    QUIT_GAP(0);
fi;
