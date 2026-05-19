# test_abelian_e_form_check.g  --  regression test for K-4a-T3 (#195).
#
# Tests:
#   1.  Trivial alpha (constant zero) on Z_2 x Z_2 -> reported trivial.
#   2.  A known non-trivial H^3 generator (built via SetupCohomology3 +
#       StandardCocycleOf) on Z_2 x Z_2 -> reported non-trivial.
#   3.  Trivial + non-trivial alphas on Z_2^3 (the m=2 maximal elementary
#       abelian of E_+(2)).
#   4.  Coboundary-witness round-trip: when reported trivial, the
#       returned witness beta satisfies delta_2 beta = alpha mod m.
#   4b. Scaling check at Z_2^4 (the m=3 maximal elementary abelian).
#   5.  The ClassifyOnAbelianE stub returns the deferral record.
#
# Run from extraspecial_orbifolds/scripts/tests/:
#   gap -q -b -c 'Read("test_abelian_e_form_check.g"); QUIT;'

BreakOnError := false;;

# ---- Locate the parent module -----------------------------------------

_aeft_loaded := false;;
_aeft_self := INPUT_FILENAME();;
if _aeft_self <> fail and _aeft_self <> "stream" then
    _aeft_dir := _aeft_self{[1..Length(_aeft_self)
        - Length("/test_abelian_e_form_check.g")]};;
    _aeft_cand := Concatenation(_aeft_dir, "/../abelian_e_form_check.g");;
    if IsExistingFile(_aeft_cand) then
        Read(_aeft_cand);
        _aeft_loaded := true;
    fi;
fi;
if not _aeft_loaded then
    for _aeft_p in [ "../abelian_e_form_check.g",
                     "abelian_e_form_check.g",
                     "extraspecial_orbifolds/scripts/abelian_e_form_check.g" ] do
        if not _aeft_loaded and IsExistingFile(_aeft_p) then
            Read(_aeft_p);
            _aeft_loaded := true;
        fi;
    od;
fi;
if not _aeft_loaded then
    Error("cannot locate abelian_e_form_check.g");
fi;

# Also load SetupCohomology3 (in transgression_kernel.g) for the
# non-trivial-cocycle witness.
_aeft_loaded_tk := IsBoundGlobal("SetupCohomology3");;
if not _aeft_loaded_tk then
    if _aeft_self <> fail and _aeft_self <> "stream" then
        _aeft_tk_cand := Concatenation(_aeft_dir, "/../transgression_kernel.g");;
        if IsExistingFile(_aeft_tk_cand) then
            Read(_aeft_tk_cand);
            _aeft_loaded_tk := true;
        fi;
    fi;
    if not _aeft_loaded_tk then
        for _aeft_p in [ "../transgression_kernel.g",
                         "transgression_kernel.g",
                         "extraspecial_orbifolds/scripts/transgression_kernel.g" ] do
            if not _aeft_loaded_tk and IsExistingFile(_aeft_p) then
                Read(_aeft_p);
                _aeft_loaded_tk := true;
            fi;
        od;
    fi;
fi;
if not _aeft_loaded_tk then
    Error("cannot locate transgression_kernel.g (needed for SetupCohomology3)");
fi;

# ---- Harness ----------------------------------------------------------

testFailures := [];;

If_loc := function(c, a, b) if c then return a; else return b; fi; end;;

AssertOrLog := function(label, cond)
    Print("  ", label, ": ", If_loc(cond, "PASS", "FAIL"), "\n");
    if not cond then Add(testFailures, label); fi;
end;;

Print("\n=== test_abelian_e_form_check.g (K-4a-T3 / #195) ===\n");

# ----------------------------------------------------------------------
# Test 1: Trivial alpha on Z_2 x Z_2.
# ----------------------------------------------------------------------

Print("\n--- Test 1: trivial (constant zero) alpha on Z_2 x Z_2 ---\n");

E2x2 := ElementaryAbelianGroup(IsPcGroup, 4);;
m_2 := 2;;
alpha_trivial := function(a, b, c) return 0; end;;

t1 := ClassifyOn3CocycleE(alpha_trivial, E2x2, m_2);;
AssertOrLog("trivial alpha: is_cocycle = true",       t1.is_cocycle);
AssertOrLog("trivial alpha: cocycle_violations = 0",  t1.cocycle_violations = 0);
AssertOrLog("trivial alpha: trivial = true",          t1.trivial = true);
AssertOrLog("trivial alpha: witness is a length-|E|^2 list",
            IsList(t1.coboundary_witness)
              and Length(t1.coboundary_witness) = Order(E2x2)^2);

# ----------------------------------------------------------------------
# Test 2: Non-trivial alpha on Z_2 x Z_2 via SetupCohomology3.
# ----------------------------------------------------------------------

Print("\n--- Test 2: non-trivial H^3 generator on Z_2 x Z_2 ---\n");

setup_2x2 := SetupCohomology3(E2x2);;
Print("  setup_2x2.exponent = ", setup_2x2.exponent, "\n");
Print("  setup_2x2.torsion  = ", setup_2x2.torsion, "\n");
Print("  number of H^3 generators = ", setup_2x2.num_generators, "\n");

# Pick the first H^3 generator as a witness cocycle.
gen_vec_2x2 := List([1..setup_2x2.num_generators], i -> 0);;
gen_vec_2x2[1] := 1;;
omega_2x2 := StandardCocycleOf(setup_2x2, gen_vec_2x2);;

m_2x2 := setup_2x2.exponent;;
Print("  using modulus m = ", m_2x2, " for ClassifyOn3CocycleE\n");

t2 := ClassifyOn3CocycleE(omega_2x2, E2x2, m_2x2);;
AssertOrLog("non-trivial alpha: is_cocycle = true",      t2.is_cocycle);
AssertOrLog("non-trivial alpha: cocycle_violations = 0", t2.cocycle_violations = 0);
AssertOrLog("non-trivial alpha: trivial = false",        t2.trivial = false);
AssertOrLog("non-trivial alpha: witness = fail",         t2.coboundary_witness = fail);

# ----------------------------------------------------------------------
# Test 3: Z_2^3 (the m=2 maximal elementary abelian).
# ----------------------------------------------------------------------

Print("\n--- Test 3: alpha checks on E = Z_2^3 (max abelian of E_+(2)) ---\n");

E2x2x2 := ElementaryAbelianGroup(IsPcGroup, 8);;
Print("  |E| = ", Order(E2x2x2), "\n");

# Trivial alpha first.
t3a := ClassifyOn3CocycleE(alpha_trivial, E2x2x2, 2);;
AssertOrLog("Z_2^3 trivial alpha: is_cocycle",   t3a.is_cocycle);
AssertOrLog("Z_2^3 trivial alpha: trivial = true", t3a.trivial = true);

# Non-trivial alpha (first generator).
setup_222 := SetupCohomology3(E2x2x2);;
Print("  setup_222.exponent = ", setup_222.exponent, "\n");
Print("  setup_222.torsion  = ", setup_222.torsion, "\n");
Print("  number of H^3 generators = ", setup_222.num_generators, "\n");

gen_vec_222 := List([1..setup_222.num_generators], i -> 0);;
gen_vec_222[1] := 1;;
omega_222 := StandardCocycleOf(setup_222, gen_vec_222);;
m_222 := setup_222.exponent;;

t3b := ClassifyOn3CocycleE(omega_222, E2x2x2, m_222);;
AssertOrLog("Z_2^3 non-trivial generator 1: is_cocycle",       t3b.is_cocycle);
AssertOrLog("Z_2^3 non-trivial generator 1: trivial = false",  t3b.trivial = false);

# ----------------------------------------------------------------------
# Test 4: round-trip the witness for the trivial cases.
# For a coboundary alpha = delta_2 beta_orig, we check that the
# returned witness beta also satisfies delta_2 beta = alpha mod m.
# Build a non-trivial 2-cochain beta_orig on Z_2 x Z_2, set
# alpha := delta_2 beta_orig, and verify.
# ----------------------------------------------------------------------

Print("\n--- Test 4: witness round-trip for a synthesised coboundary ---\n");

elts_2x2 := AsList(E2x2);;
n_2x2 := Length(elts_2x2);;
pos_2x2 := function(g) return Position(elts_2x2, g); end;;

# Build a non-zero 2-cochain beta_orig on Z_2 x Z_2 (mod 2).
# beta_orig(g, h) := pos_2x2(g) * pos_2x2(h) mod 2.
beta_orig_vec := List([1..n_2x2*n_2x2],
    k -> ((QuoInt(k - 1, n_2x2) + 1) * ((k - 1) mod n_2x2 + 1)) mod 2);;

beta_orig := CallableFromVector(E2x2, 2, beta_orig_vec);;

# Tabulate delta_2(beta_orig) on E^3 as an alpha.
alpha_cob := function(g, h, k)
    return (beta_orig(h, k) - beta_orig(g*h, k)
            + beta_orig(g, h*k) - beta_orig(g, h)) mod 2;
end;;

t4 := ClassifyOn3CocycleE(alpha_cob, E2x2, 2);;
AssertOrLog("synth coboundary: is_cocycle = true",          t4.is_cocycle);
AssertOrLog("synth coboundary: cocycle_violations = 0",     t4.cocycle_violations = 0);
AssertOrLog("synth coboundary: trivial = true",             t4.trivial = true);

# Round-trip: rebuild alpha from the returned witness and compare.
if t4.trivial then
    beta_witness := CallableFromVector(E2x2, 2, t4.coboundary_witness);
    n_mismatch := 0;
    for g_loc in elts_2x2 do
        for h_loc in elts_2x2 do
            for k_loc in elts_2x2 do
                v := (beta_witness(h_loc, k_loc)
                      - beta_witness(g_loc*h_loc, k_loc)
                      + beta_witness(g_loc, h_loc*k_loc)
                      - beta_witness(g_loc, h_loc));
                if (v - alpha_cob(g_loc, h_loc, k_loc)) mod 2 <> 0 then
                    n_mismatch := n_mismatch + 1;
                fi;
            od;
        od;
    od;
    AssertOrLog("synth coboundary: delta_2(witness) = alpha mod 2 on all of E^3",
                n_mismatch = 0);
else
    Add(testFailures, "synth coboundary: trivial was unexpectedly false; skipping round-trip");
fi;

# ----------------------------------------------------------------------
# Test 4b: scaling check at E = Z_2^4 (m=3 maximal elementary abelian).
# Larger: |E| = 16, |E|^3 = 4096, |E|^4 = 65536 -- minutes-scale.
# Covers the m=3 case in acceptance criterion #3.
# ----------------------------------------------------------------------

Print("\n--- Test 4b: alpha checks on E = Z_2^4 (max abelian of E_+(3)) ---\n");

E2x2x2x2 := ElementaryAbelianGroup(IsPcGroup, 16);;
Print("  |E| = ", Order(E2x2x2x2), "\n");

# (a) Synthesised coboundary -- delta_2 of a non-zero 2-cochain.
elts_24 := AsList(E2x2x2x2);;
n_24 := Length(elts_24);;
beta_24_vec := List([1..n_24*n_24],
    k -> ((QuoInt(k - 1, n_24) + 1) * ((k - 1) mod n_24 + 1)) mod 2);;
beta_24 := CallableFromVector(E2x2x2x2, 2, beta_24_vec);;
alpha_24_cob := function(g, h, k)
    return (beta_24(h, k) - beta_24(g*h, k)
            + beta_24(g, h*k) - beta_24(g, h)) mod 2;
end;;

t4b1 := ClassifyOn3CocycleE(alpha_24_cob, E2x2x2x2, 2);;
AssertOrLog("Z_2^4 synth coboundary: is_cocycle",         t4b1.is_cocycle);
AssertOrLog("Z_2^4 synth coboundary: trivial = true",     t4b1.trivial = true);

# (b) Known H^3 generator via SetupCohomology3.
Print("  Building HAP resolution + UCT for Z_2^4 (may take a moment)...\n");
setup_24 := SetupCohomology3(E2x2x2x2);;
Print("    setup_24.exponent = ", setup_24.exponent, "\n");
Print("    setup_24.torsion  = ", setup_24.torsion, "\n");
Print("    number of H^3 generators = ", setup_24.num_generators, "\n");

gen_vec_24 := List([1..setup_24.num_generators], i -> 0);;
gen_vec_24[1] := 1;;
omega_24 := StandardCocycleOf(setup_24, gen_vec_24);;
m_24 := setup_24.exponent;;

t4b2 := ClassifyOn3CocycleE(omega_24, E2x2x2x2, m_24);;
AssertOrLog("Z_2^4 H^3 generator 1: is_cocycle",       t4b2.is_cocycle);
AssertOrLog("Z_2^4 H^3 generator 1: trivial = false",  t4b2.trivial = false);

# ----------------------------------------------------------------------
# Test 5: ClassifyOnAbelianE stub returns the deferral.
# ----------------------------------------------------------------------

Print("\n--- Test 5: ClassifyOnAbelianE stub returns deferral ---\n");

stub_data := rec( epsilon := function(a, h) return 0; end );;
t5 := ClassifyOnAbelianE(stub_data, E2x2);;
AssertOrLog("stub: trivial = fail",          t5.trivial = fail);
AssertOrLog("stub: status = \"deferred\"",   t5.status = "deferred");
AssertOrLog("stub: returns the input E",     t5.E = E2x2);

# ----------------------------------------------------------------------
# Summary.
# ----------------------------------------------------------------------

Print("\n=== Summary ===\n");
if IsEmpty(testFailures) then
    Print("test_abelian_e_form_check: ALL PASS\n");
else
    Print("test_abelian_e_form_check: FAIL (",
          Length(testFailures), " failures)\n");
    for f in testFailures do Print("  - ", f, "\n"); od;
fi;
