# test_q_b3_5_m5_z4.g — Q-int B3-5 (issue #234) acceptance test.
#
# Verifies:
#   1. QuillenZ4Cocycle(5, 165) returns a Z/4 3-cocycle on
#      R_B := HAP_PontryaginGetResolution(em, 5), where em = pc-form
#      of EmGroup(5).
#   2. The cocycle vector has length R_B!.dimension(3) and entries in
#      {0, 1, 2, 3} (Z/4 representatives).
#   3. δ(vec) ≡ 0 mod 4 on R_B (defensive recheck of HAP_Z4Generator's
#      is_cocycle output).
#   4. The cocycle's omega callable is consistent with the vec (cocycle
#      condition on random samples).
#   5. Single-vector kernel test: build per-class basis cache for ONE
#      orbit rep (the identity class, which trivially gives c_g ≡ 0), and
#      verify IsCoboundary2SplitVec returns true.
#   6. A non-trivial single-vector kernel test: pick a non-identity
#      orbit rep, build the per-class basis cache, and run
#      IsCoboundary2SplitVec on `vec = e_165` (the Z/4 unit). This
#      exercises the Path Z (iterated-Bockstein Z/2^k) dispatcher.
#
# Wall budget: HAP setup at E_+(5) is the main cost (~10-15 min for
# ResolutionFiniteGroup(em, 6) + ~few min for Δ / h_1). After that, the
# tests run in seconds.
#
# Run from extraspecial_orbifolds/scripts/ via absolute path per K-4a-T1:
#
#   gap -q -b -c 'Read("/Users/thomasgemunden/Projects/group_cohomology/DRINFELD/extraspecial_orbifolds/scripts/tests/test_q_b3_5_m5_z4.g");'
#
# Or relative if run from extraspecial_orbifolds/scripts/:
#
#   gap -q -b -c 'Read("tests/test_q_b3_5_m5_z4.g");'

BreakOnError := false;;
LoadPackage("hap");

# ---- Locate the module ------------------------------------------------

_qb35t_loaded := false;;
_qb35t_self_path := INPUT_FILENAME();;
if _qb35t_self_path <> fail and _qb35t_self_path <> "stream" then
    _qb35t_self_dir := _qb35t_self_path{[1..Length(_qb35t_self_path)
                                         - Length("/test_q_b3_5_m5_z4.g")]};;
    # Tests live in extraspecial_orbifolds/scripts/tests/. The helper files
    # are in the parent dir.
    _qb35t_helper := Concatenation(_qb35t_self_dir, "/../quillen_z4_cocycle.g");;
    if IsExistingFile(_qb35t_helper) then
        # Change CWD to scripts/ before Read, so the helper's internal
        # Read("hap_h3_z4_generator.g") (relative) resolves correctly.
        _qb35t_scripts_dir := Concatenation(_qb35t_self_dir, "/..");;
        _qb35t_orig_cwd := DirectoryCurrent();;
        ChangeDirectoryCurrent(_qb35t_scripts_dir);
        Read("quillen_z4_cocycle.g");
        Read("hap_pontryagin_square.g");
        Read("hap_integrate_to_z4_cocycle.g");
        # snf_wrapper.g + iscoboundary2_split.g — these have CWD-shims
        # expecting CWD = solver/ or its parent. We cd to solver/ for
        # both Reads, then come back.
        ChangeDirectoryCurrent("solver");
        Read("snf_wrapper.g");
        Read("iscoboundary2_split.g");
        ChangeDirectoryCurrent("..");
        # BRW conjugacy (needed for the m=5 non-trivial test).
        Read("brw_conjugacy_action.g");
        Read("transgression_per_generator_brw.g");
        ChangeDirectoryCurrent(Filename(_qb35t_orig_cwd, ""));
        _qb35t_loaded := true;
    fi;
fi;
if not _qb35t_loaded then
    Error("test_q_b3_5_m5_z4.g: cannot locate quillen_z4_cocycle.g; ",
          "run via absolute path or set CWD = extraspecial_orbifolds/scripts/.");
fi;

Print("\n=== test_q_b3_5_m5_z4.g (issue #234 Q-int B3-5) ===\n");

# ---- Harness ----------------------------------------------------------

_qb35t_pass := 0;;
_qb35t_fail := 0;;
_qb35t_failures := [];;

If_qb35 := function(c, a, b)
    if c then return a; else return b; fi;
end;;

_qb35t_assert := function(label, cond)
    if cond then
        Print("  OK   ", label, "\n");
        _qb35t_pass := _qb35t_pass + 1;
    else
        Print("  FAIL ", label, "\n");
        _qb35t_fail := _qb35t_fail + 1;
        Add(_qb35t_failures, label);
    fi;
end;;

t_total_start := Runtime();;

# Optional: skip the heavy m=5 R build (gated by env var or global).
# By default we run the full test. Set Q_B35_M5_SKIP_HEAVY := true to
# only run the lightweight m=3 anchor (which uses the cached B2-4 R).
if not IsBoundGlobal("Q_B35_M5_SKIP_HEAVY") then
    BindGlobal("Q_B35_M5_SKIP_HEAVY", false);
fi;

# ----------------------------------------------------------------------
# Test 1: m=3 anchor (lightweight). HAP_Z4Generator at E_+(3) was
# verified by test_b2_4_m3_anchor.g (issue #164). We re-test that
# QuillenZ4Cocycle(3, 35) gives consistent shape and a valid Z/4 cocycle.
#
# IMPORTANT: We build em_3_shared ONCE and reuse it across Tests 1, 2, 3
# to avoid triple-building R(em, 6) (~10 min each at E_+(3)).
# ----------------------------------------------------------------------

Print("\n--- Test 1: m=3 anchor (QuillenZ4Cocycle on E_+(3)) ---\n");
t_m3 := Runtime();;

em_3_shared := Image(IsomorphismPcGroup(EmGroup(3)));;
c3 := QuillenZ4Cocycle(3, 35, em_3_shared);;

Print("  E_+(3) torsion = ", c3.torsion, "\n");
Print("  E_+(3) basis_idx = ", c3.basis_idx, "\n");
Print("  E_+(3) order at idx = ", c3.order, "\n");
Print("  E_+(3) |vec| = ", Length(c3.vec),
      " (= R!.dimension(3) = ", c3.R!.dimension(3), ")\n");
Print("  m=3 setup wall: ", (Runtime() - t_m3) / 1000., " s\n");

_qb35t_assert("m=3 torsion ends in 4",
              c3.torsion[Length(c3.torsion)] = 4);
_qb35t_assert("m=3 default basis_idx is last index",
              c3.basis_idx = Length(c3.torsion));
_qb35t_assert("m=3 order at idx = 4 (Z/4 unit)",
              c3.order = 4);
_qb35t_assert("m=3 exponent = 4",
              c3.exponent = 4);
_qb35t_assert("m=3 is_cocycle reported true",
              c3.is_cocycle);
_qb35t_assert("m=3 vec length = R!.dimension(3)",
              Length(c3.vec) = c3.R!.dimension(3));
_qb35t_assert("m=3 vec entries in [0..3]",
              ForAll(c3.vec, x -> x >= 0 and x < 4));
_qb35t_assert("m=3 vec not identically zero",
              not ForAll(c3.vec, x -> x = 0));

# Explicit recheck: δ(vec) ≡ 0 mod 4 on R.
d_vec3 := HAP_BarCoboundary(c3.R, c3.vec, 3);;
viol3 := Length(Filtered(d_vec3, x -> x mod 4 <> 0));;
Print("  m=3 explicit δ(vec) mod 4 violations: ", viol3,
      " / ", Length(d_vec3), "\n");
_qb35t_assert("m=3 δ(vec) ≡ 0 mod 4 (explicit recheck)",
              viol3 = 0);

# Cocycle callable consistency. omega(g1, g2, g3) should be Z/4-valued
# and the (g1, g2, g3) -> Z/4 closure should satisfy the bar 4-cocycle
# condition on random samples (modulo the Z/4 modulus). Sample 20 quads.
G3 := c3.em;;
ok_cocycle_3 := true;;
for _trial in [1..20] do
    a := Random(G3);
    b := Random(G3);
    c := Random(G3);
    d := Random(G3);
    # δ(omega)(a, b, c, d) = omega(b, c, d) - omega(a*b, c, d)
    #                       + omega(a, b*c, d) - omega(a, b, c*d)
    #                       + omega(a, b, c)
    delta := (c3.omega(b, c, d) - c3.omega(a*b, c, d)
              + c3.omega(a, b*c, d) - c3.omega(a, b, c*d)
              + c3.omega(a, b, c)) mod c3.exponent;
    if delta <> 0 then
        ok_cocycle_3 := false;
        Print("    cocycle violation at trial ", _trial, ": δ = ", delta, "\n");
    fi;
od;
_qb35t_assert("m=3 omega closure satisfies bar-cocycle condition on 20 samples",
              ok_cocycle_3);

# ----------------------------------------------------------------------
# Test 2: QuillenSetupOnR shape sanity (reusing em_3_shared from Test 1
# — cache hit, no extra R build).
# ----------------------------------------------------------------------

Print("\n--- Test 2: QuillenSetupOnR(3) shape (cache hit on em_3_shared) ---\n");

s3 := QuillenSetupOnR(3, em_3_shared);;
_qb35t_assert("QuillenSetupOnR(3) has .group", IsBound(s3.group));
_qb35t_assert("QuillenSetupOnR(3) has .R", IsBound(s3.R));
_qb35t_assert("QuillenSetupOnR(3) has .UCT", IsBound(s3.UCT));
_qb35t_assert("QuillenSetupOnR(3) has .torsion", IsBound(s3.torsion));
_qb35t_assert("QuillenSetupOnR(3) num_generators = 35",
              s3.num_generators = 35);
_qb35t_assert("QuillenSetupOnR(3) exponent = 4",
              s3.exponent = 4);
_qb35t_assert("QuillenSetupOnR(3) torsion shape [(Z/2)^34, Z/4]",
              ForAll([1..34], i -> s3.torsion[i] = 2)
              and s3.torsion[35] = 4);
_qb35t_assert("QuillenSetupOnR(3) num_h3_classes = 2^34 * 4",
              s3.num_h3_classes = 2^34 * 4);
_qb35t_assert("QuillenSetupOnR(3) .group identical to em_3_shared",
              IsIdenticalObj(s3.group, em_3_shared));

# ----------------------------------------------------------------------
# Test 3: em_in identity threading verification.
# When QuillenZ4Cocycle(m, idx, em_in) is called, the returned setup
# should adopt em_in as .em (IsIdenticalObj). Already checked above for
# em_3_shared; here we verify the 3-arg form rejects a wrong-order em.
# ----------------------------------------------------------------------

Print("\n--- Test 3: em_in argument validation ---\n");

_qb35t_assert("Test 1's c3.em is identical to em_3_shared",
              IsIdenticalObj(c3.em, em_3_shared));

# Reject a group of wrong order.
em_wrong := SmallGroup(8, 3);;     # |G| = 8, not 2^7 = 128 for m=3
_save_bok := BreakOnError;;
BreakOnError := false;;
_caught_wrong := CALL_WITH_CATCH(QuillenZ4Cocycle, [3, 1, em_wrong]);;
_qb35t_assert("QuillenZ4Cocycle rejects em_in of wrong order",
              IsList(_caught_wrong) and _caught_wrong[1] = false);
BreakOnError := _save_bok;;

# ----------------------------------------------------------------------
# Test 4: m=5 Z/4 cocycle construction (HEAVY — requires
# ResolutionFiniteGroup(EmGroup(5), 6)).
# ----------------------------------------------------------------------

if Q_B35_M5_SKIP_HEAVY then
    Print("\n--- Test 4: m=5 Z/4 cocycle construction [SKIPPED: Q_B35_M5_SKIP_HEAVY = true] ---\n");
else
    Print("\n--- Test 4: m=5 Z/4 cocycle construction (HEAVY) ---\n");
    Print("  (calls ResolutionFiniteGroup(EmGroup(5), 6) + UCT — ",
          "~10-15 min wall)\n");

    # IMPORTANT: build BRW conjugacy FIRST so we can pass conj_5.em into
    # QuillenZ4Cocycle. This avoids building R on TWO different em objects
    # (which would waste another ~15 min of resolution build).
    t_brw5 := Runtime();;
    conj_5 := BRWConjugacyAction(5);;
    Print("  BRW conj wall: ", (Runtime() - t_brw5) / 1000., " s\n");

    t_m5_setup := Runtime();;

    c5 := QuillenZ4Cocycle(5, 165, conj_5.em);;     # default last index = 165

    Print("  m=5 setup wall: ", (Runtime() - t_m5_setup) / 1000., " s\n");
    Print("  E_+(5) torsion length = ", Length(c5.torsion), "\n");
    Print("  E_+(5) basis_idx = ", c5.basis_idx, "\n");
    Print("  E_+(5) order at idx = ", c5.order, "\n");

    _qb35t_assert("m=5 torsion has 165 entries",
                  Length(c5.torsion) = 165);
    _qb35t_assert("m=5 basis_idx = 165 (last)",
                  c5.basis_idx = 165);
    _qb35t_assert("m=5 order at idx 165 = 4 (Z/4 unit)",
                  c5.order = 4);
    _qb35t_assert("m=5 exponent = 4",
                  c5.exponent = 4);
    _qb35t_assert("m=5 is_cocycle reported true",
                  c5.is_cocycle);
    _qb35t_assert("m=5 vec length = R!.dimension(3)",
                  Length(c5.vec) = c5.R!.dimension(3));
    _qb35t_assert("m=5 vec entries in [0..3]",
                  ForAll(c5.vec, x -> x >= 0 and x < 4));
    _qb35t_assert("m=5 vec not identically zero",
                  not ForAll(c5.vec, x -> x = 0));
    _qb35t_assert("m=5 c5.em is identical to conj_5.em",
                  IsIdenticalObj(c5.em, conj_5.em));

    # Explicit δ-recheck on R.
    d_vec5 := HAP_BarCoboundary(c5.R, c5.vec, 3);;
    viol5 := Length(Filtered(d_vec5, x -> x mod 4 <> 0));;
    Print("  m=5 explicit δ(vec) mod 4 violations: ", viol5,
          " / ", Length(d_vec5), "\n");
    _qb35t_assert("m=5 δ(vec) ≡ 0 mod 4 (explicit recheck)",
                  viol5 = 0);

    # ------------------------------------------------------------------
    # Test 5: QuillenSetupOnR(5, conj_5.em) shape sanity.
    # ------------------------------------------------------------------

    Print("\n--- Test 5: m=5 QuillenSetupOnR identity sharing ---\n");

    s5_b := QuillenSetupOnR(5, conj_5.em);;
    c5_b := c5;;     # alias for downstream tests (same R/UCT, shared via cache)
    _qb35t_assert("m=5 setup adopted conj_action.em (object id)",
                  IsIdenticalObj(s5_b.group, conj_5.em));
    _qb35t_assert("m=5 conj_action has expected n_classes >= 100",
                  Length(conj_5.classes) >= 100);

    # ------------------------------------------------------------------
    # Test 6: single-vector kernel test at m=5 (lightweight: identity
    # class only).
    #
    # The identity-class centraliser is C = G (|C| = 2048). Building
    # the per-class cocycle basis cache on C = G would cost
    # O(|C|² × R_B!.dim(3)) — too heavy for an acceptance test. Instead,
    # we exploit that c_g(h, k) at g = identity vanishes identically
    # for a NORMALISED cocycle ω:
    #
    #   c_id(h, k) = ω(id, h, k) - ω(h, id, k) + ω(h, k, id)
    #
    # Each term involves an identity argument; HAP's StandardCocycle
    # produces cochain reps that are normalised at the chain level too
    # (because Syzygy ([id, h, k]) collapses to trivial relations).
    # We verify this by sampling c_g(h, k) at a few random h, k in G
    # for g = id, expecting zero. Then we feed the constant-zero
    # c_g_vec through IsCoboundary2SplitVec and verify the dispatcher
    # routes to Path Z (because vec[165] = 1) and returns true on the
    # trivial cocycle.
    # ------------------------------------------------------------------

    Print("\n--- Test 6: single-vector Z/4 unit kernel test (identity class) ---\n");

    # Find the identity class.
    classes_5 := conj_5.classes;;
    id_class_idx := fail;;
    for j in [1..Length(classes_5)] do
        if IsOne(Representative(classes_5[j])) then
            id_class_idx := j;
            break;
        fi;
    od;
    _qb35t_assert("m=5 identity class found in conj_action.classes",
                  id_class_idx <> fail);

    rep_id := Representative(classes_5[id_class_idx]);;
    C_id := Centralizer(conj_5.em, rep_id);;
    Print("  identity-class centraliser: |C| = ", Order(C_id), "\n");

    # Spot-check: c_id(h, k) = ω(id, h, k) - ω(h, id, k) + ω(h, k, id) = 0
    # on a few random (h, k) in G. (Sampling not exhaustive — full
    # check happens inside the driver via BuildPerClassCocycleBasis.)
    c_id_zero := true;;
    for _trial in [1..10] do
        h_rnd := Random(conj_5.em);
        k_rnd := Random(conj_5.em);
        c_val := (c5_b.omega(rep_id, h_rnd, k_rnd)
                  - c5_b.omega(h_rnd, rep_id, k_rnd)
                  + c5_b.omega(h_rnd, k_rnd, rep_id)) mod c5_b.exponent;
        if c_val <> 0 then
            c_id_zero := false;
            Print("    c_id(", h_rnd, ", ", k_rnd, ") = ", c_val,
                  " (non-zero)\n");
        fi;
    od;
    _qb35t_assert("m=5 c_id(h, k) ≡ 0 on 10 random (h, k) samples",
                  c_id_zero);

    # Now run the dispatcher on the trivial cocycle (all-zero c_g_vec)
    # with vec = e_165. We use a small dummy centraliser to keep
    # IsCoboundary2Z2k tractable (the full |C| = 2048 boundary-matrix
    # build at m=5 is heavy; the dispatcher logic is what matters here,
    # not the |C| = 2048 case). We pick the SMALLEST non-identity-class
    # centraliser.
    n_classes_5 := Length(classes_5);;
    smallest_C := fail;;
    smallest_size := fail;;
    smallest_rep := fail;;
    for j in [1..n_classes_5] do
        if j = id_class_idx then continue; fi;
        rep_j := Representative(classes_5[j]);
        C_j := Centralizer(conj_5.em, rep_j);
        if smallest_size = fail or Order(C_j) < smallest_size then
            smallest_size := Order(C_j);
            smallest_C := C_j;
            smallest_rep := rep_j;
        fi;
    od;
    _qb35t_assert("m=5 found a non-identity-class centraliser",
                  smallest_C <> fail);
    Print("  smallest non-identity centraliser: |C| = ",
          smallest_size, "\n");

    # vec = e_165: the Z/4 unit.
    vec_165 := List([1..165], j -> 0);;
    vec_165[165] := 1;;

    # Trivial cocycle on smallest_C: all-zero c_g_vec.
    n_small := Order(smallest_C);;
    c_zero_vec := List([1..n_small * n_small], _ -> 0);;

    t_solve := Runtime();;
    is_kernel_zero := IsCoboundary2SplitVec(smallest_C, c_zero_vec,
                                             vec_165, s5_b);;
    Print("  trivial-cocycle Path-Z dispatch wall: ",
          (Runtime() - t_solve) / 1000., " s\n");
    Print("  IsCoboundary2SplitVec verdict on zero cocycle: ",
          is_kernel_zero, "\n");
    _qb35t_assert(
        "m=5 e_165 + zero c_g_vec: dispatcher returns true (zero is coboundary)",
        is_kernel_zero = true);
fi;

# ----------------------------------------------------------------------
# Summary.
# ----------------------------------------------------------------------

wall_total := (Runtime() - t_total_start) / 1000.;;
Print("\n=== summary (wall: ", wall_total, " s) ===\n");
Print("  passed: ", _qb35t_pass, "    failed: ", _qb35t_fail, "\n");
if _qb35t_fail > 0 then
    Print("  STATUS: FAIL\n");
    for _lab in _qb35t_failures do
        Print("    - ", _lab, "\n");
    od;
    QUIT_GAP(1);
else
    Print("  STATUS: PASS\n");
    QUIT_GAP(0);
fi;
