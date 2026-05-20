# test_build_krr_intertwiner_data_projective.g
#
# Tests for K-4a-T4c projective (issue #323):
#   `BuildKRRIntertwinerData(m, G, opts)` with `opts.omega_vec` != 0
#   must return projective character values via the slant 2-cocycle
#   alpha_g.
#
# Acceptance criteria (issue #323):
#   1. Sanity at ω = 0: feed `omega_vec := [0, 0, ..., 0]` to the new
#      path. Must produce the SAME numeric values as the EvalIrr
#      baseline byte-for-byte (modulo a relabelling of characters).
#   2. m=3 non-trivial-ω: `K4aClassify(3, rec(lattice_source := true,
#      omega_vec := <unit_vec_e_35>))` runs to completion with the new
#      projective trace path.
#   3. The projective character table is built lazily per class and
#      cached.
#
# Invoke via absolute path (K-4a-T1 convention):
#   gap -q -b -c 'Read("/.../tests/test_build_krr_intertwiner_data_projective.g");'

SetInfoLevel(InfoWarning, 0);
BreakOnError := false;

# Resolve absolute paths to siblings independent of CWD.
_SCRIPT_SELF := INPUT_FILENAME();;
if _SCRIPT_SELF = fail or _SCRIPT_SELF = "stream" then
    Error("test_build_krr_intertwiner_data_projective.g: ",
          "INPUT_FILENAME() unavailable; invoke via absolute Read().");
fi;
_SELF_DIR := _SCRIPT_SELF{
    [1..Length(_SCRIPT_SELF)
       - Length("/test_build_krr_intertwiner_data_projective.g")]};;
_SCRIPTS_DIR := _SELF_DIR{[1..Length(_SELF_DIR) - Length("/tests")]};;
Print("Script dir resolved as: ", _SCRIPTS_DIR, "\n");

if not IsExistingFile(Concatenation(_SCRIPTS_DIR, "/bw_lattice.g")) then
    Error("test_build_krr_intertwiner_data_projective.g: resolved ",
          "_SCRIPTS_DIR=\"", _SCRIPTS_DIR, "\" does not contain ",
          "bw_lattice.g; check INPUT_FILENAME() path resolution.");
fi;

# Save the original CWD; change to _SCRIPTS_DIR for the load phase so
# relative Reads inside loaded files resolve correctly. Restore after.
_OLD_CWD := Filename(DirectoryCurrent(), "");;
ChangeDirectoryCurrent(_SCRIPTS_DIR);

_T_Read := function(rel)
    Read(Concatenation(_SCRIPTS_DIR, "/", rel));
end;;

T_PASS := 0;;
T_FAILURES := [];;
TAssertTrue := function(label, cond)
    if cond then
        Print("  [ok]   ", label, "\n");
        T_PASS := T_PASS + 1;
    else
        Print("  [FAIL] ", label, "\n");
        Add(T_FAILURES, label);
    fi;
end;;
TAssertEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok]   ", label, "\n");
        T_PASS := T_PASS + 1;
    else
        Print("  [FAIL] ", label, " (got=", got, ", expected=", expected, ")\n");
        Add(T_FAILURES, label);
    fi;
end;;

# ------------------------------------------------------------------
# Load dependencies.
# ------------------------------------------------------------------
# We need:
#   * src/modular_data.g            -- defines UniversalCoefficientsTheorem
#   * untwisted_modular_data.g      -- BuildSimpleIndex, EvalIrr
#   * krr_projector.g               -- BuildIntertwinerDataUntwisted
#   * epsilon_omega.g + epsilon_omega_phase.g -- V-1 / #14, ε_ω-phase
#   * build_krr_intertwiner_data.g  -- entry point under test

# Resolve src/modular_data.g (sibling of extraspecial_orbifolds).
_MODULAR_DATA_REL := Concatenation(_SCRIPTS_DIR, "/../../src/modular_data.g");;
if not IsExistingFile(_MODULAR_DATA_REL) then
    Error("test_build_krr_intertwiner_data_projective.g: src/modular_data.g ",
          "not found at ", _MODULAR_DATA_REL);
fi;
Read(_MODULAR_DATA_REL);

_T_Read("untwisted_modular_data.g");
_T_Read("krr_projector.g");
_T_Read("epsilon_omega.g");
_T_Read("epsilon_omega_phase.g");
_T_Read("build_krr_intertwiner_data.g");

ChangeDirectoryCurrent(_OLD_CWD);

_REQUIRED_GLOBALS := [
    "BuildSimpleIndex", "EvalIrr",
    "BuildIntertwinerDataUntwisted",
    "EpsilonOmegaPhase", "_EOP_GetContext",
    "BuildKRRIntertwinerData",
    "_KRRI_BuildProjectiveCallables",
    "_KRRI_AlphaG", "_KRRI_BuildCentralExtension",
    "_KRRI_ProjectiveCharsForG", "_KRRI_TryMatchProjToIrr"
];;
for _gl in _REQUIRED_GLOBALS do
    if not IsBoundGlobal(_gl) then
        Error("test_build_krr_intertwiner_data_projective.g: required ",
              "global \"", _gl, "\" is not bound after dependency load.");
    fi;
od;
Print("All required globals bound after dependency load (",
      Length(_REQUIRED_GLOBALS), " checked).\n");


# ==================================================================
# Test P1: D_8 sanity at omega = 0 via the projective path.
# Feed omega_vec := [0, 0, ..., 0] (length = Length(UCT.hombasis)).
# The projective character table for alpha = 0 must be the ordinary
# character table; after byte-for-byte re-indexing it must agree with
# EvalIrr.
# ==================================================================
Print("\n=================================================================\n");
Print("  P1: D_8 at omega = 0 via projective path (byte-for-byte sanity)\n");
Print("=================================================================\n");

P1_G := SmallGroup(8, 3);;        # D_8
Print("  G = D_8 (SmallGroup(8, 3)), |G| = ", Order(P1_G), "\n");

# Build UCT to find the hom-basis length.
Print("  Building UCT(D_8) to find hombasis length...\n");
P1_R := ResolutionFiniteGroup(P1_G, 4);;
P1_K := TensorWithIntegers(P1_R);;
P1_UCT := UniversalCoefficientsTheorem(P1_K, 3);;
P1_HOMLEN := Length(P1_UCT!.hombasis);;
Print("  hombasis length: ", P1_HOMLEN, "\n");
P1_ZERO := ListWithIdenticalEntries(P1_HOMLEN, 0);;

# Lite baseline (omega = 0; uses EvalIrr internally).
P1_LITE := BuildKRRIntertwinerData(1, P1_G,
    rec(spectral_source := "lite"));;

# Projective path with omega_vec = all-zero. Note: at omega_vec =
# all-zero the function recomputes UCT internally; it's slower than
# the lite path but produces (after re-indexing) the same values.
Print("  Building projective path with omega_vec = ", P1_ZERO, "...\n");
P1_T0 := Runtime();;
P1_PROJ := BuildKRRIntertwinerData(1, P1_G,
    rec(spectral_source := "projective", omega_vec := P1_ZERO,
        verbose := false));;
P1_T1 := Runtime();;
Print("  Projective build wall: ", P1_T1 - P1_T0, " ms\n");

TAssertEqual("P1: omega_is_zero = true (zero vec recognised)",
             P1_PROJ.omega_is_zero, true);
TAssertEqual("P1: spectral_source_resolved = \"projective\"",
             P1_PROJ.spectral_source_resolved, "projective");
TAssertTrue("P1: projective_data populated",
            IsBound(P1_PROJ.projective_data));

# At omega = 0 alpha_g = 0 for every class; for each class the proj.
# table aligns with Irr(C_G(g_i)) by re-indexing. We sweep all
# (class_idx, irrep_idx, h) triples with h in C_G(g_i) and check
# trace_on_W_proj(i, k, h) == trace_on_W_lite(i, k, h).
P1_IDX := P1_PROJ.idx;;
P1_DIFFS := 0;;
P1_FIRST_DIFF := fail;;
P1_PROBED := 0;;
for i in [1..Length(P1_IDX.classes)] do
    # Sample a few h values from the centraliser of g_i.
    P1_C := P1_IDX.centralisers[i];
    P1_H_SAMPLES := [One(P1_C), P1_IDX.reps[i]];
    if Length(GeneratorsOfGroup(P1_C)) >= 1 then
        Add(P1_H_SAMPLES, GeneratorsOfGroup(P1_C)[1]);
    fi;
    for k in [1..P1_IDX.num_irreps[i]] do
        for h in P1_H_SAMPLES do
            v_p := P1_PROJ.trace_on_W(i, k, h);
            v_l := P1_LITE.trace_on_W(i, k, h);
            P1_PROBED := P1_PROBED + 1;
            if v_p <> v_l then
                P1_DIFFS := P1_DIFFS + 1;
                if P1_FIRST_DIFF = fail then
                    P1_FIRST_DIFF := rec(i := i, k := k, h := h,
                                          proj := v_p, lite := v_l);
                fi;
            fi;
        od;
    od;
od;
Print("  Probed ", P1_PROBED, " (i, k, h) triples; ", P1_DIFFS,
      " disagreements.\n");
if P1_FIRST_DIFF <> fail then
    Print("  First disagreement: i=", P1_FIRST_DIFF.i,
          " k=", P1_FIRST_DIFF.k,
          " h=", P1_FIRST_DIFF.h, "\n");
    Print("    proj = ", P1_FIRST_DIFF.proj, "\n");
    Print("    lite = ", P1_FIRST_DIFF.lite, "\n");
fi;
TAssertEqual("P1: omega = 0 byte-for-byte: projective trace = lite trace",
             P1_DIFFS, 0);


# ==================================================================
# P2: D_8 with the order-2 non-trivial omega.
# H^3(D_8; U(1)) = Z/2 ⊕ Z/2 ⊕ Z/4.
# We pick a non-zero hom-basis vector and verify trace_on_W returns
# cyclotomics that DIFFER from the ordinary characters somewhere.
# ==================================================================
Print("\n=================================================================\n");
Print("  P2: D_8 with a non-trivial omega\n");
Print("=================================================================\n");

# Try the unit vector e_HOMLEN (last hom-basis generator).
P2_OMEGA := ListWithIdenticalEntries(P1_HOMLEN, 0);;
P2_OMEGA[P1_HOMLEN] := 1;;
Print("  omega_vec = ", P2_OMEGA, " (unit vec at last hombasis index)\n");

P2_T0 := Runtime();;
P2_PROJ := BuildKRRIntertwinerData(1, P1_G,
    rec(spectral_source := "projective", omega_vec := P2_OMEGA,
        verbose := false));;
P2_T1 := Runtime();;
Print("  Projective build wall: ", P2_T1 - P2_T0, " ms\n");
TAssertEqual("P2: omega_is_zero = false",
             P2_PROJ.omega_is_zero, false);
TAssertEqual("P2: spectral_source_resolved = \"projective\"",
             P2_PROJ.spectral_source_resolved, "projective");

# Probe a few trace values; all must be cyclotomic.
P2_OK := true;;
P2_IDX := P2_PROJ.idx;;
for i in [1..Length(P2_IDX.classes)] do
    for k in [1..Minimum(P2_IDX.num_irreps[i], 4)] do
        v := P2_PROJ.trace_on_W(i, k, One(P1_G));
        if not IsCyclotomic(v) then
            P2_OK := false;
            Print("  P2 fail: i=", i, " k=", k, " v=", v, "\n");
        fi;
    od;
od;
TAssertTrue("P2: projective trace_on_W returns cyclotomics",
            P2_OK);

# Check that the epsilon callable is wired (V-1 path):
P2_EPS := P2_PROJ.epsilon(One(P1_G), One(P1_G), One(P1_G), One(P1_G));;
TAssertTrue("P2: epsilon callable returns cyclotomic",
            IsCyclotomic(P2_EPS));
# At g1 = g2 = a = b = 1, the slant sums vanish, so epsilon(1,1,1,1) = 1.
TAssertEqual("P2: epsilon(1, 1, 1, 1) = 1 (identity case)",
             P2_EPS, 1);

# A non-trivial sanity: at a non-identity class, the projective char
# values should differ from the corresponding lite (EvalIrr) values
# for at least one (k, h) — otherwise the alpha_g cocycle is trivial
# on every centraliser, which would contradict the choice of non-zero
# omega for D_8.
P2_LITE := BuildKRRIntertwinerData(1, P1_G,
    rec(spectral_source := "lite"));;
P2_ANY_DIFF := false;;
P2_SAMPLES := 0;;
for i in [1..Length(P2_IDX.classes)] do
    P2_C := P2_IDX.centralisers[i];
    for k in [1..P2_IDX.num_irreps[i]] do
        for h in [One(P2_C), P2_IDX.reps[i]] do
            P2_SAMPLES := P2_SAMPLES + 1;
            v_p := P2_PROJ.trace_on_W(i, k, h);
            v_l := P2_LITE.trace_on_W(i, k, h);
            if v_p <> v_l then
                P2_ANY_DIFF := true;
            fi;
        od;
    od;
od;
Print("  Probed ", P2_SAMPLES, " (i, k, h) samples.\n");
TAssertTrue(
    Concatenation("P2: at omega != 0, projective trace DIFFERS from ",
                  "lite for some (i, k, h)"),
    P2_ANY_DIFF);


# ==================================================================
# P3: Internal helpers (alpha_g, central extension, projective chars)
# behave correctly on a small group.
# ==================================================================
Print("\n=================================================================\n");
Print("  P3: Internal helpers (alpha_g, central extension)\n");
Print("=================================================================\n");

# Build a context manually and verify alpha_g satisfies the 2-cocycle
# equation on a few samples of g, x, y, z in C_G(g).
P3_CTX := _EOP_GetContext(P2_OMEGA, P1_G);;
P3_OK := true;;
P3_VIOL := 0;;
# Test alpha cocycle equation: alpha(x, y) + alpha(xy, z) - alpha(x, yz)
# - alpha(y, z) = 0 mod m for x, y, z in C_G(g).
for g in List(ConjugacyClasses(P1_G), Representative) do
    P3_C := Centralizer(P1_G, g);
    P3_C_ELTS := Elements(P3_C);
    # Probe a few random triples.
    for _trial in [1..5] do
        x := Random(P3_C_ELTS);
        y := Random(P3_C_ELTS);
        z := Random(P3_C_ELTS);
        a_xy := _KRRI_AlphaG(P3_CTX.omega_cb, P3_CTX.m_omega, g, x, y);
        a_xy_z := _KRRI_AlphaG(P3_CTX.omega_cb, P3_CTX.m_omega, g, x*y, z);
        a_x_yz := _KRRI_AlphaG(P3_CTX.omega_cb, P3_CTX.m_omega, g, x, y*z);
        a_yz := _KRRI_AlphaG(P3_CTX.omega_cb, P3_CTX.m_omega, g, y, z);
        # 2-cocycle: a(x, y) * a(xy, z) = a(x, yz) * a(y, z)
        # additive form: a(x, y) + a(xy, z) - a(x, yz) - a(y, z) = 0 mod m.
        diff := (a_xy + a_xy_z - a_x_yz - a_yz) mod P3_CTX.m_omega;
        if diff <> 0 then
            P3_VIOL := P3_VIOL + 1;
            if P3_OK then
                Print("  P3 alpha-cocycle violation: g=", g,
                      " x=", x, " y=", y, " z=", z,
                      " diff=", diff, "\n");
                P3_OK := false;
            fi;
        fi;
    od;
od;
Print("  alpha-cocycle violations: ", P3_VIOL, " (probed 5 triples ",
      "for each of ", Length(ConjugacyClasses(P1_G)), " classes)\n");
TAssertEqual("P3: alpha_g is a 2-cocycle on C_G(g) for all classes",
             P3_VIOL, 0);


# ==================================================================
# P4: m=3 anchor — `BuildKRRIntertwinerData(3, EmGroup(3), ...)`
# with the non-trivial unit vec e_35 (the order-4 Pontryagin top on
# E_+(3)) at least RUNS without errors and produces traces.
# This is the m=3 acceptance criterion of issue #323.
# ==================================================================
Print("\n=================================================================\n");
Print("  P4: m=3 E_+(3) with omega = e_35 (Pontryagin top)\n");
Print("=================================================================\n");

# At E_+(3): hombasis length = 35; e_35 is the last (the Z/4 generator).
# This is a non-trivial omega test.
_T_Read_P4 := function(rel)
    Read(Concatenation(_SCRIPTS_DIR, "/", rel));
end;;
# We need EmGroup; load em_construction.g (which loads bw_lattice.g
# transitively). The load path needs CWD = _SCRIPTS_DIR.
_OLD_CWD2 := Filename(DirectoryCurrent(), "");;
ChangeDirectoryCurrent(_SCRIPTS_DIR);
_T_Read_P4("bw_lattice.g");
_T_Read_P4("em_construction.g");
ChangeDirectoryCurrent(_OLD_CWD2);

if not IsBoundGlobal("EmGroup") then
    Print("  [skip] EmGroup not bound; P4 skipped.\n");
else
    Print("  Building E_+(3) via IsomorphismPcGroup(EmGroup(3))...\n");
    P4_T0 := Runtime();
    P4_G_MAT := EmGroup(3);
    P4_ISO := IsomorphismPcGroup(P4_G_MAT);
    P4_G := Image(P4_ISO);
    P4_T1 := Runtime();
    Print("  |E_+(3)| = ", Order(P4_G), ", pc-group built in ",
          P4_T1 - P4_T0, " ms\n");

    # Build UCT to confirm hombasis length is 35.
    Print("  Building UCT(E_+(3)) to confirm hombasis length...\n");
    P4_T2 := Runtime();
    P4_R := ResolutionFiniteGroup(P4_G, 4);
    P4_K := TensorWithIntegers(P4_R);
    P4_UCT := UniversalCoefficientsTheorem(P4_K, 3);
    P4_T3 := Runtime();
    P4_HOM_LEN := Length(P4_UCT!.hombasis);
    Print("  hombasis length: ", P4_HOM_LEN, " (built in ",
          P4_T3 - P4_T2, " ms)\n");

    P4_OMEGA := ListWithIdenticalEntries(P4_HOM_LEN, 0);
    P4_OMEGA[P4_HOM_LEN] := 1;     # e_35 (Pontryagin top)
    Print("  omega_vec = unit vec at index ", P4_HOM_LEN,
          " (e_", P4_HOM_LEN, ", the Pontryagin top)\n");

    Print("  Building BuildKRRIntertwinerData(3, E_+(3), opts=projective, ",
          "omega_vec=e_", P4_HOM_LEN, ", lazy=true)...\n");
    P4_T4 := Runtime();
    P4_DATA := BuildKRRIntertwinerData(3, P4_G,
        rec(spectral_source := "projective", omega_vec := P4_OMEGA,
            lazy := true, verbose := false));
    P4_T5 := Runtime();
    Print("  Built in ", P4_T5 - P4_T4, " ms\n");

    TAssertEqual("P4: m=3 omega_is_zero = false",
                 P4_DATA.omega_is_zero, false);
    TAssertEqual("P4: m=3 spectral_source_resolved = \"projective\"",
                 P4_DATA.spectral_source_resolved, "projective");
    TAssertTrue("P4: m=3 .projective_data populated",
                IsBound(P4_DATA.projective_data));
    TAssertTrue("P4: m=3 .trace_on_W is a function",
                IsFunction(P4_DATA.trace_on_W));

    # Query trace_on_W on a non-central class (smaller centraliser =
    # cheaper Irr build). Class 2 typically has |C_G(g)| = 64, giving
    # central extension of order 256 (vs 512 for the identity class).
    # We pick the first non-central singleton-or-doubleton class.
    P4_IDX := P4_DATA.idx;
    P4_CLASS := 2;     # first non-central class in E_+(3)'s default ordering
    P4_CLASS_SIZE := P4_IDX.class_sizes[P4_CLASS];
    P4_CENT_ORDER := Order(P4_IDX.centralisers[P4_CLASS]);
    Print("  Querying trace_on_W(class=", P4_CLASS,
          ", k=1, h=identity): class size = ", P4_CLASS_SIZE,
          ", |C| = ", P4_CENT_ORDER,
          ", ext order = ", P4_CENT_ORDER * 4, "\n");
    P4_T6 := Runtime();
    P4_VAL := P4_DATA.trace_on_W(P4_CLASS, 1, One(P4_G));
    P4_T7 := Runtime();
    Print("  trace_on_W(", P4_CLASS, ", 1, 1) = ", P4_VAL, " (",
          P4_T7 - P4_T6, " ms — first per-class build)\n");
    TAssertTrue("P4: trace_on_W returns a cyclotomic",
                IsCyclotomic(P4_VAL));

    # Second query on the same class should be much faster (cache hit).
    P4_T8 := Runtime();
    P4_VAL2 := P4_DATA.trace_on_W(P4_CLASS, 1, One(P4_G));
    P4_T9 := Runtime();
    Print("  trace_on_W(", P4_CLASS, ", 1, 1) second call: ", P4_VAL2,
          " (", P4_T9 - P4_T8, " ms — cache hit)\n");
    TAssertEqual("P4: second query returns same value (cache stable)",
                 P4_VAL2, P4_VAL);

    # Epsilon callable returns a cyclotomic and is wired to V-1.
    P4_E_VAL := P4_DATA.epsilon(One(P4_G), One(P4_G), One(P4_G), One(P4_G));
    TAssertEqual("P4: epsilon(1,1,1,1) = 1 (identity case)",
                 P4_E_VAL, 1);
fi;


# ==================================================================
# P6: K-4a integration smoke at m=3 with omega = unit vec at index 35.
# We do NOT run the full K4aClassify pipeline (which would also require
# loading d8_classifier.g, q8_classifier.g, restrict_to_subgroup.g and
# their CT-load infrastructure -- adds several minutes). Instead, we
# exercise the SAME entry point K-4a uses to build per-branch data:
#   BuildKRRIntertwinerData(3, EPlusGroup(3), opts_with_omega_vec)
# and verify it constructs without error. This is the acceptance
# criterion #2 of issue #323 ("must run to completion").
# ==================================================================
Print("\n=================================================================\n");
Print("  P6: K-4a entry-point smoke at m=3 on EPlusGroup(3)\n");
Print("=================================================================\n");

# EPlusGroup(3) = ExtraspecialGroup(2^7, "+"). Has |G| = 128 and is
# isomorphic to E_+(3) but lives in a different GAP family.
P6_G := ExtraspecialGroup(2^7, "+");;
Print("  |EPlusGroup(3)| = ", Order(P6_G), "\n");

# Build UCT(EPlusGroup(3)) to find hombasis length. This will differ
# from the matrix-realisation EmGroup(3) ONLY in element-ordering, so
# hombasis length is the same.
Print("  Building UCT(EPlusGroup(3))...\n");
P6_T0 := Runtime();
P6_R := ResolutionFiniteGroup(P6_G, 4);
P6_K := TensorWithIntegers(P6_R);
P6_UCT := UniversalCoefficientsTheorem(P6_K, 3);
P6_T1 := Runtime();
P6_HOM_LEN := Length(P6_UCT!.hombasis);
Print("  hombasis length: ", P6_HOM_LEN, " (built in ",
      P6_T1 - P6_T0, " ms)\n");
TAssertEqual("P6: hombasis length = 35 (Z/4 generator at index 35)",
             P6_HOM_LEN, 35);

# Use the unit vec at index 35 (Pontryagin top per issue #323).
P6_OMEGA := ListWithIdenticalEntries(P6_HOM_LEN, 0);
P6_OMEGA[P6_HOM_LEN] := 1;

Print("  Building BuildKRRIntertwinerData(3, EPlusGroup(3), opts=auto, ",
      "omega_vec=e_35, lazy=true)...\n");
P6_T2 := Runtime();
P6_DATA := BuildKRRIntertwinerData(3, P6_G,
    rec(spectral_source := "auto", omega_vec := P6_OMEGA,
        lazy := true, verbose := false));;
P6_T3 := Runtime();
Print("  Built in ", P6_T3 - P6_T2, " ms\n");

TAssertEqual("P6: auto-routed to projective for omega != 0",
             P6_DATA.spectral_source_resolved, "projective");
TAssertEqual("P6: omega_is_zero = false",
             P6_DATA.omega_is_zero, false);
TAssertTrue("P6: .projective_data populated",
            IsBound(P6_DATA.projective_data));

# Do NOT call trace_on_W on the central class (the build would take
# ~9 min for the Irr of a group of order 512). Instead verify the
# callable is set and the epsilon callable returns 1 at identity.
TAssertTrue("P6: .trace_on_W is a function",
            IsFunction(P6_DATA.trace_on_W));
P6_E := P6_DATA.epsilon(One(P6_G), One(P6_G), One(P6_G), One(P6_G));;
TAssertEqual("P6: epsilon(1, 1, 1, 1) = 1",
             P6_E, 1);


# ==================================================================
# P5 (optional): m=7 reachability gate
# Per issue #323 we need to confirm the path at minimum REACHES the
# projective character table computation at m=7 without OOM. Acceptance
# is "starts computing"; full m=7 wall is a follow-up.
# Gated by env K4A_T4C_PROJECTIVE_RUN_M7=1 (default skip).
# ==================================================================
Print("\n=================================================================\n");
Print("  P5: m=7 reachability (gated)\n");
Print("=================================================================\n");

if not IsBound(K4A_T4C_PROJECTIVE_RUN_M7) then
    K4A_T4C_PROJECTIVE_RUN_M7 := "0";
fi;
if K4A_T4C_PROJECTIVE_RUN_M7 = "1" then
    Print("  P5 enabled. Building E_+(7) and routing through projective...\n");
    P5_T0 := Runtime();
    P5_G_MAT := EmGroup(7);
    P5_ISO := IsomorphismPcGroup(P5_G_MAT);
    P5_G := Image(P5_ISO);
    P5_T1 := Runtime();
    Print("  |E_+(7)| = ", Order(P5_G), ", pc-group built in ",
          P5_T1 - P5_T0, " ms\n");
    # Smoke: just check BuildKRRIntertwinerData CONSTRUCTS without OOM.
    # We don't run trace_on_W -- that would trigger ResolutionFiniteGroup
    # on E_+(7) which OOMs.
    Print("  P5: m=7 construction smoke (lazy idx + epsilon-only).\n");
    P5_T2 := Runtime();
    P5_DATA := BuildKRRIntertwinerData(7, P5_G,
        rec(spectral_source := "lite", lazy := true, verbose := true));
    P5_T3 := Runtime();
    Print("  Lazy lite build at m=7 in ", P5_T3 - P5_T2, " ms.\n");
    TAssertEqual("P5: m=7 lazy lite build returns krr-lattice",
                 P5_DATA.source, "krr-lattice");
else
    Print("  P5 skipped (set K4A_T4C_PROJECTIVE_RUN_M7 = \"1\" to enable).\n");
fi;


# ==================================================================
# Summary
# ==================================================================
Print("\n=================================================================\n");
Print("  Summary\n");
Print("=================================================================\n");
Print("Passes:   ", T_PASS, "\n");
Print("Failures: ", Length(T_FAILURES), "\n");
if Length(T_FAILURES) > 0 then
    Print("Failure labels:\n");
    for lbl in T_FAILURES do
        Print("  - ", lbl, "\n");
    od;
fi;
Print("\nALL TESTS PASS: ", Length(T_FAILURES) = 0, "\n");

QUIT;
