# test_dvan_m7_per_gen_cert.g — D-VAN m=7 per-generator certification (#362).
#
# For each unit basis vector e_i in H^3(E_+(7); U(1)) (i in [1..k_G]),
# verify that at least one branch K in the 8-EA family + {D_8, Q_8}
# detects Res_K(e_i) as non-zero. This certifies the family is
# injective on H^3 at the basis level.
#
# COHOMOLOGY-LEVEL TEST: matrix-vector product Res_K * e_i (= row i of
# res_K^T = column i of res_K, indexed differently). No modular data.
# Per-generator wall is < 100 ms after the (heavy) cold setup.
#
# Cold setup (~30 min wall):
#   * _DETF_BuildSetupG_LHS(7)            — LHS resolution of E_+(7)
#   * LoadDVANEAFamily(7)                  — 8 EA subgroups from result.g
#   * _DETF_FindD8In(G, 7), _DETF_FindQ8In — D_8 + Q_8 sections
#   * For each of 10 subgroups: SubgroupCohomologyContext + RestrictionMatrixViaHAP
#
# Configurable:
#   M7_PER_GEN_CERT_COUNT (default 454 — full sweep).
#
# Usage:
#   cd extraspecial_orbifolds/scripts
#   gap -q -b -c 'M7_PER_GEN_CERT_COUNT := 5; \
#                 Read("tests/test_dvan_m7_per_gen_cert.g"); QUIT;'   # smoke
#   gap -q -b -c 'Read("tests/test_dvan_m7_per_gen_cert.g"); QUIT;'  # full

Read("solver/logging_util.g");
Read("detecting_family_restriction.g");
Read("k4a_classify.g");

if not IsBoundGlobal("M7_PER_GEN_CERT_COUNT") then
    M7_PER_GEN_CERT_COUNT := 454;
fi;

_LogPhase("m7-cert", "=== D-VAN m=7 per-generator certification (#362) ===");

# ---- Step 1: setup_G via LHS resolution ----
_LogPhase("m7-cert", "Step 1/4: building setup_G via _DETF_BuildSetupG_LHS(7) ...");
_M7CERT_T0 := Runtime();;
setup_G := _DETF_BuildSetupG_LHS(7);;
G := setup_G.group;;
k_G := setup_G.num_generators;;
_LogPhase("m7-cert", "setup_G built in ", (Runtime() - _M7CERT_T0) / 1000.0,
          " s. k_G = ", k_G, ", exponent = ", setup_G.exponent);

# ---- Step 2: load 8 EAs + D_8 + Q_8 ----
_LogPhase("m7-cert", "Step 2/4: loading 8 EAs via LoadDVANEAFamily(7) ...");
ea_subgroups := LoadDVANEAFamily(7);;
if ea_subgroups = fail then
    Error("LoadDVANEAFamily(7) returned fail. Verify ",
          "computed/dvan_min_family/m7/result.g has ea_generators_exp.");
fi;
_LogPhase("m7-cert", "Loaded ", Length(ea_subgroups), " EAs (expected 8)");

_LogPhase("m7-cert", "Finding D_8 section ...");
H_D8 := _DETF_FindD8In(G, 7);;
_LogPhase("m7-cert", "Finding Q_8 section ...");
H_Q8 := _DETF_FindQ8In(G, 7);;

_LogPhase("m7-cert", "|D_8| = ", Order(H_D8),
          ", |Q_8| = ", If_(H_Q8 = fail, "fail", String(Order(H_Q8))));

# ---- Step 3: build restriction matrices for 10 subgroups ----
_LogPhase("m7-cert", "Step 3/4: building restriction matrices for ",
          Length(ea_subgroups), " EAs + D_8 + Q_8 ...");
restriction_matrices := [];;
torsion_vectors := [];;
subgroup_labels := [];;

# EA branches.
for _M7CERT_I in [1..Length(ea_subgroups)] do
    _M7CERT_T := Runtime();
    _M7CERT_CTX := SubgroupCohomologyContext(ea_subgroups[_M7CERT_I]);
    _M7CERT_PHI := SubgroupInclusion(ea_subgroups[_M7CERT_I], G);
    _M7CERT_RES := RestrictionMatrixViaHAP(setup_G, _M7CERT_CTX, _M7CERT_PHI);
    Add(restriction_matrices, _M7CERT_RES);
    Add(torsion_vectors, _M7CERT_CTX.torsion);
    Add(subgroup_labels, Concatenation("EA_", String(_M7CERT_I)));
    _LogPhase("m7-cert", "  EA_", _M7CERT_I, " restriction built in ",
              (Runtime() - _M7CERT_T) / 1000.0, " s");
od;

# D_8.
_M7CERT_T := Runtime();;
_M7CERT_CTX_D8 := SubgroupCohomologyContext(H_D8);;
_M7CERT_PHI_D8 := SubgroupInclusion(H_D8, G);;
_M7CERT_RES_D8 := RestrictionMatrixViaHAP(setup_G, _M7CERT_CTX_D8, _M7CERT_PHI_D8);;
Add(restriction_matrices, _M7CERT_RES_D8);
Add(torsion_vectors, _M7CERT_CTX_D8.torsion);
Add(subgroup_labels, "D_8");
_LogPhase("m7-cert", "  D_8 restriction built in ",
          (Runtime() - _M7CERT_T) / 1000.0, " s");

# Q_8.
if H_Q8 <> fail then
    _M7CERT_T := Runtime();
    _M7CERT_CTX_Q8 := SubgroupCohomologyContext(H_Q8);
    _M7CERT_PHI_Q8 := SubgroupInclusion(H_Q8, G);
    _M7CERT_RES_Q8 := RestrictionMatrixViaHAP(setup_G, _M7CERT_CTX_Q8, _M7CERT_PHI_Q8);
    Add(restriction_matrices, _M7CERT_RES_Q8);
    Add(torsion_vectors, _M7CERT_CTX_Q8.torsion);
    Add(subgroup_labels, "Q_8");
    _LogPhase("m7-cert", "  Q_8 restriction built in ",
              (Runtime() - _M7CERT_T) / 1000.0, " s");
fi;

_LogPhase("m7-cert", "Total restriction matrices: ", Length(restriction_matrices));

# ---- Step 4: per-generator certification ----
test_count := Minimum(M7_PER_GEN_CERT_COUNT, k_G);;
_LogPhase("m7-cert", "Step 4/4: certifying ", test_count, " unit generators ...");

n_pass := 0;;
n_fail := 0;;
failures := [];;

_M7CERT_SWEEP_T0 := Runtime();;
for _M7CERT_I in [1..test_count] do
    detected_by := [];
    for _M7CERT_J in [1..Length(restriction_matrices)] do
        # omega_vec = e_i (one-hot in position i of length k_G); the
        # matvec omega_vec * res_K reduces to row i of res_K.
        row := restriction_matrices[_M7CERT_J][_M7CERT_I];
        # Mod against per-component torsion. Row may have entries that
        # are 0 mod the corresponding torsion[k] component.
        is_nonzero := false;
        for _M7CERT_K in [1..Length(row)] do
            if (row[_M7CERT_K] mod torsion_vectors[_M7CERT_J][_M7CERT_K]) <> 0 then
                is_nonzero := true;
                break;
            fi;
        od;
        if is_nonzero then
            Add(detected_by, subgroup_labels[_M7CERT_J]);
        fi;
    od;
    if Length(detected_by) > 0 then
        n_pass := n_pass + 1;
        if _M7CERT_I <= 5 or _M7CERT_I mod 50 = 0
           or _M7CERT_I = test_count then
            Print("  e_", _M7CERT_I, "/", test_count, ": PASS detected by ",
                  detected_by{[1..Minimum(Length(detected_by), 5)]},
                  If_(Length(detected_by) > 5, " ...", ""), "\n");
        fi;
    else
        n_fail := n_fail + 1;
        Add(failures, _M7CERT_I);
        Print("  e_", _M7CERT_I, "/", test_count,
              ": FAIL all branches reported zero restriction\n");
    fi;
od;

_M7CERT_WALL := (Runtime() - _M7CERT_SWEEP_T0) / 1000.0;;
_LogPhase("m7-cert", "Sweep complete in ", _M7CERT_WALL, " s CPU");

# ---- Summary ----
Print("\n=================================================================\n");
Print("D-VAN m=7 per-generator certification (#362) summary\n");
Print("=================================================================\n");
Print("Tested: ", test_count, " unit generators of H^3(E_+(7); U(1))\n");
Print("k_G:    ", k_G, "\n");
Print("Pass:   ", n_pass, " / ", test_count, "\n");
Print("Fail:   ", n_fail, "\n");
Print("Sweep CPU wall: ", _M7CERT_WALL, " s\n");

if n_fail = 0 then
    Print("\n[GREEN] all ", test_count, " unit generators detected non-trivially ",
          "by the 8-EA + D_8 + Q_8 family.\n");
    QuitGap(0);
else
    Print("\n[RED] ", n_fail, " generators failed (all branches zero):\n  ",
          failures, "\n");
    QuitGap(1);
fi;
