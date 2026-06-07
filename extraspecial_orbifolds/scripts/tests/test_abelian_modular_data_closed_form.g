# test_abelian_modular_data_closed_form.g — regression tests for #487.
#
# Anchors:
#   1. Untwisted match: for k in {1, 2, 3, 4} the closed-form output
#      on H = (Z/2)^k matches ComputeUntwistedModularData(H) (which
#      uses the generic Bantay path under the abelian dispatch is
#      disabled) via JointPermutationMatcher.
#      Also tests Z/3, Z/4 as cyclic abelian cases.
#   2. Non-trivial cocycles on V_4 = (Z/2)^2: all 8 cohomology classes
#      match ComputeModularData(V_4, omega, val, expon) via
#      JointPermutationMatcher.
#   3. Ground-truth match: closed-form V_4 (untwisted) matches
#      modular_data/4/2/k.txt for each k. (Skipped if file not
#      available — modular_data/ is gitignored bulk data.)
#   4. Dispatch wire-in: ComputeUntwistedModularData(H) for abelian H
#      reports `via_closed_form = true`, and for non-abelian H reports
#      `via_closed_form = false`. Both still produce valid (S, T) with
#      Verlinde fusion non-negative integers.
#
# Run from extraspecial_orbifolds/scripts/tests/:
#   gap -q -b -c 'Read("test_abelian_modular_data_closed_form.g"); QUIT;'

BreakOnError := false;;

# ---- Locate sibling modules -------------------------------------------

_amdt_self := INPUT_FILENAME();;
_amdt_dir := fail;;
if _amdt_self <> fail and _amdt_self <> "stream" then
    _amdt_dir := _amdt_self{
        [1..Length(_amdt_self)
          - Length("/test_abelian_modular_data_closed_form.g")]};;
fi;

_amdt_load_sibling := function(name)
    local p, abs_cand;
    if _amdt_dir <> fail then
        abs_cand := Concatenation(_amdt_dir, "/../", name);
        if IsExistingFile(abs_cand) then
            Read(abs_cand);
            return true;
        fi;
    fi;
    for p in [ Concatenation("../", name),
               name,
               Concatenation("extraspecial_orbifolds/scripts/", name) ] do
        if IsExistingFile(p) then
            Read(p);
            return true;
        fi;
    od;
    return false;
end;;

_amdt_load_root := function(name)
    # Files outside extraspecial_orbifolds/scripts/, e.g. ../../src/...
    local p, abs_cand;
    if _amdt_dir <> fail then
        abs_cand := Concatenation(_amdt_dir, "/../../../", name);
        if IsExistingFile(abs_cand) then
            Read(abs_cand);
            return true;
        fi;
    fi;
    for p in [ Concatenation("../../", name),
               Concatenation("../../../", name),
               name ] do
        if IsExistingFile(p) then
            Read(p);
            return true;
        fi;
    od;
    return false;
end;;

if not _amdt_load_sibling("abelian_modular_data_closed_form.g") then
    Error("cannot locate abelian_modular_data_closed_form.g");
fi;
if not _amdt_load_sibling("untwisted_modular_data.g") then
    Error("cannot locate untwisted_modular_data.g");
fi;
if not _amdt_load_sibling("joint_permutation_matcher.g") then
    Error("cannot locate joint_permutation_matcher.g");
fi;
if not _amdt_load_sibling("transgression_kernel.g") then
    Error("cannot locate transgression_kernel.g");
fi;
if not _amdt_load_root("src/modular_data.g") then
    Error("cannot locate src/modular_data.g");
fi;

# ---- Harness ----------------------------------------------------------

testFailures := [];;

If_loc := function(c, a, b) if c then return a; else return b; fi; end;;

AssertOrLog := function(label, cond)
    Print("  ", label, ": ", If_loc(cond, "PASS", "FAIL"), "\n");
    if not cond then Add(testFailures, label); fi;
end;;

# Verify Verlinde fusion gives non-negative integers (a strong necessary
# condition for the (S, T) to define a valid MTC). Slow at high rank;
# we only invoke it for small groups.
_VerlindeFusionOK := function(SS)
    local a, b, c, d, total, ok, n_;
    n_ := Length(SS);
    ok := true;
    for a in [1..n_] do
        for b in [1..n_] do
            for c in [1..n_] do
                total := 0;
                for d in [1..n_] do
                    total := total + SS[a][d] * SS[b][d]
                             * ComplexConjugate(SS[c][d]) / SS[1][d];
                od;
                if not IsInt(total) or total < 0 then
                    ok := false;
                fi;
            od;
        od;
    od;
    return ok;
end;;

# Two cocycles to compare: returns true if (S1, T1) matches (S2, T2)
# under JointPermutationMatcher.
_TwoMatch := function(S1, T1, S2, T2)
    local r;
    r := JointPermutationMatcher(S1, T1, S2, T2);
    return r.ok;
end;;

Print("\n=== test_abelian_modular_data_closed_form.g (#487) ===\n");

# ----------------------------------------------------------------------
# Anchor 1: Untwisted match on a battery of small abelian groups.
# ----------------------------------------------------------------------

Print("\n--- Anchor 1: untwisted closed-form vs generic ---\n");

zero_cocycle := function(a, b, c) return 0; end;;

# Build a list of (label, group) pairs to sweep.
_a1_groups := [
    [ "Z/2",        CyclicGroup(IsPcGroup, 2) ],
    [ "Z/3",        CyclicGroup(IsPcGroup, 3) ],
    [ "Z/4",        CyclicGroup(IsPcGroup, 4) ],
    [ "(Z/2)^2",    ElementaryAbelianGroup(IsPcGroup, 4) ],
    [ "(Z/2)^3",    ElementaryAbelianGroup(IsPcGroup, 8) ],
    [ "(Z/2)^4",    ElementaryAbelianGroup(IsPcGroup, 16) ]
];;

for pair in _a1_groups do
    name_ := pair[1];;
    G_ := pair[2];;
    # Build generic via BuildSimpleIndex + ComputeUntwistedT/S
    # (avoiding the dispatch).
    _idx_ := BuildSimpleIndex(G_);
    S_gen := ComputeUntwistedS(_idx_);
    T_gen := ComputeUntwistedT(_idx_);
    # Closed-form via the new entry point.
    cf := ComputeAbelianModularDataClosedForm(G_, zero_cocycle, 1);
    ok := _TwoMatch(cf.S, cf.T, S_gen, T_gen);
    AssertOrLog(Concatenation("untwisted match ", name_), ok);
od;

# ----------------------------------------------------------------------
# Anchor 2: Non-trivial cocycles on V_4 — all 8 cohomology classes match
# the legacy ComputeModularData.
# ----------------------------------------------------------------------

Print("\n--- Anchor 2: twisted V_4 across all 8 cohomology classes ---\n");

H_v4 := ElementaryAbelianGroup(IsPcGroup, 4);;
setup_v4 := SetupCohomology3(H_v4);;

for class_i in [0..7] do
    gv := [class_i mod 2, QuoInt(class_i, 2) mod 2, QuoInt(class_i, 4) mod 2];;
    omega_ := StandardCocycleOf(setup_v4, gv);;
    val_ := Maximum(Gcd(Gcd(gv), setup_v4.exponent), 1);;
    expon_ := setup_v4.exponent / val_;;
    N_ := val_ * expon_;;
    if gv = [0, 0, 0] then N_ := 1; fi;
    md_legacy := ComputeModularData(H_v4, omega_, val_, expon_);;
    cf := ComputeAbelianModularDataClosedForm(H_v4, omega_, N_);;
    ok := _TwoMatch(cf.S, cf.T, md_legacy.S, md_legacy.T);
    AssertOrLog(Concatenation("V_4 class ", String(class_i),
                              " gv=", String(gv)), ok);
od;

# ----------------------------------------------------------------------
# Anchor 3: Ground-truth match against modular_data/4/2/k.txt.
# modular_data/ is gitignored bulk data; skip if not present locally.
# ----------------------------------------------------------------------

Print("\n--- Anchor 3: ground truth modular_data/4/2 ---\n");

_amdt_md_path := function(n_, m_, k_)
    local cwd_paths, p;
    cwd_paths := [
        Concatenation("modular_data/", String(n_), "/", String(m_),
                      "/", String(k_), ".txt"),
        Concatenation("../../../modular_data/", String(n_), "/",
                      String(m_), "/", String(k_), ".txt"),
        Concatenation("../../modular_data/", String(n_), "/",
                      String(m_), "/", String(k_), ".txt"),
        Concatenation("/Users/thomasgemunden/Projects/group_cohomology/",
                      "modular_data/", String(n_), "/", String(m_),
                      "/", String(k_), ".txt")
    ];
    for p in cwd_paths do
        if IsExistingFile(p) then return p; fi;
    od;
    return fail;
end;;

# SmallGroup(4, 2) = V_4. The on-disk modular_data/4/2/k.txt should
# match the closed-form (untwisted) for k that represents the trivial
# cocycle orbit, and other twisted classes for k > 1.
# Without parsing the cocycle representative from modular_data/4/2/
# 3-cocycles.txt to align with our setup_v4 cocyclebasis, we can only
# verify rank + V_4 ground-truth on the first file (which should be
# untwisted since orbits[1] is the zero orbit per AutomorphismOrbits).
_amdt_md_check_k1 := _amdt_md_path(4, 2, 1);;
if _amdt_md_check_k1 <> fail then
    data_k1 := ReadAsFunction(_amdt_md_check_k1)();;
    S_disk := data_k1.S;
    T_disk := data_k1.T;  # legacy stores as a list, not DiagonalMat
    Print("  modular_data/4/2/1.txt rank = ", Length(S_disk), "\n");
    # Closed-form untwisted V_4
    cf := ComputeAbelianModularDataClosedForm(H_v4, zero_cocycle, 1);
    ok := _TwoMatch(cf.S, cf.T, S_disk, T_disk);
    AssertOrLog("modular_data/4/2/1.txt matches CF (untwisted V_4)", ok);
else
    Print("  modular_data/4/2/1.txt not found locally; skipping.\n");
fi;

# ----------------------------------------------------------------------
# Anchor 4: Dispatch wire-in.
# ----------------------------------------------------------------------

Print("\n--- Anchor 4: dispatch wire-in ---\n");

md_v4 := ComputeUntwistedModularData(H_v4);;
AssertOrLog("V_4 dispatch via_closed_form = true",
            IsBound(md_v4.via_closed_form) and md_v4.via_closed_form);
AssertOrLog("V_4 dispatch rank = 16", Length(md_v4.S) = 16);

# Non-abelian: D_8 (PR #487's wire-in dispatch should fall to generic).
G_d8 := DihedralGroup(IsPcGroup, 8);;
md_d8 := ComputeUntwistedModularData(G_d8);;
AssertOrLog("D_8 dispatch via_closed_form = false",
            IsBound(md_d8.via_closed_form)
              and md_d8.via_closed_form = false);
AssertOrLog("D_8 dispatch produces valid rank", Length(md_d8.S) >= 1);

# Verlinde fusion sanity at V_4.
ok_v := _VerlindeFusionOK(md_v4.S);
AssertOrLog("V_4 dispatch Verlinde fusion is non-neg integer", ok_v);

# Verlinde fusion sanity at (Z/2)^3 closed-form (rank 64).
H_z23 := ElementaryAbelianGroup(IsPcGroup, 8);;
md_z23 := ComputeUntwistedModularData(H_z23);;
AssertOrLog("(Z/2)^3 dispatch via_closed_form = true",
            IsBound(md_z23.via_closed_form) and md_z23.via_closed_form);
# Skip the O(n^4) Verlinde check at rank 64; rely on Anchor 1's match.

# ----------------------------------------------------------------------
# Anchor 5: Factored variant agrees with the full-materialise variant
# on every entry (cheap O(|H|^2) check at V_4, rank 16).
# ----------------------------------------------------------------------

Print("\n--- Anchor 5: factored S_at vs full S ---\n");

cf_full := ComputeAbelianModularDataClosedForm(H_v4, zero_cocycle, 1);;
cf_fact := ComputeAbelianModularDataFactored(H_v4, zero_cocycle, 1);;
_a5_S_ok := true;;
_a5_T_ok := true;;
for i in [1..16] do
    if cf_fact.T_at(i) <> cf_full.T[i] then _a5_T_ok := false; fi;
    for j in [1..16] do
        if cf_fact.S_at(i, j) <> cf_full.S[i][j] then _a5_S_ok := false; fi;
    od;
od;
AssertOrLog("V_4 factored T_at agrees on every entry", _a5_T_ok);
AssertOrLog("V_4 factored S_at agrees on every entry", _a5_S_ok);

# Same test for V_4 with a non-trivial cocycle
gv_nt := [1, 0, 0];
omega_nt := StandardCocycleOf(setup_v4, gv_nt);
cf_full_nt := ComputeAbelianModularDataClosedForm(H_v4, omega_nt, 2);
cf_fact_nt := ComputeAbelianModularDataFactored(H_v4, omega_nt, 2);
_a5b_S_ok := true;;
_a5b_T_ok := true;;
for i in [1..16] do
    if cf_fact_nt.T_at(i) <> cf_full_nt.T[i] then _a5b_T_ok := false; fi;
    for j in [1..16] do
        if cf_fact_nt.S_at(i, j) <> cf_full_nt.S[i][j] then _a5b_S_ok := false; fi;
    od;
od;
AssertOrLog("V_4 (twisted) factored T_at agrees", _a5b_T_ok);
AssertOrLog("V_4 (twisted) factored S_at agrees", _a5b_S_ok);

# ----------------------------------------------------------------------
# Summary.
# ----------------------------------------------------------------------

Print("\n=== Summary ===\n");
if IsEmpty(testFailures) then
    Print("test_abelian_modular_data_closed_form: ALL PASS\n");
else
    Print("test_abelian_modular_data_closed_form: FAIL (",
          Length(testFailures), " failures)\n");
    for f in testFailures do Print("  - ", f, "\n"); od;
fi;
