# research_tr_h_finer_invariant.g  --  empirical study for issue #456.
#
# Goal: identify a *finer-than-BRW* invariant of an E_+(m)-conjugacy
# class that determines `Tr(T_h | Omega_0)`.  Background:
#
#   * PR #448 disproved the (BRW-equivariant => 4-value) claim by
#     exhibiting at m=3 a sigma2 BRW orbit on which `Tr(T_h)` takes
#     both values 0 and 8, and a sigma_1sigma_2 orbit on which it
#     takes -4 and 4.  Tr is a class function of E_+(m) but NOT
#     BRW(m)-invariant.
#
#   * If a finer invariant exists, K-4b m=7 could replace its
#     ~16385 per-h trace evaluations in
#     `BuildKRRSpectralCharactersSparse` by a constant-time lookup.
#
# Strategy:
#   1. Build the per-h trace context via `_BuildTraceCtx` and the
#      Gauss-sum context via `_BuildGaussCtx`.  Extract the structural
#      invariants computed inside (kerLen, nDimAn, nDimSp, nDimND,
#      base_val, Q, t_rad, F_mat).
#
#   2. Compute additional invariants the Gauss-sum analysis depends on:
#        - phi(c_0) (the constant offset on the affine subspace M_h)
#        - dim W_h (the dimension of the kernel space M_h / c_0)
#        - Arf invariant of Q_psi
#        - radical dimension of Q_psi
#      These together with `base_val = 2^(kerLen - nDimND)` determine
#      `Tr(T_h | Omega_0)` via
#         Tr = base_val * (-1)^{phi(c_0)} * (-1)^{Arf(Q_psi)}
#              * 2^{|Rad(Q_psi)| + dim<Bn>/2}
#      (or 0 if the affine system is infeasible / Q_psi non-null on
#      its radical).
#
#   3. Tabulate over all E_+(3) conjugacy class reps; check what
#      MINIMAL combination of invariants determines Tr.
#
# Output: prints a TSV-like dump of per-class invariants + Tr values,
# plus a summary of which (orbit_type, candidate_invariant_tuple)
# combinations are constant.  Saves a .g manifest into the research
# subdir for later post-processing.
#
# Run (from extraspecial_orbifolds/scripts/):
#     gap -q -b -o 8g -c \
#       'MPARAM := 3; Read("research/research_tr_h_finer_invariant.g");' \
#       > /tmp/tr_finer_invariant_m3.log 2>&1
#
# For m=5 set MPARAM := 5 instead.  m=5 takes ~10-15 min wall.

SetInfoLevel(InfoWarning, 1);

# ------- Locate and load deps relative to this file. -------
_self_path := INPUT_FILENAME();;
if _self_path = fail or _self_path = "stream" then
    Error("research_tr_h_finer_invariant.g: INPUT_FILENAME() is fail; ",
          "please Read() this script with an absolute path.");
fi;
_basename := "research_tr_h_finer_invariant.g";;
_self_dir := _self_path{[1..Length(_self_path) - Length(_basename) - 1]};;
_scripts_dir := _self_dir{[1..Length(_self_dir) - Length("/research")]};;
ChangeDirectoryCurrent(_scripts_dir);
Print("[research] cwd set to ", _scripts_dir, "\n");

Read("bw_lattice.g");
Read("em_construction.g");
Read("twisted_group_algebra.g");
Read("qforms_f2.g");
Read("defect_rep_minus_id.g");
Read("defect_rep_minus_id_optim.g");
Read("untwisted_modular_data.g");
Read("krr_spectral_characters.g");
Read("krr_spectral_characters_sparse.g");

if not IsBound(MPARAM) then
    MPARAM := 3;
fi;
m := MPARAM;;
n := 2^m;;
k := n / 2;;

Print("\n================================================================\n");
Print("  research: finer-than-BRW invariant for Tr(T_h | Omega_0)\n");
Print("  m = ", m, ", n = 2^m = ", n, ", k = n/2 = ", k, "\n");
Print("================================================================\n");

# Reset caches to make sure we measure fresh per-h timing.
ResetSparseTraceCache();;
ResetTraceHCache();;
ResetGaussCtxCache();;

# ------------- Build E_+(m) + central class index. --------------
G := EmUnimodGroup(m);;
z := -IdentityMat(n);;
Print("[research] Building simple index ...\n");
t0 := Runtime();;
if m >= 5 and IsBoundGlobal("BuildSimpleIndexEPlusClosedForm") then
    idx := BuildSimpleIndexEPlusClosedForm(m);
else
    idx := BuildSimpleIndex(G);
fi;;
Print("[research]   done in ", (Runtime() - t0) / 1000.0,
      " s. |G| = ", idx.order,
      ", num classes = ", Length(idx.classes), "\n");

# Central class index.
i_central := PositionProperty(idx.reps, r -> r = z);;
if i_central = fail then
    Error("research: could not find central class -I in idx.");
fi;
Print("[research] Central class index = ", i_central, "\n");

cls_data := CentraliserClassData(idx, i_central);;
num_C := cls_data.num;;
Print("[research] C_G(-I) has ", num_C, " conjugacy classes ",
      "(expected 2^(2m)+1 = ", 2^(2*m) + 1, ")\n");

class_types := _SparseClassifyEmBRWTypes(cls_data.classes);;

# --------- Per-h invariant + trace extraction. -----------
# For each class j (1..num_C) we compute:
#   ord, type, |class|,
#   kerLen, nDimAn, nDimSp, nDimND,
#   t_rad_weight,   (Hamming weight of t_rad)
#   feas_rank,      (= rank of F_mat over F_2)
#   bt_rad_rank,    (= rank of BT_radmat over F_2)
#   dimW,           (= dim of M_h - 1 affine subspace == kernel of joint)
#   c_0_weight,     (= Hamming weight of c_0 over F_2^k)
#   phi_c0,         (= 0/1)
#   Q_rank,         (= rank of Q + Q^T over F_2)
#   Q_psi_rank,     (= rank of (Q_psi + Q_psi^T))
#   arf_Q_psi,      (= Arf of Q_psi)
#   gauss_sum,      (= the integer returned by _F2_QuadGaussSum(Q_psi))
#   Tr(T_h)         (= integer)
#
# Notes:
#   * "rank" over F_2 of a square matrix M can be computed by row-reducing
#     M directly and counting non-zero rows; we use the existing
#     `F2_LeftReduceRow` if present, else a small inline RREF.

# Inline F_2 rank function.
_F2_Rank := function(M)
    local r, A, c, i, j;
    if Length(M) = 0 then return 0; fi;
    A := List(M, ShallowCopy);
    A := A * Z(2)^0;
    ConvertToMatrixRep(A, GF(2));
    r := 1;
    for c in [1..Length(A[1])] do
        if r > Length(A) then break; fi;
        i := r;
        while i <= Length(A) and IsZero(A[i][c]) do i := i + 1; od;
        if i > Length(A) then continue; fi;
        if i <> r then A{[r, i]} := A{[i, r]}; fi;
        for j in [1..Length(A)] do
            if j <> r and not IsZero(A[j][c]) then
                AddRowVector(A[j], A[r]);
            fi;
        od;
        r := r + 1;
    od;
    return r - 1;
end;;

# Hamming weight on a 0/1 vector.
_Weight := function(v)
    local i, w;
    w := 0;
    for i in [1..Length(v)] do
        if v[i] mod 2 = 1 then w := w + 1; fi;
    od;
    return w;
end;;

# Run the Gauss-sum machinery (TraceOnOmega0Gauss-like) to extract the
# intermediate invariants alongside the final trace.
_ExtractInvariants := function(h, m)
    local tctx, gctx, joint_A, joint_b, sol, c_0, B_W, dimW, phi_c0,
          Q, Q_sym, L_y, Q_psi, BWQ, BW_QT_BWT, dimAn, dimSp, dimND,
          base_val, gsum, tr, B_psi, rad_q_psi, qval_rad,
          arf, sign, sympBasis, halfND, dimBn, basis_ambient,
          Qval_e, Qval_f, i, B0, Bd, Bn, B_nd;
    tctx := _BuildTraceCtx(h, m);
    gctx := _BuildGaussCtx(h, m);
    dimAn := tctx.sht.nDimAn;
    dimSp := tctx.sht.nDimSp;
    dimND := tctx.sht.nDimND;
    base_val := gctx.base_val;
    if Length(gctx.F_mat) = 0 and Length(gctx.BT_radmat) = 0 then
        c_0 := List([1..k], i -> 0);
        B_W := IdentityMat(k);
    else
        joint_A := Concatenation(gctx.F_mat, gctx.BT_radmat);
        joint_b := Concatenation(List([1..Length(gctx.F_mat)], i -> 0),
                                  gctx.t_rad);
        sol := _F2_AffineSolveCols(joint_A, joint_b);
        if sol.particular = fail then
            # Infeasible: Tr = 0; package up early.
            return rec(
                ord := Order(h), type := fail,
                kerLen := tctx.kerLen,
                nDimAn := dimAn, nDimSp := dimSp, nDimND := dimND,
                t_rad_weight := _Weight(gctx.t_rad),
                feas_rank := _F2_Rank(gctx.F_mat),
                bt_rad_rank := _F2_Rank(gctx.BT_radmat),
                dimW := -1,
                c_0_weight := -1,
                phi_c0 := -1,
                Q_rank := _F2_Rank((gctx.Q + TransposedMat(gctx.Q)) mod 2),
                Q_psi_rank := -1,
                arf_Q_psi := -1,
                gauss_sum := 0,
                base_val := base_val,
                Tr := 0,
                infeasible := true
            );
        fi;
        c_0 := sol.particular;
        B_W := sol.kerBasis;
    fi;
    dimW := Length(B_W);
    Q := gctx.Q;
    phi_c0 := QFormEval(Q, c_0);
    if dimW = 0 then
        # Single point.
        if phi_c0 = 0 then tr := base_val; else tr := - base_val; fi;
        return rec(
            ord := Order(h), type := fail,
            kerLen := tctx.kerLen,
            nDimAn := dimAn, nDimSp := dimSp, nDimND := dimND,
            t_rad_weight := _Weight(gctx.t_rad),
            feas_rank := _F2_Rank(gctx.F_mat),
            bt_rad_rank := _F2_Rank(gctx.BT_radmat),
            dimW := dimW,
            c_0_weight := _Weight(c_0),
            phi_c0 := phi_c0,
            Q_rank := _F2_Rank((Q + TransposedMat(Q)) mod 2),
            Q_psi_rank := 0,
            arf_Q_psi := 0,
            gauss_sum := 1,
            base_val := base_val,
            Tr := tr,
            infeasible := false
        );
    fi;
    Q_sym := (Q + TransposedMat(Q)) mod 2;
    L_y := F2_VMul(F2_VMul(c_0, Q_sym), F2_Trans(B_W));
    BWQ := F2_Mul(B_W, Q);
    BW_QT_BWT := F2_Mul(BWQ, F2_Trans(B_W));
    Q_psi := MutableCopyMat(BW_QT_BWT);
    for i in [1..dimW] do
        Q_psi[i][i] := (Q_psi[i][i] + L_y[i]) mod 2;
    od;
    # Compute Arf invariant ourselves to expose it as an invariant.
    # (mirror of _F2_QuadGaussSum)
    B0 := List([1..dimW], i -> List([1..dimW], j -> 0));
    for i in [1..dimW] do
        for sympBasis in [1..dimW] do
            if i <> sympBasis then
                B0[i][sympBasis] :=
                    (Q_psi[i][sympBasis] + Q_psi[sympBasis][i]) mod 2;
            fi;
        od;
    od;
    Bd := F2LeftNullspace(B0);
    rad_q_psi := Length(Bd);
    # Q|radical zero check (else Arf undefined => gauss=0).
    qval_rad := 0;
    for i in [1..rad_q_psi] do
        if QFormEval(Q_psi, Bd[i]) = 1 then qval_rad := 1; fi;
    od;
    if qval_rad = 1 then
        gsum := 0;
        arf := -1;
    else
        if rad_q_psi = dimW then
            gsum := 2 ^ dimW;
            arf := 0;
        else
            Bn := F2ComplementStandardBasis(Bd, dimW);
            dimBn := Length(Bn);
            B_nd := F2_Mul(F2_Mul(Bn, B0), F2_Trans(Bn));
            for i in [1..dimBn] do B_nd[i][i] := 0; od;
            sympBasis := _F2_FastSymplecticBasis(B_nd);
            halfND := dimBn / 2;
            basis_ambient := List(sympBasis, row -> F2_VMul(row, Bn));
            arf := 0;
            for i in [1..halfND] do
                Qval_e := QFormEval(Q_psi, basis_ambient[i]);
                Qval_f := QFormEval(Q_psi, basis_ambient[halfND + i]);
                arf := (arf + Qval_e * Qval_f) mod 2;
            od;
            if arf = 0 then sign := 1; else sign := -1; fi;
            gsum := sign * 2 ^ (rad_q_psi + halfND);
        fi;
    fi;
    if gsum = 0 then
        tr := 0;
    elif phi_c0 = 1 then
        tr := - base_val * gsum;
    else
        tr := base_val * gsum;
    fi;
    return rec(
        ord := Order(h), type := fail,
        kerLen := tctx.kerLen,
        nDimAn := dimAn, nDimSp := dimSp, nDimND := dimND,
        t_rad_weight := _Weight(gctx.t_rad),
        feas_rank := _F2_Rank(gctx.F_mat),
        bt_rad_rank := _F2_Rank(gctx.BT_radmat),
        dimW := dimW,
        c_0_weight := _Weight(c_0),
        phi_c0 := phi_c0,
        Q_rank := _F2_Rank(Q_sym),
        Q_psi_rank := dimW - rad_q_psi,
        arf_Q_psi := arf,
        gauss_sum := gsum,
        base_val := base_val,
        Tr := tr,
        infeasible := false
    );
end;;

# Per-class loop.
Print("\n[research] Extracting per-class invariants ...\n");
t0 := Runtime();;
data := [];;
for j in [1..num_C] do
    h := cls_data.reps[j];
    inv := _ExtractInvariants(h, m);
    inv.type := class_types[j];
    inv.class_size := cls_data.sizes[j];
    inv.class_idx := j;
    # Cross-check Tr against the ground-truth Tr.
    if m <= 5 then
        inv.Tr_check := TraceOnOmega0Batch(h, m);
        if inv.Tr <> inv.Tr_check then
            Print("[research]   WARN: class ", j, " Tr extract = ",
                  inv.Tr, " but TraceOnOmega0Batch = ", inv.Tr_check, "\n");
        fi;
    else
        # m=7: rely on the Gauss-sum path itself.
        inv.Tr_check := inv.Tr;
    fi;
    Add(data, inv);
    if j mod (Maximum(1, QuoInt(num_C, 20))) = 0 or j = num_C then
        Print("[research]   ", j, " / ", num_C, " classes processed",
              " (cum wall = ", (Runtime() - t0) / 1000.0, " s)\n");
    fi;
od;;

Print("[research] Per-class extraction wall: ",
      (Runtime() - t0) / 1000.0, " s\n");

# ---------------------- Reporting ------------------------
Print("\n========= Per-class invariant table (CSV) =========\n");
Print("idx,type,ord,class_size,",
      "kerLen,nDimAn,nDimSp,nDimND,t_rad_weight,",
      "feas_rank,bt_rad_rank,dimW,c_0_weight,phi_c0,",
      "Q_rank,Q_psi_rank,arf_Q_psi,gauss_sum,base_val,Tr,infeasible\n");
for inv in data do
    Print(inv.class_idx, ",", inv.type, ",", inv.ord, ",",
          inv.class_size, ",",
          inv.kerLen, ",", inv.nDimAn, ",", inv.nDimSp, ",", inv.nDimND, ",",
          inv.t_rad_weight, ",", inv.feas_rank, ",", inv.bt_rad_rank, ",",
          inv.dimW, ",", inv.c_0_weight, ",", inv.phi_c0, ",",
          inv.Q_rank, ",", inv.Q_psi_rank, ",", inv.arf_Q_psi, ",",
          inv.gauss_sum, ",", inv.base_val, ",", inv.Tr, ",",
          inv.infeasible, "\n");
od;

# --------- Aggregate: distinct Tr values per BRW type. ---------
Print("\n========= Distinct Tr values per BRW orbit type =========\n");
distinct_per_type := rec();;
for inv in data do
    if not IsBound(distinct_per_type.(inv.type)) then
        distinct_per_type.(inv.type) := [];
    fi;
    AddSet(distinct_per_type.(inv.type), inv.Tr);
od;
for tnm in SortedList(RecNames(distinct_per_type)) do
    Print("  ", tnm, " (", Number(data, x -> x.type = tnm),
          " classes) : Tr in ", distinct_per_type.(tnm), "\n");
od;

# --------- Aggregate: split sigma2 / sigma_1sigma_2 by Tr. ---------
Print("\n========= Sigma2 / sigma_1sigma_2 split by Tr value =========\n");
for tnm in ["sigma2", "sigma_1sigma_2"] do
    if not IsBound(distinct_per_type.(tnm)) then continue; fi;
    Print("--- ", tnm, " ---\n");
    for trval in distinct_per_type.(tnm) do
        Print("  Tr = ", trval, "\n");
        Print("    classes: ",
              Filtered([1..Length(data)],
                       i -> data[i].type = tnm and data[i].Tr = trval),
              "\n");
        # For each (kerLen, nDimAn, nDimSp, nDimND, phi_c0, arf_Q_psi, ...)
        # signature, show counts.
        bucket := rec();
        for inv in data do
            if inv.type = tnm and inv.Tr = trval then
                key := Concatenation(
                    "(kL=", String(inv.kerLen),
                    ",An=", String(inv.nDimAn),
                    ",Sp=", String(inv.nDimSp),
                    ",ND=", String(inv.nDimND),
                    ",dimW=", String(inv.dimW),
                    ",phi=", String(inv.phi_c0),
                    ",arf=", String(inv.arf_Q_psi),
                    ",gs=", String(inv.gauss_sum), ")");
                if not IsBound(bucket.(key)) then
                    bucket.(key) := 0;
                fi;
                bucket.(key) := bucket.(key) + 1;
            fi;
        od;
        for key in SortedList(RecNames(bucket)) do
            Print("    signature ", key, " count=", bucket.(key), "\n");
        od;
    od;
od;

# --------- Predictive: does (type, dim_invariants_tuple) determine Tr? ---------
Print("\n========= Predictive test: does (type, kL, An, Sp, ND, phi_c0, arf) determine Tr? =========\n");
predictor_buckets := rec();;
for inv in data do
    key := Concatenation(
        inv.type, "|kL=", String(inv.kerLen),
        "|An=", String(inv.nDimAn),
        "|Sp=", String(inv.nDimSp),
        "|ND=", String(inv.nDimND),
        "|phi=", String(inv.phi_c0),
        "|arf=", String(inv.arf_Q_psi));
    if not IsBound(predictor_buckets.(key)) then
        predictor_buckets.(key) := [];
    fi;
    AddSet(predictor_buckets.(key), inv.Tr);
od;
multi := [];;
for key in RecNames(predictor_buckets) do
    if Length(predictor_buckets.(key)) > 1 then
        Add(multi, key);
    fi;
od;
Print("# of (type, kL, An, Sp, ND, phi_c0, arf) buckets: ",
      Length(RecNames(predictor_buckets)), "\n");
Print("# of buckets with multiple Tr values: ", Length(multi), "\n");
if Length(multi) = 0 then
    Print(">>> SUCCESS: (type, kerLen, nDimAn, nDimSp, nDimND, phi_c0, arf_Q_psi)\n",
          ">>> determines Tr.\n");
else
    Print(">>> Buckets with multiple Tr values:\n");
    for key in multi do
        Print("  ", key, " => Tr in ", predictor_buckets.(key), "\n");
    od;
fi;

# Even tighter test: does (type, phi_c0, arf, base_val, |W|) determine Tr?
# That's equivalent to: the formula Tr = base_val * (-1)^phi * (-1)^arf * 2^(|R|+|S|/2)
# should reproduce Tr exactly.
Print("\n========= Closed-form formula sanity check =========\n");
ok := 0; mismatch := 0;;
for inv in data do
    if inv.infeasible then
        if inv.Tr = 0 then ok := ok + 1; else mismatch := mismatch + 1; fi;
        continue;
    fi;
    if inv.gauss_sum = 0 then
        if inv.Tr = 0 then ok := ok + 1; else mismatch := mismatch + 1; fi;
        continue;
    fi;
    predicted := inv.base_val * inv.gauss_sum;
    if inv.phi_c0 = 1 then predicted := - predicted; fi;
    if predicted = inv.Tr then
        ok := ok + 1;
    else
        mismatch := mismatch + 1;
        Print("  MISMATCH class ", inv.class_idx,
              ": predicted ", predicted, " vs Tr ", inv.Tr, "\n");
    fi;
od;
Print("Closed-form sanity: ok = ", ok, " / ", Length(data),
      "; mismatch = ", mismatch, "\n");

# --------- Save manifest. -----------
out_dir := Filename(DirectoryCurrent(),
    Concatenation("research_tr_h_m", String(m)));
Exec(Concatenation("mkdir -p ", out_dir));
manifest_path := Concatenation(out_dir, "/manifest.g");

stream := OutputTextFile(manifest_path, false);;
SetPrintFormattingStatus(stream, false);;
PrintTo(stream, "# research/research_tr_h_finer_invariant.g manifest\n");
PrintTo(stream, "# m = ", m, ", num_classes = ", Length(data), "\n");
PrintTo(stream, "research_tr_h_data := [\n");
for inv in data do
    PrintTo(stream, "    rec(",
            "class_idx := ", inv.class_idx,
            ", type := \"", inv.type, "\"",
            ", ord := ", inv.ord,
            ", class_size := ", inv.class_size,
            ", kerLen := ", inv.kerLen,
            ", nDimAn := ", inv.nDimAn,
            ", nDimSp := ", inv.nDimSp,
            ", nDimND := ", inv.nDimND,
            ", t_rad_weight := ", inv.t_rad_weight,
            ", feas_rank := ", inv.feas_rank,
            ", bt_rad_rank := ", inv.bt_rad_rank,
            ", dimW := ", inv.dimW,
            ", c_0_weight := ", inv.c_0_weight,
            ", phi_c0 := ", inv.phi_c0,
            ", Q_rank := ", inv.Q_rank,
            ", Q_psi_rank := ", inv.Q_psi_rank,
            ", arf_Q_psi := ", inv.arf_Q_psi,
            ", gauss_sum := ", inv.gauss_sum,
            ", base_val := ", inv.base_val,
            ", Tr := ", inv.Tr,
            ", infeasible := ", inv.infeasible,
            "),\n");
od;
PrintTo(stream, "];;\n");
CloseStream(stream);
Print("\n[research] Wrote manifest to ", manifest_path, "\n");

QUIT_GAP(0);
