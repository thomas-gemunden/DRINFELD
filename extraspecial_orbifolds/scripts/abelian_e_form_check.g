# abelian_e_form_check.g  --  K-4a-T3 (issue #195).
#
# # Purpose.
#
# Decide whether a 3-cocycle alpha on the maximal elementary abelian
# E = (Z/2)^(m+1) <= E_+(m) is a coboundary -- i.e. whether
#     [alpha] = 0   in   H^3(E; U(1)).
#
# # Background.
#
# For E_+(m) of plus type, the rank-(m+1) maximal elementary abelian
# E has H^3(E; U(1)) = H^4(E; Z) = (Z/2)^{C(m+3, 3) - (m+1)}.  KRR's
# construction yields a family of 1-cochains {eps_a : C_E(a) -> U(1)},
# a in E, that trivialise the transgressed 2-cocycles beta_a (the c_a
# from the transgression kernel of #44).  Since E is abelian,
# C_E(a) = E.
#
# This file implements a self-contained predicate
#
#     ClassifyOn3CocycleE(alpha, E, m)
#         -> rec( trivial := bool, coboundary_witness := beta or fail )
#
# accepting alpha as a callable (a, b, c) -> Z/m.  Internally, it
# tabulates alpha on E^3, builds the bar coboundary matrix
#     delta_2 : C^2(E; Z) -> C^3(E; Z),
# and decides whether alpha is in the image of delta_2 mod m.
#
# When m is prime (the elementary abelian Z_2^r case has m = 2), we reduce
# delta_2 mod m and solve over GF(m) -- orders of magnitude faster than
# the integer SolutionIntMat path for r >= 4.  When m is composite we
# augment delta_2 by [-m * I] and solve over Z via SolutionIntMat.
#
# The thin wrapper
#
#     ClassifyOnAbelianE(epsilon_data_E, E)
#
# takes the KRR eps_a data (the deliverable signature from issue #195)
# and currently returns a deferral stub: reconstructing alpha from
# {eps_a} requires the KRR per-class trivialisation interface from
# K-4a-T5b (issue not yet merged at time of writing).  Once K-4a-T5b
# lands, the alpha-from-eps reconstruction can be slotted in here and
# this wrapper becomes a one-line caller of ClassifyOn3CocycleE.
#
# # API.
#
#   ClassifyOn3CocycleE(alpha, E, m)
#       alpha : callable (a, b, c) -> integer (interpreted mod m)
#       E     : finite abelian 2-group (GAP group)
#       m     : modulus (exponent of H^3(E; U(1)); use 2 for Z/2^r)
#       Returns rec(
#           trivial            := bool,
#           coboundary_witness := beta_vec (length |E|^2 mod m) or fail,
#           is_cocycle         := bool   -- sanity check on input alpha
#       )
#
#   ClassifyOnAbelianE(epsilon_data_E, E)
#       Stub returning rec( trivial := fail, status := "deferred" )
#       pending the K-4a-T5b alpha-from-eps reconstruction.
#
# # Conventions.
#
# Bar coboundary on a 2-cochain beta : G^2 -> Z is
#   (delta_2 beta)(g, h, k) = beta(h, k) - beta(gh, k) + beta(g, hk)
#                              - beta(g, h).
# Our BarCoboundaryMatrixZ (in integrate_to_3cocycle.g) builds exactly
# this matrix with rows indexed by 3-tuples and columns by 2-tuples.
#
# # Dependencies.
#
#   * integrate_to_3cocycle.g (for BarCoboundaryMatrixZ, _I3C_TupleIndexer,
#     TabulateCochainZ).  Loaded lazily via INPUT_FILENAME() pattern.
#   * transgression_kernel.g + src/modular_data.g for the supporting
#     SetupCohomology3 used by the tests.
#
# # Tractability (with the GF(2) fast path).
#
# For E = (Z/2)^r with r = m+1:
#   r = 3 (m=2):  |E| = 8;   |E|^3 = 512, |E|^2 = 64.   ~0.1 s.
#   r = 4 (m=3):  |E| = 16;  |E|^3 = 4096, |E|^2 = 256. ~0.3 s.
#   r = 5 (m=4):  |E| = 32;  |E|^3 = 32768, |E|^2 = 1024. seconds.
#   r = 6 (m=5):  |E| = 64;  |E|^3 = 262144, |E|^2 = 4096. ~minutes.
#   r = 8 (m=7):  |E| = 256; |E|^3 = ~1.7e7. likely needs a smarter
#                            sparse solver.
#
# The cocycle verification _AEF_VerifyCocycleMod uses a precomputed
# multiplication table to keep the |E|^4 sanity-check cheap.

# ---- Locate sibling modules (INPUT_FILENAME pattern) -------------------

_aef_loaded_i3c := IsBoundGlobal("BarCoboundaryMatrixZ");;
if not _aef_loaded_i3c then
    _aef_self := INPUT_FILENAME();;
    if _aef_self <> fail and _aef_self <> "stream" then
        _aef_dir := _aef_self{[1..Length(_aef_self)
            - Length("/abelian_e_form_check.g")]};;
        _aef_cand := Concatenation(_aef_dir, "/integrate_to_3cocycle.g");;
        if IsExistingFile(_aef_cand) then
            Read(_aef_cand);
            _aef_loaded_i3c := true;
        fi;
    fi;
    if not _aef_loaded_i3c then
        for _aef_p in [ "integrate_to_3cocycle.g",
                        "extraspecial_orbifolds/scripts/integrate_to_3cocycle.g",
                        "scripts/integrate_to_3cocycle.g" ] do
            if not _aef_loaded_i3c and IsExistingFile(_aef_p) then
                Read(_aef_p);
                _aef_loaded_i3c := true;
            fi;
        od;
    fi;
fi;
if not _aef_loaded_i3c then
    Error("abelian_e_form_check.g: cannot locate integrate_to_3cocycle.g");
fi;

# ----------------------------------------------------------------------
# Local If_ helper (file-scoped, prefixed _AEF_ to avoid clobbering).
# ----------------------------------------------------------------------

_AEF_If := function(cond, a, b)
    if cond then return a; else return b; fi;
end;;

# ----------------------------------------------------------------------
# Tabulate a 3-cocycle alpha (callable) on E^3 into a length-|E|^3
# integer vector, with entries reduced mod m.
# ----------------------------------------------------------------------

_AEF_TabulateAlphaMod := function(E, alpha, m)
    local idx3, n_3, vec, row, args;
    idx3 := _I3C_TupleIndexer(E, 3);
    n_3 := idx3.size;
    vec := ListWithIdenticalEntries(n_3, 0);
    for row in [1..n_3] do
        args := idx3.of_idx(row);
        vec[row] := alpha(args[1], args[2], args[3]) mod m;
    od;
    return vec;
end;;

# ----------------------------------------------------------------------
# Verify alpha is a bar 3-cocycle mod m:
#   (delta_3 alpha)(g, h, k, l)
#     = alpha(h, k, l) - alpha(gh, k, l) + alpha(g, hk, l)
#       - alpha(g, h, kl) + alpha(g, h, k)
#     = 0   (mod m)
# for all (g, h, k, l) in E^4.
#
# Returns rec( ok := bool, violations := int ).
# ----------------------------------------------------------------------

_AEF_VerifyCocycleMod := function(E, alpha_vec, m)
    # Verify alpha (tabulated as alpha_vec in lex order on E^3) is a
    # bar 3-cocycle mod m using precomputed multiplication table.
    local idx3, elts, n, mult_tab, violations, ig, ih, ik, il, ngh, nhk,
          nkl, val, v_hkl, v_ghkl, v_g_hk_l, v_g_h_kl, v_g_h_k;
    idx3 := _I3C_TupleIndexer(E, 3);
    elts := idx3.elts;
    n := Length(elts);
    # Precompute multiplication table: mult_tab[i][j] = Position(elts, elts[i] * elts[j]).
    mult_tab := List([1..n], i ->
        List([1..n], j -> Position(elts, elts[i] * elts[j])));
    violations := 0;
    for ig in [1..n] do
        for ih in [1..n] do
            ngh := mult_tab[ig][ih];
            for ik in [1..n] do
                nhk := mult_tab[ih][ik];
                for il in [1..n] do
                    nkl := mult_tab[ik][il];
                    # alpha(h, k, l)
                    v_hkl := alpha_vec[((ih - 1) * n + ik - 1) * n + il];
                    # alpha(g*h, k, l)
                    v_ghkl := alpha_vec[((ngh - 1) * n + ik - 1) * n + il];
                    # alpha(g, h*k, l)
                    v_g_hk_l := alpha_vec[((ig - 1) * n + nhk - 1) * n + il];
                    # alpha(g, h, k*l)
                    v_g_h_kl := alpha_vec[((ig - 1) * n + ih - 1) * n + nkl];
                    # alpha(g, h, k)
                    v_g_h_k := alpha_vec[((ig - 1) * n + ih - 1) * n + ik];
                    val := v_hkl - v_ghkl + v_g_hk_l - v_g_h_kl + v_g_h_k;
                    if val mod m <> 0 then
                        violations := violations + 1;
                    fi;
                od;
            od;
        od;
    od;
    return rec( ok := violations = 0, violations := violations,
                total := n^4 );
end;;

# ----------------------------------------------------------------------
# Core triviality check.
#
# Given:
#   alpha     : callable (a, b, c) -> int (cocycle mod m on E)
#   E         : finite abelian 2-group
#   m         : modulus
#
# Returns:
#   rec(
#     trivial            := bool,         # is [alpha] = 0 in H^3(E; Z/m)?
#     coboundary_witness := list or fail, # length-|E|^2 Z/m vector beta
#                                         #   with delta_2 beta = alpha mod m
#     is_cocycle         := bool,         # alpha verified as 3-cocycle
#     cocycle_violations := int,          # diagnostic
#     E                  := E,
#     m                  := m
#   )
#
# Method.  Let BC_2 be the bar coboundary matrix
# delta_2 : C^2(E; Z) -> C^3(E; Z) of shape (|E|^3) x (|E|^2).
#
# m prime (the Z_2^r hot path):
#   Reduce BC_2 mod m to a matrix over GF(m).  SolutionMat then decides
#   alpha_vec in image(delta_2 mod m) via Gaussian elimination.
#
# m composite:
#   Solve BC_2 * beta + m * gamma = alpha_vec over Z.  Equivalently the
#   augmented matrix [BC_2 | -m*I] times [beta; gamma]^T = alpha_vec,
#   which SolutionIntMat decides.
# ----------------------------------------------------------------------

ClassifyOn3CocycleE := function(alpha, E, m)
    local n, alpha_vec, BC_2, n_rows, n_cols, sol, beta_int, beta_mod,
          check_rec, trivial, witness, F, BC_2_F, alpha_vec_F, M, i, j;

    if not IsAbelian(E) then
        Error("ClassifyOn3CocycleE: E must be abelian; got ", E);
    fi;
    if not IsFinite(E) then
        Error("ClassifyOn3CocycleE: E must be finite");
    fi;
    if not (IsInt(m) and m >= 2) then
        Error("ClassifyOn3CocycleE: m must be an integer >= 2; got ", m);
    fi;

    n := Order(E);

    # ---- Tabulate alpha on E^3 ---------------------------------------
    # Order matters: tabulate FIRST, then verify against the table so the
    # cocycle check costs only |E|^4 list lookups, not |E|^4 * 5 alpha calls.
    alpha_vec := _AEF_TabulateAlphaMod(E, alpha, m);

    # ---- Sanity-check input alpha is a bar 3-cocycle mod m ------------
    check_rec := _AEF_VerifyCocycleMod(E, alpha_vec, m);

    # ---- Build delta_2 : C^2 -> C^3 over Z ---------------------------
    BC_2 := BarCoboundaryMatrixZ(E, 2);
    n_rows := Length(BC_2);            # = n^3
    n_cols := Length(BC_2[1]);         # = n^2

    if IsPrimeInt(m) then
        # ---- Fast path: solve over GF(m) ---------------------------------
        # When the exponent m of H^3(E; U(1)) is prime, we can reduce
        # delta_2 mod m to a matrix over the field GF(m) and use Gaussian
        # elimination (orders of magnitude faster than integer SolutionIntMat
        # on the augmented matrix). For E elementary abelian 2-group,
        # m = 2 always, so this is the hot path.
        F := GF(m);
        BC_2_F := List(BC_2, row -> List(row, x -> (x mod m) * One(F)));
        alpha_vec_F := List(alpha_vec, x -> (x mod m) * One(F));
        # SolutionMat(M, v) returns x with x * M = v.  We want beta with
        # beta * TransposedMat(BC_2_F) = alpha_vec_F, i.e.
        #     BC_2_F * beta^T = alpha_vec_F^T.
        sol := SolutionMat(TransposedMat(BC_2_F), alpha_vec_F);
        trivial := sol <> fail;
        if trivial then
            beta_mod := List(sol, x -> IntFFE(x));
            witness := beta_mod;
        else
            witness := fail;
        fi;
    else
        # ---- General path: integer-augmented solve over Z ------------------
        # Solve BC_2 * beta + m * gamma = alpha_vec over Z by inverting
        # the (n_rows) x (n_cols + n_rows) augmented matrix [BC_2 | -m * I].
        # SolutionIntMat(M^T, b) finds x with x * M^T = b, i.e. M * x^T = b.
        M := List([1..n_rows], i -> Concatenation(BC_2[i],
            List([1..n_rows], j -> _AEF_If(i = j, -m, 0))));
        sol := SolutionIntMat(TransposedMat(M), alpha_vec);
        trivial := sol <> fail;
        if trivial then
            beta_int := sol{[1..n_cols]};
            beta_mod := List(beta_int, x -> x mod m);
            witness := beta_mod;
        else
            witness := fail;
        fi;
    fi;

    return rec(
        trivial            := trivial,
        coboundary_witness := witness,
        is_cocycle         := check_rec.ok,
        cocycle_violations := check_rec.violations,
        E                  := E,
        m                  := m
    );
end;;

# ----------------------------------------------------------------------
# Stub: KRR-flavoured input (issue #195's deliverable signature).
#
# epsilon_data_E.epsilon(a, h) returns eps_a(h) in U(1) (as a Z/m
# integer-valued character of C_E(a) = E).
#
# Reconstructing alpha from {eps_a} requires KRR's per-class trivialisation
# interface from K-4a-T5b.  Until that lands, this routine documents the
# intent but defers the work.
# ----------------------------------------------------------------------

ClassifyOnAbelianE := function(epsilon_data_E, E)
    return rec(
        trivial      := fail,
        status       := "deferred",
        note         :=
"alpha-from-eps reconstruction is gated on K-4a-T5b (KRR per-class \
trivialisation interface). Use ClassifyOn3CocycleE(alpha, E, m) directly \
with an explicit 3-cocycle callable until K-4a-T5b lands.",
        E            := E,
        epsilon_data := epsilon_data_E
    );
end;;

Print("Loaded abelian_e_form_check.g (K-4a-T3, issue #195).\n");
