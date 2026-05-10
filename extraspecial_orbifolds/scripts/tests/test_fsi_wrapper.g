# test_fsi_wrapper.g
#
# Smoke tests for fsi_wrapper.g.  Per V-3 #47 the first must-pass is Q_8 with omega = 0
# at the identity class g = 1: we should recover the classical Frobenius-Schur indicators
# of the 5 irreducible characters of Q_8, namely  nu_2 = [+1, +1, +1, +1, -1]
# (four 1-dimensional real reps + the quaternionic 2-dimensional rep).
#
# Stage 2: all conjugacy classes of Q_8 at omega = 0 with m=2.
# Stage 3: the non-trivial H^3(Q_8; U(1)) cocycle at omega != 0 (m=2 only).

# --- locate the wrapper (do not chdir) ------------------------------------
fsiWrapper := fail;;
for fsiCand in [".", "..", "../..", "../../..", "../../../..",
                "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-v3"] do
    if IsExistingFile(Concatenation(fsiCand, "/extraspecial_orbifolds/scripts/fsi_wrapper.g")) then
        fsiWrapper := Concatenation(fsiCand, "/extraspecial_orbifolds/scripts/fsi_wrapper.g");
        break;
    fi;
od;;
if fsiWrapper = fail then
    Error("test_fsi_wrapper.g: could not locate extraspecial_orbifolds/scripts/fsi_wrapper.g");
fi;
Read(fsiWrapper);;


# --- helpers ---------------------------------------------------------------
fsiPass := 0;;
fsiFail := 0;;
fsiAssertEqual := function(label, actual, expected)
    if actual = expected then
        Print("  OK   ", label, "  =  ", actual, "\n");
        fsiPass := fsiPass + 1;
        return true;
    else
        Print("  FAIL ", label, "  actual=", actual, "  expected=", expected, "\n");
        fsiFail := fsiFail + 1;
        return false;
    fi;
end;;


# --- Stage 1: Q_8, omega = 0, identity class g = 1 -----------------------
Print("\n=== Stage 1: Q_8, omega = 0, g = 1 ===\n");
Q8 := SmallGroup(8, 4);;
fsiAssertEqual("Q_8 = SmallGroup(8,4) is quaternion group",
               StructureDescription(Q8), "Q8");

# Build a zero cocycle vector of the correct length so FSI_LiftIfHom takes
# the "already-lifted" branch and returns it unchanged mod n.
ctxQ8triv_R := ResolutionFiniteGroup(Q8, 4);;
ctxQ8triv_zero := ListWithIdenticalEntries(ctxQ8triv_R!.dimension(3), 0);;

ctxQ8triv := FSIContext(Q8, ctxQ8triv_zero);;
Print("  Q_8 trivial cocycle: exp = ", ctxQ8triv.exp,
      ", |G| = ", Size(ctxQ8triv.G),
      ", Exponent(G) = ", ctxQ8triv.groupExp, "\n");

# Identity class.  At g = 1, listG[Position(listG, 1)] is one(G).
one_Q8 := One(Q8);;
res_g1 := FSIAllAtClass(ctxQ8triv, one_Q8, 2);;
Print("  number of projective irreps at g=1: ", Size(res_g1.proj!.table), "\n");
Print("  nu_2 at g=1: ", res_g1.nu, "\n");

# Expected: 4 copies of +1 and 1 copy of -1 (the quaternionic rep), in some order.
fsiAssertEqual("nu_2 multiset at Q_8, omega=0, g=1",
               Collected(res_g1.nu), Collected([1, 1, 1, 1, -1]));

# Also double-check: dimensions (= chi(One(Gaa))) should be 1,1,1,1,2 in some order.
fsiQ8triv_dims := List(res_g1.proj!.table, chi -> One(res_g1.proj!.Gaa)^chi);;
Print("  dims at g=1: ", fsiQ8triv_dims, "\n");
fsiAssertEqual("dim multiset at Q_8, omega=0, g=1",
               Collected(fsiQ8triv_dims), Collected([1, 1, 1, 1, 2]));


# --- Stage 2: Q_8, omega = 0, all conjugacy classes ----------------------
Print("\n=== Stage 2: Q_8, omega = 0, all classes ===\n");
classes_Q8 := List(ConjugacyClasses(Q8), Representative);;
Print("  ", Size(classes_Q8), " conjugacy classes: ",
      List(classes_Q8, Order), " (orders)\n");

stage2_results := [];;
for stage2_g in classes_Q8 do
    stage2_res := FSIAllAtClass(ctxQ8triv, stage2_g, 2);;
    Print("  class order ", Order(stage2_g),
          ": ", Size(stage2_res.proj!.table), " irreps; nu_2 = ", stage2_res.nu, "\n");
    Add(stage2_results, stage2_res.nu);
od;;

# Sanity check: at omega = 0 the doubled category Z(Vec_Q8) has total rank
# sum of |C_G(g)|/<conj class>... actually for omega=0, total objects =
# sum over classes of #irreps of centraliser = sum over classes of |C_G(g_i)|/|G| ... wait.
# For omega=0, the rank of Z(Vec_G) = number of pairs (g, chi) where g is a conjugacy class rep
# and chi is an irrep of C_G(g).  For Q_8: classes have centralisers Q_8, Q_8, <i>=Z/4, <j>=Z/4, <k>=Z/4
# (centres are Z(Q_8)={1,-1} so the order-2 class has full centraliser).
# Irreps of Q_8 = 5, irreps of Z/4 = 4.  Total = 5 + 5 + 4 + 4 + 4 = 22.
total_rank := Sum(stage2_results, Length);;
Print("  total rank of Z(Vec_Q8) at omega=0: ", total_rank, "\n");
fsiAssertEqual("total rank at Q_8, omega=0", total_rank, 22);


# --- Stage 3: Q_8 with the non-trivial cocycle (EXPLORATORY) --------------
#
# WARNING: As of 2026-05-10 the cocycle returned by HAP's `StandardCocycle` on
# Q_8 fails the inhomogeneous bar-resolution 3-cocycle equation
# (delta f(w,x,y,z) = 0) on 1105 / 4096 quadruples for the order-8 generator
# of H^3(Q_8; U(1)).  Because `alphag(g)(f)` reduces to a 2-cocycle on C_G(g)
# only when f IS such a bar-cocycle, the central-extension construction
# downstream is mathematically invalid for non-trivial omega.  At omega = 0
# everything is identically zero so we recover the classical FS indicators
# correctly (Stage 1 / Stage 2 above).
#
# We still run Stage 3 below for diagnostic purposes: any anomalies (e.g.,
# the central-extension order overshooting |C| * exp because alpha is not a
# 2-cocycle) are visible as "bad" results.
Print("\n=== Stage 3 (EXPLORATORY): Q_8, omega = order-2 generator ===\n");
Print("  WARNING: HAP's StandardCocycle does not satisfy the bar-resolution\n");
Print("  3-cocycle equation for non-trivial omega on Q_8.  Results are diagnostic only.\n");

# Build the AutomorphismOrbits decomposition so we get an orbit representative
# of the order-2 cocycle.  H^3(Q_8; U(1)) = Z/8, so orbits of Aut(Q_8) = S_4 on Z/8
# split into a small number of classes.  We want the unique order-2 element class.
ctxQ8triv_K := TensorWithIntegers(ctxQ8triv_R);;
ctxQ8triv_UCT := UniversalCoefficientsTheorem(ctxQ8triv_K, 3);;
Print("  UCT.torsion = ", ctxQ8triv_UCT!.torsion, "\n");
Print("  UCT.exponent = ", ctxQ8triv_UCT!.exponent, "\n");

# Order-2 hom-vector: every entry should be exponent/2 = 4 (since H^3 = Z/8).
order2_hom := List(ctxQ8triv_UCT!.hombasis,
                   x -> ctxQ8triv_UCT!.exponent / 2);;
Print("  order2_hom (in the hom-basis): ", order2_hom, "\n");

ctxQ8_o2 := FSIContext(Q8, order2_hom);;
Print("  built order-2 context\n");

# Identity class at order-2 omega.
o2_g1 := FSIAllAtClass(ctxQ8_o2, One(Q8), 2);;
Print("  nu_2 at order-2 omega, g=1: ", o2_g1.nu, "\n");

# At g=1 the projective characters are *ordinary* characters of Q_8 (alpha_1 trivial),
# but the pi-twist still feels the cocycle through f(1, 1^k, 1) which is zero on degenerate
# triples in a normalised cocycle.  Sanity: we still expect classical-like values.

# All classes at the order-2 omega, m=2.
Print("  --- all classes, omega = order 2, m=2 ---\n");
stage3_results := [];;
for stage3_g in classes_Q8 do
    stage3_res := FSIAllAtClass(ctxQ8_o2, stage3_g, 2);;
    Print("    class order ", Order(stage3_g),
          ": ", Size(stage3_res.proj!.table), " irreps; nu_2 = ", stage3_res.nu, "\n");
    Add(stage3_results, stage3_res.nu);
od;;
stage3_total_rank := Sum(stage3_results, Length);;
Print("  total rank of Z(Vec^omega_Q8) at omega order 2: ", stage3_total_rank, "\n");
# For Q_8 the orbifold rank does NOT depend on omega (it equals
# sum over classes of the rank of the projective rep ring of C_G(g), and for
# omega of order 2 some of the centralisers Z/4 have different projective reps).
# We don't pin a single expected value; we just record.

# m=3 timing for the order-2 cocycle at g=1.
fsiT0 := Runtime();;
o2_g1_m3 := FSIAllAtClass(ctxQ8_o2, One(Q8), 3);;
fsiT1 := Runtime();;
Print("  nu_3 at order-2 omega, g=1: ", o2_g1_m3.nu, "\n");
Print("  m=3 time at g=1 (ms): ", fsiT1 - fsiT0, "\n");

# m=3 timing across all classes (a more honest measurement).
fsiT0 := Runtime();;
for stage3_g in classes_Q8 do
    FSIAllAtClass(ctxQ8_o2, stage3_g, 3);;
od;;
fsiT1 := Runtime();;
Print("  m=3 time across all 5 classes (ms): ", fsiT1 - fsiT0, "\n");


# --- summary --------------------------------------------------------------
Print("\n=== summary ===\n");
Print("  passed: ", fsiPass, "    failed: ", fsiFail, "\n");
if fsiFail > 0 then
    Print("  STATUS: FAIL\n");
    QUIT_GAP(1);
else
    Print("  STATUS: PASS\n");
fi;
