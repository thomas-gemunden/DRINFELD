# test_dvan_m5_anchor_vs_kernel.g — issue #148 (D-VAN m=5 anchor).
#
# Cross-validates `ResIsTrivialOnDetectingFamily(5, v)` against the
# A-5b m=5 kernel basis at `computed/transgression/5/kernel.g`.
#
# Mathematical invariant: a cohomology class v ∈ H^3(E_+(5); U(1)) is
# in ker(Tr) iff its restriction to the detecting family vanishes on
# every member. So:
#   - For each kernel basis vector v: ResIsTrivialOnDetectingFamily(5, v) = true
#   - For random non-kernel vectors v': ResIsTrivialOnDetectingFamily(5, v') = false
#
# This is the m=5 instance of Gate 1E in the D-VAN methodology spec.

Read("transgression_kernel.g");
Read("detecting_family_restriction.g");
Read("fsi_wrapper.g");
Read("detecting_family_vanish.g");

# Load kernel.g.
kernel_path := "../../computed/transgression/5/kernel.g";;
if not IsExistingFile(kernel_path) then
    Print("FAIL: kernel.g not found at ", kernel_path, "\n");
    QuitGap(1);
fi;
kernel_rec := ReadAsFunction(kernel_path)();;
# kernel.g uses `basis_summary` (list of records with `vec` + `order`)
# rather than `basis_vecs`. Extract the raw vectors.
basis_vecs := List(kernel_rec.basis_summary, r -> r.vec);;
basis_orders := List(kernel_rec.basis_summary, r -> r.order);;
Print("Loaded kernel.g: ", Length(basis_vecs),
      " basis vectors of orders ", basis_orders, "\n");

# Build the detecting family setup for m=5.
Print("Building detecting family setup for m=5 (may take ~10-20 min)...\n");
t0 := Runtime();;
fail_count := 0;;
pass_count := 0;;

# Test each kernel basis vector.
for i in [1..Length(basis_vecs)] do
    v := basis_vecs[i];
    t_v := Runtime();
    res := ResIsTrivialOnDetectingFamily(5, v);
    wall := (Runtime() - t_v) / 1000.;
    if res = true then
        pass_count := pass_count + 1;
        if i <= 5 or i mod 10 = 0 then
            Print("  PASS: kernel basis vec ", i, "/",
                  Length(basis_vecs), " (order ",
                  basis_orders[i],
                  ", wall ", wall, " s)\n");
        fi;
    else
        fail_count := fail_count + 1;
        Print("  FAIL: kernel basis vec ", i,
              " should be ker-trivial but ResIsTrivialOnDetectingFamily returned ", res,
              " (vec = ", v, ")\n");
    fi;
od;

# Test a few non-kernel vectors. Build by setting a single component
# at an index NOT in the kernel basis support.
Print("\nTesting non-kernel vectors (expect ResIsTrivialOnDetectingFamily = false):\n");
basis_indices := Set([]);;
for v in basis_vecs do
    for i in [1..Length(v)] do
        if v[i] <> 0 then AddSet(basis_indices, i); fi;
    od;
od;
non_kernel_indices := Difference([1..165], basis_indices);;
if IsEmpty(non_kernel_indices) then
    Print("  (all 165 generators appear in kernel basis support; skipping non-ker check)\n");
else
    for trial in [1..Minimum(3, Length(non_kernel_indices))] do
        j := non_kernel_indices[trial];
        v_nonker := ListWithIdenticalEntries(165, 0);
        v_nonker[j] := 1;
        t_v := Runtime();
        res := ResIsTrivialOnDetectingFamily(5, v_nonker);
        wall := (Runtime() - t_v) / 1000.;
        if res = false then
            pass_count := pass_count + 1;
            Print("  PASS: e_", j, " correctly rejected (wall ", wall, " s)\n");
        else
            fail_count := fail_count + 1;
            Print("  FAIL: e_", j, " should NOT be ker-trivial but got ", res, "\n");
        fi;
    od;
fi;

wall_total := (Runtime() - t0) / 1000.;;
Print("\n=== D-VAN m=5 anchor: ", pass_count, " PASS, ",
      fail_count, " FAIL (wall ", wall_total, " s) ===\n");

if fail_count = 0 then
    Print("D-VAN m=5 anchor (#148): GREEN -- detecting family vanishes ",
          "exactly on ker(Tr).\n");
    QuitGap(0);
else
    Print("D-VAN m=5 anchor (#148): RED -- ", fail_count,
          " discrepancies.\n");
    QuitGap(1);
fi;
