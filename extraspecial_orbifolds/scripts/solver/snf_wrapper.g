# snf_wrapper.g — top-level wrapper for the transgression kernel (T-2).
#
# TransgressionKernelExact(G) computes
#     ker( Tr : H^3(G; U(1))  ->  ⊕_g H^2(C_g; U(1)) )
# by enumerating the (finite) H^3 classes and asking the public dispatcher
# IsCoboundary2Split whether each per-class restriction c_g is a coboundary.
#
# Implementation choice: brute-force enumeration.
#
#   The original plan called for an SNF-based approach that projects each
#   per-class 2-cocycle onto a fixed Z/exp basis of H^2(C; Z/exp), stacks
#   these vectors into a matrix, and intersects ker(M) with the torsion
#   lattice. That route requires a real (non-stub) ProjectToH2Basis in
#   cohomology_class.g and the cell-to-group cochain translation through
#   HAP's resolution structure — both deferred.
#
#   The brute-force route is correct as-is: the dispatcher's boolean is
#   exactly the cohomology test we need. For the rung-1 anchor (D_8, 16
#   classes × 5 conjugacy classes) and the rung-3 anchor (E_+(2), 4096
#   classes × 17 conjugacy classes; expected kernel size 2048) it is
#   easily within the time budget.
#
#   For E_+(3) (T-2 design target, ~2^34 classes × 65 conjugacy classes
#   ≈ 7e10 evaluations) brute force is NOT feasible; the proper SNF
#   approach plus the BRW-orbit reduction (PR2) is required there.
#   That work is OUT OF SCOPE for this task and is documented as a
#   known limitation.
#
# Returned record fields:
#   .setup       — SetupCohomology3(G) (so callers can reuse the cocycle data)
#   .classes     — ConjugacyClasses(G) (in GAP's iteration order)
#   .kernel      — list of NON-zero kernel coordinate vectors
#                  (the zero vector is always in the kernel and is
#                   intentionally excluded from this list, matching the
#                   plan's convention "Length(result.kernel) = 0 iff the
#                   transgression kernel is trivial")
#   .kernel_size — total count of kernel elements, including the zero
#                  cocycle (so kernel_size = 1 + Length(kernel))
#
# Read-path note: this file is intended to be Read either directly from
# solver/ or from solver/tests/. It pulls in iscoboundary2_split.g, which
# uses the same CWD-shim pattern internally. We replicate the shim here so
# we can locate iscoboundary2_split.g from either entry point.
snf_wrapper_orig_dir := DirectoryCurrent();;
snf_wrapper_target := fail;;
for snf_wrapper_try in [".", "..", "../.."] do
    if IsExistingFile(Concatenation(snf_wrapper_try, "/iscoboundary2_split.g")) then
        snf_wrapper_target := snf_wrapper_try;
        break;
    fi;
od;;
if snf_wrapper_target = fail then
    Error("snf_wrapper.g: cannot locate iscoboundary2_split.g from CWD ",
          Filename(snf_wrapper_orig_dir, ""));
fi;
ChangeDirectoryCurrent(snf_wrapper_target);;
Read("iscoboundary2_split.g");
ChangeDirectoryCurrent(Filename(snf_wrapper_orig_dir, ""));;

TransgressionKernelExact := function(G)
    local setup, classes, kernel_vecs, vec, omega, all_zero,
          j, gRep, C, c_g, zero_vec;
    setup := SetupCohomology3(G);
    classes := ConjugacyClasses(G);

    kernel_vecs := [];
    for vec in Cartesian(List(setup.torsion, t -> [0..t-1])) do
        omega := StandardCocycleOf(setup, vec);
        all_zero := true;
        for j in [1..Length(classes)] do
            gRep := Representative(classes[j]);
            C := Centralizer(G, gRep);
            c_g := CGCocycleFunc(omega, gRep);
            if not IsCoboundary2Split(C, c_g, vec, setup) then
                all_zero := false;
                break;
            fi;
        od;
        if all_zero then
            Add(kernel_vecs, vec);
        fi;
    od;

    # Drop the zero vector: it's vacuously in the kernel and the plan's
    # convention is that result.kernel is the list of NON-zero kernel
    # elements (so Length = 0 iff the kernel is trivial).
    zero_vec := List(setup.torsion, t -> 0);
    return rec(setup       := setup,
               classes     := classes,
               kernel      := Filtered(kernel_vecs, v -> v <> zero_vec),
               kernel_size := Length(kernel_vecs));
end;;
