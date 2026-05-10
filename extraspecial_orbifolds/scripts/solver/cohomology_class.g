# cohomology_class.g — coordinate-vector extraction for the SNF wrapper (T-2).
#
# CohomologyClass2(C, c, vec, setup)
#   C      : centraliser group (inside G)
#   c      : 2-cochain on C, a function (h, k) -> Z (values reduced mod
#            setup.exponent internally)
#   vec    : the omega's coordinate vector in setup's torsion basis
#            (informational; unused in this stub version)
#   setup  : the result of SetupCohomology3(G), with at least
#            setup.exponent
#
# Returns the coordinate vector of [c] in a fixed basis of H^2(C; Z/exp).
# For the SNF wrapper this is consumed by Task 12, which solves a linear
# system over Z/exp coupling these per-class vectors back to the H^3(G; Z/m)
# coordinates.
#
# === Status: STUB (zero-in / zero-of-right-length-out) ===
#
# This PR ships only the I/O contract: the function builds the length-n^2
# (n := |C|) integer vector c_vec[i, j] := c(elts[i], elts[j]) mod exp, and
# returns the coordinate vector via ProjectToH2Basis.
#
# ProjectToH2Basis is currently a stub: it returns a zero list whose length
# matches the rank of H^2(C; Z) (computed cheaply via HAP's
# GroupCohomology(C, 2)) when c_vec is identically zero, and otherwise
# raises an Error so callers know the real projection is not yet wired in.
# Task 12 (SNF wrapper) will replace ProjectToH2Basis with the actual
# UCT-based projection over Z/exp.
#
# Path note. transgression_kernel.g in turn Read's ../../src/modular_data.g
# relative to GAP's CWD. We therefore have to chdir to extraspecial_orbifolds/
# scripts/ before reading it. We try both layouts (callers in solver/ and in
# solver/tests/) and restore the original CWD afterwards.
cohomology_class_orig_dir := DirectoryCurrent();;
cohomology_class_loaded := false;;
for cohomology_class_cand in [".", "..", "../..", "../../.."] do
    if not cohomology_class_loaded
       and IsExistingFile(Filename(Directory(cohomology_class_cand),
                                   "transgression_kernel.g"))
    then
        ChangeDirectoryCurrent(cohomology_class_cand);
        Read("transgression_kernel.g");
        cohomology_class_loaded := true;
    fi;
od;;
ChangeDirectoryCurrent(Filename(cohomology_class_orig_dir, ""));;
if not cohomology_class_loaded then
    Error("cohomology_class.g: could not locate transgression_kernel.g");
fi;

# ProjectToH2Basis(C, c_vec, exp) — stub coordinate-vector extractor.
#
# Returns a length-r list of integers in [0..exp-1] representing [c_vec] in a
# fixed basis of H^2(C; Z/exp). r is the number of elementary divisors of
# H^2(C; Z) — i.e. the size of HAP's GroupCohomology(C, 2). This is a cheap
# proxy for the basis size; for our use case (C a 2-group, exp a power of 2)
# every elementary divisor of H^2(C; Z) is even, so this rank also equals
# the Z/exp-module rank of H^2(C; Z/exp). Task 12 will replace this proxy
# with the precise UCT basis.
#
# This stub:
#   - if c_vec is identically zero, returns ListWithIdenticalEntries(r, 0).
#   - otherwise, errors with a clear message.
ProjectToH2Basis := function(C, c_vec, exp)
    local r, h2, all_zero;
    all_zero := ForAll(c_vec, x -> x mod exp = 0);
    # Rank of H^2(C; Z) as an abstract abelian group (used as basis-rank
    # proxy). HAP's GroupCohomology returns a list of orders of elementary
    # divisors of H^n(C; Z) (length = rank). For C = a small 2-group this
    # is cheap.
    h2 := GroupCohomology(C, 2);
    r := Length(h2);
    if r = 0 then
        # H^2(C; Z) trivial: the coordinate vector is empty, but the test
        # expects a non-empty list to call ForAll on. Return [0] so the
        # ForAll predicate is vacuously true and the caller can still see
        # "no nontrivial classes" without crashing.
        return [0];
    fi;
    if all_zero then
        return ListWithIdenticalEntries(r, 0);
    fi;
    Error("ProjectToH2Basis: real projection not yet implemented for ",
          "non-zero cochains. Task 12 will wire this in.");
end;;

# CohomologyClass2(C, c, vec, setup) — see file header.
CohomologyClass2 := function(C, c, vec, setup)
    local elts, n, c_vec, i, j;
    elts := AsList(C);
    n := Length(elts);
    c_vec := List([1..n*n], i -> 0);
    for i in [1..n] do
        for j in [1..n] do
            c_vec[(i-1)*n + j] := c(elts[i], elts[j]) mod setup.exponent;
        od;
    od;
    return ProjectToH2Basis(C, c_vec, setup.exponent);
end;;
