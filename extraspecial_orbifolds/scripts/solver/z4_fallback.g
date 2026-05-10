# z4_fallback.g — Z/exp coboundary test for the order-exp generator.
#
# Strategy: defer to the existing augmented-Z baseline IsCoboundary2 from
# transgression_kernel.g (built for arbitrary modulus). This is the
# fallback path for Path Z (the ord-exp generator); the GF(2)+Bockstein
# fast path covers the order-2 generators in mod2_solver.g.

# Reuse the augmented-Z helper from the existing baseline.
#
# Note on Read paths. transgression_kernel.g internally does
#     Read("../../src/modular_data.g")
# which GAP resolves relative to the process CWD, not relative to the
# calling file. So we briefly cd into the scripts/ directory before
# pulling in transgression_kernel.g, then restore the original CWD.
# This mirrors the pattern in spikes/spike_2divisibility.g.
#
# Convention: this file is intended to be Read from solver/tests/ or
# from solver/ directly. We locate transgression_kernel.g by walking
# up from CWD until we find it, so the file works from either entry.
z4_fallback_orig_dir := DirectoryCurrent();;
z4_fallback_target := fail;;
for z4_fallback_try in [".", "..", "../.."] do
    if IsExistingFile(Concatenation(z4_fallback_try, "/transgression_kernel.g")) then
        z4_fallback_target := z4_fallback_try;
        break;
    fi;
od;;
if z4_fallback_target = fail then
    Error("z4_fallback.g: cannot locate transgression_kernel.g from CWD ",
          Filename(z4_fallback_orig_dir, ""));
fi;
ChangeDirectoryCurrent(z4_fallback_target);;
Read("transgression_kernel.g");
ChangeDirectoryCurrent(Filename(z4_fallback_orig_dir, ""));;

IsCoboundary2Zexp := function(C, c, exp)
    return IsCoboundary2(C, c, exp);
end;;
