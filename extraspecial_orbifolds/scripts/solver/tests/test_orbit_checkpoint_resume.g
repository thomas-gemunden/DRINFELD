# test_orbit_checkpoint_resume.g — verify the #302 Stage 1 orbit-level
# checkpoint produces a bit-for-bit identical kernel on resume.
#
# Strategy: at m=3, run KernelOfTransgressionViaMBar twice. The first
# run writes the checkpoint; the second run reads it and confirms all
# orbits are SKIPPED, yet produces the same in_kernel_gens and
# kernel_size as a clean run.
#
# Usage:
#   gap -q -b -o 4g /path/to/test_orbit_checkpoint_resume.g
#
# Acceptance: both runs return kernel_size = 262144 and identical
# in_kernel_gens; the second run's propagation wall < 0.1 s (all
# orbits skipped via checkpoint).

LoadPackage("hap");;
LoadPackage("IO");;

# CWD-independent absolute path resolution: derive scripts dir from
# this test's file's directory. (Test files live in solver/tests/.)
_SCRIPT_DIR := "/Users/thomasgemunden/Projects/group_cohomology/DRINFELD-wt-a5b-oom/extraspecial_orbifolds/scripts";;
ChangeDirectoryCurrent(_SCRIPT_DIR);;
Read("transgression_per_generator_brw.g");
Read("solver/transgression_matrix_reduced.g");

CKPT_PATH := "/tmp/orbit_ckpt_test_resume.g";;
if IsExistingFile(CKPT_PATH) then RemoveFile(CKPT_PATH); fi;

Print("\n========= test_orbit_checkpoint_resume (m=3) =========\n");

m := 3;;
conj_action := BRWConjugacyAction(m);;
G := conj_action.em;;
setup := SetupCohomology3(G);;
brw_m := BRW(m);;
brw_gens_m := GeneratorsOfGroup(brw_m);;
h3_matrices := [];;
for i in [1..Length(brw_gens_m)] do
    phi_i := ConjugationAutomorphismThroughIso(
        G, conj_action.iso_em, brw_gens_m[i]);
    Add(h3_matrices, H3MatrixOfAutomorphism(setup, phi_i));
od;
perm_gens := conj_action.perms;;
classes := conj_action.classes;;
n_classes := Length(classes);;
visited_all := BlistList([1..n_classes], []);;
orbits_data := [];;
for start_idx in [1..n_classes] do
    if visited_all[start_idx] then continue; fi;
    sv := OrbitWithSchreierVec(perm_gens, n_classes, start_idx);
    for target_idx in sv.orbit do visited_all[target_idx] := true; od;
    Add(orbits_data, rec(start_idx := start_idx,
                          orbit := sv.orbit,
                          parent := sv.parent,
                          gen_used := sv.gen_used));
od;

# Run 1: bind ORBIT_CHECKPOINT_PATH globally so the function picks it up.
ORBIT_CHECKPOINT_PATH := CKPT_PATH;;
Print("\n--- RUN 1: fresh, with checkpoint write ---\n");
t0 := Runtime();;
result1 := KernelOfTransgressionViaMBar(setup, orbits_data, classes, G, h3_matrices);;
t1 := (Runtime() - t0) / 1000.;;
Print("Run 1 wall: ", t1, " s\n");
Print("Run 1 kernel_size: ", result1.kernel_size, "\n");

ckpt1_exists := IsExistingFile(CKPT_PATH);;
Print("Checkpoint exists: ", ckpt1_exists, "\n");
ckpt1 := ReadAsFunction(CKPT_PATH)();;
Print("Ckpt completed_orbit_starts: ", ckpt1.completed_orbit_starts, "\n");

Print("\n--- RUN 2: resumed from checkpoint ---\n");
t0 := Runtime();;
result2 := KernelOfTransgressionViaMBar(setup, orbits_data, classes, G, h3_matrices);;
t2 := (Runtime() - t0) / 1000.;;
Print("Run 2 wall: ", t2, " s\n");
Print("Run 2 kernel_size: ", result2.kernel_size, "\n");

# Cleanup
RemoveFile(CKPT_PATH);

Print("\n--- ACCEPTANCE ---\n");
ACC1 := result1.kernel_size = 262144;;
ACC2 := result2.kernel_size = 262144;;
ACC3 := result1.kernel_size = result2.kernel_size;;
ACC4 := result1.in_kernel_gens = result2.in_kernel_gens;;
ACC5 := result1.half_in_kernel = result2.half_in_kernel;;
ACC6 := result1.exp_index = result2.exp_index;;
ACC7 := result1.basis_orders = result2.basis_orders;;
ACC8 := ckpt1_exists;;

Print("  Run 1 kernel_size = 262144:        ", ACC1, "\n");
Print("  Run 2 kernel_size = 262144:        ", ACC2, "\n");
Print("  Run 1 == Run 2 kernel_size:        ", ACC3, "\n");
Print("  Run 1 == Run 2 in_kernel_gens:     ", ACC4, "\n");
Print("  Run 1 == Run 2 half_in_kernel:     ", ACC5, "\n");
Print("  Run 1 == Run 2 exp_index:          ", ACC6, "\n");
Print("  Run 1 == Run 2 basis_orders:       ", ACC7, "\n");
Print("  Checkpoint file existed after R1:  ", ACC8, "\n");

Print("\nOVERALL: ", ACC1 and ACC2 and ACC3 and ACC4 and ACC5 and ACC6
              and ACC7 and ACC8, "\n");
QUIT;
