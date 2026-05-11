# test_aut_nt_mod_brw.g — tests for V-6 (AutNTModBRW).
#
# Tested modules:
#   ../aut_nt_partition.g  (V-5a)
#   ../aut_nt_refine.g     (V-5b)
#   ../aut_nt.g            (V-5c)
#   ../aut_nt_mod_brw.g    (V-6)
#
# Acceptance criteria (issue #37):
#   * D(Q_8) trivial cocycle: full |Aut| = 6, BRW trivial, quotient = 6.
#   * D(Q_8) order-2 cocycle: full |Aut| = 24, BRW trivial, quotient
#     = 24.
#   * For E_+(2) and beyond, the BRW(m)/E_+(m) -> Aut(N, T) lift on
#     simples is needed; the lift itself is gated on V-5c E_+(2) ground
#     truth and on a separate brw_simple_action_*.g (not part of this
#     PR). Tests for those cases are marked TODO.
#
# We also include:
#   * Synthetic ad-hoc tests where we construct a BRW-like subgroup
#     by hand, to exercise the (post-hoc) quotient logic.
#   * Tests of all four accepted input shapes for BRW_action.
#
# Run from anywhere:
#     gap test_aut_nt_mod_brw.g
#
# Success is signalled by "test_aut_nt_mod_brw: PASS".

# ---- Locate and load the sibling modules -----------------------------
_loaded := false;;
_self_path := INPUT_FILENAME();;
if _self_path <> fail and _self_path <> "stream" then
    _self_dir := _self_path{[1..Length(_self_path) - Length("/test_aut_nt_mod_brw.g")]};;
    _cand_part   := Concatenation(_self_dir, "/../aut_nt_partition.g");;
    _cand_refine := Concatenation(_self_dir, "/../aut_nt_refine.g");;
    _cand_autnt  := Concatenation(_self_dir, "/../aut_nt.g");;
    _cand_modbrw := Concatenation(_self_dir, "/../aut_nt_mod_brw.g");;
    if IsExistingFile(_cand_part) and IsExistingFile(_cand_refine)
       and IsExistingFile(_cand_autnt) and IsExistingFile(_cand_modbrw)
    then
        Read(_cand_part);
        Read(_cand_refine);
        Read(_cand_autnt);
        Read(_cand_modbrw);
        _loaded := true;
    fi;
fi;
if not _loaded then
    for _p in [ [ "../aut_nt_partition.g", "../aut_nt_refine.g",
                  "../aut_nt.g", "../aut_nt_mod_brw.g" ],
                [ "aut_nt_partition.g", "aut_nt_refine.g",
                  "aut_nt.g", "aut_nt_mod_brw.g" ],
                [ "extraspecial_orbifolds/scripts/aut_nt_partition.g",
                  "extraspecial_orbifolds/scripts/aut_nt_refine.g",
                  "extraspecial_orbifolds/scripts/aut_nt.g",
                  "extraspecial_orbifolds/scripts/aut_nt_mod_brw.g" ] ] do
        if not _loaded
           and IsExistingFile(_p[1])
           and IsExistingFile(_p[2])
           and IsExistingFile(_p[3])
           and IsExistingFile(_p[4]) then
            Read(_p[1]); Read(_p[2]); Read(_p[3]); Read(_p[4]);
            _loaded := true;
        fi;
    od;
fi;
if not _loaded then
    Error("cannot locate aut_nt*.g and aut_nt_mod_brw.g; run from ",
          "extraspecial_orbifolds/scripts/tests/.");
fi;

failures := [];

CheckEqual := function(label, got, expected)
    if got = expected then
        Print("  [ok] ", label, "\n");
    else
        Print("  [FAIL] ", label, "\n");
        Print("        expected: ", expected, "\n");
        Print("        got     : ", got, "\n");
        Add(failures, label);
    fi;
end;;

CheckTrue := function(label, cond)
    if cond then
        Print("  [ok] ", label, "\n");
    else
        Print("  [FAIL] ", label, "\n");
        Add(failures, label);
    fi;
end;;

# ---- Locate modular_data ---------------------------------------------
_md_root := fail;;
for _cand in [ "../../../../modular_data",
               "../../../../../modular_data",
               "/Users/thomasgemunden/Projects/group_cohomology/modular_data" ] do
    if _md_root = fail and IsExistingFile(Concatenation(_cand, "/8/4/1.txt")) then
        _md_root := _cand;
    fi;
od;
if _md_root = fail then
    Error("cannot locate modular_data/ root.");
fi;

# ---- Helper: load a precomputed (S, T) -------------------------------
LoadModularDataFromFile := function(path)
    local f, data;
    f := ReadAsFunction(path);
    if f = fail then
        Error("cannot read ", path);
    fi;
    return f();
end;;

# ---- Argument-normalisation tests ------------------------------------
# These don't touch Aut(N, T) yet — they only exercise the input
# shapes of AutNTModBRW.

Print("Section 0: BRW_action input-shape sanity.\n");

# Tiny fusion ring: Z/2 with the trivial T (|Aut(N,T)| = 1 by
# test_aut_nt.g's analysis). We pass a few BRW_action shapes; the
# quotient must be 1 in every case.
N_z2 := [ [ [1, 0], [0, 1] ],
          [ [0, 1], [1, 0] ] ];;
T_z2 := [1, 1];;
QD_z2 := [1, 1];;

# Shape (iv): fail.
_z2_fail := AutNTModBRW(N_z2, T_z2, QD_z2, fail);;
CheckEqual("Z/2 with BRW=fail quotient order", _z2_fail.order, 1);
CheckEqual("Z/2 with BRW=fail brw_order", _z2_fail.brw_order, 1);

# Shape (iv'): empty list.
_z2_empty := AutNTModBRW(N_z2, T_z2, QD_z2, []);;
CheckEqual("Z/2 with BRW=[] quotient order", _z2_empty.order, 1);

# Shape (i): trivial Group.
_z2_trivgrp := AutNTModBRW(N_z2, T_z2, QD_z2, Group(()));;
CheckEqual("Z/2 with BRW=Group(()) quotient order",
           _z2_trivgrp.order, 1);

# Shape (iii): a list of GAP perms — only the identity is in Aut(Z/2,T)
# (Aut(N,T) on Z/2 is trivial since the swap doesn't preserve N). The
# empty perm list = identity subgroup.
_z2_permlist := AutNTModBRW(N_z2, T_z2, QD_z2, [()]);;
CheckEqual("Z/2 with BRW=[()] quotient order", _z2_permlist.order, 1);

# Shape (ii): image-list. [1,2] is the identity permutation.
_z2_imglist := AutNTModBRW(N_z2, T_z2, QD_z2, [ [1, 2] ]);;
CheckEqual("Z/2 with BRW=[[1,2]] quotient order",
           _z2_imglist.order, 1);

# ---- Acceptance test 1: D(Q_8) trivial cocycle, BRW trivial ----------
# Q_8 is not plus-type extraspecial; BRW subgroup is the trivial group.
# Expected: full |Aut| = 6, BRW = 1, quotient = 6.
Print("\nAcceptance 1: D(Q_8) trivial cocycle, BRW = trivial.\n");
q8_path := Concatenation(_md_root, "/8/4/1.txt");;
q8_data := LoadModularDataFromFile(q8_path);;
CheckEqual("Q_8 rank", Length(q8_data.T), 22);

q8_S := q8_data.S;;
q8_T := q8_data.T;;
q8_QD := QuantumDimensionsFromS(q8_S);;
q8_N := FusionCoefficientsFromS(q8_S);;

_t0 := Runtime();;
q8_modbrw := AutNTModBRW(q8_N, q8_T, q8_QD, fail);;
_elapsed := Runtime() - _t0;;
Print("  Q_8 trivial cocycle:\n");
Print("    |Aut(N, T)|       = ", q8_modbrw.full.order, "\n");
Print("    |BRW ∩ Aut|       = ", q8_modbrw.brw_order, "\n");
Print("    quotient order    = ", q8_modbrw.order, "\n");
Print("    BRW ⊆ Aut?        = ", q8_modbrw.brw_subset_of_aut, "\n");
Print("    # coset reps      = ", Length(q8_modbrw.coset_reps), "\n");
Print("    elapsed           = ", _elapsed, "ms.\n");

CheckEqual("Q_8 trivial: full |Aut|", q8_modbrw.full.order, 6);
CheckEqual("Q_8 trivial: |BRW ∩ Aut|", q8_modbrw.brw_order, 1);
CheckEqual("Q_8 trivial: quotient order", q8_modbrw.order, 6);
CheckTrue("Q_8 trivial: BRW ⊆ Aut",
          q8_modbrw.brw_subset_of_aut);
CheckEqual("Q_8 trivial: # coset reps = quotient order",
           Length(q8_modbrw.coset_reps), q8_modbrw.order);

# ---- Acceptance test 1b: D(Q_8) order-2 cocycle, BRW trivial ---------
Print("\nAcceptance 1b: D(Q_8) order-2 cocycle, BRW = trivial.\n");
q8b_path := Concatenation(_md_root, "/8/4/2.txt");;
q8b_data := LoadModularDataFromFile(q8b_path);;
q8b_S := q8b_data.S;;
q8b_T := q8b_data.T;;
q8b_QD := QuantumDimensionsFromS(q8b_S);;
q8b_N := FusionCoefficientsFromS(q8b_S);;

_t0 := Runtime();;
q8b_modbrw := AutNTModBRW(q8b_N, q8b_T, q8b_QD, fail);;
_elapsed := Runtime() - _t0;;
Print("  Q_8 (k=2):\n");
Print("    |Aut(N, T)|       = ", q8b_modbrw.full.order, "\n");
Print("    |BRW ∩ Aut|       = ", q8b_modbrw.brw_order, "\n");
Print("    quotient order    = ", q8b_modbrw.order, "\n");
Print("    BRW ⊆ Aut?        = ", q8b_modbrw.brw_subset_of_aut, "\n");
Print("    elapsed           = ", _elapsed, "ms.\n");

CheckEqual("Q_8 (k=2): full |Aut|", q8b_modbrw.full.order, 24);
CheckEqual("Q_8 (k=2): |BRW ∩ Aut|", q8b_modbrw.brw_order, 1);
CheckEqual("Q_8 (k=2): quotient order", q8b_modbrw.order, 24);
CheckTrue("Q_8 (k=2): BRW ⊆ Aut",
          q8b_modbrw.brw_subset_of_aut);

# ---- Synthetic test: BRW = whole Aut(N, T) on D(Q_8) order-2 ---------
# Pass in BRW = full Aut(N, T); quotient must be 1.
# We get the full Aut as a permutation group from the .full.generators
# of the previous run.
Print("\nSection 2: synthetic — pass BRW = full Aut(N, T) on Q_8 (k=2).\n");
_q8b_full_gens_perms := List(q8b_modbrw.full.generators, PermList);;
_q8b_full_grp := Group(_q8b_full_gens_perms);;
Print("  built full-Aut group with order ", Size(_q8b_full_grp), ".\n");
_q8b_full_quot := AutNTModBRW(q8b_N, q8b_T, q8b_QD, _q8b_full_grp);;
CheckEqual("Q_8 (k=2): BRW = full Aut, quotient order = 1",
           _q8b_full_quot.order, 1);
CheckEqual("Q_8 (k=2): BRW = full Aut, |BRW ∩ Aut| = |Aut|",
           _q8b_full_quot.brw_order, 24);

# ---- Synthetic test: BRW = an order-2 subgroup of Aut(N, T) on Q_8 ---
# Pick a generator from the full Aut, build the order-2 (or larger)
# cyclic subgroup, check the quotient is |Aut| / order_of_that_sub.
Print("\nSection 3: synthetic — pass BRW = a cyclic subgroup of Aut.\n");
if Length(_q8b_full_gens_perms) > 0 then
    _g := _q8b_full_gens_perms[1];;
    _gsub := Group(_g);;
    Print("  using single-generator subgroup of order ",
          Size(_gsub), ".\n");
    _gsub_quot := AutNTModBRW(q8b_N, q8b_T, q8b_QD, _gsub);;
    Print("  quotient order = ", _gsub_quot.order, "\n");
    # |Aut| / |<g>|.
    CheckEqual("Q_8 (k=2): BRW = <g>, quotient = |Aut|/|<g>|",
               _gsub_quot.order, 24 / Size(_gsub));
    CheckEqual("Q_8 (k=2): BRW = <g>, brw_order = |<g>|",
               _gsub_quot.brw_order, Size(_gsub));
    # The full set of coset reps has size = quotient order; each coset
    # rep must be in Aut.
    CheckEqual("Q_8 (k=2): BRW = <g>, # coset reps = quotient order",
               Length(_gsub_quot.coset_reps), _gsub_quot.order);
    _coset_in_aut := ForAll(_gsub_quot.coset_reps,
                            p -> p in _q8b_full_grp);;
    CheckTrue("Q_8 (k=2): BRW = <g>, all coset reps lie in Aut",
              _coset_in_aut);
fi;

# ---- Pass BRW via image-list shape; verify it agrees with group shape
Print("\nSection 4: pass BRW via image-list shape (Q_8 k=2).\n");
if Length(q8b_modbrw.full.generators) > 0 then
    _imgs := [ q8b_modbrw.full.generators[1] ];;  # one length-22 list
    _imglist_quot := AutNTModBRW(q8b_N, q8b_T, q8b_QD, _imgs);;
    # Expected: same as the cyclic <g> quotient above.
    Print("  image-list quotient order = ", _imglist_quot.order, "\n");
    Print("  expected (matches Group(_g) variant) = ",
          24 / Size(Group(PermList(_imgs[1]))), "\n");
    CheckEqual("Q_8 (k=2): image-list shape consistent with group shape",
               _imglist_quot.order,
               24 / Size(Group(PermList(_imgs[1]))));
fi;

# ---- Quotient generators sanity --------------------------------------
# When BRW = full Aut, there should be zero non-identity coset reps
# (i.e. quotient generators is empty).
Print("\nSection 5: quotient-generators sanity.\n");
CheckEqual("Q_8 (k=2): BRW = full Aut, # quotient generators = 0",
           Length(_q8b_full_quot.quotient_generators), 0);
# When BRW is trivial, # quotient generators = |Aut| - 1 (the entire
# non-identity part of Aut). But we also reported # coset reps =
# |Aut|; one of those is identity. Confirm.
CheckEqual("Q_8 trivial: # quotient generators = |Aut| - 1",
           Length(q8_modbrw.quotient_generators), 6 - 1);
CheckEqual("Q_8 (k=2): # quotient generators = |Aut| - 1",
           Length(q8b_modbrw.quotient_generators), 24 - 1);

# ---- skip-coset-reps / skip-generators options sanity ----------------
Print("\nSection 6: opts.skip_coset_reps / skip_generators.\n");
_q8_skip_cosets := AutNTModBRW(q8_N, q8_T, q8_QD, fail,
                                rec(skip_coset_reps := true));;
CheckEqual("Q_8 trivial skip_coset_reps: order still correct",
           _q8_skip_cosets.order, 6);
CheckEqual("Q_8 trivial skip_coset_reps: coset_reps empty",
           Length(_q8_skip_cosets.coset_reps), 0);

_q8_skip_gens := AutNTModBRW(q8_N, q8_T, q8_QD, fail,
                              rec(skip_generators := true));;
CheckEqual("Q_8 trivial skip_generators: order still correct",
           _q8_skip_gens.order, 6);
CheckEqual("Q_8 trivial skip_generators: brw_order = brw_input_order",
           _q8_skip_gens.brw_order, _q8_skip_gens.brw_input_order);

# ---- E_+(2) test: TODO (gated) ---------------------------------------
# The E_+(2) (= 32/49/1.txt) test for V-6 requires
#   (a) V-5c E_+(2) ground truth: |Aut(N, T)| on r=184, which has not
#       been computed/locked in by V-5c yet.
#   (b) the BRW(2)/E_+(2) lift to Sym(184): a separate task
#       (brw_simple_action_*.g not in this PR).
# So we skip it here and document the gating.
Print("\nE_+(2) test: SKIP (gated on V-5c E_+(2) ground truth and ",
      "the BRW-on-simples lift).\n");

# ---- Final report ----------------------------------------------------
if Length(failures) = 0 then
    Print("\ntest_aut_nt_mod_brw: PASS\n");
else
    Print("\ntest_aut_nt_mod_brw: FAIL (", Length(failures),
          " failure(s)):\n");
    for i in [1..Length(failures)] do
        Print("  - ", failures[i], "\n");
    od;
fi;

QUIT;
