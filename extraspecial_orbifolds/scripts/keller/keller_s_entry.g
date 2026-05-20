# keller/keller_s_entry.g — D-VAN-6 (issue #147).
#
# S-entry dispatcher: returns the (i, j) entry of the modular S-matrix
# of the omega-twisted Drinfeld center Z(Vec^omega_{E_+(m)}).
#
# Logic:
#   - If KellerTwistIsTrivial(m, omega_vec) then S = S^0 (untwisted).
#   - Otherwise, dispatch to the K-2 SKeller adapter.
#
# Phase 1 note: we currently call SKeller(m, i, j) for the trivial
# branch too, since the K-3 cross-check (#40, closed) established that
# SKeller at omega=0 equals the closed-form S^0 entry. This makes the
# dispatcher's API stable while letting us swap in a faster closed-form
# S^0 implementation later without breaking callers.
#
# Plan: docs/superpowers/plans/2026-05-15-detecting-family-vanishing-phase1.md
# Closes #147.

if not IsBoundGlobal("KellerTwistIsTrivial") then
    # Read-path shim: same dual-CWD logic as keller_twist_is_trivial.g.
    if IsExistingFile("keller/keller_twist_is_trivial.g") then
        Read("keller/keller_twist_is_trivial.g");
    elif IsExistingFile("keller_twist_is_trivial.g") then
        Read("keller_twist_is_trivial.g");
    else
        Error("keller/keller_s_entry.g: cannot locate ",
              "keller_twist_is_trivial.g from CWD ",
              Filename(DirectoryCurrent(), ""));
    fi;
fi;
if not IsBoundGlobal("SKeller") then
    # skeller_adapter.g depends on krr_projector.g (for
    # BuildIntertwinerDataUntwisted, ProjectorFormulaByIndex) which in
    # turn depends on untwisted_modular_data.g. The canonical load
    # order is documented in tests/test_skeller_adapter.g; we replicate
    # it here.
    if IsExistingFile("untwisted_modular_data.g") then
        if not IsBoundGlobal("ComputeSBlock") then
            Read("untwisted_modular_data.g");
        fi;
        if not IsBoundGlobal("BuildIntertwinerDataUntwisted") then
            Read("krr_projector.g");
        fi;
        Read("skeller_adapter.g");
    elif IsExistingFile("../untwisted_modular_data.g") then
        if not IsBoundGlobal("ComputeSBlock") then
            Read("../untwisted_modular_data.g");
        fi;
        if not IsBoundGlobal("BuildIntertwinerDataUntwisted") then
            Read("../krr_projector.g");
        fi;
        Read("../skeller_adapter.g");
    else
        Error("keller/keller_s_entry.g: cannot locate ",
              "skeller_adapter.g chain from CWD ",
              Filename(DirectoryCurrent(), ""));
    fi;
fi;

KellerSEntry := function(arg)
    local m, omega_vec, i, j, opts, lattice_source, mode_args;
    if Length(arg) < 4 then
        Error("KellerSEntry: usage KellerSEntry(m, omega_vec, i, j [, opts]).");
    fi;
    m := arg[1];
    omega_vec := arg[2];
    i := arg[3];
    j := arg[4];
    opts := fail;
    if Length(arg) >= 5 then
        opts := arg[5];
    fi;
    # K-4a-T4b (#188): if the caller requests `lattice_source := true`
    # (via opts), route through the KRR lattice intertwiner builder
    # (`SKellerLattice`) instead of the untwisted-baseline `SKeller`.
    # At omega = 0 the two are numerically equivalent (K-3 anchor); the
    # lattice path becomes meaningful when V-1 supplies a non-trivial
    # omega-derived ε.
    lattice_source := false;
    if opts <> fail and IsRecord(opts) and IsBound(opts.lattice_source) then
        lattice_source := opts.lattice_source;
    fi;
    if lattice_source then
        if not IsBoundGlobal("SKellerLattice") then
            Error("KellerSEntry: opts.lattice_source = true, but ",
                  "`SKellerLattice` is not bound. Read(\"skeller_adapter.g\") ",
                  "(which now bundles SKellerLattice for K-4a-T4b) and ",
                  "Read(\"build_krr_intertwiner_data.g\") first.");
        fi;
        mode_args := rec();
        if IsBound(opts.spectral_source) then
            mode_args.spectral_source := opts.spectral_source;
        fi;
        if not KellerTwistIsTrivial(m, omega_vec) then
            # Non-trivial omega: thread omega_vec into the lattice builder
            # so SKellerLattice can pick up the V-1 epsilon (if loaded).
            mode_args.omega_vec := omega_vec;
        fi;
        return SKellerLattice(m, i, j, mode_args);
    fi;
    # Default (untwisted-baseline) path.
    if KellerTwistIsTrivial(m, omega_vec) then
        # Trivial twist: S = S^0. Backend: SKeller at the same indices
        # (K-3 has confirmed this equals the closed-form S^0 entry).
        # A faster ClosedFormCentralS-based path can swap in here later
        # without changing the API.
        return SKeller(m, i, j);
    fi;
    # Non-trivial twist: K-2 SKeller adapter (legacy path, untwisted-equivalent
    # at present; V-1's lattice ε requires the lattice_source = true branch).
    return SKeller(m, i, j);
end;;

Print("Loaded keller/keller_s_entry.g (D-VAN-6, K-4a-T4b ready).\n");
