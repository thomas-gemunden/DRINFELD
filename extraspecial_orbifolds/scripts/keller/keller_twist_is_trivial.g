# keller/keller_twist_is_trivial.g — D-VAN-5 (issue #146).
#
# Keller-namespace wrapper around ResIsTrivialOnDetectingFamily. The
# semantic question this answers is "is [omega] = 0 in
# H^3(E_+(m); U(1))?" — equivalent to "does the Keller twist on the
# Drinfeld center collapse to the untwisted center?"
#
# Plan: docs/superpowers/plans/2026-05-15-detecting-family-vanishing-phase1.md
# Closes #146.

if not IsBoundGlobal("ResIsTrivialOnDetectingFamily") then
    # Read-path shim: callers may sit either in scripts/ (most tests)
    # or in scripts/keller/ (when running this file directly). GAP's
    # Read resolves against CWD, not against this file's location.
    if IsExistingFile("detecting_family_vanish.g") then
        Read("detecting_family_vanish.g");
    elif IsExistingFile("../detecting_family_vanish.g") then
        Read("../detecting_family_vanish.g");
    else
        Error("keller/keller_twist_is_trivial.g: cannot locate ",
              "detecting_family_vanish.g from CWD ",
              Filename(DirectoryCurrent(), ""));
    fi;
fi;

KellerTwistIsTrivial := function(m, omega_vec)
    return ResIsTrivialOnDetectingFamily(m, omega_vec).trivial;
end;;

Print("Loaded keller/keller_twist_is_trivial.g (D-VAN-5).\n");
