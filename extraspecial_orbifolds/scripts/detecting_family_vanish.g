# detecting_family_vanish.g — D-VAN-3 (issue #144).
#
# Core vanishing test: decides whether [omega] = 0 in H^3(E_+(m); U(1))
# by checking omega|_E = 0 and omega|_{D_8} = 0 on the AM04 detecting
# family F = {E, D_8}. Injectivity of res : H^3(G; U(1)) -> H^3(E) ⊕ H^3(D_8)
# is given by AM04 IV.7 + Quillen 1971 (essential ideal starts in degree
# 2m, clear of degree 3 for m >= 2).
#
# Spec: docs/superpowers/specs/2026-05-15-detecting-family-vanishing-test-design.md
# Plan: docs/superpowers/plans/2026-05-15-detecting-family-vanishing-phase1.md
# Closes #144.

if not IsBoundGlobal("BuildRestrictionMatrices") then
    Read("detecting_family_restriction.g");
fi;
if not IsBoundGlobal("FSI_LiftIfHom") then
    Read("fsi_wrapper.g");
fi;
if not IsBoundGlobal("StandardCocycleOf") then
    Read("transgression_kernel.g");
fi;

If_ := function(c, a, b) if c then return a; else return b; fi; end;;

Print("Loaded detecting_family_vanish.g (D-VAN-3).\n");
