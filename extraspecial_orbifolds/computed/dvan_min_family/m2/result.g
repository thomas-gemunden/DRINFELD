# All max EAs of E_+(2); persisted by persist_dvan_family_all_max_eas.g
# Schema: dvan_m2_result.ea_generators_exp = list of exponent-vector tuples
# against FamilyPcgs(ExtraspecialGroup(2^(2*2+1), "+")).
dvan_m2_result := rec(
ea_count := 6,
ea_generators_exp := [ [ [ 0, 0, 0, 0, 1 ], [ 1, 0, 0, 0, 0 ], [ 0, 0, 1, 0, 0 ] ], [ [ 0, 0, 0, 0, 1 ], [ 0, 1, 0, 0, 0 ], [ 0, 0, 1, 0, 0 ] ], [ [ 0, 0, 0, 0, 1 ], [ 1, 0, 1, 0, 0 ], [ 0, 1, 0, 1, 0 ] ], [ [ 0, 0, 0, 0, 1 ], [ 0, 1, 0, 0, 0 ], [ 0, 0, 0, 1, 0 ] ], [ [ 0, 0, 0, 0, 1 ], [ 1, 0, 0, 0, 0 ], [ 0, 0, 0, 1, 0 ] ], [ [ 0, 0, 0, 0, 1 ], [ 1, 0, 0, 1, 0 ], [ 0, 1, 1, 0, 0 ] ] ],
family_size := 6,
include_D8 := true,
include_Q8 := true,
m := 2,
notes := "All maximal elementary abelian subgroups of E_+(2) of rank m+1. This is NOT the D-VAN trimmed minimum family; it's the union over all max EAs. Detection is by Quillen + AM04 (every nonzero class of H^3(E_+(m); U(1)) restricts non-trivially to at least one of {max EA, D_8, Q_8}). Provides a unified `LoadDVANEAFamily(m)` for m < 7 without requiring a prior D-VAN trim production run.",
source := "hap-all-max-eas" );;
