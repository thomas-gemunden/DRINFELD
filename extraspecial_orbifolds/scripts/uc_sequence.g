# uc_sequence.g — Integer cohomology H^n(G; Z) via the Universal
# Coefficient sequence, for n in [0..max_n].
#
# Issue Q-5 (#25). See `extraspecial_orbifolds/parallel_workstreams_design.md`
# § Q-5.
#
# # Background — UC sequence for a finite group with trivial Z-coeffs.
#
# For any group G and abelian module M, the UC short exact sequence reads
#
#     0  ->  Ext^1_Z(H_{n-1}(G; Z), M)  ->  H^n(G; M)  ->  Hom(H_n(G; Z), M)  ->  0
#
# and splits (non-canonically) over Z.  For M = Z and G *finite* every
# H_n(G; Z) (n >= 1) is finite, so Hom(H_n(G; Z), Z) = 0 and the sequence
# collapses to
#
#     H^n(G; Z)  ~=  Ext^1_Z(H_{n-1}(G; Z), Z)  ~=  H_{n-1}(G; Z)
#
# (the last iso because Ext(Z/m, Z) = Z/m and Ext is additive).  Concretely:
#
#     H^0(G; Z)  =  Z                           (one free factor)
#     H^n(G; Z)  =  H_{n-1}(G; Z)   for n >= 1.
#
# For a finite 2-group G all torsion is 2-primary so this iso encodes the
# whole answer.
#
# # Spike result (Approach A timings, see issue brief).
#
#   * D_8         (SmallGroup(8, 3),  |G| = 8):    H^0..H^4 each <2 ms.
#   * E_+(2)      (SmallGroup(32, 49), |G| = 32):  H^0..H^4 each <20 ms.
#   * E_+(3)      (SmallGroup(128, 2326), |G|=128): H^4 in ~20 ms;
#                 H^3 in ~10 ms; total budget for n in [0..4] well under
#                 a second.
#
# Conclusion: HAP's `GroupCohomology(G, n)` solves the problem trivially
# at every target group up to E_+(3) (m = 3).  Approach A (thin wrapper
# around HAP) is the right call.  Approach B (build the BSS from
# H^*(G; F_2) + Bockstein) would re-derive what HAP already gives us,
# and the existing `quillen_bockstein.g` only knows beta(w) for m = 1;
# extending it for m = 3, 5, 7 is a separate workstream.
#
# # Naming.
#
# `IntegerCohomologyViaUC` is the public entry point requested by the
# Q-5 brief: returns a *list of records*, one per degree n in [0..max_n].
# It is a strict super-set of the single-degree `IntegralCohomologyTorsion`
# already shipped in `integral_cohomology.g` (issue Q-5 first pass).
#
# # HAP output convention.
#
# `GroupCohomology(G, n)` returns a list of non-negative integers
# encoding H^n(G; Z) as a finitely-generated abelian group:
#   * each `0` entry represents a Z (free) summand;
#   * each `k >= 2` entry is an invariant factor representing Z/k.
# For a finite group, n=0 returns `[0]` (the single Z) and n >= 1 returns
# torsion only.  `_UC_ParseHAPCohomology` below splits these apart.

LoadPackage("hap");

# Make sure the single-degree wrapper is available; we re-use its naming.
if not IsBoundGlobal("IntegralCohomologyTorsion") then
    _uc_self := INPUT_FILENAME();;
    if _uc_self <> fail and _uc_self <> "stream" then
        _uc_dir := _uc_self{[1..Length(_uc_self) -
                          Length("/uc_sequence.g")]};;
        _uc_cand := Concatenation(_uc_dir, "/integral_cohomology.g");;
        if IsExistingFile(_uc_cand) then Read(_uc_cand); fi;
    fi;
    if not IsBoundGlobal("IntegralCohomologyTorsion")
       and IsExistingFile("integral_cohomology.g") then
        Read("integral_cohomology.g");
    fi;
fi;

# ---------------------------------------------------------------------
# Parse HAP's `GroupCohomology` list output into (free_rank, torsion).
#
# Input: a list of non-negative integers (HAP convention; see header).
# Output: rec(free_rank := <int>, torsion := <list of ints >= 2>).
# ---------------------------------------------------------------------
_UC_ParseHAPCohomology := function(hap_list)
    local free_rank, torsion, x;
    if not IsList(hap_list) then
        Error("_UC_ParseHAPCohomology: input must be a list, got ",
              hap_list);
    fi;
    free_rank := 0;
    torsion := [];
    for x in hap_list do
        if not IsInt(x) then
            Error("_UC_ParseHAPCohomology: non-integer entry ", x);
        fi;
        if x < 0 then
            Error("_UC_ParseHAPCohomology: negative entry ", x,
                  " (HAP should return non-negative ints only)");
        fi;
        if x = 0 then
            free_rank := free_rank + 1;
        elif x = 1 then
            # A `1` entry would mean Z/1 = 0, which is degenerate but
            # would correspond to a trivial summand.  HAP doesn't emit
            # these in practice; skip silently to be safe.
            continue;
        else
            Add(torsion, x);
        fi;
    od;
    return rec(free_rank := free_rank, torsion := torsion);
end;;

# ---------------------------------------------------------------------
# Compute H^n(G; Z) for n in [0..max_n] using the UC sequence
# applied to H^*(G; F_2) computed via HAP, plus Bockstein.
#
# Approach taken: thin wrapper around HAP's `GroupCohomology(G, n)`,
# which already implements the integer cohomology via the Z-resolution
# (effectively the same UCT/BSS pipeline, but on Z-coefficient chain
# complexes).  This avoids re-deriving the Bockstein machinery for
# m >= 2 (which `quillen_bockstein.g` only has for m = 1).
#
# G     : a finite group (preferably a 2-group; extension to other
#         primes works too — HAP handles general finite groups — but
#         the "2-torsion only" guarantee no longer holds).
# max_n : maximum degree to compute (typically 4 for D-VAN Phase 2).
#
# Returns a list of records, one per degree n in [0..max_n]:
#   rec(
#     degree    := n,
#     torsion   := list of invariant factors >= 2, e.g. [2, 2, 4]
#                  for Z/2 + Z/2 + Z/4,
#     free_rank := number of Z summands (1 at n=0, 0 elsewhere for
#                  finite G),
#     source    := "hap-direct",
#     basis     := fail   (reserved for future Approach-B output)
#   ).
# ---------------------------------------------------------------------
IntegerCohomologyViaUC := function(G, max_n)
    local result, n, raw, parsed;
    if not IsGroup(G) then
        Error("IntegerCohomologyViaUC: first arg must be a group");
    fi;
    if not (IsInt(max_n) and max_n >= 0) then
        Error("IntegerCohomologyViaUC: max_n must be a non-negative ",
              "integer, got ", max_n);
    fi;
    if not IsFinite(G) then
        Error("IntegerCohomologyViaUC: G must be finite (HAP's ",
              "GroupCohomology supports finite groups only via this path)");
    fi;

    result := [];
    for n in [0..max_n] do
        raw := GroupCohomology(G, n);
        parsed := _UC_ParseHAPCohomology(raw);
        Add(result, rec(
            degree    := n,
            torsion   := parsed.torsion,
            free_rank := parsed.free_rank,
            source    := "hap-direct",
            basis     := fail
        ));
    od;
    return result;
end;;

# ---------------------------------------------------------------------
# Convenience: render a single degree result as a compact string.
# E.g. "Z + (Z/2)^2 + Z/4" or "0" or "Z" or "(Z/2)^9 + Z/8".
# ---------------------------------------------------------------------
IntegerCohomologyFormat := function(rec_n)
    local parts, count_table, k, count;
    parts := [];
    if rec_n.free_rank > 0 then
        if rec_n.free_rank = 1 then
            Add(parts, "Z");
        else
            Add(parts, Concatenation("Z^", String(rec_n.free_rank)));
        fi;
    fi;
    # Collapse torsion to "Z/k" or "(Z/k)^e".
    count_table := Collected(rec_n.torsion);
    Sort(count_table);
    for k in count_table do
        if k[2] = 1 then
            Add(parts, Concatenation("Z/", String(k[1])));
        else
            Add(parts, Concatenation("(Z/", String(k[1]), ")^",
                                     String(k[2])));
        fi;
    od;
    if IsEmpty(parts) then return "0"; fi;
    return JoinStringsWithSeparator(parts, " + ");
end;;

# ---------------------------------------------------------------------
# Convenience: pretty-print a full IntegerCohomologyViaUC result.
# ---------------------------------------------------------------------
IntegerCohomologyPrint := function(result)
    local r;
    for r in result do
        Print("  H^", r.degree, " = ", IntegerCohomologyFormat(r),
              "   (free_rank=", r.free_rank,
              ", torsion=", r.torsion,
              ", source=", r.source, ")\n");
    od;
end;;

Print("Loaded uc_sequence.g (Q-5: IntegerCohomologyViaUC; Approach A: ",
      "HAP-direct).\n");
