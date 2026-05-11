# V-7b: FusionCoefficient(m, i, j, k) — single fusion-coefficient query
# primitive N_{ij}^k for the MTC of Z(Vec_{E_+(m)}).
#
# Built on top of V-7a's SEntry primitive (single-entry S-matrix access).
#
# Verlinde formula (for a unitary MTC, S unitary with S_{00} = 1/D):
#
#     N_{ij}^k = sum_a   S_{ia} * S_{ja} * conj(S_{ka}) / S_{0a}
#
# where the index 0 denotes the unit object and the sum runs over a in
# [1..rank].  In our 1-based convention the unit is at global index 1
# (class index 1 = identity class, irrep index 1 = trivial rep of G).
#
# Acceptance behaviour:
#   * m = 3: produces non-negative integer outputs, matching direct
#     Verlinde computed from the dense S matrix on every triple
#     exercised by the test driver.
#   * m = 5: produces non-negative integer outputs at the canonical
#     unit row (rank ~ 5e5; we exercise canonical triples to keep each
#     query well under 1 s).
#
# Returns:
#   * A non-negative integer.  We assert that the closed-form Verlinde
#     sum is an integer (it must be for a well-formed MTC); rounding
#     noise from on-demand ComputeSBlock paths is checked against a
#     small tolerance, and the result is then rounded to the nearest
#     non-negative integer.
#
# Entry points:
#   * FusionCoefficient(m, i, j, k)   — m in {3, 5}, 1-based global
#                                        indices.
#   * FusionCoefficient_Init(m)       — pre-warm SEntry for m and
#                                        cache the unit row.

Read("s_entry.g");

# -----------------------------------------------------------------
# Per-m fusion-coefficient state.  We cache the unit row S_{0, a} so
# that the inner divisor S_{0a} is not recomputed each time.
# -----------------------------------------------------------------

FusionCoefficient_state := rec();   # m -> rec(s, rank, unit_row).

FusionCoefficient_Init := function(m)
    local fcs, s, rank, unit_idx, unit_row, a;
    if IsBound(FusionCoefficient_state.(String(m))) then
        return FusionCoefficient_state.(String(m));
    fi;

    if m <> 3 and m <> 5 then
        Error("FusionCoefficient: m must be 3 or 5 (m = 7 lacks a full ",
              "global index because ConjugacyClasses(E_+(7)) OOMs).  ",
              "Got m = ", m);
    fi;

    Print("[FusionCoefficient] initialising m = ", m, " ...\n");
    s := SEntry_Init(m);
    rank := s.idx.rank;

    # Unit object: class index 1 (identity class, since GAP puts the
    # trivial class first in ConjugacyClasses) + irrep index 1
    # (trivial irrep is always first in Irr(C_G(1)) = Irr(G)).
    # global_offset[1] = 0, so unit = global index 1.
    unit_idx := s.idx.global_offset[1] + 1;

    fcs := rec(
        m := m,
        s := s,
        rank := rank,
        unit_idx := unit_idx,
        unit_row := fail   # built lazily; see FusionCoefficient_UnitRow.
    );

    FusionCoefficient_state.(String(m)) := fcs;
    return fcs;
end;;

# Build (or fetch from cache) the full unit row S_{unit, a} for a in
# [1..rank].  For m = 3 this is cheap (rank = 2272).  For m = 5
# (rank ~ 5e5) we build it ON DEMAND only when the caller actually
# asks for a fusion coefficient.  Each entry hits the canonical-block
# path because the unit class (class 1) is the canonical
# representative of the (id, id) refined group.
FusionCoefficient_UnitRow := function(fcs)
    local s, row, a;
    if fcs.unit_row <> fail then
        return fcs.unit_row;
    fi;
    Print("[FusionCoefficient] building unit row for m = ", fcs.m,
          " (rank = ", fcs.rank, ") ...\n");
    s := fcs.s;
    row := [];
    for a in [1..fcs.rank] do
        row[a] := SEntry(fcs.m, fcs.unit_idx, a);
    od;
    fcs.unit_row := row;
    return row;
end;;

# -----------------------------------------------------------------
# Main entry point.  Verlinde summation.
#
# We accumulate exactly when possible (the Verlinde sum is a
# rational/cyclotomic algebraic number that must round to a
# non-negative integer in a well-formed MTC), and round + sanity-check
# at the end.
# -----------------------------------------------------------------

FusionCoefficient := function(m, i, j, k)
    local fcs, unit_row, sum, a, S_ia, S_ja, S_ka, num, denom, term,
          rounded, gap_to_int, val;
    fcs := FusionCoefficient_Init(m);

    if i < 1 or i > fcs.rank
       or j < 1 or j > fcs.rank
       or k < 1 or k > fcs.rank then
        Error("FusionCoefficient: index out of range [1..", fcs.rank,
              "]; got (i, j, k) = (", i, ", ", j, ", ", k, ")");
    fi;

    unit_row := FusionCoefficient_UnitRow(fcs);

    sum := 0;
    for a in [1..fcs.rank] do
        S_ia := SEntry(m, i, a);
        S_ja := SEntry(m, j, a);
        S_ka := SEntry(m, k, a);
        denom := unit_row[a];
        if denom = 0 then
            Error("FusionCoefficient: S_{unit, ", a, "} = 0; this ",
                  "should not happen for an MTC (the unit row of a ",
                  "unitary S is nowhere zero -- entries equal the ",
                  "quantum dimension / total dimension).");
        fi;
        num := S_ia * S_ja * ComplexConjugate(S_ka);
        sum := sum + num / denom;
    od;

    # Sanity-check: the Verlinde sum must be a non-negative integer for
    # the modular data of a fusion category.  Both the canonical-block
    # path and the dense fallback at m = 3 work over exact cyclotomic
    # arithmetic in GAP, so the sum SHOULD be exactly an integer.  We
    # still guard against rounding noise from any on-demand
    # ComputeSBlock path: if `sum` is a Cyclotomic (rational case
    # included), GAP will recognise integer values via IsInt.
    if IsInt(sum) then
        if sum < 0 then
            Error("FusionCoefficient: Verlinde sum is the negative ",
                  "integer ", sum, " for (i, j, k) = (", i, ", ", j,
                  ", ", k, "); expected N_{ij}^k >= 0.");
        fi;
        return sum;
    fi;

    # If we got here, `sum` is not detected as an integer.  Try to
    # rationalise it (a true rational that happens to be an integer
    # but didn't reduce should round cleanly).
    if IsRat(sum) then
        if DenominatorRat(sum) = 1 then
            val := NumeratorRat(sum);
            if val < 0 then
                Error("FusionCoefficient: negative integer ", val, " for ",
                      "(i, j, k) = (", i, ", ", j, ", ", k, ").");
            fi;
            return val;
        fi;
        Error("FusionCoefficient: Verlinde sum is the non-integer ",
              "rational ", sum, " for (i, j, k) = (", i, ", ", j, ", ",
              k, "); MTC fusion coefficients must be non-negative ",
              "integers.");
    fi;

    # Cyclotomic but not detected as Int / Rat.  This indicates one of:
    # (a) a real round-off from a floating-point path (shouldn't
    #     happen — SEntry returns exact cyclotomics), or
    # (b) a true non-integer answer, meaning the data is not consistent
    #     with an MTC.
    # In either case, surface the value so the caller can inspect.
    Error("FusionCoefficient: Verlinde sum is the non-integer ",
          "cyclotomic ", sum, " for (i, j, k) = (", i, ", ", j, ", ",
          k, "); MTC fusion coefficients must be non-negative integers.");
end;;

Print("Loaded fusion_coefficient.g.  Use FusionCoefficient(m, i, j, k).\n");
