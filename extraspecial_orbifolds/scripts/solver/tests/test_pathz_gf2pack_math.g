# test_pathz_gf2pack_math.g — verifies the bit-slice math for the Path Z
# GF(2) bit-pack route (issue #391 Approach B).
#
# Strategy:
#   1. Build synthetic table (n²×k integer matrix in {0,1,2,3}) and
#      vec_target (length-k integer vec). Choose k=4, n=4 for clarity.
#   2. Compute c_int = table * vec_target mod 4 via the integer path.
#   3. Compute slice_top, slice_bot via the bit-slice formula from
#      the spec (final simplified form):
#        slice_top = (table_gf2_top * u_bot) + col_bot_exp * v_top_exp
#        slice_bot = col_bot_exp * v_bot_exp
#   4. Assert (slice_top == bit_1(c_int)) and (slice_bot == bit_0(c_int)).
#
# Constraints on synthetic input that mirror the production constraints:
#   - For j != exp_index, table[i][j] ∈ {0, 2} (order-2 columns).
#   - For j = exp_index, table[i][j] ∈ {0, 1, 2, 3}.
#   - For j != exp_index, vec_target[j] ∈ {0, 1}.
#   - For j = exp_index, vec_target[j] ∈ {1, 2, 3} (Path Z entry condition).

n := 4;;
n_sq := n * n;;
k := 4;;
exp_index := 4;;
one := One(GF(2));;

# Helper to build a single random valid (table, vec_target) instance and
# verify the bit-slice formula.
TestOne := function(trial)
    local table, vec_target, j, c_int, c_bot_ref, c_top_ref,
          u_bot, table_gf2_top, table_gf2_bot, col_bot_exp,
          v_bot_exp, v_top_exp, slice_top, slice_bot,
          slice_top_int, slice_bot_int, i, ok_top, ok_bot;
    table := List([1..n_sq], i -> List([1..k], j -> 0));
    for i in [1..n_sq] do
        for j in [1..k] do
            if j = exp_index then
                table[i][j] := Random([0..3]);
            else
                table[i][j] := 2 * Random([0..1]);  # in {0, 2}
            fi;
        od;
    od;
    vec_target := List([1..k], j -> 0);
    for j in [1..k] do
        if j = exp_index then
            vec_target[j] := Random([1..3]);  # Path Z entry: != 0
        else
            vec_target[j] := Random([0..1]);
        fi;
    od;

    # Reference integer computation.
    c_int := (table * vec_target) mod 4;
    c_bot_ref := c_int mod 2;
    c_top_ref := List(c_int, x -> QuoInt(x, 2) mod 2);

    # Bit-slice computation.
    table_gf2_top := List(table, row ->
        List(row, x -> (QuoInt(x, 2) mod 2) * one));
    ConvertToMatrixRep(table_gf2_top, GF(2));
    table_gf2_bot := List(table, row ->
        List(row, x -> (x mod 2) * one));
    ConvertToMatrixRep(table_gf2_bot, GF(2));
    col_bot_exp := List(table_gf2_bot, row -> row[exp_index]);
    ConvertToVectorRep(col_bot_exp, GF(2));

    u_bot := (vec_target mod 2) * one;
    ConvertToVectorRep(u_bot, GF(2));
    v_bot_exp := (vec_target[exp_index] mod 2) * one;
    v_top_exp := (QuoInt(vec_target[exp_index], 2) mod 2) * one;

    slice_top := table_gf2_top * u_bot;
    slice_top := slice_top + col_bot_exp * v_top_exp;
    slice_bot := col_bot_exp * v_bot_exp;
    ConvertToVectorRep(slice_top, GF(2));
    ConvertToVectorRep(slice_bot, GF(2));

    # Convert to int for comparison.
    slice_top_int := IntVecFFE(slice_top);
    slice_bot_int := IntVecFFE(slice_bot);

    ok_top := slice_top_int = c_top_ref;
    ok_bot := slice_bot_int = c_bot_ref;
    if not (ok_top and ok_bot) then
        Print("Trial ", trial, " FAIL:\n");
        Print("  table = ", table, "\n");
        Print("  vec_target = ", vec_target, "\n");
        Print("  c_int = ", c_int, "\n");
        Print("  c_bot_ref = ", c_bot_ref, "\n");
        Print("  slice_bot_int = ", slice_bot_int, "\n");
        Print("  c_top_ref = ", c_top_ref, "\n");
        Print("  slice_top_int = ", slice_top_int, "\n");
    fi;
    return ok_top and ok_bot;
end;;

# Run 50 random trials.
n_pass := 0;;
n_fail := 0;;
for trial in [1..50] do
    if TestOne(trial) then
        n_pass := n_pass + 1;
    else
        n_fail := n_fail + 1;
    fi;
od;

Assert(0, n_fail = 0,
       Concatenation("Bit-slice math: ", String(n_fail), " disagreements"));
Print("test_pathz_gf2pack_math.g: ", n_pass, "/", n_pass + n_fail, " trials passed.\n");
