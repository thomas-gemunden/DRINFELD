# Mod(D^1(E_+(7))) untwisted, structural T-vector
# 4 sector types; per-type T data is determined by type alone.
# Total rank = 134275072
manifest := rec(
    m := 7,
    group_order := 32768,
    rank := 134275072,
    cocycle := "trivial",
    sector_counts := rec(
        identity := 1,
        minus_one := 1,
        order2 := 8255,
        order4 := 8128
    ),
    T_per_sector_RLE := rec(
        identity := [ [ 16385, 1 ] ],
        minus_one := [ [ 16384, 1 ], [ 1, -1 ] ],
        order2 := [ [ 4097, 1 ], [ 4097, -1 ] ],
        order4 := [ [ 4096, 1 ], [ 4096, -1 ], [ 1, E(4) ], [ 1, -E(4) ] ]
    ),
    TMultiset := rec(
        one := 67145792,
        minus_one := 67113024,
        i := 8128,
        minus_i := 8128
    )
);;
