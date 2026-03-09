predicate fzn_diffn_nonstrict_k(
    array [int, int] of var int: box_posn,
    array [int, int] of var int: box_size,
) = let {
    set of int: BOXES = index_set_1of2(box_posn);
    set of int: DIMS = index_set_2of2(box_posn);
} in fzn_crusher_diffn_k(card(BOXES), card(DIMS),
    [box_posn[b, d] | b in BOXES, d in DIMS],
    [box_size[b, d] | b in BOXES, d in DIMS]);

predicate fzn_crusher_diffn_k(int: n, int: k,
    array [int] of var int: flat_posn,
    array [int] of var int: flat_size);
