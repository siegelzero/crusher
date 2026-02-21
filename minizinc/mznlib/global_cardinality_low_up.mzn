% Crusher: native global_cardinality_low_up.
% Emits FZN predicate instead of decomposing into int_eq_reif/bool2int chains.
predicate global_cardinality_low_up(array [int] of var int: x,
                                    array [int] of int: cover,
                                    array [int] of int: lbound,
                                    array [int] of int: ubound) =
    fzn_global_cardinality_low_up(x, cover, lbound, ubound);

predicate fzn_global_cardinality_low_up(array [int] of var int: x,
                                        array [int] of int: cover,
                                        array [int] of int: lbound,
                                        array [int] of int: ubound);
