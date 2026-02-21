% Crusher: native fzn_global_cardinality_closed.
% Prevents decomposition into int_eq_reif domain restriction + open variant.
predicate fzn_global_cardinality_closed(array [int] of var int: x,
                                        array [int] of int: cover,
                                        array [int] of var int: counts);
