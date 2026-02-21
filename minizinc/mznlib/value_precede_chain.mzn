% Crusher: value_precede_chain is symmetry breaking — counterproductive for local search.
% Override with no-op so MiniZinc doesn't decompose it into int_eq_reif/int_max chains.
predicate value_precede_chain(array [int] of int: c, array [int] of var int: x) = true;
