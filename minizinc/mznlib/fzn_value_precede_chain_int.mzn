% Crusher: decompose the chain into pairwise value_precede on consecutive
% values. value_precede_chain([c_1,...,c_k], x) holds iff, for every i,
% value_precede(c_i, c_{i+1}, x) holds: the standard seq_precede_chain over the
% rank array requires rank j to appear only after rank j-1, which is exactly the
% conjunction of the consecutive value_precede constraints. We prefer this form
% over MiniZinc's default seq_precede_chain decomposition (array_int_element +
% int_max running-maximum) because that running-max formulation leaves local
% search stuck in a cost-1 local minimum, whereas the boolean-chain
% value_precede decomposition is search-friendly.
include "fzn_value_precede_int.mzn";

predicate fzn_value_precede_chain_int(array [int] of int: T, array [int] of var int: X) =
  forall (i in min(index_set(T))..max(index_set(T)) - 1) (
    fzn_value_precede_int(T[i], T[i + 1], X)
  );
