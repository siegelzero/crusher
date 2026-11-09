include "fzn_disjunctive_opt.mzn";
include "fzn_disjunctive_strict_opt_decomp.mzn";

% Strict and non-strict coincide when no task can have duration 0.
predicate fzn_disjunctive_strict_opt(array [int] of var opt int: s, array [int] of var int: d) =
  if lb_array(d) > 0 then fzn_disjunctive_opt(s, d)
  else fzn_disjunctive_strict_opt_decomp(s, d)
  endif;
