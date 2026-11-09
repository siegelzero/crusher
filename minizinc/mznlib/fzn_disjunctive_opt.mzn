include "crusher_disjunctive_opt.mzn";

% Elements known to be absent at compile time are dropped (deopt(<>) is undefined).
predicate fzn_disjunctive_opt(array [int] of var opt int: s, array [int] of var int: d) =
  let {
    array [int] of int: idx = [i | i in index_set(s)
                                 where not (is_fixed(occurs(s[i])) /\ not fix(occurs(s[i])))];
  } in
  crusher_disjunctive_opt([deopt(s[i]) | i in idx], [occurs(s[i]) | i in idx], [d[i] | i in idx]);
