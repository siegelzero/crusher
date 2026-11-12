include "fzn_connected.mzn";

% Undirected tree rooted at r: the selected edges join selected nodes only,
% connect all selected nodes, and number one less than them. This replaces the
% standard parent/distance decomposition with crusher's native connected
% constraint (which honours es unless it proves es is induced by ns).
predicate fzn_tree(
  int: N,
  int: E,
  array [int] of int: from,
  array [int] of int: to,
  var int: r,
  array [int] of var bool: ns,
  array [int] of var bool: es,
) =
  ns[r] /\
    forall (e in index_set(es)) (es[e] -> (ns[from[e]] /\ ns[to[e]])) /\
    sum (e in index_set(es)) (bool2int(es[e])) = sum (n in index_set(ns)) (bool2int(ns[n])) - 1 /\
    fzn_connected(from, to, ns, es);
