% Override array_int_element to add compile-time domain filtering.
% For constant arrays, restrict the index to values where the array
% maps into the result variable's domain. This propagates domain
% tightenings (e.g., from hard constraints) back to the index variable.
predicate array_int_element(var int: idx, array [int] of int: x, var int: c) =
    idx in { i | i in index_set(x) where x[i] in dom(c) } /\
    fzn_array_int_element(idx, x, c);
