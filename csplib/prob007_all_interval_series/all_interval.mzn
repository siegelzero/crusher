% All-Interval Series in MiniZinc.
% CSPLib Problem 007
%
% Given the twelve standard pitch classes (c, c#, d, ...), a series of
% all twelve without repetition is called an all-interval series if
% each of the eleven intervals between consecutive notes is unique.
%
% Generalized: find a permutation of {0, 1, ..., n-1} such that the
% absolute differences between consecutive elements form a permutation
% of {1, 2, ..., n-1}.
%
% This model by Hakan Kjellerstrand.
% Licenced under CC-BY-4.0 : http://creativecommons.org/licenses/by/4.0/

include "globals.mzn";

int: n;

set of int: classes = 0..n-1;
set of int: differ = 1..n-1;

% Search space: The set of permutations of integer range [0..n-1]
array[classes] of var classes: series;
array[0..n-2] of var differ: differences;

solve :: int_search(series, first_fail, indomain_max, complete) satisfy;

constraint
   % C1: Each pitch class occurs exactly once
   all_different(series)
   /\
   % C2: Differences between neighbouring notes are all different
   forall(i in 0..n-2) (
          differences[i] = abs(series[i+1] - series[i])
   )
   /\
   all_different(differences)
   /\
   % Symmetry breaking: first note < last note
   series[0] < series[n-1]
;

output [
   "series: " ++ show(series) ++ "\n" ++
   "differences: " ++ show(differences)
];
