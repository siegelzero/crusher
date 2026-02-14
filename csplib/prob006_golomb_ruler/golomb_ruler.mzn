%-----------------------------------------------------------------------------
% Golomb rulers
% CSPLib Problem 006
%-----------------------------------------------------------------------------
% From CSPLib:
% A Golomb ruler may be defined as a set of m integers 0 = a_1 < a_2 <
% ... < a_m such that the m(m-1)/2 differences a_j - a_i, 1 <= i < j
% <= m are distinct. Such a ruler is said to contain m marks and is of
% length a_m. The objective is to find optimal (minimum length) or
% near optimal rulers.
%
% This is the "ternary constraints and an alldifferent" model from the
% MiniZinc benchmarks repository.
%-----------------------------------------------------------------------------

include "globals.mzn";

int: m;
int: n = m * m;

array[1..m] of var 0..n: mark;

array[1..(m*(m-1)) div 2] of var 0..n: differences =
    [ mark[j] - mark[i] | i in 1..m, j in i+1..m];

% First mark is at position 0
constraint mark[1] = 0;

% Marks are strictly increasing
constraint forall ( i in 1..m-1 ) ( mark[i] < mark[i+1] );

% All pairwise differences are distinct
constraint alldifferent(differences);

% Symmetry breaking: first difference < last difference
constraint differences[1] < differences[(m*(m-1)) div 2];

solve :: int_search(mark, input_order, indomain, complete)
    minimize mark[m];

output [show(mark)];
