% MIT License
%
% Copyright (c) 2026 Kenneth Brown
%
% Permission is hereby granted, free of charge, to any person obtaining a copy
% of this software and associated documentation files (the "Software"), to deal
% in the Software without restriction, including without limitation the rights
% to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
% copies of the Software, and to permit persons to whom the Software is
% furnished to do so, subject to the following conditions:
%
% The above copyright notice and this permission notice shall be included in
% all copies or substantial portions of the Software.
%
% THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
% IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
% FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
% AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
% LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
% OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
% SOFTWARE.

% Turán-type extremal problem for C4 (the Zarankiewicz problem z(n; 2,2)).
%
% Maximise the number of edges in a simple graph on n vertices that contains
% no 4-cycle (C4). A graph is C4-free iff every pair of distinct vertices has
% at most one common neighbour. The maximum edge count is the Zarankiewicz
% number ex(n; C4) = OEIS A006855; for n = q^2 + q + 1 with q a prime power the
% incidence graph of a projective plane is extremal. Exact optima are known
% only up to n = 40 (B. McKay), so larger instances are at the research
% frontier. See https://oeis.org/A006855 for optima and bounds.
%
% Decision variables: the adjacency matrix (0/1). The model is a pure integer
% optimisation problem (no floats, no sets).

int: n;

array[1..n, 1..n] of var 0..1: adj;

% No self-loops.
constraint forall(i in 1..n)(adj[i,i] = 0);

% Undirected: the adjacency matrix is symmetric.
constraint forall(i in 1..n, j in i+1..n)(adj[i,j] = adj[j,i]);

% C4-free: every pair of vertices shares at most one common neighbour.
constraint forall(i in 1..n, j in i+1..n)(
    sum(k in 1..n where k != i /\ k != j)(adj[i,k] * adj[j,k]) <= 1
);

var int: edges = sum(i in 1..n, j in i+1..n)(adj[i,j]);

solve
    :: int_search([adj[i,j] | i, j in 1..n where i < j],
                  input_order, indomain_max, complete)
    maximize edges;

output [
    "edges = \(edges)\n",
] ++ [
    if j = 1 then "\n" else "" endif ++
    if fix(adj[i,j]) = 1 then "1 " else ". " endif
    | i in 1..n, j in 1..n
] ++ ["\n"];
