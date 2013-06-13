% latin-squares-hybrid.mzn
% vim: ft=zinc ts=4 sw=4 et
%
% By Peter Stuckey
% Edited to conform to FD/LP hybrid by Ralph Becket.
%
% Latin squares FD version.
%
% A latin square of size n is an n x n square
% where each row and column is a permutation of the numbers 1..n.
%
% A latin square of size 3 is 
%       1 2 3
%       2 3 1
%       3 1 2
%
% This model uses alldifferent.

include "globals.mzn";

int: n;

set of int: rg = 1..n;

array [rg, rg] of var rg: x;

constraint forall (i in rg) (alldifferent (j in rg) (x[i, j]));
constraint forall (j in rg) (alldifferent (i in rg) (x[i, j]));

solve
    :: int_search(
        [x[i, j] | i, j in rg],
        input_order,
        indomain_max,
        complete
    )
    satisfy;

output [show(x[r, c]) ++ if c = n then "\n" else " " endif | r in rg, c in rg];
