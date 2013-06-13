% latin-squares-hybrid.mzn
% vim: ft=zinc ts=4 sw=4 et
%
% By Peter Stuckey
% Edited to conform to FD/LP hybrid by Ralph Becket.
%
% Latin squares hybrid.
%
% A latin square of size n is an n x n square
% where each row and column is a permutation of the numbers 1..n.
%
% A latin square of size 3 is 
%       1 2 3
%       2 3 1
%       3 1 2
%
% This model encodes the latin square x[i,j,k] = 1 if 
% the value of the square (i,j) is k and 0 otherwise.
%
% All the constraints should be handled by the MIP propagator
% whereas the search is handled by setting FD variables to 1.
% This should give very good search behaviour, with almost no
% backtracks.

int: n;

set of int: rg = 1..n;

array [rg, rg, rg] of var 0..1: x;
array [rg, rg, rg] of var 0.0..1.0: x_lp;

constraint
    forall (i, j, k in rg) (
        channel_fd_int_to_lp_float(x[i, j, k], x_lp[i, j, k])
    );

constraint forall (i, j in rg) (sum (k in rg) (x_lp[i, j, k]) = 1.0);
constraint forall (i, k in rg) (sum (j in rg) (x_lp[i, j, k]) = 1.0);
constraint forall (j, k in rg) (sum (i in rg) (x_lp[i, j, k]) = 1.0);

solve
    :: int_search(
        [x[i, j, k] | i, j, k in rg],
        input_order,
        indomain_max,
        complete
    )
    satisfy;

array [rg, rg] of var rg: solution =
    array2d(rg, rg, [sum (k in rg) (k * x[i, j, k]) | i, j in rg]);

output [show(solution[r, c]) ++ if c = n then "\n" else " " endif | r in rg, c in rg];
