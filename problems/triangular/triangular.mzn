%------------------------------------------------------------------------------%
% Placing 'Hearts' on Corners in Equilateral Triangular Grids
%
% The problem is to find, for an equilateral triangular grid of
% side N, the maximum number of grid nodes that can have a 'heart' placed
% on them without any placed heart lying on the corners of an equilateral
% triangle of any size or orientation. 
%
% (Taken from Daily Telegraph and Sunday Times)
%------------------------------------------------------------------------------%
% Parameters

int: n;                 % Number of sides of the grid
set of int: N = 1..n;

%------------------------------------------------------------------------------%
% Variables

array [N, N] of var 0..1: heart;    % Grid of equilateral triangulars

var 1..n*n: objective;              % Number of 'hearts' in the grid

constraint objective = sum(i in N, j in 1..i)(heart[i, j]);

%------------------------------------------------------------------------------%
% Constraints

    % 'Hearts' constraints
    %
constraint
    forall(i in 1..n, j in 1..i, k in 1..n-i, m in 0..k-1)(
        heart[i+m, j] + heart[i+k, j+m] + heart[i+k-m, j+k-m] <= 2
    );

constraint
    forall(i in 1..n, j in (i+1)..n)(
        heart[i, j] = 0
    );

%------------------------------------------------------------------------------%
% Search and Objective

solve 
    :: search
    maximize objective;

ann: search = 
    int_search(
        [heart[i, j] | i in N, j in 1..i], input_order, indomain_max, complete
    );

%------------------------------------------------------------------------------%
% Output

output [ 
    "objective = ", show(objective), ";\n",
    "heart = array2d(", show(N), ", ", show(N), ", [\n"
] ++ [
    show(heart[i, j])
    ++ if j = n /\ i = n then "" else ", " endif 
    ++ if j = n then "\n" else "" endif
| i in N, j in 1..n
] ++ [
    "]);\n"
] ++ [
    if j = 1 then "%%   " else "" endif
    ++ show(heart[i, j]) ++ " "
    ++ if j == i then "\n" else "" endif
| i in N, j in 1..i ];


%------------------------------------------------------------------------------%
