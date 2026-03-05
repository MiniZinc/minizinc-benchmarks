%
% Put n pennies on a chessboard, so that all distances between pennies are distinct
%
% Inspired by https://blog.computationalcomplexity.org/2023/06/can-you-put-n-pennies-on-n-x-n.html
%
% Model by Mikael Zayenz Lagerkvist
%

include "globals.mzn";

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Data definitions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Size of chess board
int: n;
set of int: N = 1..n;

set of int: NN = 1..n*n;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Data definitions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% If the penny is placed
array[N] of var bool: is_present;

% X position of pennies
array[N] of var opt N: x;
% Y posittion of pennies
array[N] of var opt N: y;

% Position of pennies  on board
array[N] of var opt NN: xy;

var N: pennies;

% Distances between pennies
% Note: without the square root for keeping integrality, 
%       but will still maintains uniqueness properties
array[int] of var opt int: distances = [
    if absent(x[i]) \/ absent(x[j]) \/ absent(y[i]) \/ absent(y[j]) then
        <>
    else 
        pow(deopt(x[i])-deopt(x[j]), 2) + pow(deopt(y[i])-deopt(y[j]), 2)
    endif
  | i, j in N where i < j
];

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Constraints
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Only a single penny on a square
constraint all_different(xy);

% All the distances are unique
constraint all_different(distances);

% Connect the x and y variables with the combined xy-variables
constraint forall (i in N) (
    xy[i] = ((x[i]~-1) ~* n) ~+ (y[i]~-1)
);

% Connection, presence is connected through the variables
constraint forall (i in N) (
    is_present[i] = occurs(x[i]) /\
    is_present[i] = occurs(y[i]) /\
    is_present[i] = occurs(xy[i])
);

% Symmetry breaking, the pennies have no identity
constraint symmetry_breaking_constraint(forall (i, j in N where i+1=j) (
    xy[i] < xy[j] /\
    if j > pennies then
       xy[j] = <>
    else
       xy[j] != <>
    endif
));
constraint symmetry_breaking_constraint(decreasing(is_present));

% Count the number of pennies
constraint pennies = sum(is_present);


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Serarch and output
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

solve 
    :: int_search([
        % Search placement for each penny in order
        [
            % With indomain_min, the negation makes the penny used as first choice
            not is_present[i], 
            % Then select the placement with the x and y component separately
            x[i], 
            y[i]
        ][p] | i in N, p in 1..3], 
        input_order, 
        indomain_min)
     maximize pennies;

output [
    show2d(array2d(N, N, [exists(p in N) (x[p] = i /\ y[p] = j) | i,j in N])), "\n", 
    show(distances), "\n", 
    show(x), "\n", 
    show(y), "\n", 
    show(pennies)
];