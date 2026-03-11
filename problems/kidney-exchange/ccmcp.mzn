% Cardinality-constrained Multi-cycle Problem (CCMCP)
% 
% This problem appears as one of the main optimization problems modelling 
% kidney exchange. The problem consists of the prize-collecting assignment
% problem and an addition constraint stipulating that each subtour in the graph
% has a maximum length K. If K = 2 or K = infinity, the problem is 
% polynomially-solvable. Otherwise, it is NP-hard.
%
% Further details on the problem can be found in:
% On the kidney exchange problem: cardinality constrained cycle and chain
% problems on directed graphs: a survey of integer programming approaches.
% Vicky Mak-Hau, J Comb Optim (2017) 33:35–59
%
% Edward Lam <edward.lam@monash.edu>
% Vicky Mak-Hau <vicky.mak@deakin.edu.au>

include "globals.mzn";

int: V;                                          % Number of vertices
int: K;                                          % Maximum length of each subtour

set of int: VERTICES = 1..V;                     % Set of vertices
array[VERTICES,VERTICES] of int: edge_weight;    % Weight of each edge

array[VERTICES] of var VERTICES: succ;           % Successor variable indicating next vertex in the cycle
array[VERTICES] of var VERTICES: cycle;          % Index of a cycle

int: obj_ub = sum(i in VERTICES)(max(j in VERTICES)(edge_weight[i,j]));
var 0..obj_ub: objective;                        % Objective variable

% Check
constraint forall(i in VERTICES)(assert(edge_weight[i,i] == 0, "Loop must have zero cost"));

% Path in a cycle
constraint alldifferent(succ);                                                                         % Out-degree of two
constraint forall(i in VERTICES)(cycle[i] == cycle[succ[i]]);                                          % Connectivity
constraint forall(i in VERTICES, j in VERTICES where i != j)(edge_weight[i,j] < 0 -> succ[i] != j);    % Disable infeasible edges

% Maximum cycle length
constraint bin_packing(K, cycle, [1 | i in VERTICES]);

% Objective function
constraint objective = sum(i in VERTICES)(edge_weight[i,succ[i]]);

% Symmetry-breaking
constraint symmetry_breaking_constraint(seq_precede_chain(cycle));

% Search strategy
solve 
    :: seq_search([
        int_search(succ, first_fail, indomain_median, complete)
    ]) 
    maximize objective;

% Output
output [
	"succ = array1d(1..\(V), \(succ));\n",
	"cycle = array1d(1..\(V), \(cycle));\n",
	"objective = \(objective);\n"
];
