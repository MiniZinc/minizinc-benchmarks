% Open Stacks problem
% Peter J. Stuckey
% 1/7/2009

include "globals.mzn";

int: c; % number of customers
int: p; % numer of products

%-- Types ---------------------------------------------------------------------
set of int: Custs = 1..c;
set of int: Prods = 1..p;

% Orders matrix: binary array indicating which customers ordered which products.
array[Custs,Prods] of 0..1: orders;

% Total number of products ordered by each customer.
array[Custs] of int: norders = [ sum(j in Prods)(orders[i,j]) | i in Custs ];

%-- Decision variables --------------------------------------------------------

% Production schedule: a permutation of all products, defining manufacturing order.
array[Prods] of var Prods: s;

%-- Auxiliary variables ------------------------------------------------------

% Cumulative orders fulfilled: o[i,t] counts how many products customer i has received by time t.
array[Custs,0..p] of var 0..max(norders): o;
% Objective: peak number of simultaneously open stacks across all time steps.
var 0..c: objective;

%-- Constraints ---------------------------------------------------------------

constraint alldifferent(s); % each product scheduled once

constraint forall (i in Custs)(o[i,0] = 0);   % no orders at time 0
	
constraint forall(t in 1..p, i in Custs)(o[i,t] = o[i,t-1] + orders[i,s[t]]);

constraint objective = 
    max(j in Prods)(
  	    sum(i in Custs)(
		    bool2int( o[i,j-1] < norders[i] /\ o[i,j] > 0 )
	    )
    );

%-- Solving objective and solution output -------------------------------------

solve ::
      int_search(s, input_order, indomain_min, complete)
      minimize objective;

output [
    "s = \(s);\n",
    "objective = \(objective);\n",
] ++ [
    if t = 1 then "% " else "" endif ++
    "\(o[i,t])" ++ 
    if t = p then "\n" else " " endif
| i in Custs, t in 1..p
];
