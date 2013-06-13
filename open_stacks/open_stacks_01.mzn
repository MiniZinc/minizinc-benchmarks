% Open Stacks problem
% Peter J. Stuckey
% 1/7/2009

include "globals.mzn";

int: c; % number of customers
int: p; % numer of products

%-- Types ---------------------------------------------------------------------
set of int: Custs = 1..c;
set of int: Prods = 1..p;

array[Custs,Prods] of 0..1: orders; % which customer orders which product

array[Custs] of int: norders = [ sum(j in Prods)(orders[i,j]) | i in Custs ];
	     %% total orders of each customer

%-- Decision variables --------------------------------------------------------

array[Prods] of var Prods: s; % schedule of products

%-- Auxilliary variables ------------------------------------------------------

array[Custs,0..p] of var int: o ; % orders filled after time t
%% array[Prods] of var int: open; 
var int: objective;

%-- Constraints ---------------------------------------------------------------

constraint alldifferent(s); % each product scheduled once

constraint
        forall (i in Custs)(o[i,0] = 0) /\   % no orders at time 0
	forall(t in 1..p, i in Custs)(
               o[i,t] = o[i,t-1] + orders[i,s[t]] );

%% constraint objective = max(j in Prods)(open[j]);
%% constraint forall(j in Prods)(
%% 	   	     open[j] == sum(i in Custs)(
%% 		     	   bool2int( o[i,j-1] < norders[i] /\ o[i,j] > 0 )
%% 		     )
%% 	       );
constraint objective = max(j in Prods)(
  	                   sum(i in Custs)(
		     	       bool2int( o[i,j-1] < norders[i] /\ o[i,j] > 0 )
		           )
	               );

%-- Solving objective and solution output -------------------------------------

solve ::
      int_search(s, input_order, indomain, complete)
      minimize objective;

output [
    "s = ", show(s), "\n",
    "objective = ", show(objective), "\n"
];
