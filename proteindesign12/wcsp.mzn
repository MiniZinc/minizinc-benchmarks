%
% Binary Weighted CSP wcsp format reader for MiniZinc
%
% A Weighted Constraint Satisfaction Problem (WCSP) P is a triplet P=(X,F,k)
% where X is a set of variables and F a set of cost functions. 
% Each variable has a finite domain of values that can be assigned to it. 
% A binary (resp. unary) cost function f(x,y) in F (resp. f(x))
% is a function which associates to every assignment t of its variable(s) 
% a positive integer in [0,k] where k is a maximum integer cost 
% used for representing forbidden assignments.
% 
% The Weighted Constraint Satisfaction Problem is to find a complete assignment t
% minimizing the total cost sum_{f(x) in F} f(t[x]) + sum_{f(x,y) in F} f(t[x],t[y])
% where t[x] denotes the projection of t over variable x.
% This optimization problem has an associated NP-complete decision problem.
%
% See https://mulcyber.toulouse.inra.fr/scm/viewvc.php/trunk/toulbar2/doc/?root=toulbar2
% or http://costfunction.org/mobyle/htdocs/portal/help/wcsp.html
% or http://graphmod.ics.uci.edu/group/WCSP_file_format
% for a more general description of the wcsp format (including global cost functions)
%
% Usage: awk -f wcsp2dzn.awk smallrandom.wcsp 10 1 > smallrandom.dzn
%        minizinc wcsp.mzn smallrandom.dzn
%
% Warning: wcsp problem file must have only unary and binary cost functions in extension with all tuples defined
%

% 
% This MiniZinc model was created by Simon de Givry, degivry@toulouse.inra.fr
%

include "globals.mzn"; 

int: num_variables;

% domains
int:max_domain;
array[1..num_variables] of int: domains;

% unary and binary cost functions in extension
int: top;
int: num_constraints1;
int: max_constraints1;
int: max_costs1;
int: num_constraints2;
int: max_constraints2;
int: max_costs2;
array[1..num_constraints1] of int: func1x;
array[1..num_constraints1] of int: num_tuples1;
array[1..num_constraints1] of int: cum_tuples1;
array[1..max_constraints1] of int: costs1;
array[1..num_constraints2] of int: func2x;
array[1..num_constraints2] of int: func2y;
array[1..num_constraints2] of int: num_tuples2;
array[1..num_constraints2] of int: cum_tuples2;
array[1..max_constraints2] of int: costs2;

% the assignments
array[1..num_variables] of var 0..max_domain: p;

% objective function costs
array[1..num_constraints1] of var 0..max_costs1: ocosts1;
array[1..num_constraints2] of var 0..max_costs2: ocosts2;
var 0..(top-1): objective;

% solve minimize objective;
solve 
	:: seq_search([
		int_search(p, first_fail, indomain_min, complete),
		int_search(ocosts1, first_fail, indomain_min, complete),
		int_search(ocosts2, first_fail, indomain_min, complete),
		int_search([objective], input_order, indomain_min, complete)
	])
	minimize objective;

constraint
   	objective = sum(j in 1..num_constraints1)( ocosts1[j] ) 
   		+ sum(j in 1..num_constraints2) ( ocosts2[j] );

	% ensure that each variable takes a value in its domain
constraint
   forall(j in 1..num_variables) (
       p[j] < domains[j]
   );

   	% unary cost functions
constraint
   	forall(j in 1..num_constraints1) (
       	table(
	   		[ocosts1[j], p[func1x[j]]], 
			array2d(1..num_tuples1[j],1..2,
				[costs1[u] | u in (2*cum_tuples1[j]+1)..(2*cum_tuples1[j]+num_tuples1[j]*2)]
			)
		)
   	);
	
	% binary cost functions
constraint
	forall(j in 1..num_constraints2) (
       	table(
			[ocosts2[j], p[func2x[j]], p[func2y[j]]], 
			array2d(1..num_tuples2[j],1..3,
				[costs2[u] | u in (3*cum_tuples2[j]+1)..(3*cum_tuples2[j]+num_tuples2[j]*3)]
			)
		)
   	);

output
[
  "p = ", show(p), ";\n",
  "objective = ", show(objective), ";\n"
];
