% 
% SPOT5 earth observation satellite management problem in MiniZinc.
%
% E. Bensana, Michel Lemaitre, Gerard Verfaillie
% Earth Observation Satellite Management
% Constraints 4(3): 293-299 (1999)

% The  management problems  to  be solved  can  be roughly  described as
% follows:
%
% - given a set S of photographs which  can be taken  the next day from
%at   least  one of   the    three instruments,  w.r.t. the   satellite
%trajectory;  given,  for  each   photograph, a  weight  expressing its
%importance;
%
% - given a set of imperative constraints:  non overlapping and minimal
%transition   time  between two  successive    photographs on the  same
%instrument,  limitation  on the instantaneous  data   flow through the
%satellite telemetry and on the recording capacity on board;
%
% -  find  an admissible subset S'  of  S (imperative  constraints met)
%which maximizes the sum of the weights of the photographs in S'.

% 
% This MiniZinc model was created by Simon de Givry, degivry@toulouse.inra.fr
%

include "globals.mzn"; 

int: num_variables;

% domains
int:min_domain;
int:max_domain;
array[1..num_variables] of set of int: domains;

% objective function costs
% (memory consumption is not taken into account)
array[1..num_variables] of int: costs;

% binary and ternary constraints in extension
int: num_constraints2;
int: max_constraints2;
int: num_constraints3;
int: max_constraints3;
array[1..num_constraints2] of int: scopes2x;
array[1..num_constraints2] of int: scopes2y;
array[1..max_constraints2] of int: constraints2;
array[1..num_constraints2] of int: num_tuples2;
array[1..num_constraints2] of int: cum_tuples2;
array[1..num_constraints3] of int: scopes3x;
array[1..num_constraints3] of int: scopes3y;
array[1..num_constraints3] of int: scopes3z;
array[1..max_constraints3] of int: constraints3;
array[1..num_constraints3] of int: num_tuples3;
array[1..num_constraints3] of int: cum_tuples3;

% the assignments
array[1..num_variables] of var min_domain..max_domain: p;
int: obj_min = sum(j in 1..num_variables)(if costs[j] < 0 then costs[j] else 0 endif);
int: obj_max = sum(j in 1..num_variables)(if costs[j] > 0 then costs[j] else 0 endif);
var obj_min..obj_max: objective;

% solve minimize objective;
solve 
	:: seq_search([
		int_search(p, first_fail, indomain_min, complete),
		int_search([objective], input_order, indomain_min, complete)
	])
	minimize objective;

constraint
   objective = sum(j in 1..num_variables) ( costs[j] * bool2int(p[j] = 0) );
   
   % ensure that each variable takes a value in its domain
constraint
   forall(j in 1..num_variables) (
       p[j] in domains[j]
   );

   % hard binary constraints
constraint
   	forall(j in 1..num_constraints2) (
       	table(
			[p[scopes2x[j]], p[scopes2y[j]]], 
	   		array2d(1..num_tuples2[j], 1..2, 
				[ constraints2[u] 
				| u in (2*cum_tuples2[j]+1)..(2*cum_tuples2[j]+num_tuples2[j]*2)]
			)
		)
   );

   % hard ternary constraints
constraint
   	forall(j in 1..num_constraints3) (
       	table(
	   		[p[scopes3x[j]], p[scopes3y[j]], p[scopes3z[j]]], 
			array2d(1..num_tuples3[j],1..3,
				[ constraints3[u] 
				| u in (3*cum_tuples3[j]+1)..(3*cum_tuples3[j]+num_tuples3[j]*3)]
			)
		)
   );

output
[
  "p = ", show(p), ";\n",
  "objective = ", show(objective), ";\n"
];
