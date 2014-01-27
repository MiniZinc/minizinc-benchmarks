% 
% CELAR radio link frequency assignment problem in MiniZinc.
%
% B. Cabon, S. de Givry, L. Lobjois, T. Schiex, and J.P. Warners
% Radio Link Frequency Assignment
% Constraints, 4(1):79-89, 1999
%
% The  "Radio  Link   Frequency Assignment Problem"   (RLFAP)  consists in
% assigning frequencies   to communication  links in such   a way  that  no
% interferences  occurs. Domains  are   set  of integers (non   necessarily
% consecutives). In the simplest case  which is  considered here, only two
% types of constraint occur: 
% 1- the absolute  difference  between   two  frequencies   should  be
%   greater than a given number k (|x-y|>k);
% 2- the absolute  difference between two  frequencies should  exactly
%   be equal to a given number k' (|x-y|=k).
% If there is no solution, (1) become soft constraints while (2) remain hard constraints
% and you have to minimize a weighted sum of the violated soft constraints.

% 
% This MiniZinc model was created by Simon de Givry, degivry@toulouse.inra.fr
%

include "globals.mzn"; 

% objective function weights
% (mobility costs are not taken into account)
array[1..4] of int: costs;

% domain categories
int: num_categories;
array[1..num_categories] of set of int: categories;
int:min_freq;
int:max_freq;

% number of frequency variables
int: num_variables;

% domain category index for each variable
array[1..num_variables] of int: domains;

% hard equality constraints
int: num_hardconstraints;
array[1..num_hardconstraints] of int: hardctrx;
array[1..num_hardconstraints] of int: hardctry;
array[1..num_hardconstraints] of int: hardctrk;

% soft inequality constraints
int: num_softconstraints;
array[1..num_softconstraints] of int: softctrx;
array[1..num_softconstraints] of int: softctry;
array[1..num_softconstraints] of int: softctrk;
array[1..num_softconstraints] of int: softctrw;

% the assignments
array[1..num_variables] of var min_freq..max_freq: f;

int: obj_min = sum(j in 1..num_softconstraints)(min(0, costs[softctrw[j]]));
int: obj_max = sum(j in 1..num_softconstraints)(max(0, costs[softctrw[j]]));
var obj_min..obj_max: objective;

% solve minimize objective;
solve 
	:: seq_search([
		int_search(f, first_fail, indomain_min, complete),
		int_search([objective], input_order, indomain_min, complete)
	])
	minimize objective;

% Constraints
constraint
   	objective = sum(j in 1..num_softconstraints)( 
   		costs[softctrw[j]] * 
			bool2int(abs(f[softctrx[j]] - f[softctry[j]]) <= softctrk[j])
	);

	% ensure that each variable takes a value in its domain
constraint
   forall(j in 1..num_variables) (
       f[j] in categories[domains[j]]
   );

   % hard equality constraints
constraint
   forall(j in 1..num_hardconstraints) (
       abs(f[hardctrx[j]] - f[hardctry[j]]) = hardctrk[j]
   );

% Output item
output
[
	"f = ", show(f), ";\n",
  	"objective = ", show(objective), ";\n"
];
