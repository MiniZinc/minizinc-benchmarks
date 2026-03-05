%
% Make Leagues (group tournament)
%
% Make group tournament for some games.
%   - Ranking should be close in each group.
%   - In one group, variety of country (where player comes from) is needed.

include "globals.mzn";

%
% Parameter: max persons in one group
%
int: n_persons_in_group;

% n_persons_in_group = 3;

%
% Parameter: number of persons
%
int: n;

% n = 15;

%
% Parameter: ranking of persons
%
array [1..n] of int: ranking;

% ranking = [ 1, 2, 3, 3, 3, 4, 4, 4, 4, 4, 5, 5, 5, 5, 6 ];

%
% Parameter: where does he/she come from
%
array [1..n] of int: country;

% country = [ 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 3, 2, 1 ];


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% How many groups in this model?
int: n_groups = (n + n_persons_in_group - 1) div n_persons_in_group;

% How many people in each group
array [1..n_groups] of var 0..n_persons_in_group : n_persons;

% Which group person is assigned to 
array [1..n] of var 1..n_groups: assign_to;

% Ranking in each groups
array [1..n_groups] of var min(ranking)..max(ranking): max_rank;
array [1..n_groups] of var min(ranking)..max(ranking): min_rank;
array [1..n_groups] of var 0..max(ranking): rank_diff;

% Count of countries in group
% if group G contains country C, countries_in_group_tmp[G, C] = 1
array[1..n_groups, 1..max(country)] of var 0..1: countries_in_group_tmp;
array[1..n_groups] of var 1..n_persons_in_group: countries_in_group;



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%
% apply n_persons_in_group
%
constraint
	forall (i in 1..n_groups) (
		count(assign_to, i, n_persons[i])
		/\ (n_persons_in_group - 1) <= n_persons[i]
		/\ n_persons[i] <= n_persons_in_group
	);

%
% set rank_diff
%
constraint
	forall (i in 1..n_groups) (
		rank_diff[i] = max_rank[i] - min_rank[i]
	);

%
% min, max rank in group
%
constraint
	forall (i in 1..n_groups) (
		max_rank[i] = max([ranking[j] * bool2int(assign_to[j] == i)
				 | j in 1..n])
	);

constraint
	forall (i in 1..n_groups) (
		min_rank[i] = min([ranking[j] + 10000* bool2int(assign_to[j] != i)
				 | j in 1..n])
	);

%
% how many countries in group?
%
constraint
	forall (i in 1..n_groups) (
		forall (j in 1..max(country)) (
			countries_in_group_tmp[i, j]
				= bool2int(exists(p in 1..n)
					(assign_to[p] = i /\ country[p] = j))
		)
	);

constraint
	forall (i in 1..n_groups) (
		countries_in_group[i]
		 = sum([countries_in_group_tmp[i, j] | j in 1..max(country)])
	);

%
% sort result
%
constraint
	forall (i in 1..n_groups - 1) (
		max_rank[i] <= max_rank[i + 1]
	/\ 	min_rank[i] <= min_rank[i + 1]
	);

var 1..100000 : objective = (100 * sum(rank_diff) - sum(countries_in_group));

solve
	:: seq_search([
		int_search(assign_to, first_fail, indomain_max, complete),
		int_search([objective], input_order, indomain_min, complete)
	])
	minimize objective;

output [
	"max_rank = ", show(max_rank), ";\n",
	"min_rank = ", show(min_rank), ";\n",
	"countries_in_group = ", show(countries_in_group),  ";\n",
	"objective = ", show(objective), ";\n"
] ++ [
	show(assign_to[i]) ++
	", person: " ++ show(i) ++
	", ranking: " ++ show(ranking[i]) ++
	", country: " ++ show(country[i]) ++
	"\n"
| i in 1..n];

