%
% Make Leagues
%
% Make leagues for some games.
%   - Ranking should be close in each league.
%   - In a league, variety of country (where player comes from) is needed.

include "globals.mzn";

%
% Parameter: max persons in one league
%
int: n_persons_in_league;

% n_persons_in_league = 3;

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

% How many leagues in this model?
int: n_league = (n + n_persons_in_league - 1) div n_persons_in_league;

% How many people in each league
array [1..n_league] of var 0..n_persons_in_league : n_persons;

% Which league person assigned to 
array [1..n] of var 1..n_league: assign_to;

% ranking in each league
array [1..n_league] of var min(ranking)..max(ranking): max_rank;
array [1..n_league] of var min(ranking)..max(ranking): min_rank;
array [1..n_league] of var min(ranking)..max(ranking): rank_diff;

% for cardinality of a league
array[1..n_league*(max(country)+1)] of var 0..1: card_of_league_tmp;
array[1..n_league] of var 1..n_persons_in_league: card_of_league;



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%
% apply n_persons_in_league
%
constraint
	forall (i in 1..n_league) (
		count(assign_to, i, n_persons[i])
		/\ (n_persons_in_league - 1) <= n_persons[i]
		/\ n_persons[i] <= n_persons_in_league
	);

%
% min, max rank in league
%
constraint
	forall (i in 1..n_league) (
		forall (j in 1..n) (
			((assign_to[j] = i)
				-> (max_rank[i] >= ranking[j]))
		)
	);

constraint
	forall (i in 1..n_league) (
		forall (j in 1..n) (
			((assign_to[j] = i)
				-> (min_rank[i] <= ranking[j]))
		)
	);

%
% difference of ranking in same league
%
constraint
	forall (i in 1..n_league) (
		rank_diff[i] = max_rank[i] - min_rank[i]
	);
%
% cardinality of the league
%
constraint
	forall (i in 1..n_league) (
		forall (j in 1..max(country)) (
			card_of_league_tmp[(i-1) * max(country) + (j-1) + 1]
				= bool2int(exists(p in 1..n)
					(assign_to[p] = i /\ country[p] = j))
		)
	);

constraint
	forall (i in 1..n_league) (
		card_of_league[i]
		 = sum([card_of_league_tmp[(i-1) * max(country) + (j-1) + 1]
					   | j in 1..max(country)])
	);

constraint
	forall (i in 1..n_league - 1) (
		max_rank[i] <= max_rank[i + 1]
	);

var 1..10000000 : obj = (10000 * sum(rank_diff) - sum(card_of_league));

solve
	:: seq_search([
		int_search(assign_to, first_fail, indomain_max, complete),
		int_search(rank_diff, first_fail, indomain_min, complete)
	])
	minimize obj;

output ["max_rank: " ++ show(max_rank)  ++ "\n"
	++ "min_rank: " ++ show(min_rank) ++ "\n"
	++ "card_of_league: " ++ show(card_of_league) ++ "\n"
	++ "obj: " ++ show(obj) ++ "\n"
	]
	++ [show(assign_to[i])
	    ++ ", " ++ "person: " ++ show(i)
	    ++ ", " ++ "ranking: " ++ show(ranking[i])
	    ++ ", " ++ "country: " ++ show(country[i])
	    ++ "\n"
	    | i in 1..n]
