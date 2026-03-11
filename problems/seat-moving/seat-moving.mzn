%------------------------------------------------------------------------------%
% Seat Moving -
% MiniZinc Challenge 2018 Problem Submission
%
% Submitter: Toshimitsu Fujiwara
%
% Move person sitting at start position to goal position.
%  Person can empty seat as temporary space.
%  Some person can be swapped directly. (for an instance, having small luggage)
%
% Modified by MiniZinc team:
%   - Beautification of code
%   - Adjustments of the output item
%------------------------------------------------------------------------------%
% Includes

include "alldifferent_except_0.mzn";
include "alldifferent.mzn";

%------------------------------------------------------------------------------%
% Parameters and Variables

% number of seats
int: S;

% number of person
int: P;

% flags
array[1..P] of bool: Can_swap;

% max step.
% (keep small to keep search space small)
int: MAX_STEP = (2 * S) div (S - P + 1) + 1;
% int: MAX_STEP = (2 * S);

% move cost
var 0..P * MAX_STEP: cost;

% step
var 0..MAX_STEP: step;

% objective = step * ub(cost) + cost
var 0..MAX_STEP * MAX_STEP * P + MAX_STEP * P : objective;

% state of start and goal
array[1..S] of int: Start;
array[1..S] of int: Goal;


% seat[i, s] means "Who is at s in step i"
% 0 means "empty seat"
array[1..MAX_STEP, 1..S] of var 0..P: seat;

% person[i, p] means persion "p" is at "person[i, p]" in step i
array[1..MAX_STEP, 1..P] of var 1..S: person;

%------------------------------------------------------------------------------%
% Constraints

%
% bind initial and last seating
%
constraint
	forall(i in 1..S) (
		 seat[1, i] = Start[i]
		 /\ seat[MAX_STEP, i] = Goal[i]
	);

%
% bind person and seat
%
constraint
	forall(i in 1..MAX_STEP) (
		forall(p in 1..P) (
			seat[i, person[i, p]] = p
		)
	);

% person don't appear twice
constraint
	forall(i in 1..MAX_STEP) (
		alldifferent_except_0 ([seat[i, s] | s in 1..S])
	);

constraint redundant_constraint(
	forall(i in 1..MAX_STEP) (
		alldifferent([person[i, p] | p in 1..P])
	)
);

%
% objective
%
constraint objective = step * P * MAX_STEP + cost;

%
% cost
%
constraint cost = sum([ 
    sum(
        [ bool2int(person[i, p] != person[i + 1, p]) 
        | p in 1..P]
    ) 
| i in 1..MAX_STEP - 1
]);


% Don't move after all seats are fixed.
constraint
	forall(i in 1..MAX_STEP) (
		step < i -> forall(s in 1..S) (seat[i, s] = Goal[s])
	);

%
% moving constraint
%
% allowed moves:
%   * person having small equipments (Can_swap = 1) and swap two seats
%   * move to empty seat
%
constraint
	forall(i in 1..MAX_STEP - 1, p in 1..P) (
	    person[i, p] != person[i + 1, p] -> (
                (Can_swap[p] /\ person[i, p] = person[i + 1, seat[i, person[i + 1, p]]])
	        \/  seat[i, person[i + 1, p]] = 0
        )
	);

%------------------------------------------------------------------------------%
% Solve item and search

solve 
    :: seq_search([
        int_search(array1d(person), first_fail, indomain_min, complete),
        int_search(array1d(seat), first_fail, indomain_min, complete),
	    int_search([step], first_fail, indomain_split, complete),
	    int_search([cost], first_fail, indomain_split, complete),
	    int_search([objective], first_fail, indomain_min, complete),
    ])
    minimize objective;

%------------------------------------------------------------------------------%
% Output item

output [
    "seat = array2d(1..\(MAX_STEP), 1..\(S), \(seat));\n",
    "step = \(step);\n",
    "cost = \(cost);\n",
    "objective = \(objective);\n"
];

%------------------------------------------------------------------------------%
