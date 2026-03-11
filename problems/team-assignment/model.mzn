%------------------------------------------------------------------------------%
% Optimal Team Assignment -
% MiniZinc Challenge 2018 Problem Submission
%
% Author: Erik Thörnbald (Uppsala University)
%
% Modified by MiniZinc team:
%   - Replaced the value_precede_chain constraint by redundant equality 
%     constraints, which assigns the first top ranked players to the head
%     of their teams.
%
%------------------------------------------------------------------------------%
% Includes

include "globals.mzn";

%--------------Parameters----------------
int: boards; 
int: teams;
int: players;

int: maxRating;
int: minRating;
int: requests;
int: singleRequests;
int: doubleRequests;

set of int: Requestees;

array[1..singleRequests,1..2] of 1..players: SingleRequested;
array[1..doubleRequests,1..2] of 1..players: DoubleRequested;

array[1..players] of 1..boards: Board;
array[1..players] of int: Rating;


%--------------Variables----------------

array[1..players] of var 1..teams: Team;
array[1..teams] of var 0..boards*maxRating: TeamRating = bin_packing_load(Team, Rating);
var 0..boards*maxRating: balance = max(TeamRating) - min(TeamRating);

var 0..requests: happiness = 
    2 * sum(r in 1..doubleRequests)(
            bool2int(Team[DoubleRequested[r,1]] = Team[DoubleRequested[r,2]])
        ) 
    +   sum(r in 1..singleRequests)(
            bool2int(Team[SingleRequested[r,1]] = Team[SingleRequested[r,2]])
        );


%--------------Constraints--------------

constraint forall(b in 1..boards)(
    alldifferent([Team[(b-1)*teams+t] | t in 1..teams])
);

constraint redundant_constraint(
    bin_packing(boards, Team, [1 | i in 1..players])
);

constraint symmetry_breaking_constraint(
    forall(t in 1..teams)(
        Team[t] = t
    )
);

constraint objective = 1000 * happiness - balance;

%---------------Objective-------------

int: lb_obj = -boards*maxRating;
int: ub_obj = 1000 * requests;
var lb_obj..ub_obj: objective;

solve 
    :: int_search(Team, input_order, indomain_min, complete) 
    maximize objective;

%-----------------Output--------------

output [
    "Team = \(Team);\n",
    "objective = \(objective);\n"
];
