%------------------------------------------------------------------------------%
% Soccer Computational Problem (Position in Ranking Problem)
%
% See README file for a detail description.
%
% Submission by:
%   Robinson Duque (robinson.duque@correounivalle.edu.co)
%   Alejandro Arbelaez (alejandro.arbelaez@insight-centre.org)
%   Juan Francisco Díaz (juanfco.diaz@correounivalle.edu.co)
%
% Modification by MiniZinc team:
%   - Beautification of model
%   - Output adjustments
%
%------------------------------------------------------------------------------%
% Includes

include "alldifferent.mzn";

%------------------------------------------------------------------------------%
% Parameters

int: n;     % Number of teams
set of int: TEAMS = 1..n;
array[TEAMS] of int: iPoints;   % Initial points
array[int,int] of int: games;   % Games to play
array[int,int] of int: positionConstraints; % Position constraints

set of int: pt = {0, 1, 3};
set of int: numberOfGames = 1..(length(games) div 2);

    % Determining the bounds on the fPoints variables
    %
int: min_fPoints = min(i in TEAMS)(iPoints[i] + sum(j in numberOfGames where i = games[j,1] \/ i = games[j,2])(min(pt)));
int: max_fPoints = max(i in TEAMS)(iPoints[i] + sum(j in numberOfGames where i = games[j,1] \/ i = games[j,2])(max(pt)));
set of int: DfPoints = min_fPoints..max_fPoints;

%------------------------------------------------------------------------------%
% Decision Variables

array[numberOfGames, 1..2] of var pt: points;

array[TEAMS] of var DfPoints: fPoints;          % Final points of a team
array[TEAMS] of var    TEAMS: finalPosition;    % Final position of a team
array[TEAMS] of var    TEAMS: bestPosition;     % Best position of a team
array[TEAMS] of var    TEAMS: worstPosition;    % Worst position of a team


%------------------------------------------------------------------------------%
% Constraints

    % The addition of the points of team 1 and 2 must be a valid point 
    % assignment (0,3), (3,0) or (1,1):
constraint forall(g in numberOfGames)(
    points[g,1] + points[g,2] >= 2 
/\  points[g,1] + points[g,2] <= 3
);

    % The final points of team i are the addition of its initial points and 
    % the points it gets in the games.
constraint forall(i in TEAMS)( 
    fPoints[i] = iPoints[i] 
               + sum(j in numberOfGames where i = games[j,1] \/ i = games[j,2])(
                    if i = games[j,1] then
                        points[j,1]
                    else
                        points[j,2]
                    endif
                )
);


    % The worst position of team i is given by the number of teams with greater 
    % total points than team i
constraint forall(i, j in TEAMS)( 
    worstPosition[i] = sum(j in TEAMS)( bool2int(fPoints[j] >= fPoints[i]) ) 
);

    % The best position of team i is given by the subtraction of the worst position 
    % and the number of teams with equal points as i.
constraint forall(i, j in TEAMS)( 
    bestPosition[i] = worstPosition[i] 
                    - sum(j in TEAMS where i != j)(
                        bool2int(fPoints[j] == fPoints[i])
                      ) 
);

    % The position of a team is bounded by the worst and best position that 
    % it can take.
constraint forall(i in TEAMS)(
    finalPosition[i] >= bestPosition[i] 
/\  finalPosition[i] <= worstPosition[i]
);

    % All the final positions must be different
    %
constraint alldifferent(finalPosition);


%POSITION CONSTRAINTS & REDUNDANT CONSTRAINTS
int: numberPositionConstraints = length(positionConstraints) div 3; %Find out the number of position constraints

constraint forall(i in 1..numberPositionConstraints) (
    if positionConstraints[i,2] = 1 then
        finalPosition[positionConstraints[i,1]] = positionConstraints[i,3]
    /\  sum(j in TEAMS where positionConstraints[i,1] != j)(
            bool2int(fPoints[j] > fPoints[positionConstraints[i,1]])
        ) < positionConstraints[i,3]
    /\  sum(j in TEAMS where positionConstraints[i,1] != j)(
            bool2int(fPoints[j] < fPoints[positionConstraints[i,1]])
        ) <= (n - positionConstraints[i,3] + 1)
    elseif positionConstraints[i,2] = 2 then
        finalPosition[positionConstraints[i,1]] > positionConstraints[i,3]
    /\  sum(j in TEAMS where positionConstraints[i,1] != j)(
            bool2int(fPoints[j] < fPoints[positionConstraints[i,1]])
        ) < (n - positionConstraints[i,3])
    elseif positionConstraints[i,2] = 3 then
        finalPosition[positionConstraints[i,1]] >= positionConstraints[i,3]
    /\  sum(j in TEAMS where positionConstraints[i,1] != j)(
            bool2int(fPoints[j] < fPoints[positionConstraints[i,1]])
        ) <= (n - positionConstraints[i,3])
    elseif positionConstraints[i,2] = 4 then
        finalPosition[positionConstraints[i,1]] < positionConstraints[i,3]
    /\  sum(j in TEAMS where positionConstraints[i,1] != j)(
            bool2int(fPoints[j] > fPoints[positionConstraints[i,1]])
        ) < (positionConstraints[i,3]-1)
    else
        finalPosition[positionConstraints[i,1]] <= positionConstraints[i,3]
    /\  sum(j in TEAMS where positionConstraints[i,1] != j)(
            bool2int(fPoints[j] > fPoints[positionConstraints[i,1]])
        ) <= (positionConstraints[i,3] - 1)
    endif
);

%------------------------------------------------------------------------------%
% Solve item and search

solve 
    :: seq_search([
        int_search(finalPosition, first_fail, indomain_split, complete),
        int_search(array1d(points), first_fail, indomain_split, complete),
        int_search(bestPosition, first_fail, indomain_max, complete),
        int_search(worstPosition, first_fail, indomain_min, complete),
    ])
    satisfy;

%------------------------------------------------------------------------------%
% Output item

output [
    "% Game Results:\n",
	"% Team1 \tpts \tTeam2 \tpts: \n" 
] ++ [
    if j = 1 then "% " else "" endif
    ++ show_int(2, games[i,j])
    ++ "\t" 
    ++ show_int(2, points[i,j]) 
    ++ "\t" 
    ++ if j = 2 then "\n" else " " endif 
| i in numberOfGames, j in 1..2
] ++ [
    "points = array2d(\(numberOfGames), 1..2, \(points));\n",
    "fPoints = \(fPoints);\n",
    "finalPosition = \(finalPosition);\n",
    "bestPosition = \(bestPosition);\n",
    "worstPosition = \(worstPosition);\n",
];

%------------------------------------------------------------------------------%

