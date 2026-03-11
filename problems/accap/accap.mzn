%------------------------------------------------------------------------------
% Airport Check-in Counter Allocation Problem (ACCAP) with fixed opening/closing times
%------------------------------------------------------------------------------
% 
% Airports have certain number of check-in counters that can be used by any airlines(common-use
% check-in counters) throughout the day. Airlines need to start and end  the check-in operations
% for their flights at given times before the departure time of the flights. Each flight has a
% given time interval/duration (opDur) that they need to keep the check-in open, and this is
% fixed for the whole duration of the check-in. Given the number of airlines, their flights
% (FLIGHTS), starting time of each check-in (xCoor) ,required number of counters (cNum), and
% duration of the check-in (opDur), the objective is to find such an allocation  of flights
% (check-ins) to counters (yCoor: starting counter ID ) to minimise the maximum used number of
% counters throughout the day (D), as well as making sure that the flights of the same airlines
% are clustered in the same check-in area by minimising the sum of the total distances (S)
% between the counters of each pair of flights of the same airline (S).
%
%
%------------------------------------------------------------------------------
% Includes

include "diffn.mzn";

%------------------------------------------------------------------------------
% Sets and indices

% set of flights
int: flights;
set of int: FLIGHT = 1..flights;

% time intervals
int: times; 
set of int: TIME = 1..times;

% set of counter IDs
set of int: COUNTER = 1..sum(cNum);

% set of airlines
int: airlines;
set of int: AIRLINE = 1..airlines;

% set of flights of airlines
array[AIRLINE] of set of FLIGHT: FA; 

% set of steart-end check-in times of flights
array[FLIGHT] of set of TIME: ISet = 
    [ {k| k in xCoor[f]..(opDur[f] + xCoor[f] - 1)} | f in FLIGHT];

%------------------------------------------------------------------------------
% Variables and parameters

array[FLIGHT] of int: xCoor;           %starting time
array[FLIGHT] of var COUNTER: yCoor;   %lower-bottom corner of the rectangle (counter) : variable
array[FLIGHT] of int: opDur;           %Length - opening Duration
array[FLIGHT] of int: cNum;            %Height - required numebr of counters
var max(cNum)..((airlines + 1) * sum(cNum)): objective;   %objective: variable

% Distance between two flights :variable
array[AIRLINE] of var 0..sum(cNum): S;  

% Domain of D(maximum counter use) :variable
var max(cNum)..sum(cNum): D; 

%------------------------------------------------------------------------------
% Constraints

% C1: Non-overlapping constraint
constraint diffn(xCoor, yCoor, opDur, cNum); 

% C2: Capacity constraint
constraint forall(f in FLIGHT)( (yCoor[f] + cNum[f] - 1) <= D ); 

% C3: Distance constraint
constraint forall(a in AIRLINE, f, g in FA[a] where f != g)(
    ((yCoor[f] + cNum[f] - 1) - (yCoor[g]) <= S[a])
);  
 
% C4: Objective function
constraint objective = sum(a in AIRLINE)(S[a]) + D;

%------------------------------------------------------------------------------
% Solve item

solve 
    :: seq_search([
        int_search(yCoor, first_fail, indomain_min, complete),
        int_search(S, first_fail, indomain_min, complete),
        int_search([D], input_order, indomain_min, complete)
    ])
    minimize objective;

%------------------------------------------------------------------------------
% Output

output [
    "yCoor = \(yCoor);\n",
    "S = \(S);\n",
    "D = \(D);\n",
    "objective = \(objective);\n"
];


