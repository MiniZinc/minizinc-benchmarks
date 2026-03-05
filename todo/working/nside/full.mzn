% N-SITE problem
% Road Network Maintenance Problem
%
% Determine which worksheets to execute on which day so that the road network is not perterbed too much
% Each worksheet is a contiguous set of daily tasks on roads: specified by a road and number of workers
% Worksheets have an importance defining how important they are to execute
% 
% Constraints to satisfy are:
%     Earliest and latest start times of worksheets
%     Not too many workers from each work center on any day
%     For each of a number of given sets of roads never blocking more than a given amount 
%     Some worksheets must be executed
%     Precedence rules between pairs of worksheets
% PARAMETERS
int: days;                                % number of dayso
set of int: DAY = 0..days-1;
int: roads;                               % number of roads
int: centers;                             % number of centers
int: worksheets;                          % number of worksheets
int: activities;                          % number of activities

set of int: ROAD = 0..roads-1;
set of int: ROAD0 = -1..roads-1; 
array[ROAD0,DAY] of int: perterb;         % perturbation cost of road on each day

set of int: CENTER = 0..centers-1;        % index set for centers
array [CENTER] of int: c_id;              % id of each center
array [CENTER] of int: available_workers; % number of available workers per center

set of int: WORKSHEET = 0..worksheets-1;  % index set for workseets
array [WORKSHEET] of int: w_id;           % id of each worksheet
array [WORKSHEET] of int: work_center;    % id of the work center where used by each worksheet 
array [WORKSHEET] of 0..1: mandatory;     % whether each worksheet is mandatory
array [WORKSHEET] of int: importance;     % importance of each worksheet
array [WORKSHEET] of int: est;            % earliest starting time for each worksheet
array [WORKSHEET] of int: lst;            % latest starting time for each worksheet
array [WORKSHEET] of int: duration;       % duration in days of each worksheet
set of int: ACTIVITY = 0..activities-1;
array [WORKSHEET,ACTIVITY] of ROAD0: road;  % road used by each worksheet on a given day -1 = none
array [WORKSHEET,ACTIVITY] of int: workers; % number of workers used by each worksheet on a given day

int: blocked_max;                         % number of maximum blocked rules for this instance
set of int: BLOCKED = 1..blocked_max;     % index set for maximum blocked rules
array [BLOCKED] of ROAD: blocked_max_amount;    % max amount of roads that can be blocked of a given set
array [BLOCKED] of set of ROAD: blocked_roads;  % the set of roads that the max amount refers to

int: precedences;                         % number of precedence rules for this instance
set of int: PREC = 1..precedences;        % index set for the precedence rules
array [PREC] of WORKSHEET: preceeds;      % the predecessor worksheet in a given rule
array [PREC] of WORKSHEET: succeeds;      % the successor worksheet in a given rule


% DECISION VARIABLES
array [WORKSHEET] of var 0..1: g;         % 1 if the worksheet is executed

array [WORKSHEET] of var DAY: d;          % start time of worksheet 
array [WORKSHEET] of var DAY: e = array1d(WORKSHEET,[ d[w] + duration[w] | w in WORKSHEET ]);  % end time of worksheet 
% Fixing unused variables 
constraint forall(w in WORKSHEET)(g[w] = 0 <-> d[w] = est[w]);  

% Fits in schedule
constraint forall(w in WORKSHEET)(e[w] <= days);


% CONSTRAINTS
% Precedences within Worksheet

% Worksheet Earliest Starting Time
constraint forall (w in WORKSHEET) (est[w] <= d[w]);

% Worksheet Latest Starting Time
constraint forall (w in WORKSHEET) (d[w] <= lst[w]);

% Complete WORKSHEET

% Mandatory WORKSHEET
constraint forall (w in WORKSHEET) (g[w] >= mandatory[w]);

% Precedence Between Worksheets
% if both worksheets execute then the end of w1 is before the start of w2
constraint forall (i in PREC)
                  (let { WORKSHEET: w1 = preceeds[i];
		                     WORKSHEET: w2 = succeeds[i]; } in
                   g[w1] * e[w1] <= d[w2] + days * (1 - g[w2]));


% Maximal Number of Roads Simultaneously Blocked
include "global_cardinality_low_up.mzn";
constraint forall(b in BLOCKED)(
    global_cardinality_low_up(
        [ (d[w] + a + 1)*g[w]        %% add one to separate 0 = not executed
		| w in WORKSHEET, a in 0..duration[w]-1 where road[w,a] in blocked_roads[b]], 
		[ d + 1 | d in DAY],         %% looking for day + 1
		[ 0 | d in DAY],
		[blocked_max_amount[b] |d in DAY]
    )
);
				                                  

% Work Center Capacity
include "cumulative.mzn";
constraint forall(c in CENTER)
                 ( if length([w | w in WORKSHEET where work_center[w] = c]) > 0 then
                   cumulative([ d[w] + a
		                         | w in WORKSHEET where work_center[w] = c, a in 0..duration[w] - 1 ],
			                       [ g[w]
		                         | w in WORKSHEET where work_center[w] = c, a in 0..duration[w] - 1 ],
			                       [ workers[w,a] | w in WORKSHEET where work_center[w] = c,
			                                        a in 0..duration[w]-1 ],
			                       available_workers[c])
			             else true endif);

% OBJECTIVE               
var 0..worksheets * max(importance): importance_obj = sum (w in WORKSHEET) (g[w]*importance[w]);
int: perterb_obj_ub = max(array1d(perterb)) * days;
var 0..perterb_obj_ub: perterb_obj = max(i in DAY)(
    sum(w in WORKSHEET, a in 0..duration[w]-1)(
        g[w] * perterb[road[w,a], i] * (i = d[w]+a)
    )
);                            
var -ub(perterb_obj)..ub(importance_obj): objective; 
constraint objective = importance_obj - perterb_obj;
                           
array[int] of int: import_first = reverse(arg_sort(importance));                         
                           
solve 
    :: int_search(
        [ if j = 1 then g[import_first[i]] else -d[import_first[i]] endif  | i in 1..worksheets, j in 1..2], 
        input_order, indomain_max, complete)
    maximize objective;


output [
    "g = array1d(\(WORKSHEET), \(g));\n",
    "d = array1d(\(WORKSHEET), \(d));\n",
    "objective = \(objective);\n"
];
