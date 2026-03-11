%-----------------------------------------------------------------------------%
% Model example for Resource-Constrained Project Scheduling Problems (RCPSP)
%
% A RCPSP consists of resources, tasks, and precedences between some tasks 
% where resources have of a specific capacity and tasks need some capacity of 
% some resource to be executed.
% Here, we consider resources with a constant discrete capacity over time and
% tasks with a constant discrete duration and resource requirements.
% The objective is to find a optimal schedule with respect to the earliest end
% time of the schedule where the tasks' resource requirements do not exceed
% the resource capacities to any time and each precedence is met.
%
%-----------------------------------------------------------------------------%

include "globals.mzn";

%-----------------------------------------------------------------------------%
% Model parameters.
%

% Resource parameters
%
int: n_res;							% The number of resources
set of int: Res = 1..n_res;			% Set of resources
array [Res] of int: rc;             % The resource capacities

% Task parameters
%
int: n_tasks;                       % The number of tasks
set of int: Tasks = 1..n_tasks;		% Set of tasks
array [Tasks] of int: d;            % The task durations
int: sum_d = sum(d);    			% The total duration
array [Res, Tasks] of int: rr;     	% The resource requirements
array [Tasks] of set of int: suc;	% The task successors

%-----------------------------------------------------------------------------%
% Model variables.
%
array [Tasks] of var 0..sum_d: s;       % The start times
var 0..sum_d: objective;                       % The total end time (makespan)


%-----------------------------------------------------------------------------%
% Constraints.
%

	% successor constraints
constraint
	forall(i in Tasks, j in suc[i])(
    	s[i] + d[i] <= s[j]
   	);

	% Redundant non-overlapping constraints
constraint
	forall(i, j in Tasks where i < j)(
		if exists(r in Res)(rr[r,i] + rr[r,j] > rc[r]) then
			let {var bool: b} in (
				(    b  -> s[i] + d[i] <= s[j])
			/\	(not(b) -> s[j] + d[j] <= s[i])
			)
		else
			true
		endif
	);

	% cumulative resource constraints
constraint
   	forall(r in Res)(
      	cumulative(s, d, [rr[r,i] | i in Tasks], rc[r])
	);

	% makespan constraints
constraint
   	forall(i in Tasks)(
    	s[i] + d[i] <= objective
   	);

%-----------------------------------------------------------------------------%
% Objective.
%
solve
   	:: seq_search([
   		int_search(s, smallest, indomain_min, complete),
		int_search([objective], input_order, indomain_min, complete)
	])
   	minimize objective;

output [
   "s = ", show(s), ";\n",
   "objective = ", show(objective), ";\n"
];

%-----------------------------------------------------------------------------%
%%% EOF %%%

